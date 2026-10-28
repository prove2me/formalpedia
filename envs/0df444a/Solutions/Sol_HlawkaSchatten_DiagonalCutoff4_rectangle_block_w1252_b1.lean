-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1252_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:23:56.511288+00:00
-- url     : https://prove2.me/submissions/4f259eff-fcc5-4b72-bdf4-b781e19e5c8e

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
theorem support_rectangle_w1252_s3_0 (p : ℝ) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-66018843/312500000 : ℝ)*x 0 + (1083757413/2000000000 : ℝ)*x 1 + (524138329/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66018843/312500000 : ℝ)^8445 ≤ (642137881157/5000000000000 : ℝ)^6397 := by
    have hnat : (66018843 : ℕ)^8445*5000000000000^6397 ≤ 642137881157^6397*312500000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66018843 312500000 642137881157 5000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1083757413/2000000000 : ℝ)^8445 ≤ (4453596011727/10000000000000 : ℝ)^6397 := by
    have hnat : (1083757413 : ℕ)^8445*10000000000000^6397 ≤ 4453596011727^6397*2000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083757413 2000000000 4453596011727 10000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524138329/1000000000 : ℝ)^8445 ≤ (42621282257127/100000000000000 : ℝ)^6397 := by
    have hnat : (524138329 : ℕ)^8445*100000000000000^6397 ≤ 42621282257127^6397*1000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524138329 1000000000 42621282257127 100000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8445/2048 : ℝ)) 8445 6397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-66018843/312500000 : ℝ), (1083757413/2000000000 : ℝ), (524138329/1000000000 : ℝ)] ![(642137881157/5000000000000 : ℝ), (4453596011727/10000000000000 : ℝ), (42621282257127/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-66018843/312500000 : ℝ)|^8445 ≤ (642137881157/5000000000000 : ℝ)^6397
        have hw : |(-66018843/312500000 : ℝ)|=(66018843/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1083757413/2000000000 : ℝ)|^8445 ≤ (4453596011727/10000000000000 : ℝ)^6397
        have hw : |(1083757413/2000000000 : ℝ)|=(1083757413/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(524138329/1000000000 : ℝ)|^8445 ≤ (42621282257127/100000000000000 : ℝ)^6397
        have hw : |(524138329/1000000000 : ℝ)|=(524138329/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1252_s3_1 (p : ℝ) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2675635009/5000000000 : ℝ)*x 0 + (-1101543551/5000000000 : ℝ)*x 1 + (5241383389/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675635009/5000000000 : ℝ)^8445 ≤ (2737803845529/6250000000000 : ℝ)^6397 := by
    have hnat : (2675635009 : ℕ)^8445*6250000000000^6397 ≤ 2737803845529^6397*5000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675635009 5000000000 2737803845529 6250000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1101543551/5000000000 : ℝ)^8445 ≤ (1357385514231/10000000000000 : ℝ)^6397 := by
    have hnat : (1101543551 : ℕ)^8445*10000000000000^6397 ≤ 1357385514231^6397*5000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101543551 5000000000 1357385514231 10000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5241383389/10000000000 : ℝ)^8445 ≤ (42621283319897/100000000000000 : ℝ)^6397 := by
    have hnat : (5241383389 : ℕ)^8445*100000000000000^6397 ≤ 42621283319897^6397*10000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241383389 10000000000 42621283319897 100000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8445/2048 : ℝ)) 8445 6397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675635009/5000000000 : ℝ), (-1101543551/5000000000 : ℝ), (5241383389/10000000000 : ℝ)] ![(2737803845529/6250000000000 : ℝ), (1357385514231/10000000000000 : ℝ), (42621283319897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675635009/5000000000 : ℝ)|^8445 ≤ (2737803845529/6250000000000 : ℝ)^6397
        have hw : |(2675635009/5000000000 : ℝ)|=(2675635009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1101543551/5000000000 : ℝ)|^8445 ≤ (1357385514231/10000000000000 : ℝ)^6397
        have hw : |(-1101543551/5000000000 : ℝ)|=(1101543551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5241383389/10000000000 : ℝ)|^8445 ≤ (42621283319897/100000000000000 : ℝ)^6397
        have hw : |(5241383389/10000000000 : ℝ)|=(5241383389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1252_s3_2 (p : ℝ) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1337817493/2500000000 : ℝ)*x 0 + (5241383851/10000000000 : ℝ)*x 1 + (-275385819/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337817493/2500000000 : ℝ)^8445 ≤ (43804861031361/100000000000000 : ℝ)^6397 := by
    have hnat : (1337817493 : ℕ)^8445*100000000000000^6397 ≤ 43804861031361^6397*2500000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337817493 2500000000 43804861031361 100000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5241383851/10000000000 : ℝ)^8445 ≤ (665957629367/1562500000000 : ℝ)^6397 := by
    have hnat : (5241383851 : ℕ)^8445*1562500000000^6397 ≤ 665957629367^6397*10000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241383851 10000000000 665957629367 1562500000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (275385819/1250000000 : ℝ)^8445 ≤ (6786925334353/50000000000000 : ℝ)^6397 := by
    have hnat : (275385819 : ℕ)^8445*50000000000000^6397 ≤ 6786925334353^6397*1250000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275385819 1250000000 6786925334353 50000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8445/2048 : ℝ)) 8445 6397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337817493/2500000000 : ℝ), (5241383851/10000000000 : ℝ), (-275385819/1250000000 : ℝ)] ![(43804861031361/100000000000000 : ℝ), (665957629367/1562500000000 : ℝ), (6786925334353/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337817493/2500000000 : ℝ)|^8445 ≤ (43804861031361/100000000000000 : ℝ)^6397
        have hw : |(1337817493/2500000000 : ℝ)|=(1337817493/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5241383851/10000000000 : ℝ)|^8445 ≤ (665957629367/1562500000000 : ℝ)^6397
        have hw : |(5241383851/10000000000 : ℝ)|=(5241383851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-275385819/1250000000 : ℝ)|^8445 ≤ (6786925334353/50000000000000 : ℝ)^6397
        have hw : |(-275385819/1250000000 : ℝ)|=(275385819/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1252_s3_3 (p : ℝ) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (217387641/500000000 : ℝ)*x 0 + (4171090307/10000000000 : ℝ)*x 1 + (1132914939/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (217387641/500000000 : ℝ)^8445 ≤ (16650424667049/50000000000000 : ℝ)^6397 := by
    have hnat : (217387641 : ℕ)^8445*50000000000000^6397 ≤ 16650424667049^6397*500000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217387641 500000000 16650424667049 50000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4171090307/10000000000 : ℝ)^8445 ≤ (3152626146783/10000000000000 : ℝ)^6397 := by
    have hnat : (4171090307 : ℕ)^8445*10000000000000^6397 ≤ 3152626146783^6397*10000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171090307 10000000000 3152626146783 10000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1132914939/2500000000 : ℝ)^8445 ≤ (35172889179839/100000000000000 : ℝ)^6397 := by
    have hnat : (1132914939 : ℕ)^8445*100000000000000^6397 ≤ 35172889179839^6397*2500000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1132914939 2500000000 35172889179839 100000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8445/2048 : ℝ)) 8445 6397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(217387641/500000000 : ℝ), (4171090307/10000000000 : ℝ), (1132914939/2500000000 : ℝ)] ![(16650424667049/50000000000000 : ℝ), (3152626146783/10000000000000 : ℝ), (35172889179839/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(217387641/500000000 : ℝ)|^8445 ≤ (16650424667049/50000000000000 : ℝ)^6397
        have hw : |(217387641/500000000 : ℝ)|=(217387641/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4171090307/10000000000 : ℝ)|^8445 ≤ (3152626146783/10000000000000 : ℝ)^6397
        have hw : |(4171090307/10000000000 : ℝ)|=(4171090307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1132914939/2500000000 : ℝ)|^8445 ≤ (35172889179839/100000000000000 : ℝ)^6397
        have hw : |(1132914939/2500000000 : ℝ)|=(1132914939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1252_s3_4 (p : ℝ) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1056308597/5000000000 : ℝ)*x 0 + (1310506007/2500000000 : ℝ)*x 1 + (5418142577/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1056308597/5000000000 : ℝ)^8445 ≤ (25083733843/195312500000 : ℝ)^6397 := by
    have hnat : (1056308597 : ℕ)^8445*195312500000^6397 ≤ 25083733843^6397*5000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056308597 5000000000 25083733843 195312500000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310506007/2500000000 : ℝ)^8445 ≤ (10657040185847/25000000000000 : ℝ)^6397 := by
    have hnat : (1310506007 : ℕ)^8445*25000000000000^6397 ≤ 10657040185847^6397*2500000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310506007 2500000000 10657040185847 25000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5418142577/10000000000 : ℝ)^8445 ≤ (4452896751859/10000000000000 : ℝ)^6397 := by
    have hnat : (5418142577 : ℕ)^8445*10000000000000^6397 ≤ 4452896751859^6397*10000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5418142577 10000000000 4452896751859 10000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8445/2048 : ℝ)) 8445 6397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1056308597/5000000000 : ℝ), (1310506007/2500000000 : ℝ), (5418142577/10000000000 : ℝ)] ![(25083733843/195312500000 : ℝ), (10657040185847/25000000000000 : ℝ), (4452896751859/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1056308597/5000000000 : ℝ)|^8445 ≤ (25083733843/195312500000 : ℝ)^6397
        have hw : |(-1056308597/5000000000 : ℝ)|=(1056308597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310506007/2500000000 : ℝ)|^8445 ≤ (10657040185847/25000000000000 : ℝ)^6397
        have hw : |(1310506007/2500000000 : ℝ)|=(1310506007/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5418142577/10000000000 : ℝ)|^8445 ≤ (4452896751859/10000000000000 : ℝ)^6397
        have hw : |(5418142577/10000000000 : ℝ)|=(5418142577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1252_s3_5 (p : ℝ) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2652990201/5000000000 : ℝ)*x 0 + (-63322729/312500000 : ℝ)*x 1 + (1083628483/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652990201/5000000000 : ℝ)^8445 ≤ (2707256216807/6250000000000 : ℝ)^6397 := by
    have hnat : (2652990201 : ℕ)^8445*6250000000000^6397 ≤ 2707256216807^6397*5000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652990201 5000000000 2707256216807 6250000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (63322729/312500000 : ℝ)^8445 ≤ (303873368701/2500000000000 : ℝ)^6397 := by
    have hnat : (63322729 : ℕ)^8445*2500000000000^6397 ≤ 303873368701^6397*312500000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63322729 312500000 303873368701 2500000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1083628483/2000000000 : ℝ)^8445 ≤ (11132241440237/25000000000000 : ℝ)^6397 := by
    have hnat : (1083628483 : ℕ)^8445*25000000000000^6397 ≤ 11132241440237^6397*2000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083628483 2000000000 11132241440237 25000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8445/2048 : ℝ)) 8445 6397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652990201/5000000000 : ℝ), (-63322729/312500000 : ℝ), (1083628483/2000000000 : ℝ)] ![(2707256216807/6250000000000 : ℝ), (303873368701/2500000000000 : ℝ), (11132241440237/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652990201/5000000000 : ℝ)|^8445 ≤ (2707256216807/6250000000000 : ℝ)^6397
        have hw : |(2652990201/5000000000 : ℝ)|=(2652990201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-63322729/312500000 : ℝ)|^8445 ≤ (303873368701/2500000000000 : ℝ)^6397
        have hw : |(-63322729/312500000 : ℝ)|=(63322729/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1083628483/2000000000 : ℝ)|^8445 ≤ (11132241440237/25000000000000 : ℝ)^6397
        have hw : |(1083628483/2000000000 : ℝ)|=(1083628483/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1252_s3_6 (p : ℝ) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (165811867/312500000 : ℝ)*x 0 + (5418142893/10000000000 : ℝ)*x 1 + (-2026327569/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165811867/312500000 : ℝ)^8445 ≤ (21658046188749/50000000000000 : ℝ)^6397 := by
    have hnat : (165811867 : ℕ)^8445*50000000000000^6397 ≤ 21658046188749^6397*312500000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165811867 312500000 21658046188749 50000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5418142893/10000000000 : ℝ)^8445 ≤ (22264485473539/50000000000000 : ℝ)^6397 := by
    have hnat : (5418142893 : ℕ)^8445*50000000000000^6397 ≤ 22264485473539^6397*10000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5418142893 10000000000 22264485473539 50000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2026327569/10000000000 : ℝ)^8445 ≤ (12154936656501/100000000000000 : ℝ)^6397 := by
    have hnat : (2026327569 : ℕ)^8445*100000000000000^6397 ≤ 12154936656501^6397*10000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2026327569 10000000000 12154936656501 100000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8445/2048 : ℝ)) 8445 6397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165811867/312500000 : ℝ), (5418142893/10000000000 : ℝ), (-2026327569/10000000000 : ℝ)] ![(21658046188749/50000000000000 : ℝ), (22264485473539/50000000000000 : ℝ), (12154936656501/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165811867/312500000 : ℝ)|^8445 ≤ (21658046188749/50000000000000 : ℝ)^6397
        have hw : |(165811867/312500000 : ℝ)|=(165811867/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5418142893/10000000000 : ℝ)|^8445 ≤ (22264485473539/50000000000000 : ℝ)^6397
        have hw : |(5418142893/10000000000 : ℝ)|=(5418142893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2026327569/10000000000 : ℝ)|^8445 ≤ (12154936656501/100000000000000 : ℝ)^6397
        have hw : |(-2026327569/10000000000 : ℝ)|=(2026327569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1252_s3_7 (p : ℝ) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4347781317/10000000000 : ℝ)*x 0 + (906071329/2000000000 : ℝ)*x 1 + (2086199733/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4347781317/10000000000 : ℝ)^8445 ≤ (33301137480609/100000000000000 : ℝ)^6397 := by
    have hnat : (4347781317 : ℕ)^8445*100000000000000^6397 ≤ 33301137480609^6397*10000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4347781317 10000000000 33301137480609 100000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (906071329/2000000000 : ℝ)^8445 ≤ (35159537513517/100000000000000 : ℝ)^6397 := by
    have hnat : (906071329 : ℕ)^8445*100000000000000^6397 ≤ 35159537513517^6397*2000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      906071329 2000000000 35159537513517 100000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2086199733/5000000000 : ℝ)^8445 ≤ (15769662496659/50000000000000 : ℝ)^6397 := by
    have hnat : (2086199733 : ℕ)^8445*50000000000000^6397 ≤ 15769662496659^6397*5000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086199733 5000000000 15769662496659 50000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8445/2048 : ℝ)) 8445 6397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4347781317/10000000000 : ℝ), (906071329/2000000000 : ℝ), (2086199733/5000000000 : ℝ)] ![(33301137480609/100000000000000 : ℝ), (35159537513517/100000000000000 : ℝ), (15769662496659/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4347781317/10000000000 : ℝ)|^8445 ≤ (33301137480609/100000000000000 : ℝ)^6397
        have hw : |(4347781317/10000000000 : ℝ)|=(4347781317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(906071329/2000000000 : ℝ)|^8445 ≤ (35159537513517/100000000000000 : ℝ)^6397
        have hw : |(906071329/2000000000 : ℝ)|=(906071329/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2086199733/5000000000 : ℝ)|^8445 ≤ (15769662496659/50000000000000 : ℝ)^6397
        have hw : |(2086199733/5000000000 : ℝ)|=(2086199733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1252_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151624409/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16197/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (477/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (10937/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3673/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16197/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (477/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16197/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (477/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16197/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (477/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16197/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (477/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16197/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (477/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16197/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (477/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (477/5000 : ℝ) ^ (2111/512 : ℝ) ≤ (620340470689239/10000000000000000000 : ℝ) := by
    have hpowers : (477/5000 : ℝ)^2111 ≤ (620340470689239/10000000000000000000 : ℝ)^512 := by
      have hnat : (477 : ℕ)^2111*10000000000000000000^512 ≤ 620340470689239^512*5000^2111 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        477 5000 620340470689239 10000000000000000000 2111 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (477/5000 : ℝ)) (X := (620340470689239/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2111 512 (by norm_num) hpowers
    exact h
  have hpowhi : (16197/100000 : ℝ) ^ (2111/512 : ℝ) ≤ (55012543454255177/100000000000000000000 : ℝ) := by
    have hpowers : (16197/100000 : ℝ)^2111 ≤ (55012543454255177/100000000000000000000 : ℝ)^512 := by
      have hnat : (16197 : ℕ)^2111*100000000000000000000^512 ≤ 55012543454255177^512*100000^2111 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16197 100000 55012543454255177 100000000000000000000 2111 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16197/100000 : ℝ)) (X := (55012543454255177/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2111 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000620340470689239/5000000000000000000 : ℝ) ≤ (1000030089947693/1000000000000000 : ℝ) ^ (2111/512 : ℝ) := by
    have hpowers : (5000620340470689239/5000000000000000000 : ℝ)^512 ≤ (1000030089947693/1000000000000000 : ℝ)^2111 := by
      have hnat : (5000620340470689239 : ℕ)^512*1000000000000000^2111 ≤ 1000030089947693^2111*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000620340470689239 5000000000000000000 1000030089947693 1000000000000000 512 2111 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000030089947693/1000000000000000 : ℝ)) (X := (5000620340470689239/5000000000000000000 : ℝ)) (by norm_num) 2111 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100061215948161147567/100000000000000000000 : ℝ) ≤ (1250185547735049/1250000000000000 : ℝ) ^ (2111/512 : ℝ) := by
    have hpowers : (100061215948161147567/100000000000000000000 : ℝ)^512 ≤ (1250185547735049/1250000000000000 : ℝ)^2111 := by
      have hnat : (100061215948161147567 : ℕ)^512*1250000000000000^2111 ≤ 1250185547735049^2111*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100061215948161147567 100000000000000000000 1250185547735049 1250000000000000 512 2111 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250185547735049/1250000000000000 : ℝ)) (X := (100061215948161147567/100000000000000000000 : ℝ)) (by norm_num) 2111 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50055012543454255177/50000000000000000000 : ℝ) ≤ (5001333932141927/5000000000000000 : ℝ) ^ (2111/512 : ℝ) := by
    have hpowers : (50055012543454255177/50000000000000000000 : ℝ)^512 ≤ (5001333932141927/5000000000000000 : ℝ)^2111 := by
      have hnat : (50055012543454255177 : ℕ)^512*5000000000000000^2111 ≤ 5001333932141927^2111*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50055012543454255177 50000000000000000000 5001333932141927 5000000000000000 512 2111 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001333932141927/5000000000000000 : ℝ)) (X := (50055012543454255177/50000000000000000000 : ℝ)) (by norm_num) 2111 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(620340470689239/10000000000000000000 : ℝ) ≤ ((443662814957065787/443800000000000000 : ℝ)+2*(591741201731/332850000000000 : ℝ)*(477/5000 : ℝ))^(2111/512 : ℝ) := by
    rw [show (443662814957065787/443800000000000000 : ℝ)+2*(591741201731/332850000000000 : ℝ)*(477/5000 : ℝ)=(1000030089947693/1000000000000000 : ℝ) by norm_num, show 1+2*(620340470689239/10000000000000000000 : ℝ)=(5000620340470689239/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(55012543454255177/100000000000000000000 : ℝ)+(620340470689239/10000000000000000000 : ℝ) ≤ ((443662814957065787/443800000000000000 : ℝ)+(591741201731/332850000000000 : ℝ)*((16197/100000 : ℝ)+(477/5000 : ℝ)))^(2111/512 : ℝ) := by
    rw [show (443662814957065787/443800000000000000 : ℝ)+(591741201731/332850000000000 : ℝ)*((16197/100000 : ℝ)+(477/5000 : ℝ))=(1250185547735049/1250000000000000 : ℝ) by norm_num, show 1+(55012543454255177/100000000000000000000 : ℝ)+(620340470689239/10000000000000000000 : ℝ)=(100061215948161147567/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(55012543454255177/100000000000000000000 : ℝ) ≤ ((443662814957065787/443800000000000000 : ℝ)+2*(591741201731/332850000000000 : ℝ)*(16197/100000 : ℝ))^(2111/512 : ℝ) := by
    rw [show (443662814957065787/443800000000000000 : ℝ)+2*(591741201731/332850000000000 : ℝ)*(16197/100000 : ℝ)=(5001333932141927/5000000000000000 : ℝ) by norm_num, show 1+2*(55012543454255177/100000000000000000000 : ℝ)=(50055012543454255177/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (443662814957065787/443800000000000000 : ℝ)*(X 1 0+X 2 0)+(591741201731/332850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2111/512 : ℝ)) (lo := (477/5000 : ℝ)) (hi := (16197/100000 : ℝ)) (c := (443662814957065787/443800000000000000 : ℝ)) (alpha := (591741201731/332850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (443662814957065787/443800000000000000 : ℝ)*(X 0 1+X 2 1)+(591741201731/332850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2111/512 : ℝ)) (lo := (477/5000 : ℝ)) (hi := (16197/100000 : ℝ)) (c := (443662814957065787/443800000000000000 : ℝ)) (alpha := (591741201731/332850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (443662814957065787/443800000000000000 : ℝ)*(X 0 2+X 1 2)+(591741201731/332850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2111/512 : ℝ)) (lo := (477/5000 : ℝ)) (hi := (16197/100000 : ℝ)) (c := (443662814957065787/443800000000000000 : ℝ)) (alpha := (591741201731/332850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-66018843/312500000 : ℝ)*X 0 0+(1083757413/2000000000 : ℝ)*X 0 1+(524138329/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1252_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675635009/5000000000 : ℝ)*X 1 0+(-1101543551/5000000000 : ℝ)*X 1 1+(5241383389/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1252_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337817493/2500000000 : ℝ)*X 2 0+(5241383851/10000000000 : ℝ)*X 2 1+(-275385819/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1252_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((217387641/500000000 : ℝ)*X 0 0+(4171090307/10000000000 : ℝ)*X 0 1+(1132914939/2500000000 : ℝ)*X 0 2+(217387641/500000000 : ℝ)*X 1 0+(4171090307/10000000000 : ℝ)*X 1 1+(1132914939/2500000000 : ℝ)*X 1 2+(217387641/500000000 : ℝ)*X 2 0+(4171090307/10000000000 : ℝ)*X 2 1+(1132914939/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1252_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1056308597/5000000000 : ℝ)*X 0 0+(1310506007/2500000000 : ℝ)*X 0 1+(5418142577/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1252_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652990201/5000000000 : ℝ)*X 1 0+(-63322729/312500000 : ℝ)*X 1 1+(1083628483/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1252_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((165811867/312500000 : ℝ)*X 2 0+(5418142893/10000000000 : ℝ)*X 2 1+(-2026327569/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1252_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4347781317/10000000000 : ℝ)*X 0 0+(906071329/2000000000 : ℝ)*X 0 1+(2086199733/5000000000 : ℝ)*X 0 2+(4347781317/10000000000 : ℝ)*X 1 0+(906071329/2000000000 : ℝ)*X 1 1+(2086199733/5000000000 : ℝ)*X 1 2+(4347781317/10000000000 : ℝ)*X 2 0+(906071329/2000000000 : ℝ)*X 2 1+(2086199733/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1252_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (37333515582700857030679837/11095000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (528101/10000000000000 : ℝ)*(base19) + (2912763/2500000000000 : ℝ)*(lower2) + (118840369/100000000000000 : ℝ)*(lower3) + (40166999/50000000000000 : ℝ)*(lower4) + (4205149029332717/100000000000000 : ℝ)*(major0) + (4205149029332717/100000000000000 : ℝ)*(major1) + (4205149029332717/100000000000000 : ℝ)*(major2) + (5636876371385263/100000000000000 : ℝ)*(sp0) + (5636886388681637/100000000000000 : ℝ)*(sp1) + (5636899483110557/100000000000000 : ℝ)*(sp2) + (1386697601676741/50000000000000 : ℝ)*(sp3) + (11555862647/50000000000000 : ℝ)*(sp4) + (13089147909/100000000000000 : ℝ)*(sp5) + (3260038199/100000000000000 : ℝ)*(sp7) + (8666870198099/312500000000 : ℝ)*(f.failure) + (5636899483110557/100000000000000 : ℝ)*(f.sum) + (208054944986461/33285000000000000000000000000 : ℝ)*base66 + (157045624983710309/19020000000000000000000000000000 : ℝ)*base68 + (210815191193270309/19020000000000000000000000000000 : ℝ)*base70 + (238367870803730309/19020000000000000000000000000000 : ℝ)*base72 + (100986373320601/33285000000000000000000000000 : ℝ)*base74 + (41144838724329691/19020000000000000000000000000000 : ℝ)*base75 + (279674660794130309/19020000000000000000000000000000 : ℝ)*base78 + (190293111457310309/19020000000000000000000000000000 : ℝ)*base80 + (12665888927401/2080312500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (264009/31250000000000000000 : ℝ)*base90 + (264009/31250000000000000000 : ℝ)*base92 + (264009/31250000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (36383234783131128151236981/5547500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1452806891/50000000000000 : ℝ)*(base19) + (561973253/25000000000000 : ℝ)*(base23) + (12805663/20000000000000 : ℝ)*(upper3) + (108619429/100000000000000 : ℝ)*(lower4) + (475973343/100000000000000 : ℝ)*(upper5) + (1058952584217579/25000000000000 : ℝ)*(major0) + (1058952584217579/25000000000000 : ℝ)*(major1) + (1058952584217579/25000000000000 : ℝ)*(major2) + (66491593907/100000000000000 : ℝ)*(sp1) + (23972649843/50000000000000 : ℝ)*(sp2) + (709750013842997/12500000000000 : ℝ)*(sp4) + (5677930713536287/100000000000000 : ℝ)*(sp5) + (2838974958775639/50000000000000 : ℝ)*(sp6) + (349202543047531/12500000000000 : ℝ)*(sp7) + (349202543047531/12500000000000 : ℝ)*(f.failure) + (709750013842997/12500000000000 : ℝ)*(f.sum) + (1034543724091/173359375000000000000000000 : ℝ)*base65 + (7529626088120239/1585000000000000000000000000000 : ℝ)*base67 + (8004158553400239/1585000000000000000000000000000 : ℝ)*base69 + (6863369708740239/1585000000000000000000000000000 : ℝ)*base71 + (39964294675107/5547500000000000000000000000 : ℝ)*base73 + (4821703978440239/1585000000000000000000000000000 : ℝ)*base75 + (10387316860799761/1585000000000000000000000000000 : ℝ)*base78 + (817432010399761/1585000000000000000000000000000 : ℝ)*base80 + (27178236913917/5547500000000000000000000000 : ℝ)*base81 + (3215821/1250000000000000000000 : ℝ)*base90 + (3215821/1250000000000000000000 : ℝ)*base92 + (3215821/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1252_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151624409/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16197/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (477/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10937/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3673/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1252_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1252_s4_0 (p : ℝ) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-422966419/2000000000 : ℝ)*x 0 + (2698547269/5000000000 : ℝ)*x 1 + (657701867/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (422966419/2000000000 : ℝ)^8445 ≤ (6430325046331/50000000000000 : ℝ)^6397 := by
    have hnat : (422966419 : ℕ)^8445*50000000000000^6397 ≤ 6430325046331^6397*2000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422966419 2000000000 6430325046331 50000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2698547269/5000000000 : ℝ)^8445 ≤ (22150372957827/50000000000000 : ℝ)^6397 := by
    have hnat : (2698547269 : ℕ)^8445*50000000000000^6397 ≤ 22150372957827^6397*5000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698547269 5000000000 22150372957827 50000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (657701867/1250000000 : ℝ)^8445 ≤ (8567720796047/20000000000000 : ℝ)^6397 := by
    have hnat : (657701867 : ℕ)^8445*20000000000000^6397 ≤ 8567720796047^6397*1250000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657701867 1250000000 8567720796047 20000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8445/2048 : ℝ)) 8445 6397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-422966419/2000000000 : ℝ), (2698547269/5000000000 : ℝ), (657701867/1250000000 : ℝ)] ![(6430325046331/50000000000000 : ℝ), (22150372957827/50000000000000 : ℝ), (8567720796047/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-422966419/2000000000 : ℝ)|^8445 ≤ (6430325046331/50000000000000 : ℝ)^6397
        have hw : |(-422966419/2000000000 : ℝ)|=(422966419/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2698547269/5000000000 : ℝ)|^8445 ≤ (22150372957827/50000000000000 : ℝ)^6397
        have hw : |(2698547269/5000000000 : ℝ)|=(2698547269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(657701867/1250000000 : ℝ)|^8445 ≤ (8567720796047/20000000000000 : ℝ)^6397
        have hw : |(657701867/1250000000 : ℝ)|=(657701867/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1252_s4_1 (p : ℝ) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345796909/10000000000 : ℝ)*x 0 + (-1091805863/5000000000 : ℝ)*x 1 + (657701867/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345796909/10000000000 : ℝ)^8445 ≤ (43745725558837/100000000000000 : ℝ)^6397 := by
    have hnat : (5345796909 : ℕ)^8445*100000000000000^6397 ≤ 43745725558837^6397*10000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345796909 10000000000 43745725558837 100000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1091805863/5000000000 : ℝ)^8445 ≤ (335391761133/2500000000000 : ℝ)^6397 := by
    have hnat : (1091805863 : ℕ)^8445*2500000000000^6397 ≤ 335391761133^6397*5000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091805863 5000000000 335391761133 2500000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (657701867/1250000000 : ℝ)^8445 ≤ (8567720796047/20000000000000 : ℝ)^6397 := by
    have hnat : (657701867 : ℕ)^8445*20000000000000^6397 ≤ 8567720796047^6397*1250000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657701867 1250000000 8567720796047 20000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8445/2048 : ℝ)) 8445 6397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345796909/10000000000 : ℝ), (-1091805863/5000000000 : ℝ), (657701867/1250000000 : ℝ)] ![(43745725558837/100000000000000 : ℝ), (335391761133/2500000000000 : ℝ), (8567720796047/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345796909/10000000000 : ℝ)|^8445 ≤ (43745725558837/100000000000000 : ℝ)^6397
        have hw : |(5345796909/10000000000 : ℝ)|=(5345796909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1091805863/5000000000 : ℝ)|^8445 ≤ (335391761133/2500000000000 : ℝ)^6397
        have hw : |(-1091805863/5000000000 : ℝ)|=(1091805863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(657701867/1250000000 : ℝ)|^8445 ≤ (8567720796047/20000000000000 : ℝ)^6397
        have hw : |(657701867/1250000000 : ℝ)|=(657701867/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1252_s4_2 (p : ℝ) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1069159389/2000000000 : ℝ)*x 0 + (2630807447/5000000000 : ℝ)*x 1 + (-2183611733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069159389/2000000000 : ℝ)^8445 ≤ (21872862973873/50000000000000 : ℝ)^6397 := by
    have hnat : (1069159389 : ℕ)^8445*50000000000000^6397 ≤ 21872862973873^6397*2000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069159389 2000000000 21872862973873 50000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2630807447/5000000000 : ℝ)^8445 ≤ (42838603528807/100000000000000 : ℝ)^6397 := by
    have hnat : (2630807447 : ℕ)^8445*100000000000000^6397 ≤ 42838603528807^6397*5000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630807447 5000000000 42838603528807 100000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2183611733/10000000000 : ℝ)^8445 ≤ (2683134100419/20000000000000 : ℝ)^6397 := by
    have hnat : (2183611733 : ℕ)^8445*20000000000000^6397 ≤ 2683134100419^6397*10000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183611733 10000000000 2683134100419 20000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8445/2048 : ℝ)) 8445 6397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069159389/2000000000 : ℝ), (2630807447/5000000000 : ℝ), (-2183611733/10000000000 : ℝ)] ![(21872862973873/50000000000000 : ℝ), (42838603528807/100000000000000 : ℝ), (2683134100419/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069159389/2000000000 : ℝ)|^8445 ≤ (21872862973873/50000000000000 : ℝ)^6397
        have hw : |(1069159389/2000000000 : ℝ)|=(1069159389/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2630807447/5000000000 : ℝ)|^8445 ≤ (42838603528807/100000000000000 : ℝ)^6397
        have hw : |(2630807447/5000000000 : ℝ)|=(2630807447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2183611733/10000000000 : ℝ)|^8445 ≤ (2683134100419/20000000000000 : ℝ)^6397
        have hw : |(-2183611733/10000000000 : ℝ)|=(2183611733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1252_s4_3 (p : ℝ) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (543636379/1250000000 : ℝ)*x 0 + (13167263/31250000 : ℝ)*x 1 + (4488884891/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (543636379/1250000000 : ℝ)^8445 ≤ (4164297659341/12500000000000 : ℝ)^6397 := by
    have hnat : (543636379 : ℕ)^8445*12500000000000^6397 ≤ 4164297659341^6397*1250000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543636379 1250000000 4164297659341 12500000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (13167263/31250000 : ℝ)^8445 ≤ (1996897312757/6250000000000 : ℝ)^6397 := by
    have hnat : (13167263 : ℕ)^8445*6250000000000^6397 ≤ 1996897312757^6397*31250000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13167263 31250000 1996897312757 6250000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4488884891/10000000000 : ℝ)^8445 ≤ (1736763084871/5000000000000 : ℝ)^6397 := by
    have hnat : (4488884891 : ℕ)^8445*5000000000000^6397 ≤ 1736763084871^6397*10000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4488884891 10000000000 1736763084871 5000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8445/2048 : ℝ)) 8445 6397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(543636379/1250000000 : ℝ), (13167263/31250000 : ℝ), (4488884891/10000000000 : ℝ)] ![(4164297659341/12500000000000 : ℝ), (1996897312757/6250000000000 : ℝ), (1736763084871/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(543636379/1250000000 : ℝ)|^8445 ≤ (4164297659341/12500000000000 : ℝ)^6397
        have hw : |(543636379/1250000000 : ℝ)|=(543636379/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(13167263/31250000 : ℝ)|^8445 ≤ (1996897312757/6250000000000 : ℝ)^6397
        have hw : |(13167263/31250000 : ℝ)|=(13167263/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4488884891/10000000000 : ℝ)|^8445 ≤ (1736763084871/5000000000000 : ℝ)^6397
        have hw : |(4488884891/10000000000 : ℝ)|=(4488884891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1252_s4_4 (p : ℝ) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-422967619/2000000000 : ℝ)*x 0 + (5261989173/10000000000 : ℝ)*x 1 + (5396718881/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (422967619/2000000000 : ℝ)^8445 ≤ (12860698261013/100000000000000 : ℝ)^6397 := by
    have hnat : (422967619 : ℕ)^8445*100000000000000^6397 ≤ 12860698261013^6397*2000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422967619 2000000000 12860698261013 100000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5261989173/10000000000 : ℝ)^8445 ≤ (21421313217731/50000000000000 : ℝ)^6397 := by
    have hnat : (5261989173 : ℕ)^8445*50000000000000^6397 ≤ 21421313217731^6397*10000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261989173 10000000000 21421313217731 50000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5396718881/10000000000 : ℝ)^8445 ≤ (11074168822973/25000000000000 : ℝ)^6397 := by
    have hnat : (5396718881 : ℕ)^8445*25000000000000^6397 ≤ 11074168822973^6397*10000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396718881 10000000000 11074168822973 25000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8445/2048 : ℝ)) 8445 6397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-422967619/2000000000 : ℝ), (5261989173/10000000000 : ℝ), (5396718881/10000000000 : ℝ)] ![(12860698261013/100000000000000 : ℝ), (21421313217731/50000000000000 : ℝ), (11074168822973/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-422967619/2000000000 : ℝ)|^8445 ≤ (12860698261013/100000000000000 : ℝ)^6397
        have hw : |(-422967619/2000000000 : ℝ)|=(422967619/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5261989173/10000000000 : ℝ)|^8445 ≤ (21421313217731/50000000000000 : ℝ)^6397
        have hw : |(5261989173/10000000000 : ℝ)|=(5261989173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5396718881/10000000000 : ℝ)|^8445 ≤ (11074168822973/25000000000000 : ℝ)^6397
        have hw : |(5396718881/10000000000 : ℝ)|=(5396718881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1252_s4_5 (p : ℝ) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (531120711/1000000000 : ℝ)*x 0 + (-1024253889/5000000000 : ℝ)*x 1 + (337294929/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531120711/1000000000 : ℝ)^8445 ≤ (43372437764291/100000000000000 : ℝ)^6397 := by
    have hnat : (531120711 : ℕ)^8445*100000000000000^6397 ≤ 43372437764291^6397*1000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531120711 1000000000 43372437764291 100000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1024253889/5000000000 : ℝ)^8445 ≤ (6165443558141/50000000000000 : ℝ)^6397 := by
    have hnat : (1024253889 : ℕ)^8445*50000000000000^6397 ≤ 6165443558141^6397*5000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1024253889 5000000000 6165443558141 50000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337294929/625000000 : ℝ)^8445 ≤ (44296675107681/100000000000000 : ℝ)^6397 := by
    have hnat : (337294929 : ℕ)^8445*100000000000000^6397 ≤ 44296675107681^6397*625000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337294929 625000000 44296675107681 100000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8445/2048 : ℝ)) 8445 6397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531120711/1000000000 : ℝ), (-1024253889/5000000000 : ℝ), (337294929/625000000 : ℝ)] ![(43372437764291/100000000000000 : ℝ), (6165443558141/50000000000000 : ℝ), (44296675107681/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531120711/1000000000 : ℝ)|^8445 ≤ (43372437764291/100000000000000 : ℝ)^6397
        have hw : |(531120711/1000000000 : ℝ)|=(531120711/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1024253889/5000000000 : ℝ)|^8445 ≤ (6165443558141/50000000000000 : ℝ)^6397
        have hw : |(-1024253889/5000000000 : ℝ)|=(1024253889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(337294929/625000000 : ℝ)|^8445 ≤ (44296675107681/100000000000000 : ℝ)^6397
        have hw : |(337294929/625000000 : ℝ)|=(337294929/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1252_s4_6 (p : ℝ) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1327801783/2500000000 : ℝ)*x 0 + (1079343771/2000000000 : ℝ)*x 1 + (-25606347/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1327801783/2500000000 : ℝ)^8445 ≤ (5421554750183/12500000000000 : ℝ)^6397 := by
    have hnat : (1327801783 : ℕ)^8445*12500000000000^6397 ≤ 5421554750183^6397*2500000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327801783 2500000000 5421554750183 12500000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1079343771/2000000000 : ℝ)^8445 ≤ (22148337505079/50000000000000 : ℝ)^6397 := by
    have hnat : (1079343771 : ℕ)^8445*50000000000000^6397 ≤ 22148337505079^6397*2000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079343771 2000000000 22148337505079 50000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (25606347/125000000 : ℝ)^8445 ≤ (12330886973243/100000000000000 : ℝ)^6397 := by
    have hnat : (25606347 : ℕ)^8445*100000000000000^6397 ≤ 12330886973243^6397*125000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25606347 125000000 12330886973243 100000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8445/2048 : ℝ)) 8445 6397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1327801783/2500000000 : ℝ), (1079343771/2000000000 : ℝ), (-25606347/125000000 : ℝ)] ![(5421554750183/12500000000000 : ℝ), (22148337505079/50000000000000 : ℝ), (12330886973243/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1327801783/2500000000 : ℝ)|^8445 ≤ (5421554750183/12500000000000 : ℝ)^6397
        have hw : |(1327801783/2500000000 : ℝ)|=(1327801783/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1079343771/2000000000 : ℝ)|^8445 ≤ (22148337505079/50000000000000 : ℝ)^6397
        have hw : |(1079343771/2000000000 : ℝ)|=(1079343771/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-25606347/125000000 : ℝ)|^8445 ≤ (12330886973243/100000000000000 : ℝ)^6397
        have hw : |(-25606347/125000000 : ℝ)|=(25606347/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1252_s4_7 (p : ℝ) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (434910341/1000000000 : ℝ)*x 0 + (4488124307/10000000000 : ℝ)*x 1 + (421428777/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (434910341/1000000000 : ℝ)^8445 ≤ (1665725322337/5000000000000 : ℝ)^6397 := by
    have hnat : (434910341 : ℕ)^8445*5000000000000^6397 ≤ 1665725322337^6397*1000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434910341 1000000000 1665725322337 5000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4488124307/10000000000 : ℝ)^8445 ≤ (34727492237783/100000000000000 : ℝ)^6397 := by
    have hnat : (4488124307 : ℕ)^8445*100000000000000^6397 ≤ 34727492237783^6397*10000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4488124307 10000000000 34727492237783 100000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (421428777/1000000000 : ℝ)^8445 ≤ (1997375081521/6250000000000 : ℝ)^6397 := by
    have hnat : (421428777 : ℕ)^8445*6250000000000^6397 ≤ 1997375081521^6397*1000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      421428777 1000000000 1997375081521 6250000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8445/2048 : ℝ)) 8445 6397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(434910341/1000000000 : ℝ), (4488124307/10000000000 : ℝ), (421428777/1000000000 : ℝ)] ![(1665725322337/5000000000000 : ℝ), (34727492237783/100000000000000 : ℝ), (1997375081521/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(434910341/1000000000 : ℝ)|^8445 ≤ (1665725322337/5000000000000 : ℝ)^6397
        have hw : |(434910341/1000000000 : ℝ)|=(434910341/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4488124307/10000000000 : ℝ)|^8445 ≤ (34727492237783/100000000000000 : ℝ)^6397
        have hw : |(4488124307/10000000000 : ℝ)|=(4488124307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(421428777/1000000000 : ℝ)|^8445 ≤ (1997375081521/6250000000000 : ℝ)^6397
        have hw : |(421428777/1000000000 : ℝ)|=(421428777/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1252_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151624409/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3673/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10937/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1421/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7119/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3673/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10937/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3673/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10937/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3673/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10937/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3673/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10937/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3673/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10937/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3673/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10937/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10937/100000 : ℝ) ^ (2111/512 : ℝ) ≤ (5448817740073871/50000000000000000000 : ℝ) := by
    have hpowers : (10937/100000 : ℝ)^2111 ≤ (5448817740073871/50000000000000000000 : ℝ)^512 := by
      have hnat : (10937 : ℕ)^2111*50000000000000000000^512 ≤ 5448817740073871^512*100000^2111 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10937 100000 5448817740073871 50000000000000000000 2111 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10937/100000 : ℝ)) (X := (5448817740073871/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2111 512 (by norm_num) hpowers
    exact h
  have hpowhi : (3673/25000 : ℝ) ^ (2111/512 : ℝ) ≤ (18399481854400051/50000000000000000000 : ℝ) := by
    have hpowers : (3673/25000 : ℝ)^2111 ≤ (18399481854400051/50000000000000000000 : ℝ)^512 := by
      have hnat : (3673 : ℕ)^2111*50000000000000000000^512 ≤ 18399481854400051^512*25000^2111 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3673 25000 18399481854400051 50000000000000000000 2111 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3673/25000 : ℝ)) (X := (18399481854400051/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2111 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005448817740073871/25000000000000000000 : ℝ) ≤ (156258259013583/156250000000000 : ℝ) ^ (2111/512 : ℝ) := by
    have hpowers : (25005448817740073871/25000000000000000000 : ℝ)^512 ≤ (156258259013583/156250000000000 : ℝ)^2111 := by
      have hnat : (25005448817740073871 : ℕ)^512*156250000000000^2111 ≤ 156258259013583^2111*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005448817740073871 25000000000000000000 156258259013583 156250000000000 512 2111 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156258259013583/156250000000000 : ℝ)) (X := (25005448817740073871/25000000000000000000 : ℝ)) (by norm_num) 2111 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011924149797236961/25000000000000000000 : ℝ) ≤ (625072288751277/625000000000000 : ℝ) ^ (2111/512 : ℝ) := by
    have hpowers : (25011924149797236961/25000000000000000000 : ℝ)^512 ≤ (625072288751277/625000000000000 : ℝ)^2111 := by
      have hnat : (25011924149797236961 : ℕ)^512*625000000000000^2111 ≤ 625072288751277^2111*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011924149797236961 25000000000000000000 625072288751277 625000000000000 512 2111 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625072288751277/625000000000000 : ℝ)) (X := (25011924149797236961/25000000000000000000 : ℝ)) (by norm_num) 2111 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018399481854400051/25000000000000000000 : ℝ) ≤ (312555770724111/312500000000000 : ℝ) ^ (2111/512 : ℝ) := by
    have hpowers : (25018399481854400051/25000000000000000000 : ℝ)^512 ≤ (312555770724111/312500000000000 : ℝ)^2111 := by
      have hnat : (25018399481854400051 : ℕ)^512*312500000000000^2111 ≤ 312555770724111^2111*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018399481854400051 25000000000000000000 312555770724111 312500000000000 512 2111 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312555770724111/312500000000000 : ℝ)) (X := (25018399481854400051/25000000000000000000 : ℝ)) (by norm_num) 2111 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5448817740073871/50000000000000000000 : ℝ) ≤ ((234614043689104173/234687500000000000 : ℝ)+2*(7850539389/4693750000000 : ℝ)*(10937/100000 : ℝ))^(2111/512 : ℝ) := by
    rw [show (234614043689104173/234687500000000000 : ℝ)+2*(7850539389/4693750000000 : ℝ)*(10937/100000 : ℝ)=(156258259013583/156250000000000 : ℝ) by norm_num, show 1+2*(5448817740073871/50000000000000000000 : ℝ)=(25005448817740073871/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18399481854400051/50000000000000000000 : ℝ)+(5448817740073871/50000000000000000000 : ℝ) ≤ ((234614043689104173/234687500000000000 : ℝ)+(7850539389/4693750000000 : ℝ)*((3673/25000 : ℝ)+(10937/100000 : ℝ)))^(2111/512 : ℝ) := by
    rw [show (234614043689104173/234687500000000000 : ℝ)+(7850539389/4693750000000 : ℝ)*((3673/25000 : ℝ)+(10937/100000 : ℝ))=(625072288751277/625000000000000 : ℝ) by norm_num, show 1+(18399481854400051/50000000000000000000 : ℝ)+(5448817740073871/50000000000000000000 : ℝ)=(25011924149797236961/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18399481854400051/50000000000000000000 : ℝ) ≤ ((234614043689104173/234687500000000000 : ℝ)+2*(7850539389/4693750000000 : ℝ)*(3673/25000 : ℝ))^(2111/512 : ℝ) := by
    rw [show (234614043689104173/234687500000000000 : ℝ)+2*(7850539389/4693750000000 : ℝ)*(3673/25000 : ℝ)=(312555770724111/312500000000000 : ℝ) by norm_num, show 1+2*(18399481854400051/50000000000000000000 : ℝ)=(25018399481854400051/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (234614043689104173/234687500000000000 : ℝ)*(X 1 0+X 2 0)+(7850539389/4693750000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2111/512 : ℝ)) (lo := (10937/100000 : ℝ)) (hi := (3673/25000 : ℝ)) (c := (234614043689104173/234687500000000000 : ℝ)) (alpha := (7850539389/4693750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (234614043689104173/234687500000000000 : ℝ)*(X 0 1+X 2 1)+(7850539389/4693750000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2111/512 : ℝ)) (lo := (10937/100000 : ℝ)) (hi := (3673/25000 : ℝ)) (c := (234614043689104173/234687500000000000 : ℝ)) (alpha := (7850539389/4693750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (234614043689104173/234687500000000000 : ℝ)*(X 0 2+X 1 2)+(7850539389/4693750000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2111/512 : ℝ)) (lo := (10937/100000 : ℝ)) (hi := (3673/25000 : ℝ)) (c := (234614043689104173/234687500000000000 : ℝ)) (alpha := (7850539389/4693750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-422966419/2000000000 : ℝ)*X 0 0+(2698547269/5000000000 : ℝ)*X 0 1+(657701867/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1252_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345796909/10000000000 : ℝ)*X 1 0+(-1091805863/5000000000 : ℝ)*X 1 1+(657701867/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1252_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069159389/2000000000 : ℝ)*X 2 0+(2630807447/5000000000 : ℝ)*X 2 1+(-2183611733/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1252_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((543636379/1250000000 : ℝ)*X 0 0+(13167263/31250000 : ℝ)*X 0 1+(4488884891/10000000000 : ℝ)*X 0 2+(543636379/1250000000 : ℝ)*X 1 0+(13167263/31250000 : ℝ)*X 1 1+(4488884891/10000000000 : ℝ)*X 1 2+(543636379/1250000000 : ℝ)*X 2 0+(13167263/31250000 : ℝ)*X 2 1+(4488884891/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1252_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-422967619/2000000000 : ℝ)*X 0 0+(5261989173/10000000000 : ℝ)*X 0 1+(5396718881/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1252_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((531120711/1000000000 : ℝ)*X 1 0+(-1024253889/5000000000 : ℝ)*X 1 1+(337294929/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1252_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1327801783/2500000000 : ℝ)*X 2 0+(1079343771/2000000000 : ℝ)*X 2 1+(-25606347/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1252_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((434910341/1000000000 : ℝ)*X 0 0+(4488124307/10000000000 : ℝ)*X 0 1+(421428777/1000000000 : ℝ)*X 0 2+(434910341/1000000000 : ℝ)*X 1 0+(4488124307/10000000000 : ℝ)*X 1 1+(421428777/1000000000 : ℝ)*X 1 2+(434910341/1000000000 : ℝ)*X 2 0+(4488124307/10000000000 : ℝ)*X 2 1+(421428777/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1252_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7835839213625703686103741/1173437500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1325689593/100000000000000 : ℝ)*(base19) + (171434869/12500000000000 : ℝ)*(base23) + (159966909/100000000000000 : ℝ)*(upper3) + (2094447/100000000000000 : ℝ)*(upper4) + (155084551/100000000000000 : ℝ)*(upper5) + (137661104459597/2500000000000 : ℝ)*(major0) + (137661104459597/2500000000000 : ℝ)*(major1) + (137661104459597/2500000000000 : ℝ)*(major2) + (7381219091330703/100000000000000 : ℝ)*(sp0) + (7381252420133951/100000000000000 : ℝ)*(sp1) + (461328273396537/6250000000000 : ℝ)*(sp2) + (72632338273621/2000000000000 : ℝ)*(sp3) + (34654492841/100000000000000 : ℝ)*(sp4) + (17474673849/100000000000000 : ℝ)*(sp7) + (3631634388354899/100000000000000 : ℝ)*(f.failure) + (922656718227943/12500000000000 : ℝ)*(f.sum) + (1580868603843/375500000000000000000000000 : ℝ)*base66 + (20129929297831563/1173437500000000000000000000000 : ℝ)*base68 + (41946386005378751/2346875000000000000000000000000 : ℝ)*base70 + (46238052811441251/2346875000000000000000000000000 : ℝ)*base72 + (265204808857/751000000000000000000000000 : ℝ)*base73 + (30142584514219/586718750000000000000000000000 : ℝ)*base76 + (25077627342800313/1173437500000000000000000000000 : ℝ)*base78 + (24522988121572501/2346875000000000000000000000000 : ℝ)*base80 + (1485150613/18775000000000000000000000 : ℝ)*base82 + (43129691/10000000000000000000000 : ℝ)*base89 + (43129691/10000000000000000000000 : ℝ)*base91 + (43129691/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11855788353931330905021591/1173437500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1751621463/100000000000000 : ℝ)*(base19) + (496215441/25000000000000 : ℝ)*(base23) + (190600037/100000000000000 : ℝ)*(upper3) + (88635687/100000000000000 : ℝ)*(lower4) + (195734451/100000000000000 : ℝ)*(upper5) + (553703985465939/10000000000000 : ℝ)*(major0) + (553703985465939/10000000000000 : ℝ)*(major1) + (553703985465939/10000000000000 : ℝ)*(major2) + (89279819/200000000000 : ℝ)*(sp1) + (50108000393/100000000000000 : ℝ)*(sp2) + (296890655544517/4000000000000 : ℝ)*(sp4) + (7422219997081963/100000000000000 : ℝ)*(sp5) + (7422214295750769/100000000000000 : ℝ)*(sp6) + (1825906491961789/50000000000000 : ℝ)*(sp7) + (1825906491961789/50000000000000 : ℝ)*(f.failure) + (296890655544517/4000000000000 : ℝ)*(f.sum) + (1040731271183/751000000000000000000000000 : ℝ)*base66 + (1249883627844839/1173437500000000000000000000000 : ℝ)*base68 + (2624772176691643/586718750000000000000000000000 : ℝ)*base69 + (10624845006219697/2346875000000000000000000000000 : ℝ)*base71 + (13990905607/9387500000000000000000000 : ℝ)*base74 + (50088787028724053/2346875000000000000000000000000 : ℝ)*base76 + (2206156708377107/586718750000000000000000000000 : ℝ)*base78 + (8257466754113589/1173437500000000000000000000000 : ℝ)*base80 + (1396960195129/751000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (7707701/5000000000000000000000 : ℝ)*base89 + (7707701/5000000000000000000000 : ℝ)*base91 + (7707701/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1252_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151624409/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3673/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10937/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1421/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7119/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1252_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1252_s5_0 (p : ℝ) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2115266657/10000000000 : ℝ)*x 0 + (674021659/1250000000 : ℝ)*x 1 + (105325009/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2115266657/10000000000 : ℝ)^8445 ≤ (6432069447497/50000000000000 : ℝ)^6397 := by
    have hnat : (2115266657 : ℕ)^8445*50000000000000^6397 ≤ 6432069447497^6397*10000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115266657 10000000000 6432069447497 50000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674021659/1250000000 : ℝ)^8445 ≤ (1769897048377/4000000000000 : ℝ)^6397 := by
    have hnat : (674021659 : ℕ)^8445*4000000000000^6397 ≤ 1769897048377^6397*1250000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674021659 1250000000 1769897048377 4000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105325009/200000000 : ℝ)^8445 ≤ (8577686974851/20000000000000 : ℝ)^6397 := by
    have hnat : (105325009 : ℕ)^8445*20000000000000^6397 ≤ 8577686974851^6397*200000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105325009 200000000 8577686974851 20000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8445/2048 : ℝ)) 8445 6397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2115266657/10000000000 : ℝ), (674021659/1250000000 : ℝ), (105325009/200000000 : ℝ)] ![(6432069447497/50000000000000 : ℝ), (1769897048377/4000000000000 : ℝ), (8577686974851/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2115266657/10000000000 : ℝ)|^8445 ≤ (6432069447497/50000000000000 : ℝ)^6397
        have hw : |(-2115266657/10000000000 : ℝ)|=(2115266657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674021659/1250000000 : ℝ)|^8445 ≤ (1769897048377/4000000000000 : ℝ)^6397
        have hw : |(674021659/1250000000 : ℝ)|=(674021659/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(105325009/200000000 : ℝ)|^8445 ≤ (8577686974851/20000000000000 : ℝ)^6397
        have hw : |(105325009/200000000 : ℝ)|=(105325009/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1252_s5_1 (p : ℝ) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344550511/10000000000 : ℝ)*x 0 + (-1089563253/5000000000 : ℝ)*x 1 + (329140653/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344550511/10000000000 : ℝ)^8445 ≤ (43732261158837/100000000000000 : ℝ)^6397 := by
    have hnat : (5344550511 : ℕ)^8445*100000000000000^6397 ≤ 43732261158837^6397*10000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344550511 10000000000 43732261158837 100000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1089563253/5000000000 : ℝ)^8445 ≤ (13379303976709/100000000000000 : ℝ)^6397 := by
    have hnat : (1089563253 : ℕ)^8445*100000000000000^6397 ≤ 13379303976709^6397*5000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089563253 5000000000 13379303976709 100000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (329140653/625000000 : ℝ)^8445 ≤ (2680527178297/6250000000000 : ℝ)^6397 := by
    have hnat : (329140653 : ℕ)^8445*6250000000000^6397 ≤ 2680527178297^6397*625000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329140653 625000000 2680527178297 6250000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8445/2048 : ℝ)) 8445 6397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344550511/10000000000 : ℝ), (-1089563253/5000000000 : ℝ), (329140653/625000000 : ℝ)] ![(43732261158837/100000000000000 : ℝ), (13379303976709/100000000000000 : ℝ), (2680527178297/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344550511/10000000000 : ℝ)|^8445 ≤ (43732261158837/100000000000000 : ℝ)^6397
        have hw : |(5344550511/10000000000 : ℝ)|=(5344550511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1089563253/5000000000 : ℝ)|^8445 ≤ (13379303976709/100000000000000 : ℝ)^6397
        have hw : |(-1089563253/5000000000 : ℝ)|=(1089563253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(329140653/625000000 : ℝ)|^8445 ≤ (2680527178297/6250000000000 : ℝ)^6397
        have hw : |(329140653/625000000 : ℝ)|=(329140653/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1252_s5_2 (p : ℝ) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344550497/10000000000 : ℝ)*x 0 + (2633125223/5000000000 : ℝ)*x 1 + (-2179126527/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344550497/10000000000 : ℝ)^8445 ≤ (21866130503803/50000000000000 : ℝ)^6397 := by
    have hnat : (5344550497 : ℕ)^8445*50000000000000^6397 ≤ 21866130503803^6397*10000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344550497 10000000000 21866130503803 50000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633125223/5000000000 : ℝ)^8445 ≤ (6862149573/16000000000 : ℝ)^6397 := by
    have hnat : (2633125223 : ℕ)^8445*16000000000^6397 ≤ 6862149573^6397*5000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633125223 5000000000 6862149573 16000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2179126527/10000000000 : ℝ)^8445 ≤ (6689652073461/50000000000000 : ℝ)^6397 := by
    have hnat : (2179126527 : ℕ)^8445*50000000000000^6397 ≤ 6689652073461^6397*10000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179126527 10000000000 6689652073461 50000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8445/2048 : ℝ)) 8445 6397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344550497/10000000000 : ℝ), (2633125223/5000000000 : ℝ), (-2179126527/10000000000 : ℝ)] ![(21866130503803/50000000000000 : ℝ), (6862149573/16000000000 : ℝ), (6689652073461/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344550497/10000000000 : ℝ)|^8445 ≤ (21866130503803/50000000000000 : ℝ)^6397
        have hw : |(5344550497/10000000000 : ℝ)|=(5344550497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633125223/5000000000 : ℝ)|^8445 ≤ (6862149573/16000000000 : ℝ)^6397
        have hw : |(2633125223/5000000000 : ℝ)|=(2633125223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2179126527/10000000000 : ℝ)|^8445 ≤ (6689652073461/50000000000000 : ℝ)^6397
        have hw : |(-2179126527/10000000000 : ℝ)|=(2179126527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1252_s5_3 (p : ℝ) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (173973837/400000000 : ℝ)*x 0 + (422320369/1000000000 : ℝ)*x 1 + (4479140363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (173973837/400000000 : ℝ)^8445 ≤ (16658479446317/50000000000000 : ℝ)^6397 := by
    have hnat : (173973837 : ℕ)^8445*50000000000000^6397 ≤ 16658479446317^6397*400000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173973837 400000000 16658479446317 50000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (422320369/1000000000 : ℝ)^8445 ≤ (1602364452643/5000000000000 : ℝ)^6397 := by
    have hnat : (422320369 : ℕ)^8445*5000000000000^6397 ≤ 1602364452643^6397*1000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422320369 1000000000 1602364452643 5000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4479140363/10000000000 : ℝ)^8445 ≤ (34635752046539/100000000000000 : ℝ)^6397 := by
    have hnat : (4479140363 : ℕ)^8445*100000000000000^6397 ≤ 34635752046539^6397*10000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4479140363 10000000000 34635752046539 100000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8445/2048 : ℝ)) 8445 6397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(173973837/400000000 : ℝ), (422320369/1000000000 : ℝ), (4479140363/10000000000 : ℝ)] ![(16658479446317/50000000000000 : ℝ), (1602364452643/5000000000000 : ℝ), (34635752046539/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(173973837/400000000 : ℝ)|^8445 ≤ (16658479446317/50000000000000 : ℝ)^6397
        have hw : |(173973837/400000000 : ℝ)|=(173973837/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(422320369/1000000000 : ℝ)|^8445 ≤ (1602364452643/5000000000000 : ℝ)^6397
        have hw : |(422320369/1000000000 : ℝ)|=(422320369/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4479140363/10000000000 : ℝ)|^8445 ≤ (34635752046539/100000000000000 : ℝ)^6397
        have hw : |(4479140363/10000000000 : ℝ)|=(4479140363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1252_s5_4 (p : ℝ) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1057635777/5000000000 : ℝ)*x 0 + (82290217/156250000 : ℝ)*x 1 + (5391848637/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057635777/5000000000 : ℝ)^8445 ≤ (643208910549/5000000000000 : ℝ)^6397 := by
    have hnat : (1057635777 : ℕ)^8445*5000000000000^6397 ≤ 643208910549^6397*5000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057635777 5000000000 643208910549 5000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (82290217/156250000 : ℝ)^8445 ≤ (42891912295509/100000000000000 : ℝ)^6397 := by
    have hnat : (82290217 : ℕ)^8445*100000000000000^6397 ≤ 42891912295509^6397*156250000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82290217 156250000 42891912295509 100000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391848637/10000000000 : ℝ)^8445 ≤ (44243909482611/100000000000000 : ℝ)^6397 := by
    have hnat : (5391848637 : ℕ)^8445*100000000000000^6397 ≤ 44243909482611^6397*10000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391848637 10000000000 44243909482611 100000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8445/2048 : ℝ)) 8445 6397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1057635777/5000000000 : ℝ), (82290217/156250000 : ℝ), (5391848637/10000000000 : ℝ)] ![(643208910549/5000000000000 : ℝ), (42891912295509/100000000000000 : ℝ), (44243909482611/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1057635777/5000000000 : ℝ)|^8445 ≤ (643208910549/5000000000000 : ℝ)^6397
        have hw : |(-1057635777/5000000000 : ℝ)|=(1057635777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(82290217/156250000 : ℝ)|^8445 ≤ (42891912295509/100000000000000 : ℝ)^6397
        have hw : |(82290217/156250000 : ℝ)|=(82290217/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391848637/10000000000 : ℝ)|^8445 ≤ (44243909482611/100000000000000 : ℝ)^6397
        have hw : |(5391848637/10000000000 : ℝ)|=(5391848637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1252_s5_5 (p : ℝ) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (531239937/1000000000 : ℝ)*x 0 + (-1026764161/5000000000 : ℝ)*x 1 + (1347962161/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531239937/1000000000 : ℝ)^8445 ≤ (43385291532887/100000000000000 : ℝ)^6397 := by
    have hnat : (531239937 : ℕ)^8445*100000000000000^6397 ≤ 43385291532887^6397*1000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531239937 1000000000 43385291532887 100000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1026764161/5000000000 : ℝ)^8445 ≤ (3092699722727/25000000000000 : ℝ)^6397 := by
    have hnat : (1026764161 : ℕ)^8445*25000000000000^6397 ≤ 3092699722727^6397*5000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026764161 5000000000 3092699722727 25000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347962161/2500000000 : ℝ)^8445 ≤ (44243909558441/100000000000000 : ℝ)^6397 := by
    have hnat : (1347962161 : ℕ)^8445*100000000000000^6397 ≤ 44243909558441^6397*2500000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347962161 2500000000 44243909558441 100000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8445/2048 : ℝ)) 8445 6397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531239937/1000000000 : ℝ), (-1026764161/5000000000 : ℝ), (1347962161/2500000000 : ℝ)] ![(43385291532887/100000000000000 : ℝ), (3092699722727/25000000000000 : ℝ), (44243909558441/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531239937/1000000000 : ℝ)|^8445 ≤ (43385291532887/100000000000000 : ℝ)^6397
        have hw : |(531239937/1000000000 : ℝ)|=(531239937/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1026764161/5000000000 : ℝ)|^8445 ≤ (3092699722727/25000000000000 : ℝ)^6397
        have hw : |(-1026764161/5000000000 : ℝ)|=(1026764161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347962161/2500000000 : ℝ)|^8445 ≤ (44243909558441/100000000000000 : ℝ)^6397
        have hw : |(1347962161/2500000000 : ℝ)|=(1347962161/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1252_s5_6 (p : ℝ) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656199689/5000000000 : ℝ)*x 0 + (5391848637/10000000000 : ℝ)*x 1 + (-2053528321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656199689/5000000000 : ℝ)^8445 ≤ (21692645809569/50000000000000 : ℝ)^6397 := by
    have hnat : (2656199689 : ℕ)^8445*50000000000000^6397 ≤ 21692645809569^6397*5000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656199689 5000000000 21692645809569 50000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391848637/10000000000 : ℝ)^8445 ≤ (44243909482611/100000000000000 : ℝ)^6397 := by
    have hnat : (5391848637 : ℕ)^8445*100000000000000^6397 ≤ 44243909482611^6397*10000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391848637 10000000000 44243909482611 100000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2053528321/10000000000 : ℝ)^8445 ≤ (2474159776591/20000000000000 : ℝ)^6397 := by
    have hnat : (2053528321 : ℕ)^8445*20000000000000^6397 ≤ 2474159776591^6397*10000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2053528321 10000000000 2474159776591 20000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8445/2048 : ℝ)) 8445 6397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656199689/5000000000 : ℝ), (5391848637/10000000000 : ℝ), (-2053528321/10000000000 : ℝ)] ![(21692645809569/50000000000000 : ℝ), (44243909482611/100000000000000 : ℝ), (2474159776591/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656199689/5000000000 : ℝ)|^8445 ≤ (21692645809569/50000000000000 : ℝ)^6397
        have hw : |(2656199689/5000000000 : ℝ)|=(2656199689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391848637/10000000000 : ℝ)|^8445 ≤ (44243909482611/100000000000000 : ℝ)^6397
        have hw : |(5391848637/10000000000 : ℝ)|=(5391848637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2053528321/10000000000 : ℝ)|^8445 ≤ (2474159776591/20000000000000 : ℝ)^6397
        have hw : |(-2053528321/10000000000 : ℝ)|=(2053528321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1252_s5_7 (p : ℝ) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4349355877/10000000000 : ℝ)*x 0 + (2239241483/5000000000 : ℝ)*x 1 + (1055965877/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4349355877/10000000000 : ℝ)^8445 ≤ (33317059533701/100000000000000 : ℝ)^6397 := by
    have hnat : (4349355877 : ℕ)^8445*100000000000000^6397 ≤ 33317059533701^6397*10000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4349355877 10000000000 33317059533701 100000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2239241483/5000000000 : ℝ)^8445 ≤ (34629041301067/100000000000000 : ℝ)^6397 := by
    have hnat : (2239241483 : ℕ)^8445*100000000000000^6397 ≤ 34629041301067^6397*5000000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2239241483 5000000000 34629041301067 100000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1055965877/2500000000 : ℝ)^8445 ≤ (32053899146203/100000000000000 : ℝ)^6397 := by
    have hnat : (1055965877 : ℕ)^8445*100000000000000^6397 ≤ 32053899146203^6397*2500000000^8445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055965877 2500000000 32053899146203 100000000000000 8445 6397 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8445/2048 : ℝ)) 8445 6397 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4349355877/10000000000 : ℝ), (2239241483/5000000000 : ℝ), (1055965877/2500000000 : ℝ)] ![(33317059533701/100000000000000 : ℝ), (34629041301067/100000000000000 : ℝ), (32053899146203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4349355877/10000000000 : ℝ)|^8445 ≤ (33317059533701/100000000000000 : ℝ)^6397
        have hw : |(4349355877/10000000000 : ℝ)|=(4349355877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2239241483/5000000000 : ℝ)|^8445 ≤ (34629041301067/100000000000000 : ℝ)^6397
        have hw : |(2239241483/5000000000 : ℝ)|=(2239241483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1055965877/2500000000 : ℝ)|^8445 ≤ (32053899146203/100000000000000 : ℝ)^6397
        have hw : |(1055965877/2500000000 : ℝ)|=(1055965877/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1252_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151624409/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7119/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1421/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (11467/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7067/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7119/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1421/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7119/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1421/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7119/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1421/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7119/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1421/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7119/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1421/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7119/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1421/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1421/12500 : ℝ) ^ (2111/512 : ℝ) ≤ (12780302543862839/100000000000000000000 : ℝ) := by
    have hpowers : (1421/12500 : ℝ)^2111 ≤ (12780302543862839/100000000000000000000 : ℝ)^512 := by
      have hnat : (1421 : ℕ)^2111*100000000000000000000^512 ≤ 12780302543862839^512*12500^2111 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1421 12500 12780302543862839 100000000000000000000 2111 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1421/12500 : ℝ)) (X := (12780302543862839/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2111 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7119/50000 : ℝ) ^ (2111/512 : ℝ) ≤ (16165922865335921/50000000000000000000 : ℝ) := by
    have hpowers : (7119/50000 : ℝ)^2111 ≤ (16165922865335921/50000000000000000000 : ℝ)^512 := by
      have hnat : (7119 : ℕ)^2111*50000000000000000000^512 ≤ 16165922865335921^512*50000^2111 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7119 50000 16165922865335921 50000000000000000000 2111 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7119/50000 : ℝ)) (X := (16165922865335921/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2111 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50012780302543862839/50000000000000000000 : ℝ) ≤ (5000309942280773/5000000000000000 : ℝ) ^ (2111/512 : ℝ) := by
    have hpowers : (50012780302543862839/50000000000000000000 : ℝ)^512 ≤ (5000309942280773/5000000000000000 : ℝ)^2111 := by
      have hnat : (50012780302543862839 : ℕ)^512*5000000000000000^2111 ≤ 5000309942280773^2111*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50012780302543862839 50000000000000000000 5000309942280773 5000000000000000 512 2111 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000309942280773/5000000000000000 : ℝ)) (X := (50012780302543862839/50000000000000000000 : ℝ)) (by norm_num) 2111 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045112148274534681/100000000000000000000 : ℝ) ≤ (5000546979504627/5000000000000000 : ℝ) ^ (2111/512 : ℝ) := by
    have hpowers : (100045112148274534681/100000000000000000000 : ℝ)^512 ≤ (5000546979504627/5000000000000000 : ℝ)^2111 := by
      have hnat : (100045112148274534681 : ℕ)^512*5000000000000000^2111 ≤ 5000546979504627^2111*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045112148274534681 100000000000000000000 5000546979504627 5000000000000000 512 2111 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000546979504627/5000000000000000 : ℝ)) (X := (100045112148274534681/100000000000000000000 : ℝ)) (by norm_num) 2111 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016165922865335921/25000000000000000000 : ℝ) ≤ (5000784016728481/5000000000000000 : ℝ) ^ (2111/512 : ℝ) := by
    have hpowers : (25016165922865335921/25000000000000000000 : ℝ)^512 ≤ (5000784016728481/5000000000000000 : ℝ)^2111 := by
      have hnat : (25016165922865335921 : ℕ)^512*5000000000000000^2111 ≤ 5000784016728481^2111*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016165922865335921 25000000000000000000 5000784016728481 5000000000000000 512 2111 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000784016728481/5000000000000000 : ℝ)) (X := (25016165922865335921/25000000000000000000 : ℝ)) (by norm_num) 2111 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(12780302543862839/100000000000000000000 : ℝ) ≤ ((1024678589716019569/1025000000000000000 : ℝ)+2*(118518611927/71750000000000 : ℝ)*(1421/12500 : ℝ))^(2111/512 : ℝ) := by
    rw [show (1024678589716019569/1025000000000000000 : ℝ)+2*(118518611927/71750000000000 : ℝ)*(1421/12500 : ℝ)=(5000309942280773/5000000000000000 : ℝ) by norm_num, show 1+2*(12780302543862839/100000000000000000000 : ℝ)=(50012780302543862839/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16165922865335921/50000000000000000000 : ℝ)+(12780302543862839/100000000000000000000 : ℝ) ≤ ((1024678589716019569/1025000000000000000 : ℝ)+(118518611927/71750000000000 : ℝ)*((7119/50000 : ℝ)+(1421/12500 : ℝ)))^(2111/512 : ℝ) := by
    rw [show (1024678589716019569/1025000000000000000 : ℝ)+(118518611927/71750000000000 : ℝ)*((7119/50000 : ℝ)+(1421/12500 : ℝ))=(5000546979504627/5000000000000000 : ℝ) by norm_num, show 1+(16165922865335921/50000000000000000000 : ℝ)+(12780302543862839/100000000000000000000 : ℝ)=(100045112148274534681/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16165922865335921/50000000000000000000 : ℝ) ≤ ((1024678589716019569/1025000000000000000 : ℝ)+2*(118518611927/71750000000000 : ℝ)*(7119/50000 : ℝ))^(2111/512 : ℝ) := by
    rw [show (1024678589716019569/1025000000000000000 : ℝ)+2*(118518611927/71750000000000 : ℝ)*(7119/50000 : ℝ)=(5000784016728481/5000000000000000 : ℝ) by norm_num, show 1+2*(16165922865335921/50000000000000000000 : ℝ)=(25016165922865335921/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1024678589716019569/1025000000000000000 : ℝ)*(X 1 0+X 2 0)+(118518611927/71750000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2111/512 : ℝ)) (lo := (1421/12500 : ℝ)) (hi := (7119/50000 : ℝ)) (c := (1024678589716019569/1025000000000000000 : ℝ)) (alpha := (118518611927/71750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1024678589716019569/1025000000000000000 : ℝ)*(X 0 1+X 2 1)+(118518611927/71750000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2111/512 : ℝ)) (lo := (1421/12500 : ℝ)) (hi := (7119/50000 : ℝ)) (c := (1024678589716019569/1025000000000000000 : ℝ)) (alpha := (118518611927/71750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1024678589716019569/1025000000000000000 : ℝ)*(X 0 2+X 1 2)+(118518611927/71750000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2111/512 : ℝ)) (lo := (1421/12500 : ℝ)) (hi := (7119/50000 : ℝ)) (c := (1024678589716019569/1025000000000000000 : ℝ)) (alpha := (118518611927/71750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2115266657/10000000000 : ℝ)*X 0 0+(674021659/1250000000 : ℝ)*X 0 1+(105325009/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1252_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344550511/10000000000 : ℝ)*X 1 0+(-1089563253/5000000000 : ℝ)*X 1 1+(329140653/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1252_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344550497/10000000000 : ℝ)*X 2 0+(2633125223/5000000000 : ℝ)*X 2 1+(-2179126527/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1252_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((173973837/400000000 : ℝ)*X 0 0+(422320369/1000000000 : ℝ)*X 0 1+(4479140363/10000000000 : ℝ)*X 0 2+(173973837/400000000 : ℝ)*X 1 0+(422320369/1000000000 : ℝ)*X 1 1+(4479140363/10000000000 : ℝ)*X 1 2+(173973837/400000000 : ℝ)*X 2 0+(422320369/1000000000 : ℝ)*X 2 1+(4479140363/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1252_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1057635777/5000000000 : ℝ)*X 0 0+(82290217/156250000 : ℝ)*X 0 1+(5391848637/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1252_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((531239937/1000000000 : ℝ)*X 1 0+(-1026764161/5000000000 : ℝ)*X 1 1+(1347962161/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1252_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656199689/5000000000 : ℝ)*X 2 0+(5391848637/10000000000 : ℝ)*X 2 1+(-2053528321/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1252_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4349355877/10000000000 : ℝ)*X 0 0+(2239241483/5000000000 : ℝ)*X 0 1+(1055965877/2500000000 : ℝ)*X 0 2+(4349355877/10000000000 : ℝ)*X 1 0+(2239241483/5000000000 : ℝ)*X 1 1+(1055965877/2500000000 : ℝ)*X 1 2+(4349355877/10000000000 : ℝ)*X 2 0+(2239241483/5000000000 : ℝ)*X 2 1+(1055965877/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1252_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (124736064885175839253675041/25625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (908533099/100000000000000 : ℝ)*(base19) + (839489309/100000000000000 : ℝ)*(base23) + (6445703/25000000000000 : ℝ)*(lower2) + (16409909/12500000000000 : ℝ)*(upper3) + (28873121/50000000000000 : ℝ)*(upper5) + (2962166116314563/50000000000000 : ℝ)*(major0) + (2962166116314563/50000000000000 : ℝ)*(major1) + (2962166116314563/50000000000000 : ℝ)*(major2) + (7941398875656957/100000000000000 : ℝ)*(sp0) + (7941421630623189/100000000000000 : ℝ)*(sp1) + (7941421699666979/100000000000000 : ℝ)*(sp2) + (1953614148333023/50000000000000 : ℝ)*(sp3) + (23663499331/100000000000000 : ℝ)*(sp4) + (6733588807/50000000000000 : ℝ)*(sp7) + (3907241763843661/100000000000000 : ℝ)*(f.failure) + (124084727174317/1562500000000 : ℝ)*(f.sum) + (21830156328229/7175000000000000000000000000 : ℝ)*base65 + (1920883118473883429/358750000000000000000000000000000 : ℝ)*base67 + (3601933940472366571/358750000000000000000000000000000 : ℝ)*base70 + (1750329224847366571/358750000000000000000000000000000 : ℝ)*base72 + (6581512076823/3587500000000000000000000000 : ℝ)*base74 + (6715430431746383429/358750000000000000000000000000000 : ℝ)*base75 + (1510160085357366571/358750000000000000000000000000000 : ℝ)*base78 + (189966150743616571/358750000000000000000000000000000 : ℝ)*base80 + (48669780914129/7175000000000000000000000000 : ℝ)*base81 + (67521349/10000000000000000000000 : ℝ)*base89 + (67521349/10000000000000000000000 : ℝ)*base91 + (67521349/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (211964339594753379733303731/89687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (81881399/20000000000000 : ℝ)*(base19) + (220121577/50000000000000 : ℝ)*(base23) + (48551281/100000000000000 : ℝ)*(upper3) + (61191/800000000000 : ℝ)*(lower4) + (44527557/100000000000000 : ℝ)*(upper5) + (2977471030773181/50000000000000 : ℝ)*(major0) + (2977471030773181/50000000000000 : ℝ)*(major1) + (2977471030773181/50000000000000 : ℝ)*(major2) + (1450034549/12500000000000 : ℝ)*(sp1) + (12330138411/100000000000000 : ℝ)*(sp2) + (7982454350888737/100000000000000 : ℝ)*(sp4) + (7982442341205351/100000000000000 : ℝ)*(sp5) + (7982441580507171/100000000000000 : ℝ)*(sp6) + (490928711678141/12500000000000 : ℝ)*(sp7) + (490928711678141/12500000000000 : ℝ)*(f.failure) + (7982454350888737/100000000000000 : ℝ)*(f.sum) + (6929252685249/3587500000000000000000000000 : ℝ)*base65 + (1150476803506647077/358750000000000000000000000000000 : ℝ)*base68 + (1887826673189602923/358750000000000000000000000000000 : ℝ)*base69 + (4915959387920852923/358750000000000000000000000000000 : ℝ)*base71 + (31038990123401/3587500000000000000000000000 : ℝ)*base74 + (6524090614668352923/358750000000000000000000000000000 : ℝ)*base75 + (3324574981044602923/358750000000000000000000000000000 : ℝ)*base77 + (6018044968994602923/358750000000000000000000000000000 : ℝ)*base79 + (8686990569163/1793750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (2343669/1250000000000000000000 : ℝ)*base89 + (2343669/1250000000000000000000 : ℝ)*base91 + (2343669/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1252_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151624409/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7119/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1421/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11467/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7067/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1252_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1252_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151624409/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16197/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (477/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11467/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7067/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1252_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1252_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1252_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2111/512 : ℝ) ≤ p) (hpb : p ≤ (8445/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151624409/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16197/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (477/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11467/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7067/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1252_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
