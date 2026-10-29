-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1482_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:13:23.359984+00:00
-- url     : https://prove2.me/submissions/87017401-1d1f-4387-8fe1-90bd30402e7e

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
theorem support_rectangle_w1482_s0_0 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-343624051/2000000000 : ℝ)*x 0 + (742037971/1250000000 : ℝ)*x 1 + (2421138583/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (343624051/2000000000 : ℝ)^4461 ≤ (2541498312869/25000000000000 : ℝ)^3437 := by
    have hnat : (343624051 : ℕ)^4461*25000000000000^3437 ≤ 2541498312869^3437*2000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      343624051 2000000000 2541498312869 25000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (742037971/1250000000 : ℝ)^4461 ≤ (12705121423591/25000000000000 : ℝ)^3437 := by
    have hnat : (742037971 : ℕ)^4461*25000000000000^3437 ≤ 12705121423591^3437*1250000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      742037971 1250000000 12705121423591 25000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2421138583/5000000000 : ℝ)^4461 ≤ (19506760517051/50000000000000 : ℝ)^3437 := by
    have hnat : (2421138583 : ℕ)^4461*50000000000000^3437 ≤ 19506760517051^3437*5000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2421138583 5000000000 19506760517051 50000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-343624051/2000000000 : ℝ), (742037971/1250000000 : ℝ), (2421138583/5000000000 : ℝ)] ![(2541498312869/25000000000000 : ℝ), (12705121423591/25000000000000 : ℝ), (19506760517051/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-343624051/2000000000 : ℝ)|^4461 ≤ (2541498312869/25000000000000 : ℝ)^3437
        have hw : |(-343624051/2000000000 : ℝ)|=(343624051/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(742037971/1250000000 : ℝ)|^4461 ≤ (12705121423591/25000000000000 : ℝ)^3437
        have hw : |(742037971/1250000000 : ℝ)|=(742037971/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2421138583/5000000000 : ℝ)|^4461 ≤ (19506760517051/50000000000000 : ℝ)^3437
        have hw : |(2421138583/5000000000 : ℝ)|=(2421138583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_s0_1 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1371134177/2500000000 : ℝ)*x 0 + (-1166878969/5000000000 : ℝ)*x 1 + (12105693/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1371134177/2500000000 : ℝ)^4461 ≤ (45858601331449/100000000000000 : ℝ)^3437 := by
    have hnat : (1371134177 : ℕ)^4461*100000000000000^3437 ≤ 45858601331449^3437*2500000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1371134177 2500000000 45858601331449 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1166878969/5000000000 : ℝ)^4461 ≤ (7563938635067/50000000000000 : ℝ)^3437 := by
    have hnat : (1166878969 : ℕ)^4461*50000000000000^3437 ≤ 7563938635067^3437*5000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1166878969 5000000000 7563938635067 50000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (12105693/25000000 : ℝ)^4461 ≤ (39013521389649/100000000000000 : ℝ)^3437 := by
    have hnat : (12105693 : ℕ)^4461*100000000000000^3437 ≤ 39013521389649^3437*25000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12105693 25000000 39013521389649 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1371134177/2500000000 : ℝ), (-1166878969/5000000000 : ℝ), (12105693/25000000 : ℝ)] ![(45858601331449/100000000000000 : ℝ), (7563938635067/50000000000000 : ℝ), (39013521389649/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1371134177/2500000000 : ℝ)|^4461 ≤ (45858601331449/100000000000000 : ℝ)^3437
        have hw : |(1371134177/2500000000 : ℝ)|=(1371134177/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1166878969/5000000000 : ℝ)|^4461 ≤ (7563938635067/50000000000000 : ℝ)^3437
        have hw : |(-1166878969/5000000000 : ℝ)|=(1166878969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(12105693/25000000 : ℝ)|^4461 ≤ (39013521389649/100000000000000 : ℝ)^3437
        have hw : |(12105693/25000000 : ℝ)|=(12105693/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_s0_2 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (685567077/1250000000 : ℝ)*x 0 + (4842277249/10000000000 : ℝ)*x 1 + (-583439499/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (685567077/1250000000 : ℝ)^4461 ≤ (45858600333011/100000000000000 : ℝ)^3437 := by
    have hnat : (685567077 : ℕ)^4461*100000000000000^3437 ≤ 45858600333011^3437*1250000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      685567077 1250000000 45858600333011 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4842277249/10000000000 : ℝ)^4461 ≤ (7802704380411/20000000000000 : ℝ)^3437 := by
    have hnat : (4842277249 : ℕ)^4461*20000000000000^3437 ≤ 7802704380411^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4842277249 10000000000 7802704380411 20000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (583439499/2500000000 : ℝ)^4461 ≤ (3025575551623/20000000000000 : ℝ)^3437 := by
    have hnat : (583439499 : ℕ)^4461*20000000000000^3437 ≤ 3025575551623^3437*2500000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      583439499 2500000000 3025575551623 20000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(685567077/1250000000 : ℝ), (4842277249/10000000000 : ℝ), (-583439499/2500000000 : ℝ)] ![(45858600333011/100000000000000 : ℝ), (7802704380411/20000000000000 : ℝ), (3025575551623/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(685567077/1250000000 : ℝ)|^4461 ≤ (45858600333011/100000000000000 : ℝ)^3437
        have hw : |(685567077/1250000000 : ℝ)|=(685567077/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4842277249/10000000000 : ℝ)|^4461 ≤ (7802704380411/20000000000000 : ℝ)^3437
        have hw : |(4842277249/10000000000 : ℝ)|=(4842277249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-583439499/2500000000 : ℝ)|^4461 ≤ (3025575551623/20000000000000 : ℝ)^3437
        have hw : |(-583439499/2500000000 : ℝ)|=(583439499/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_s0_3 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2076666843/5000000000 : ℝ)*x 0 + (3091438253/10000000000 : ℝ)*x 1 + (5519885439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2076666843/5000000000 : ℝ)^4461 ≤ (6393433703933/20000000000000 : ℝ)^3437 := by
    have hnat : (2076666843 : ℕ)^4461*20000000000000^3437 ≤ 6393433703933^3437*5000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2076666843 5000000000 6393433703933 20000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3091438253/10000000000 : ℝ)^4461 ≤ (2723779618579/12500000000000 : ℝ)^3437 := by
    have hnat : (3091438253 : ℕ)^4461*12500000000000^3437 ≤ 2723779618579^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3091438253 10000000000 2723779618579 12500000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5519885439/10000000000 : ℝ)^4461 ≤ (23121297260931/50000000000000 : ℝ)^3437 := by
    have hnat : (5519885439 : ℕ)^4461*50000000000000^3437 ≤ 23121297260931^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5519885439 10000000000 23121297260931 50000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2076666843/5000000000 : ℝ), (3091438253/10000000000 : ℝ), (5519885439/10000000000 : ℝ)] ![(6393433703933/20000000000000 : ℝ), (2723779618579/12500000000000 : ℝ), (23121297260931/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2076666843/5000000000 : ℝ)|^4461 ≤ (6393433703933/20000000000000 : ℝ)^3437
        have hw : |(2076666843/5000000000 : ℝ)|=(2076666843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3091438253/10000000000 : ℝ)|^4461 ≤ (2723779618579/12500000000000 : ℝ)^3437
        have hw : |(3091438253/10000000000 : ℝ)|=(3091438253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5519885439/10000000000 : ℝ)|^4461 ≤ (23121297260931/50000000000000 : ℝ)^3437
        have hw : |(5519885439/10000000000 : ℝ)|=(5519885439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_s0_4 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1721905423/10000000000 : ℝ)*x 0 + (4870334313/10000000000 : ℝ)*x 1 + (590723779/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1721905423/10000000000 : ℝ)^4461 ≤ (10195072055699/100000000000000 : ℝ)^3437 := by
    have hnat : (1721905423 : ℕ)^4461*100000000000000^3437 ≤ 10195072055699^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1721905423 10000000000 10195072055699 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4870334313/10000000000 : ℝ)^4461 ≤ (39307175015547/100000000000000 : ℝ)^3437 := by
    have hnat : (4870334313 : ℕ)^4461*100000000000000^3437 ≤ 39307175015547^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4870334313 10000000000 39307175015547 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (590723779/1000000000 : ℝ)^4461 ≤ (10099550583097/20000000000000 : ℝ)^3437 := by
    have hnat : (590723779 : ℕ)^4461*20000000000000^3437 ≤ 10099550583097^3437*1000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      590723779 1000000000 10099550583097 20000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1721905423/10000000000 : ℝ), (4870334313/10000000000 : ℝ), (590723779/1000000000 : ℝ)] ![(10195072055699/100000000000000 : ℝ), (39307175015547/100000000000000 : ℝ), (10099550583097/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1721905423/10000000000 : ℝ)|^4461 ≤ (10195072055699/100000000000000 : ℝ)^3437
        have hw : |(-1721905423/10000000000 : ℝ)|=(1721905423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4870334313/10000000000 : ℝ)|^4461 ≤ (39307175015547/100000000000000 : ℝ)^3437
        have hw : |(4870334313/10000000000 : ℝ)|=(4870334313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(590723779/1000000000 : ℝ)|^4461 ≤ (10099550583097/20000000000000 : ℝ)^3437
        have hw : |(590723779/1000000000 : ℝ)|=(590723779/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_s0_5 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2592902113/5000000000 : ℝ)*x 0 + (-634398563/5000000000 : ℝ)*x 1 + (5907237783/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2592902113/5000000000 : ℝ)^4461 ≤ (21321614005383/50000000000000 : ℝ)^3437 := by
    have hnat : (2592902113 : ℕ)^4461*50000000000000^3437 ≤ 21321614005383^3437*5000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592902113 5000000000 21321614005383 50000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (634398563/5000000000 : ℝ)^4461 ≤ (274360765251/4000000000000 : ℝ)^3437 := by
    have hnat : (634398563 : ℕ)^4461*4000000000000^3437 ≤ 274360765251^3437*5000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      634398563 5000000000 274360765251 4000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5907237783/10000000000 : ℝ)^4461 ≤ (25248876418909/50000000000000 : ℝ)^3437 := by
    have hnat : (5907237783 : ℕ)^4461*50000000000000^3437 ≤ 25248876418909^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5907237783 10000000000 25248876418909 50000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2592902113/5000000000 : ℝ), (-634398563/5000000000 : ℝ), (5907237783/10000000000 : ℝ)] ![(21321614005383/50000000000000 : ℝ), (274360765251/4000000000000 : ℝ), (25248876418909/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2592902113/5000000000 : ℝ)|^4461 ≤ (21321614005383/50000000000000 : ℝ)^3437
        have hw : |(2592902113/5000000000 : ℝ)|=(2592902113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-634398563/5000000000 : ℝ)|^4461 ≤ (274360765251/4000000000000 : ℝ)^3437
        have hw : |(-634398563/5000000000 : ℝ)|=(634398563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5907237783/10000000000 : ℝ)|^4461 ≤ (25248876418909/50000000000000 : ℝ)^3437
        have hw : |(5907237783/10000000000 : ℝ)|=(5907237783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_s0_6 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1296451027/2500000000 : ℝ)*x 0 + (5907237767/10000000000 : ℝ)*x 1 + (-317199333/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1296451027/2500000000 : ℝ)^4461 ≤ (5330403343919/12500000000000 : ℝ)^3437 := by
    have hnat : (1296451027 : ℕ)^4461*12500000000000^3437 ≤ 5330403343919^3437*2500000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296451027 2500000000 5330403343919 12500000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5907237767/10000000000 : ℝ)^4461 ≤ (50497752660293/100000000000000 : ℝ)^3437 := by
    have hnat : (5907237767 : ℕ)^4461*100000000000000^3437 ≤ 50497752660293^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5907237767 10000000000 50497752660293 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (317199333/2500000000 : ℝ)^4461 ≤ (171475514417/2500000000000 : ℝ)^3437 := by
    have hnat : (317199333 : ℕ)^4461*2500000000000^3437 ≤ 171475514417^3437*2500000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      317199333 2500000000 171475514417 2500000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1296451027/2500000000 : ℝ), (5907237767/10000000000 : ℝ), (-317199333/2500000000 : ℝ)] ![(5330403343919/12500000000000 : ℝ), (50497752660293/100000000000000 : ℝ), (171475514417/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1296451027/2500000000 : ℝ)|^4461 ≤ (5330403343919/12500000000000 : ℝ)^3437
        have hw : |(1296451027/2500000000 : ℝ)|=(1296451027/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5907237767/10000000000 : ℝ)|^4461 ≤ (50497752660293/100000000000000 : ℝ)^3437
        have hw : |(5907237767/10000000000 : ℝ)|=(5907237767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-317199333/2500000000 : ℝ)|^4461 ≤ (171475514417/2500000000000 : ℝ)^3437
        have hw : |(-317199333/2500000000 : ℝ)|=(317199333/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_s0_7 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4161736269/10000000000 : ℝ)*x 0 + (5457605841/10000000000 : ℝ)*x 1 + (631191427/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4161736269/10000000000 : ℝ)^4461 ≤ (16025567277933/50000000000000 : ℝ)^3437 := by
    have hnat : (4161736269 : ℕ)^4461*50000000000000^3437 ≤ 16025567277933^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4161736269 10000000000 16025567277933 50000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5457605841/10000000000 : ℝ)^4461 ≤ (45566545605971/100000000000000 : ℝ)^3437 := by
    have hnat : (5457605841 : ℕ)^4461*100000000000000^3437 ≤ 45566545605971^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5457605841 10000000000 45566545605971 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (631191427/2000000000 : ℝ)^4461 ≤ (22382319821781/100000000000000 : ℝ)^3437 := by
    have hnat : (631191427 : ℕ)^4461*100000000000000^3437 ≤ 22382319821781^3437*2000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      631191427 2000000000 22382319821781 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4161736269/10000000000 : ℝ), (5457605841/10000000000 : ℝ), (631191427/2000000000 : ℝ)] ![(16025567277933/50000000000000 : ℝ), (45566545605971/100000000000000 : ℝ), (22382319821781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4161736269/10000000000 : ℝ)|^4461 ≤ (16025567277933/50000000000000 : ℝ)^3437
        have hw : |(4161736269/10000000000 : ℝ)|=(4161736269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5457605841/10000000000 : ℝ)|^4461 ≤ (45566545605971/100000000000000 : ℝ)^3437
        have hw : |(5457605841/10000000000 : ℝ)|=(5457605841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(631191427/2000000000 : ℝ)|^4461 ≤ (22382319821781/100000000000000 : ℝ)^3437
        have hw : |(631191427/2000000000 : ℝ)|=(631191427/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1482_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5030833/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (2433/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (12939/50000 : ℝ)*pair X 0 0 := by
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
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (4459/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4459 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4459*1^1024 ≤ 0^1024*1^4459 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4459 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4459 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4459/1024 : ℝ) ≤ (57812714685567553/3125000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4459 ≤ (57812714685567553/3125000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4459*3125000000000000000^1024 ≤ 57812714685567553^1024*5^4459 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 57812714685567553 3125000000000000000 4459 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (57812714685567553/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4459 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4459/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4459 := by
      have hnat : (1 : ℕ)^1024*1^4459 ≤ 1^4459*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4459 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4459 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (3182812714685567553/3125000000000000000 : ℝ) ≤ (10042185544096981/10000000000000000 : ℝ) ^ (4459/1024 : ℝ) := by
    have hpowers : (3182812714685567553/3125000000000000000 : ℝ)^1024 ≤ (10042185544096981/10000000000000000 : ℝ)^4459 := by
      have hnat : (3182812714685567553 : ℕ)^1024*10000000000000000^4459 ≤ 10042185544096981^4459*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3182812714685567553 3125000000000000000 10042185544096981 10000000000000000 1024 4459 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10042185544096981/10000000000000000 : ℝ)) (X := (3182812714685567553/3125000000000000000 : ℝ)) (by norm_num) 4459 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1620312714685567553/1562500000000000000 : ℝ) ≤ (5042185544096981/5000000000000000 : ℝ) ^ (4459/1024 : ℝ) := by
    have hpowers : (1620312714685567553/1562500000000000000 : ℝ)^1024 ≤ (5042185544096981/5000000000000000 : ℝ)^4459 := by
      have hnat : (1620312714685567553 : ℕ)^1024*5000000000000000^4459 ≤ 5042185544096981^4459*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1620312714685567553 1562500000000000000 5042185544096981 5000000000000000 1024 4459 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5042185544096981/5000000000000000 : ℝ)) (X := (1620312714685567553/1562500000000000000 : ℝ)) (by norm_num) 4459 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(42185544096981/4000000000000000 : ℝ)*(0 : ℝ))^(4459/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(42185544096981/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(57812714685567553/3125000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(42185544096981/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4459/1024 : ℝ) := by
    rw [show (1 : ℝ)+(42185544096981/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10042185544096981/10000000000000000 : ℝ) by norm_num, show 1+(57812714685567553/3125000000000000000 : ℝ)+(0 : ℝ)=(3182812714685567553/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(57812714685567553/3125000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(42185544096981/4000000000000000 : ℝ)*(2/5 : ℝ))^(4459/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(42185544096981/4000000000000000 : ℝ)*(2/5 : ℝ)=(5042185544096981/5000000000000000 : ℝ) by norm_num, show 1+2*(57812714685567553/3125000000000000000 : ℝ)=(1620312714685567553/1562500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(42185544096981/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4459/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (42185544096981/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(42185544096981/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4459/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (42185544096981/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(42185544096981/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4459/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (42185544096981/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-343624051/2000000000 : ℝ)*X 0 0+(742037971/1250000000 : ℝ)*X 0 1+(2421138583/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1371134177/2500000000 : ℝ)*X 1 0+(-1166878969/5000000000 : ℝ)*X 1 1+(12105693/25000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((685567077/1250000000 : ℝ)*X 2 0+(4842277249/10000000000 : ℝ)*X 2 1+(-583439499/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2076666843/5000000000 : ℝ)*X 0 0+(3091438253/10000000000 : ℝ)*X 0 1+(5519885439/10000000000 : ℝ)*X 0 2+(2076666843/5000000000 : ℝ)*X 1 0+(3091438253/10000000000 : ℝ)*X 1 1+(5519885439/10000000000 : ℝ)*X 1 2+(2076666843/5000000000 : ℝ)*X 2 0+(3091438253/10000000000 : ℝ)*X 2 1+(5519885439/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1721905423/10000000000 : ℝ)*X 0 0+(4870334313/10000000000 : ℝ)*X 0 1+(590723779/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2592902113/5000000000 : ℝ)*X 1 0+(-634398563/5000000000 : ℝ)*X 1 1+(5907237783/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1296451027/2500000000 : ℝ)*X 2 0+(5907237767/10000000000 : ℝ)*X 2 1+(-317199333/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4161736269/10000000000 : ℝ)*X 0 0+(5457605841/10000000000 : ℝ)*X 0 1+(631191427/2000000000 : ℝ)*X 0 2+(4161736269/10000000000 : ℝ)*X 1 0+(5457605841/10000000000 : ℝ)*X 1 1+(631191427/2000000000 : ℝ)*X 1 2+(4161736269/10000000000 : ℝ)*X 2 0+(5457605841/10000000000 : ℝ)*X 2 1+(631191427/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (68181557146871482412361/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2613269/25000000000000 : ℝ)*(base1) + (3747357/625000000000 : ℝ)*(base19) + (73030539/12500000000000 : ℝ)*(base23) + (17356749/20000000000000 : ℝ)*(upper3) + (33134209/50000000000000 : ℝ)*(upper5) + (165730817381673/25000000000000 : ℝ)*(major0) + (165730817381673/25000000000000 : ℝ)*(major1) + (165730817381673/25000000000000 : ℝ)*(major2) + (114257084335719/12500000000000 : ℝ)*(sp0) + (914058135226423/100000000000000 : ℝ)*(sp1) + (914058150559231/100000000000000 : ℝ)*(sp2) + (25736667945231/6250000000000 : ℝ)*(sp3) + (2070570867/100000000000000 : ℝ)*(sp4) + (1015764321/100000000000000 : ℝ)*(sp7) + (411787713341093/100000000000000 : ℝ)*(f.failure) + (914058734803543/100000000000000 : ℝ)*(f.sum) + (89372438829213/50000000000000000000000000000 : ℝ)*base65 + (412744108429213/100000000000000000000000000000 : ℝ)*base67 + (48411039929213/100000000000000000000000000000 : ℝ)*base69 + (337283875129213/100000000000000000000000000000 : ℝ)*base71 + (9591709720787/50000000000000000000000000000 : ℝ)*base74 + (510425756129213/100000000000000000000000000000 : ℝ)*base75 + (491157193929213/100000000000000000000000000000 : ℝ)*base77 + (409097847229213/100000000000000000000000000000 : ℝ)*base79 + (101603486120787/50000000000000000000000000000 : ℝ)*base82 + (1579531/312500000000000000000 : ℝ)*base90 + (1579531/312500000000000000000 : ℝ)*base92 + (1579531/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (33832298413711202808279/10000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (198479163/25000000000000 : ℝ)*(base19) + (769399987/100000000000000 : ℝ)*(base23) + (9594351/12500000000000 : ℝ)*(base32) + (6984517/6250000000000 : ℝ)*(upper3) + (70011489/100000000000000 : ℝ)*(upper5) + (34972017736051/5000000000000 : ℝ)*(major0) + (34972017736051/5000000000000 : ℝ)*(major1) + (34972017736051/5000000000000 : ℝ)*(major2) + (399083033/20000000000000 : ℝ)*(sp1) + (975382533/50000000000000 : ℝ)*(sp2) + (964409583914313/100000000000000 : ℝ)*(sp4) + (30137712330703/3125000000000 : ℝ)*(sp5) + (48220343187463/5000000000000 : ℝ)*(sp6) + (86894187199717/20000000000000 : ℝ)*(sp7) + (27154438297087/6250000000000 : ℝ)*(f.failure) + (964409583914313/100000000000000 : ℝ)*(f.sum) + (16952795697969/10000000000000000000000000000 : ℝ)*base66 + (18709664882031/20000000000000000000000000000 : ℝ)*base67 + (70024040937969/20000000000000000000000000000 : ℝ)*base70 + (33540881657969/20000000000000000000000000000 : ℝ)*base72 + (23348183227969/10000000000000000000000000000 : ℝ)*base74 + (85578037102031/20000000000000000000000000000 : ℝ)*base75 + (47057118057969/20000000000000000000000000000 : ℝ)*base78 + (65302387182031/20000000000000000000000000000 : ℝ)*base79 + (48708315227969/10000000000000000000000000000 : ℝ)*base82 + (135279/19531250000000000000 : ℝ)*base90 + (135279/19531250000000000000 : ℝ)*base92 + (135279/19531250000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1482_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5030833/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2433/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (12939/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1482_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1482_s1_0 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-939988923/5000000000 : ℝ)*x 0 + (5591285837/10000000000 : ℝ)*x 1 + (5083395631/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (939988923/5000000000 : ℝ)^4461 ≤ (1428262345213/12500000000000 : ℝ)^3437 := by
    have hnat : (939988923 : ℕ)^4461*12500000000000^3437 ≤ 1428262345213^3437*5000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      939988923 5000000000 1428262345213 12500000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5591285837/10000000000 : ℝ)^4461 ≤ (47020450113669/100000000000000 : ℝ)^3437 := by
    have hnat : (5591285837 : ℕ)^4461*100000000000000^3437 ≤ 47020450113669^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5591285837 10000000000 47020450113669 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5083395631/10000000000 : ℝ)^4461 ≤ (20776725554289/50000000000000 : ℝ)^3437 := by
    have hnat : (5083395631 : ℕ)^4461*50000000000000^3437 ≤ 20776725554289^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5083395631 10000000000 20776725554289 50000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-939988923/5000000000 : ℝ), (5591285837/10000000000 : ℝ), (5083395631/10000000000 : ℝ)] ![(1428262345213/12500000000000 : ℝ), (47020450113669/100000000000000 : ℝ), (20776725554289/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-939988923/5000000000 : ℝ)|^4461 ≤ (1428262345213/12500000000000 : ℝ)^3437
        have hw : |(-939988923/5000000000 : ℝ)|=(939988923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5591285837/10000000000 : ℝ)|^4461 ≤ (47020450113669/100000000000000 : ℝ)^3437
        have hw : |(5591285837/10000000000 : ℝ)|=(5591285837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5083395631/10000000000 : ℝ)|^4461 ≤ (20776725554289/50000000000000 : ℝ)^3437
        have hw : |(5083395631/10000000000 : ℝ)|=(5083395631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_s1_1 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5392184259/10000000000 : ℝ)*x 0 + (-2148461051/10000000000 : ℝ)*x 1 + (254169803/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5392184259/10000000000 : ℝ)^4461 ≤ (8971772356923/20000000000000 : ℝ)^3437 := by
    have hnat : (5392184259 : ℕ)^4461*20000000000000^3437 ≤ 8971772356923^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392184259 10000000000 8971772356923 20000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2148461051/10000000000 : ℝ)^4461 ≤ (2717536506569/20000000000000 : ℝ)^3437 := by
    have hnat : (2148461051 : ℕ)^4461*20000000000000^3437 ≤ 2717536506569^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2148461051 10000000000 2717536506569 20000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (254169803/500000000 : ℝ)^4461 ≤ (41553455660169/100000000000000 : ℝ)^3437 := by
    have hnat : (254169803 : ℕ)^4461*100000000000000^3437 ≤ 41553455660169^3437*500000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      254169803 500000000 41553455660169 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5392184259/10000000000 : ℝ), (-2148461051/10000000000 : ℝ), (254169803/500000000 : ℝ)] ![(8971772356923/20000000000000 : ℝ), (2717536506569/20000000000000 : ℝ), (41553455660169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5392184259/10000000000 : ℝ)|^4461 ≤ (8971772356923/20000000000000 : ℝ)^3437
        have hw : |(5392184259/10000000000 : ℝ)|=(5392184259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2148461051/10000000000 : ℝ)|^4461 ≤ (2717536506569/20000000000000 : ℝ)^3437
        have hw : |(-2148461051/10000000000 : ℝ)|=(2148461051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(254169803/500000000 : ℝ)|^4461 ≤ (41553455660169/100000000000000 : ℝ)^3437
        have hw : |(254169803/500000000 : ℝ)|=(254169803/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_s1_2 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2696092373/5000000000 : ℝ)*x 0 + (5083395823/10000000000 : ℝ)*x 1 + (-2148460717/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2696092373/5000000000 : ℝ)^4461 ≤ (8971773408631/20000000000000 : ℝ)^3437 := by
    have hnat : (2696092373 : ℕ)^4461*20000000000000^3437 ≤ 8971773408631^3437*5000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696092373 5000000000 8971773408631 20000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5083395823/10000000000 : ℝ)^4461 ≤ (20776726572827/50000000000000 : ℝ)^3437 := by
    have hnat : (5083395823 : ℕ)^4461*50000000000000^3437 ≤ 20776726572827^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5083395823 10000000000 20776726572827 50000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2148460717/10000000000 : ℝ)^4461 ≤ (13587679791163/100000000000000 : ℝ)^3437 := by
    have hnat : (2148460717 : ℕ)^4461*100000000000000^3437 ≤ 13587679791163^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2148460717 10000000000 13587679791163 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2696092373/5000000000 : ℝ), (5083395823/10000000000 : ℝ), (-2148460717/10000000000 : ℝ)] ![(8971773408631/20000000000000 : ℝ), (20776726572827/50000000000000 : ℝ), (13587679791163/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2696092373/5000000000 : ℝ)|^4461 ≤ (8971773408631/20000000000000 : ℝ)^3437
        have hw : |(2696092373/5000000000 : ℝ)|=(2696092373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5083395823/10000000000 : ℝ)|^4461 ≤ (20776726572827/50000000000000 : ℝ)^3437
        have hw : |(5083395823/10000000000 : ℝ)|=(5083395823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2148460717/10000000000 : ℝ)|^4461 ≤ (13587679791163/100000000000000 : ℝ)^3437
        have hw : |(-2148460717/10000000000 : ℝ)|=(2148460717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_s1_3 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4260540123/10000000000 : ℝ)*x 0 + (372912091/1000000000 : ℝ)*x 1 + (1214125321/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4260540123/10000000000 : ℝ)^4461 ≤ (33042240861987/100000000000000 : ℝ)^3437 := by
    have hnat : (4260540123 : ℕ)^4461*100000000000000^3437 ≤ 33042240861987^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4260540123 10000000000 33042240861987 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (372912091/1000000000 : ℝ)^4461 ≤ (5559085530271/20000000000000 : ℝ)^3437 := by
    have hnat : (372912091 : ℕ)^4461*20000000000000^3437 ≤ 5559085530271^3437*1000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      372912091 1000000000 5559085530271 20000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1214125321/2500000000 : ℝ)^4461 ≤ (4895291434721/12500000000000 : ℝ)^3437 := by
    have hnat : (1214125321 : ℕ)^4461*12500000000000^3437 ≤ 4895291434721^3437*2500000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1214125321 2500000000 4895291434721 12500000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4260540123/10000000000 : ℝ), (372912091/1000000000 : ℝ), (1214125321/2500000000 : ℝ)] ![(33042240861987/100000000000000 : ℝ), (5559085530271/20000000000000 : ℝ), (4895291434721/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4260540123/10000000000 : ℝ)|^4461 ≤ (33042240861987/100000000000000 : ℝ)^3437
        have hw : |(4260540123/10000000000 : ℝ)|=(4260540123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(372912091/1000000000 : ℝ)|^4461 ≤ (5559085530271/20000000000000 : ℝ)^3437
        have hw : |(372912091/1000000000 : ℝ)|=(372912091/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1214125321/2500000000 : ℝ)|^4461 ≤ (4895291434721/12500000000000 : ℝ)^3437
        have hw : |(1214125321/2500000000 : ℝ)|=(1214125321/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_s1_4 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-235042809/1250000000 : ℝ)*x 0 + (5089321541/10000000000 : ℝ)*x 1 + (2792630099/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (235042809/1250000000 : ℝ)^4461 ≤ (1142897522021/10000000000000 : ℝ)^3437 := by
    have hnat : (235042809 : ℕ)^4461*10000000000000^3437 ≤ 1142897522021^3437*1250000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      235042809 1250000000 1142897522021 10000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5089321541/10000000000 : ℝ)^4461 ≤ (41616334552837/100000000000000 : ℝ)^3437 := by
    have hnat : (5089321541 : ℕ)^4461*100000000000000^3437 ≤ 41616334552837^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5089321541 10000000000 41616334552837 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2792630099/5000000000 : ℝ)^4461 ≤ (46954690213811/100000000000000 : ℝ)^3437 := by
    have hnat : (2792630099 : ℕ)^4461*100000000000000^3437 ≤ 46954690213811^3437*5000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2792630099 5000000000 46954690213811 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-235042809/1250000000 : ℝ), (5089321541/10000000000 : ℝ), (2792630099/5000000000 : ℝ)] ![(1142897522021/10000000000000 : ℝ), (41616334552837/100000000000000 : ℝ), (46954690213811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-235042809/1250000000 : ℝ)|^4461 ≤ (1142897522021/10000000000000 : ℝ)^3437
        have hw : |(-235042809/1250000000 : ℝ)|=(235042809/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5089321541/10000000000 : ℝ)|^4461 ≤ (41616334552837/100000000000000 : ℝ)^3437
        have hw : |(5089321541/10000000000 : ℝ)|=(5089321541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2792630099/5000000000 : ℝ)|^4461 ≤ (46954690213811/100000000000000 : ℝ)^3437
        have hw : |(2792630099/5000000000 : ℝ)|=(2792630099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_s1_5 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5258914063/10000000000 : ℝ)*x 0 + (-205824561/1250000000 : ℝ)*x 1 + (5585260243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5258914063/10000000000 : ℝ)^4461 ≤ (43425162922141/100000000000000 : ℝ)^3437 := by
    have hnat : (5258914063 : ℕ)^4461*100000000000000^3437 ≤ 43425162922141^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258914063 10000000000 43425162922141 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (205824561/1250000000 : ℝ)^4461 ≤ (2405036588677/25000000000000 : ℝ)^3437 := by
    have hnat : (205824561 : ℕ)^4461*25000000000000^3437 ≤ 2405036588677^3437*1250000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205824561 1250000000 2405036588677 25000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5585260243/10000000000 : ℝ)^4461 ≤ (46954690704833/100000000000000 : ℝ)^3437 := by
    have hnat : (5585260243 : ℕ)^4461*100000000000000^3437 ≤ 46954690704833^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5585260243 10000000000 46954690704833 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5258914063/10000000000 : ℝ), (-205824561/1250000000 : ℝ), (5585260243/10000000000 : ℝ)] ![(43425162922141/100000000000000 : ℝ), (2405036588677/25000000000000 : ℝ), (46954690704833/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5258914063/10000000000 : ℝ)|^4461 ≤ (43425162922141/100000000000000 : ℝ)^3437
        have hw : |(5258914063/10000000000 : ℝ)|=(5258914063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-205824561/1250000000 : ℝ)|^4461 ≤ (2405036588677/25000000000000 : ℝ)^3437
        have hw : |(-205824561/1250000000 : ℝ)|=(205824561/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5585260243/10000000000 : ℝ)|^4461 ≤ (46954690704833/100000000000000 : ℝ)^3437
        have hw : |(5585260243/10000000000 : ℝ)|=(5585260243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_s1_6 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1314728519/2500000000 : ℝ)*x 0 + (5585260217/10000000000 : ℝ)*x 1 + (-411649127/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1314728519/2500000000 : ℝ)^4461 ≤ (4342516306147/10000000000000 : ℝ)^3437 := by
    have hnat : (1314728519 : ℕ)^4461*10000000000000^3437 ≤ 4342516306147^3437*2500000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314728519 2500000000 4342516306147 10000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5585260217/10000000000 : ℝ)^4461 ≤ (11738672605283/25000000000000 : ℝ)^3437 := by
    have hnat : (5585260217 : ℕ)^4461*25000000000000^3437 ≤ 11738672605283^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5585260217 10000000000 11738672605283 25000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (411649127/2500000000 : ℝ)^4461 ≤ (962014650637/10000000000000 : ℝ)^3437 := by
    have hnat : (411649127 : ℕ)^4461*10000000000000^3437 ≤ 962014650637^3437*2500000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      411649127 2500000000 962014650637 10000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1314728519/2500000000 : ℝ), (5585260217/10000000000 : ℝ), (-411649127/2500000000 : ℝ)] ![(4342516306147/10000000000000 : ℝ), (11738672605283/25000000000000 : ℝ), (962014650637/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1314728519/2500000000 : ℝ)|^4461 ≤ (4342516306147/10000000000000 : ℝ)^3437
        have hw : |(1314728519/2500000000 : ℝ)|=(1314728519/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5585260217/10000000000 : ℝ)|^4461 ≤ (11738672605283/25000000000000 : ℝ)^3437
        have hw : |(5585260217/10000000000 : ℝ)|=(5585260217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-411649127/2500000000 : ℝ)|^4461 ≤ (962014650637/10000000000000 : ℝ)^3437
        have hw : |(-411649127/2500000000 : ℝ)|=(411649127/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_s1_7 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (426134963/1000000000 : ℝ)*x 0 + (1210836993/2500000000 : ℝ)*x 1 + (374249599/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (426134963/1000000000 : ℝ)^4461 ≤ (2065649350081/6250000000000 : ℝ)^3437 := by
    have hnat : (426134963 : ℕ)^4461*6250000000000^3437 ≤ 2065649350081^3437*1000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      426134963 1000000000 2065649350081 6250000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1210836993/2500000000 : ℝ)^4461 ≤ (2439044944197/6250000000000 : ℝ)^3437 := by
    have hnat : (1210836993 : ℕ)^4461*6250000000000^3437 ≤ 2439044944197^3437*2500000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1210836993 2500000000 2439044944197 6250000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (374249599/1000000000 : ℝ)^4461 ≤ (872652852353/3125000000000 : ℝ)^3437 := by
    have hnat : (374249599 : ℕ)^4461*3125000000000^3437 ≤ 872652852353^3437*1000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      374249599 1000000000 872652852353 3125000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(426134963/1000000000 : ℝ), (1210836993/2500000000 : ℝ), (374249599/1000000000 : ℝ)] ![(2065649350081/6250000000000 : ℝ), (2439044944197/6250000000000 : ℝ), (872652852353/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(426134963/1000000000 : ℝ)|^4461 ≤ (2065649350081/6250000000000 : ℝ)^3437
        have hw : |(426134963/1000000000 : ℝ)|=(426134963/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1210836993/2500000000 : ℝ)|^4461 ≤ (2439044944197/6250000000000 : ℝ)^3437
        have hw : |(1210836993/2500000000 : ℝ)|=(1210836993/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(374249599/1000000000 : ℝ)|^4461 ≤ (872652852353/3125000000000 : ℝ)^3437
        have hw : |(374249599/1000000000 : ℝ)|=(374249599/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1482_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5030833/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (12939/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2433/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1587/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1167/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (12939/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2433/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (12939/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2433/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (12939/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2433/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (12939/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2433/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (12939/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2433/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (12939/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2433/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2433/100000 : ℝ) ^ (4459/1024 : ℝ) ≤ (1173217235833/12500000000000000000 : ℝ) := by
    have hpowers : (2433/100000 : ℝ)^4459 ≤ (1173217235833/12500000000000000000 : ℝ)^1024 := by
      have hnat : (2433 : ℕ)^4459*12500000000000000000^1024 ≤ 1173217235833^1024*100000^4459 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2433 100000 1173217235833 12500000000000000000 4459 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2433/100000 : ℝ)) (X := (1173217235833/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4459 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (12939/50000 : ℝ) ^ (4459/1024 : ℝ) ≤ (138861342961365233/50000000000000000000 : ℝ) := by
    have hpowers : (12939/50000 : ℝ)^4459 ≤ (138861342961365233/50000000000000000000 : ℝ)^1024 := by
      have hnat : (12939 : ℕ)^4459*50000000000000000000^1024 ≤ 138861342961365233^1024*50000^4459 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12939 50000 138861342961365233 50000000000000000000 4459 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (12939/50000 : ℝ)) (X := (138861342961365233/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4459 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250001173217235833/6250000000000000000 : ℝ) ≤ (5000000215541487/5000000000000000 : ℝ) ^ (4459/1024 : ℝ) := by
    have hpowers : (6250001173217235833/6250000000000000000 : ℝ)^1024 ≤ (5000000215541487/5000000000000000 : ℝ)^4459 := by
      have hnat : (6250001173217235833 : ℕ)^1024*5000000000000000^4459 ≤ 5000000215541487^4459*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250001173217235833 6250000000000000000 5000000215541487 5000000000000000 1024 4459 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000215541487/5000000000000000 : ℝ)) (X := (6250001173217235833/6250000000000000000 : ℝ)) (by norm_num) 4459 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10027773207166061713/10000000000000000000 : ℝ) ≤ (125079640587173/125000000000000 : ℝ) ^ (4459/1024 : ℝ) := by
    have hpowers : (10027773207166061713/10000000000000000000 : ℝ)^1024 ≤ (125079640587173/125000000000000 : ℝ)^4459 := by
      have hnat : (10027773207166061713 : ℕ)^1024*125000000000000^4459 ≤ 125079640587173^4459*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10027773207166061713 10000000000000000000 125079640587173 125000000000000 1024 4459 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125079640587173/125000000000000 : ℝ)) (X := (10027773207166061713/10000000000000000000 : ℝ)) (by norm_num) 4459 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25138861342961365233/25000000000000000000 : ℝ) ≤ (5006371031432353/5000000000000000 : ℝ) ^ (4459/1024 : ℝ) := by
    have hpowers : (25138861342961365233/25000000000000000000 : ℝ)^1024 ≤ (5006371031432353/5000000000000000 : ℝ)^4459 := by
      have hnat : (25138861342961365233 : ℕ)^1024*5000000000000000^4459 ≤ 5006371031432353^4459*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25138861342961365233 25000000000000000000 5006371031432353 5000000000000000 1024 4459 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5006371031432353/5000000000000000 : ℝ)) (X := (25138861342961365233/25000000000000000000 : ℝ)) (by norm_num) 4459 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1173217235833/12500000000000000000 : ℝ) ≤ ((39069834952769228579/39075000000000000000 : ℝ)+2*(3185407945433/1172250000000000 : ℝ)*(2433/100000 : ℝ))^(4459/1024 : ℝ) := by
    rw [show (39069834952769228579/39075000000000000000 : ℝ)+2*(3185407945433/1172250000000000 : ℝ)*(2433/100000 : ℝ)=(5000000215541487/5000000000000000 : ℝ) by norm_num, show 1+2*(1173217235833/12500000000000000000 : ℝ)=(6250001173217235833/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(138861342961365233/50000000000000000000 : ℝ)+(1173217235833/12500000000000000000 : ℝ) ≤ ((39069834952769228579/39075000000000000000 : ℝ)+(3185407945433/1172250000000000 : ℝ)*((12939/50000 : ℝ)+(2433/100000 : ℝ)))^(4459/1024 : ℝ) := by
    rw [show (39069834952769228579/39075000000000000000 : ℝ)+(3185407945433/1172250000000000 : ℝ)*((12939/50000 : ℝ)+(2433/100000 : ℝ))=(125079640587173/125000000000000 : ℝ) by norm_num, show 1+(138861342961365233/50000000000000000000 : ℝ)+(1173217235833/12500000000000000000 : ℝ)=(10027773207166061713/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(138861342961365233/50000000000000000000 : ℝ) ≤ ((39069834952769228579/39075000000000000000 : ℝ)+2*(3185407945433/1172250000000000 : ℝ)*(12939/50000 : ℝ))^(4459/1024 : ℝ) := by
    rw [show (39069834952769228579/39075000000000000000 : ℝ)+2*(3185407945433/1172250000000000 : ℝ)*(12939/50000 : ℝ)=(5006371031432353/5000000000000000 : ℝ) by norm_num, show 1+2*(138861342961365233/50000000000000000000 : ℝ)=(25138861342961365233/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (39069834952769228579/39075000000000000000 : ℝ)*(X 1 0+X 2 0)+(3185407945433/1172250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4459/1024 : ℝ)) (lo := (2433/100000 : ℝ)) (hi := (12939/50000 : ℝ)) (c := (39069834952769228579/39075000000000000000 : ℝ)) (alpha := (3185407945433/1172250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (39069834952769228579/39075000000000000000 : ℝ)*(X 0 1+X 2 1)+(3185407945433/1172250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4459/1024 : ℝ)) (lo := (2433/100000 : ℝ)) (hi := (12939/50000 : ℝ)) (c := (39069834952769228579/39075000000000000000 : ℝ)) (alpha := (3185407945433/1172250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (39069834952769228579/39075000000000000000 : ℝ)*(X 0 2+X 1 2)+(3185407945433/1172250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4459/1024 : ℝ)) (lo := (2433/100000 : ℝ)) (hi := (12939/50000 : ℝ)) (c := (39069834952769228579/39075000000000000000 : ℝ)) (alpha := (3185407945433/1172250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-939988923/5000000000 : ℝ)*X 0 0+(5591285837/10000000000 : ℝ)*X 0 1+(5083395631/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5392184259/10000000000 : ℝ)*X 1 0+(-2148461051/10000000000 : ℝ)*X 1 1+(254169803/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2696092373/5000000000 : ℝ)*X 2 0+(5083395823/10000000000 : ℝ)*X 2 1+(-2148460717/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4260540123/10000000000 : ℝ)*X 0 0+(372912091/1000000000 : ℝ)*X 0 1+(1214125321/2500000000 : ℝ)*X 0 2+(4260540123/10000000000 : ℝ)*X 1 0+(372912091/1000000000 : ℝ)*X 1 1+(1214125321/2500000000 : ℝ)*X 1 2+(4260540123/10000000000 : ℝ)*X 2 0+(372912091/1000000000 : ℝ)*X 2 1+(1214125321/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-235042809/1250000000 : ℝ)*X 0 0+(5089321541/10000000000 : ℝ)*X 0 1+(2792630099/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5258914063/10000000000 : ℝ)*X 1 0+(-205824561/1250000000 : ℝ)*X 1 1+(5585260243/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1314728519/2500000000 : ℝ)*X 2 0+(5585260217/10000000000 : ℝ)*X 2 1+(-411649127/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((426134963/1000000000 : ℝ)*X 0 0+(1210836993/2500000000 : ℝ)*X 0 1+(374249599/1000000000 : ℝ)*X 0 2+(426134963/1000000000 : ℝ)*X 1 0+(1210836993/2500000000 : ℝ)*X 1 1+(374249599/1000000000 : ℝ)*X 1 2+(426134963/1000000000 : ℝ)*X 2 0+(1210836993/2500000000 : ℝ)*X 2 1+(374249599/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (75931967601286637434112037/10175781250000000000000000000000 : ℝ) := by norm_num
    linear_combination (42627363/100000000000000 : ℝ)*(base1) + (1401919789/100000000000000 : ℝ)*(base19) + (31594947/2000000000000 : ℝ)*(base23) + (1908713/2000000000000 : ℝ)*(upper3) + (58140353/20000000000000 : ℝ)*(upper5) + (178498417685563/12500000000000 : ℝ)*(major0) + (178498417685563/12500000000000 : ℝ)*(major1) + (178498417685563/12500000000000 : ℝ)*(major2) + (492234803888001/25000000000000 : ℝ)*(sp0) + (984475427423349/50000000000000 : ℝ)*(sp1) + (3845606791053/195312500000 : ℝ)*(sp2) + (221754363147023/25000000000000 : ℝ)*(sp3) + (2616768369/20000000000000 : ℝ)*(sp4) + (292640799/6250000000000 : ℝ)*(sp7) + (887022177468239/100000000000000 : ℝ)*(f.failure) + (984476128383243/50000000000000 : ℝ)*(f.sum) + (11764943372809/29306250000000000000000000000 : ℝ)*base66 + (6915661766217252431/1465312500000000000000000000000000 : ℝ)*base67 + (10091114313020689931/1465312500000000000000000000000000 : ℝ)*base69 + (267826511038189931/1465312500000000000000000000000000 : ℝ)*base71 + (123859616831107/58612500000000000000000000000 : ℝ)*base73 + (2107509745008685069/1465312500000000000000000000000000 : ℝ)*base76 + (1622401427167564931/1465312500000000000000000000000000 : ℝ)*base77 + (11112875878181314931/1465312500000000000000000000000000 : ℝ)*base79 + (8432972220277/3663281250000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1786913/312500000000000000000 : ℝ)*base90 + (1786913/312500000000000000000 : ℝ)*base92 + (1786913/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (128576102655566810781488941/48843750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (516588157/100000000000000 : ℝ)*(base19) + (546053833/100000000000000 : ℝ)*(base23) + (79608253/100000000000000 : ℝ)*(upper3) + (120999/1562500000000 : ℝ)*(lower4) + (7761327/20000000000000 : ℝ)*(upper5) + (73119136148207/5000000000000 : ℝ)*(major0) + (73119136148207/5000000000000 : ℝ)*(major1) + (73119136148207/5000000000000 : ℝ)*(major2) + (1569405429/50000000000000 : ℝ)*(sp1) + (3523769617/100000000000000 : ℝ)*(sp2) + (1008188909464353/50000000000000 : ℝ)*(sp4) + (2016374163529691/100000000000000 : ℝ)*(sp5) + (252046718638157/12500000000000 : ℝ)*(sp6) + (90838753925303/10000000000000 : ℝ)*(sp7) + (90838753925303/10000000000000 : ℝ)*(f.failure) + (1008188909464353/50000000000000 : ℝ)*(f.sum) + (6619914595697/5861250000000000000000000000 : ℝ)*base65 + (1627107214770873559/586125000000000000000000000000000 : ℝ)*base67 + (3123729116121123559/586125000000000000000000000000000 : ℝ)*base69 + (3414966324988248559/586125000000000000000000000000000 : ℝ)*base71 + (22596562824641/11722500000000000000000000000 : ℝ)*base74 + (3291741492765498559/586125000000000000000000000000000 : ℝ)*base75 + (210695654172626441/586125000000000000000000000000000 : ℝ)*base78 + (3405730256329248559/586125000000000000000000000000000 : ℝ)*base79 + (53200298116987/23445000000000000000000000000 : ℝ)*base82 + (117399/31250000000000000000 : ℝ)*base89 + (117399/31250000000000000000 : ℝ)*base91 + (117399/31250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1482_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5030833/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (12939/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2433/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1587/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1167/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1482_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1482_s2_0 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1908161709/10000000000 : ℝ)*x 0 + (2734089599/5000000000 : ℝ)*x 1 + (518830469/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1908161709/10000000000 : ℝ)^4461 ≤ (2912230936851/25000000000000 : ℝ)^3437 := by
    have hnat : (1908161709 : ℕ)^4461*25000000000000^3437 ≤ 2912230936851^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1908161709 10000000000 2912230936851 25000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2734089599/5000000000 : ℝ)^4461 ≤ (45681158846089/100000000000000 : ℝ)^3437 := by
    have hnat : (2734089599 : ℕ)^4461*100000000000000^3437 ≤ 45681158846089^3437*5000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2734089599 5000000000 45681158846089 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (518830469/1000000000 : ℝ)^4461 ≤ (42669917388147/100000000000000 : ℝ)^3437 := by
    have hnat : (518830469 : ℕ)^4461*100000000000000^3437 ≤ 42669917388147^3437*1000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518830469 1000000000 42669917388147 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1908161709/10000000000 : ℝ), (2734089599/5000000000 : ℝ), (518830469/1000000000 : ℝ)] ![(2912230936851/25000000000000 : ℝ), (45681158846089/100000000000000 : ℝ), (42669917388147/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1908161709/10000000000 : ℝ)|^4461 ≤ (2912230936851/25000000000000 : ℝ)^3437
        have hw : |(-1908161709/10000000000 : ℝ)|=(1908161709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2734089599/5000000000 : ℝ)|^4461 ≤ (45681158846089/100000000000000 : ℝ)^3437
        have hw : |(2734089599/5000000000 : ℝ)|=(2734089599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(518830469/1000000000 : ℝ)|^4461 ≤ (42669917388147/100000000000000 : ℝ)^3437
        have hw : |(518830469/1000000000 : ℝ)|=(518830469/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_s2_1 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5361210187/10000000000 : ℝ)*x 0 + (-410502823/2000000000 : ℝ)*x 1 + (5188304841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5361210187/10000000000 : ℝ)^4461 ≤ (44524695806219/100000000000000 : ℝ)^3437 := by
    have hnat : (5361210187 : ℕ)^4461*100000000000000^3437 ≤ 44524695806219^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5361210187 10000000000 44524695806219 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (410502823/2000000000 : ℝ)^4461 ≤ (320134629571/2500000000000 : ℝ)^3437 := by
    have hnat : (410502823 : ℕ)^4461*2500000000000^3437 ≤ 320134629571^3437*2000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410502823 2000000000 320134629571 2500000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5188304841/10000000000 : ℝ)^4461 ≤ (21334959500001/50000000000000 : ℝ)^3437 := by
    have hnat : (5188304841 : ℕ)^4461*50000000000000^3437 ≤ 21334959500001^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5188304841 10000000000 21334959500001 50000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5361210187/10000000000 : ℝ), (-410502823/2000000000 : ℝ), (5188304841/10000000000 : ℝ)] ![(44524695806219/100000000000000 : ℝ), (320134629571/2500000000000 : ℝ), (21334959500001/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5361210187/10000000000 : ℝ)|^4461 ≤ (44524695806219/100000000000000 : ℝ)^3437
        have hw : |(5361210187/10000000000 : ℝ)|=(5361210187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-410502823/2000000000 : ℝ)|^4461 ≤ (320134629571/2500000000000 : ℝ)^3437
        have hw : |(-410502823/2000000000 : ℝ)|=(410502823/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5188304841/10000000000 : ℝ)|^4461 ≤ (21334959500001/50000000000000 : ℝ)^3437
        have hw : |(5188304841/10000000000 : ℝ)|=(5188304841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_s2_2 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5361210321/10000000000 : ℝ)*x 0 + (5188304813/10000000000 : ℝ)*x 1 + (-2052513973/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5361210321/10000000000 : ℝ)^4461 ≤ (22262348625323/50000000000000 : ℝ)^3437 := by
    have hnat : (5361210321 : ℕ)^4461*50000000000000^3437 ≤ 22262348625323^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5361210321 10000000000 22262348625323 50000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5188304813/10000000000 : ℝ)^4461 ≤ (8533983740223/20000000000000 : ℝ)^3437 := by
    have hnat : (5188304813 : ℕ)^4461*20000000000000^3437 ≤ 8533983740223^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5188304813 10000000000 8533983740223 20000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2052513973/10000000000 : ℝ)^4461 ≤ (12805384032973/100000000000000 : ℝ)^3437 := by
    have hnat : (2052513973 : ℕ)^4461*100000000000000^3437 ≤ 12805384032973^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2052513973 10000000000 12805384032973 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5361210321/10000000000 : ℝ), (5188304813/10000000000 : ℝ), (-2052513973/10000000000 : ℝ)] ![(22262348625323/50000000000000 : ℝ), (8533983740223/20000000000000 : ℝ), (12805384032973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5361210321/10000000000 : ℝ)|^4461 ≤ (22262348625323/50000000000000 : ℝ)^3437
        have hw : |(5361210321/10000000000 : ℝ)|=(5361210321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5188304813/10000000000 : ℝ)|^4461 ≤ (8533983740223/20000000000000 : ℝ)^3437
        have hw : |(5188304813/10000000000 : ℝ)|=(5188304813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2052513973/10000000000 : ℝ)|^4461 ≤ (12805384032973/100000000000000 : ℝ)^3437
        have hw : |(-2052513973/10000000000 : ℝ)|=(2052513973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_s2_3 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2140330191/5000000000 : ℝ)*x 0 + (3979836841/10000000000 : ℝ)*x 1 + (4601083889/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2140330191/5000000000 : ℝ)^4461 ≤ (16622456994869/50000000000000 : ℝ)^3437 := by
    have hnat : (2140330191 : ℕ)^4461*50000000000000^3437 ≤ 16622456994869^3437*5000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2140330191 5000000000 16622456994869 50000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3979836841/10000000000 : ℝ)^4461 ≤ (15122424779927/50000000000000 : ℝ)^3437 := by
    have hnat : (3979836841 : ℕ)^4461*50000000000000^3437 ≤ 15122424779927^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3979836841 10000000000 15122424779927 50000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4601083889/10000000000 : ℝ)^4461 ≤ (36510236435781/100000000000000 : ℝ)^3437 := by
    have hnat : (4601083889 : ℕ)^4461*100000000000000^3437 ≤ 36510236435781^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4601083889 10000000000 36510236435781 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2140330191/5000000000 : ℝ), (3979836841/10000000000 : ℝ), (4601083889/10000000000 : ℝ)] ![(16622456994869/50000000000000 : ℝ), (15122424779927/50000000000000 : ℝ), (36510236435781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2140330191/5000000000 : ℝ)|^4461 ≤ (16622456994869/50000000000000 : ℝ)^3437
        have hw : |(2140330191/5000000000 : ℝ)|=(2140330191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3979836841/10000000000 : ℝ)|^4461 ≤ (15122424779927/50000000000000 : ℝ)^3437
        have hw : |(3979836841/10000000000 : ℝ)|=(3979836841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4601083889/10000000000 : ℝ)|^4461 ≤ (36510236435781/100000000000000 : ℝ)^3437
        have hw : |(4601083889/10000000000 : ℝ)|=(4601083889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_s2_4 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-954111499/5000000000 : ℝ)*x 0 + (5190113293/10000000000 : ℝ)*x 1 + (5466353713/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (954111499/5000000000 : ℝ)^4461 ≤ (11649409380113/100000000000000 : ℝ)^3437 := by
    have hnat : (954111499 : ℕ)^4461*100000000000000^3437 ≤ 11649409380113^3437*5000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      954111499 5000000000 11649409380113 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5190113293/10000000000 : ℝ)^4461 ≤ (42689224389069/100000000000000 : ℝ)^3437 := by
    have hnat : (5190113293 : ℕ)^4461*100000000000000^3437 ≤ 42689224389069^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5190113293 10000000000 42689224389069 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5466353713/10000000000 : ℝ)^4461 ≤ (9132273241141/20000000000000 : ℝ)^3437 := by
    have hnat : (5466353713 : ℕ)^4461*20000000000000^3437 ≤ 9132273241141^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5466353713 10000000000 9132273241141 20000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-954111499/5000000000 : ℝ), (5190113293/10000000000 : ℝ), (5466353713/10000000000 : ℝ)] ![(11649409380113/100000000000000 : ℝ), (42689224389069/100000000000000 : ℝ), (9132273241141/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-954111499/5000000000 : ℝ)|^4461 ≤ (11649409380113/100000000000000 : ℝ)^3437
        have hw : |(-954111499/5000000000 : ℝ)|=(954111499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5190113293/10000000000 : ℝ)|^4461 ≤ (42689224389069/100000000000000 : ℝ)^3437
        have hw : |(5190113293/10000000000 : ℝ)|=(5190113293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5466353713/10000000000 : ℝ)|^4461 ≤ (9132273241141/20000000000000 : ℝ)^3437
        have hw : |(5466353713/10000000000 : ℝ)|=(5466353713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_s2_5 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (661007831/1250000000 : ℝ)*x 0 + (-443616357/2500000000 : ℝ)*x 1 + (5466353719/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661007831/1250000000 : ℝ)^4461 ≤ (21868911894411/50000000000000 : ℝ)^3437 := by
    have hnat : (661007831 : ℕ)^4461*50000000000000^3437 ≤ 21868911894411^3437*1250000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661007831 1250000000 21868911894411 50000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (443616357/2500000000 : ℝ)^4461 ≤ (10600809925369/100000000000000 : ℝ)^3437 := by
    have hnat : (443616357 : ℕ)^4461*100000000000000^3437 ≤ 10600809925369^3437*2500000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      443616357 2500000000 10600809925369 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5466353719/10000000000 : ℝ)^4461 ≤ (11415341567689/25000000000000 : ℝ)^3437 := by
    have hnat : (5466353719 : ℕ)^4461*25000000000000^3437 ≤ 11415341567689^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5466353719 10000000000 11415341567689 25000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661007831/1250000000 : ℝ), (-443616357/2500000000 : ℝ), (5466353719/10000000000 : ℝ)] ![(21868911894411/50000000000000 : ℝ), (10600809925369/100000000000000 : ℝ), (11415341567689/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661007831/1250000000 : ℝ)|^4461 ≤ (21868911894411/50000000000000 : ℝ)^3437
        have hw : |(661007831/1250000000 : ℝ)|=(661007831/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-443616357/2500000000 : ℝ)|^4461 ≤ (10600809925369/100000000000000 : ℝ)^3437
        have hw : |(-443616357/2500000000 : ℝ)|=(443616357/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5466353719/10000000000 : ℝ)|^4461 ≤ (11415341567689/25000000000000 : ℝ)^3437
        have hw : |(5466353719/10000000000 : ℝ)|=(5466353719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_s2_6 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5288062927/10000000000 : ℝ)*x 0 + (2733176881/5000000000 : ℝ)*x 1 + (-887232491/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288062927/10000000000 : ℝ)^4461 ≤ (10934456695991/25000000000000 : ℝ)^3437 := by
    have hnat : (5288062927 : ℕ)^4461*25000000000000^3437 ≤ 10934456695991^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288062927 10000000000 10934456695991 25000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2733176881/5000000000 : ℝ)^4461 ≤ (11415341684239/25000000000000 : ℝ)^3437 := by
    have hnat : (2733176881 : ℕ)^4461*25000000000000^3437 ≤ 11415341684239^3437*5000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2733176881 5000000000 11415341684239 25000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (887232491/5000000000 : ℝ)^4461 ≤ (5300403233549/50000000000000 : ℝ)^3437 := by
    have hnat : (887232491 : ℕ)^4461*50000000000000^3437 ≤ 5300403233549^3437*5000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      887232491 5000000000 5300403233549 50000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288062927/10000000000 : ℝ), (2733176881/5000000000 : ℝ), (-887232491/5000000000 : ℝ)] ![(10934456695991/25000000000000 : ℝ), (11415341684239/25000000000000 : ℝ), (5300403233549/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288062927/10000000000 : ℝ)|^4461 ≤ (10934456695991/25000000000000 : ℝ)^3437
        have hw : |(5288062927/10000000000 : ℝ)|=(5288062927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2733176881/5000000000 : ℝ)|^4461 ≤ (11415341684239/25000000000000 : ℝ)^3437
        have hw : |(2733176881/5000000000 : ℝ)|=(2733176881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-887232491/5000000000 : ℝ)|^4461 ≤ (5300403233549/50000000000000 : ℝ)^3437
        have hw : |(-887232491/5000000000 : ℝ)|=(887232491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_s2_7 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070199031/2500000000 : ℝ)*x 0 + (4597068761/10000000000 : ℝ)*x 1 + (3890517/9765625 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070199031/2500000000 : ℝ)^4461 ≤ (16623141148177/50000000000000 : ℝ)^3437 := by
    have hnat : (1070199031 : ℕ)^4461*50000000000000^3437 ≤ 16623141148177^3437*2500000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070199031 2500000000 16623141148177 50000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4597068761/10000000000 : ℝ)^4461 ≤ (36468888854643/100000000000000 : ℝ)^3437 := by
    have hnat : (4597068761 : ℕ)^4461*100000000000000^3437 ≤ 36468888854643^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4597068761 10000000000 36468888854643 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3890517/9765625 : ℝ)^4461 ≤ (15142414417357/50000000000000 : ℝ)^3437 := by
    have hnat : (3890517 : ℕ)^4461*50000000000000^3437 ≤ 15142414417357^3437*9765625^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3890517 9765625 15142414417357 50000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070199031/2500000000 : ℝ), (4597068761/10000000000 : ℝ), (3890517/9765625 : ℝ)] ![(16623141148177/50000000000000 : ℝ), (36468888854643/100000000000000 : ℝ), (15142414417357/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070199031/2500000000 : ℝ)|^4461 ≤ (16623141148177/50000000000000 : ℝ)^3437
        have hw : |(1070199031/2500000000 : ℝ)|=(1070199031/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4597068761/10000000000 : ℝ)|^4461 ≤ (36468888854643/100000000000000 : ℝ)^3437
        have hw : |(4597068761/10000000000 : ℝ)|=(4597068761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3890517/9765625 : ℝ)|^4461 ≤ (15142414417357/50000000000000 : ℝ)^3437
        have hw : |(3890517/9765625 : ℝ)|=(3890517/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1482_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5030833/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1167/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1587/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (5101/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8061/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1167/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1587/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1167/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1587/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1167/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1587/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1167/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1587/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1167/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1587/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1167/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1587/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1587/20000 : ℝ) ^ (4459/1024 : ℝ) ≤ (1614677184562161/100000000000000000000 : ℝ) := by
    have hpowers : (1587/20000 : ℝ)^4459 ≤ (1614677184562161/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1587 : ℕ)^4459*100000000000000000000^1024 ≤ 1614677184562161^1024*20000^4459 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1587 20000 1614677184562161 100000000000000000000 4459 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1587/20000 : ℝ)) (X := (1614677184562161/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4459 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1167/6250 : ℝ) ^ (4459/1024 : ℝ) ≤ (33525572689779787/50000000000000000000 : ℝ) := by
    have hpowers : (1167/6250 : ℝ)^4459 ≤ (33525572689779787/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1167 : ℕ)^4459*50000000000000000000^1024 ≤ 33525572689779787^1024*6250^4459 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1167 6250 33525572689779787 50000000000000000000 4459 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1167/6250 : ℝ)) (X := (33525572689779787/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4459 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001614677184562161/50000000000000000000 : ℝ) ≤ (400002966420939/400000000000000 : ℝ) ^ (4459/1024 : ℝ) := by
    have hpowers : (50001614677184562161/50000000000000000000 : ℝ)^1024 ≤ (400002966420939/400000000000000 : ℝ)^4459 := by
      have hnat : (50001614677184562161 : ℕ)^1024*400000000000000^4459 ≤ 400002966420939^4459*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001614677184562161 50000000000000000000 400002966420939 400000000000000 1024 4459 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400002966420939/400000000000000 : ℝ)) (X := (50001614677184562161/50000000000000000000 : ℝ)) (by norm_num) 4459 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20013733164512824347/20000000000000000000 : ℝ) ≤ (10001576479321391/10000000000000000 : ℝ) ^ (4459/1024 : ℝ) := by
    have hpowers : (20013733164512824347/20000000000000000000 : ℝ)^1024 ≤ (10001576479321391/10000000000000000 : ℝ)^4459 := by
      have hnat : (20013733164512824347 : ℕ)^1024*10000000000000000^4459 ≤ 10001576479321391^4459*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20013733164512824347 20000000000000000000 10001576479321391 10000000000000000 1024 4459 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001576479321391/10000000000000000 : ℝ)) (X := (20013733164512824347/20000000000000000000 : ℝ)) (by norm_num) 4459 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25033525572689779787/25000000000000000000 : ℝ) ≤ (10003078798119307/10000000000000000 : ℝ) ^ (4459/1024 : ℝ) := by
    have hpowers : (25033525572689779787/25000000000000000000 : ℝ)^1024 ≤ (10003078798119307/10000000000000000 : ℝ)^4459 := by
      have hnat : (25033525572689779787 : ℕ)^1024*10000000000000000^4459 ≤ 10003078798119307^4459*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25033525572689779787 25000000000000000000 10003078798119307 10000000000000000 1024 4459 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003078798119307/10000000000000000 : ℝ)) (X := (25033525572689779787/25000000000000000000 : ℝ)) (by norm_num) 4459 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1614677184562161/100000000000000000000 : ℝ) ≤ ((7156463630814508277/7158000000000000000 : ℝ)+2*(375579699479/268425000000000 : ℝ)*(1587/20000 : ℝ))^(4459/1024 : ℝ) := by
    rw [show (7156463630814508277/7158000000000000000 : ℝ)+2*(375579699479/268425000000000 : ℝ)*(1587/20000 : ℝ)=(400002966420939/400000000000000 : ℝ) by norm_num, show 1+2*(1614677184562161/100000000000000000000 : ℝ)=(50001614677184562161/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33525572689779787/50000000000000000000 : ℝ)+(1614677184562161/100000000000000000000 : ℝ) ≤ ((7156463630814508277/7158000000000000000 : ℝ)+(375579699479/268425000000000 : ℝ)*((1167/6250 : ℝ)+(1587/20000 : ℝ)))^(4459/1024 : ℝ) := by
    rw [show (7156463630814508277/7158000000000000000 : ℝ)+(375579699479/268425000000000 : ℝ)*((1167/6250 : ℝ)+(1587/20000 : ℝ))=(10001576479321391/10000000000000000 : ℝ) by norm_num, show 1+(33525572689779787/50000000000000000000 : ℝ)+(1614677184562161/100000000000000000000 : ℝ)=(20013733164512824347/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33525572689779787/50000000000000000000 : ℝ) ≤ ((7156463630814508277/7158000000000000000 : ℝ)+2*(375579699479/268425000000000 : ℝ)*(1167/6250 : ℝ))^(4459/1024 : ℝ) := by
    rw [show (7156463630814508277/7158000000000000000 : ℝ)+2*(375579699479/268425000000000 : ℝ)*(1167/6250 : ℝ)=(10003078798119307/10000000000000000 : ℝ) by norm_num, show 1+2*(33525572689779787/50000000000000000000 : ℝ)=(25033525572689779787/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7156463630814508277/7158000000000000000 : ℝ)*(X 1 0+X 2 0)+(375579699479/268425000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4459/1024 : ℝ)) (lo := (1587/20000 : ℝ)) (hi := (1167/6250 : ℝ)) (c := (7156463630814508277/7158000000000000000 : ℝ)) (alpha := (375579699479/268425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7156463630814508277/7158000000000000000 : ℝ)*(X 0 1+X 2 1)+(375579699479/268425000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4459/1024 : ℝ)) (lo := (1587/20000 : ℝ)) (hi := (1167/6250 : ℝ)) (c := (7156463630814508277/7158000000000000000 : ℝ)) (alpha := (375579699479/268425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7156463630814508277/7158000000000000000 : ℝ)*(X 0 2+X 1 2)+(375579699479/268425000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4459/1024 : ℝ)) (lo := (1587/20000 : ℝ)) (hi := (1167/6250 : ℝ)) (c := (7156463630814508277/7158000000000000000 : ℝ)) (alpha := (375579699479/268425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1908161709/10000000000 : ℝ)*X 0 0+(2734089599/5000000000 : ℝ)*X 0 1+(518830469/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5361210187/10000000000 : ℝ)*X 1 0+(-410502823/2000000000 : ℝ)*X 1 1+(5188304841/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5361210321/10000000000 : ℝ)*X 2 0+(5188304813/10000000000 : ℝ)*X 2 1+(-2052513973/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2140330191/5000000000 : ℝ)*X 0 0+(3979836841/10000000000 : ℝ)*X 0 1+(4601083889/10000000000 : ℝ)*X 0 2+(2140330191/5000000000 : ℝ)*X 1 0+(3979836841/10000000000 : ℝ)*X 1 1+(4601083889/10000000000 : ℝ)*X 1 2+(2140330191/5000000000 : ℝ)*X 2 0+(3979836841/10000000000 : ℝ)*X 2 1+(4601083889/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-954111499/5000000000 : ℝ)*X 0 0+(5190113293/10000000000 : ℝ)*X 0 1+(5466353713/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((661007831/1250000000 : ℝ)*X 1 0+(-443616357/2500000000 : ℝ)*X 1 1+(5466353719/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5288062927/10000000000 : ℝ)*X 2 0+(2733176881/5000000000 : ℝ)*X 2 1+(-887232491/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1070199031/2500000000 : ℝ)*X 0 0+(4597068761/10000000000 : ℝ)*X 0 1+(3890517/9765625 : ℝ)*X 0 2+(1070199031/2500000000 : ℝ)*X 1 0+(4597068761/10000000000 : ℝ)*X 1 1+(3890517/9765625 : ℝ)*X 1 2+(1070199031/2500000000 : ℝ)*X 2 0+(4597068761/10000000000 : ℝ)*X 2 1+(3890517/9765625 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (382348102580295481691813207/119300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (286034777/100000000000000 : ℝ)*(base19) + (277378899/100000000000000 : ℝ)*(base23) + (3282457/6250000000000 : ℝ)*(lower2) + (38740259/100000000000000 : ℝ)*(upper3) + (43321579/50000000000000 : ℝ)*(upper5) + (2591354596619909/100000000000000 : ℝ)*(major0) + (2591354596619909/100000000000000 : ℝ)*(major1) + (2591354596619909/100000000000000 : ℝ)*(major2) + (1786516580089851/50000000000000 : ℝ)*(sp0) + (111657449098607/3125000000000 : ℝ)*(sp1) + (1786519189905651/50000000000000 : ℝ)*(sp2) + (804833994212087/50000000000000 : ℝ)*(sp3) + (2748505249/50000000000000 : ℝ)*(sp4) + (2440794449/100000000000000 : ℝ)*(sp7) + (25151100456541/1562500000000 : ℝ)*(f.failure) + (3573038657190201/100000000000000 : ℝ)*(f.sum) + (71951300327713/26842500000000000000000000000 : ℝ)*base66 + (22417458742979140379/2147400000000000000000000000000000 : ℝ)*base67 + (6174912965566540379/2147400000000000000000000000000000 : ℝ)*base69 + (5096952309226540379/2147400000000000000000000000000000 : ℝ)*base71 + (41033321170489/53685000000000000000000000000 : ℝ)*base73 + (6346417805995459621/2147400000000000000000000000000000 : ℝ)*base76 + (3934461613373059621/2147400000000000000000000000000000 : ℝ)*base78 + (13076681868380740379/2147400000000000000000000000000000 : ℝ)*base79 + (35186207004569/13421250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (276099/39062500000000000000 : ℝ)*base89 + (276099/39062500000000000000 : ℝ)*base91 + (276099/39062500000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (161108388558728442034729341/14912500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1387148211/100000000000000 : ℝ)*(base19) + (440120869/25000000000000 : ℝ)*(base23) + (189427363/100000000000000 : ℝ)*(upper3) + (25912661/50000000000000 : ℝ)*(lower4) + (68677353/25000000000000 : ℝ)*(upper5) + (328180106627289/12500000000000 : ℝ)*(major0) + (328180106627289/12500000000000 : ℝ)*(major1) + (328180106627289/12500000000000 : ℝ)*(major2) + (15883128007/100000000000000 : ℝ)*(sp1) + (21980123931/100000000000000 : ℝ)*(sp2) + (56563087093513/1562500000000 : ℝ)*(sp4) + (1810010151854307/50000000000000 : ℝ)*(sp5) + (144800553335097/4000000000000 : ℝ)*(sp6) + (815421885966223/50000000000000 : ℝ)*(sp7) + (815421885966223/50000000000000 : ℝ)*(f.failure) + (56563087093513/1562500000000 : ℝ)*(f.sum) + (106735095129/745625000000000000000000000 : ℝ)*base66 + (165726532377760351/29825000000000000000000000000000 : ℝ)*base67 + (303472638668110351/29825000000000000000000000000000 : ℝ)*base69 + (359875194215785351/29825000000000000000000000000000 : ℝ)*base71 + (23280675227597/5965000000000000000000000000 : ℝ)*base74 + (244922103382085351/29825000000000000000000000000000 : ℝ)*base75 + (301571564953660351/29825000000000000000000000000000 : ℝ)*base77 + (96686698488735351/29825000000000000000000000000000 : ℝ)*base79 + (15198889909513/5965000000000000000000000000 : ℝ)*base81 + (946241/156250000000000000000 : ℝ)*base90 + (946241/156250000000000000000 : ℝ)*base92 + (946241/156250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1482_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5030833/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1167/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1587/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5101/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8061/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1482_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1482_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5030833/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5101/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8061/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1482_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1482_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1482_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5030833/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5101/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8061/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1482_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
