-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1091_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:57:07.567027+00:00
-- url     : https://prove2.me/submissions/d3c85ff5-f7c7-488c-be8e-9c5e5a26e92f

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
theorem support_rectangle_w1091_s0_0 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-477014427/2500000000 : ℝ)*x 0 + (3033096453/5000000000 : ℝ)*x 1 + (596748553/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (477014427/2500000000 : ℝ)^2071 ≤ (221491208173/2000000000000 : ℝ)^1559 := by
    have hnat : (477014427 : ℕ)^2071*2000000000000^1559 ≤ 221491208173^1559*2500000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      477014427 2500000000 221491208173 2000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3033096453/5000000000 : ℝ)^2071 ≤ (5147809948507/10000000000000 : ℝ)^1559 := by
    have hnat : (3033096453 : ℕ)^2071*10000000000000^1559 ≤ 5147809948507^1559*5000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3033096453 5000000000 5147809948507 10000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (596748553/1250000000 : ℝ)^2071 ≤ (2340458755587/6250000000000 : ℝ)^1559 := by
    have hnat : (596748553 : ℕ)^2071*6250000000000^1559 ≤ 2340458755587^1559*1250000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      596748553 1250000000 2340458755587 6250000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-477014427/2500000000 : ℝ), (3033096453/5000000000 : ℝ), (596748553/1250000000 : ℝ)] ![(221491208173/2000000000000 : ℝ), (5147809948507/10000000000000 : ℝ), (2340458755587/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-477014427/2500000000 : ℝ)|^2071 ≤ (221491208173/2000000000000 : ℝ)^1559
        have hw : |(-477014427/2500000000 : ℝ)|=(477014427/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3033096453/5000000000 : ℝ)|^2071 ≤ (5147809948507/10000000000000 : ℝ)^1559
        have hw : |(3033096453/5000000000 : ℝ)|=(3033096453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(596748553/1250000000 : ℝ)|^2071 ≤ (2340458755587/6250000000000 : ℝ)^1559
        have hw : |(596748553/1250000000 : ℝ)|=(596748553/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1091_s0_1 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1379916423/2500000000 : ℝ)*x 0 + (-1325559853/5000000000 : ℝ)*x 1 + (4773988507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1379916423/2500000000 : ℝ)^2071 ≤ (45410145205501/100000000000000 : ℝ)^1559 := by
    have hnat : (1379916423 : ℕ)^2071*100000000000000^1559 ≤ 45410145205501^1559*2500000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1379916423 2500000000 45410145205501 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1325559853/5000000000 : ℝ)^2071 ≤ (3428502765827/20000000000000 : ℝ)^1559 := by
    have hnat : (1325559853 : ℕ)^2071*20000000000000^1559 ≤ 3428502765827^1559*5000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325559853 5000000000 3428502765827 20000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4773988507/10000000000 : ℝ)^2071 ≤ (37447340954263/100000000000000 : ℝ)^1559 := by
    have hnat : (4773988507 : ℕ)^2071*100000000000000^1559 ≤ 37447340954263^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4773988507 10000000000 37447340954263 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1379916423/2500000000 : ℝ), (-1325559853/5000000000 : ℝ), (4773988507/10000000000 : ℝ)] ![(45410145205501/100000000000000 : ℝ), (3428502765827/20000000000000 : ℝ), (37447340954263/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1379916423/2500000000 : ℝ)|^2071 ≤ (45410145205501/100000000000000 : ℝ)^1559
        have hw : |(1379916423/2500000000 : ℝ)|=(1379916423/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1325559853/5000000000 : ℝ)|^2071 ≤ (3428502765827/20000000000000 : ℝ)^1559
        have hw : |(-1325559853/5000000000 : ℝ)|=(1325559853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4773988507/10000000000 : ℝ)|^2071 ≤ (37447340954263/100000000000000 : ℝ)^1559
        have hw : |(4773988507/10000000000 : ℝ)|=(4773988507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1091_s0_2 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5519665873/10000000000 : ℝ)*x 0 + (4773988587/10000000000 : ℝ)*x 1 + (-2651119379/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5519665873/10000000000 : ℝ)^2071 ≤ (45410147183621/100000000000000 : ℝ)^1559 := by
    have hnat : (5519665873 : ℕ)^2071*100000000000000^1559 ≤ 45410147183621^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5519665873 10000000000 45410147183621 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4773988587/10000000000 : ℝ)^2071 ≤ (299578734303/800000000000 : ℝ)^1559 := by
    have hnat : (4773988587 : ℕ)^2071*800000000000^1559 ≤ 299578734303^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4773988587 10000000000 299578734303 800000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2651119379/10000000000 : ℝ)^2071 ≤ (2142813877537/12500000000000 : ℝ)^1559 := by
    have hnat : (2651119379 : ℕ)^2071*12500000000000^1559 ≤ 2142813877537^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651119379 10000000000 2142813877537 12500000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5519665873/10000000000 : ℝ), (4773988587/10000000000 : ℝ), (-2651119379/10000000000 : ℝ)] ![(45410147183621/100000000000000 : ℝ), (299578734303/800000000000 : ℝ), (2142813877537/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5519665873/10000000000 : ℝ)|^2071 ≤ (45410147183621/100000000000000 : ℝ)^1559
        have hw : |(5519665873/10000000000 : ℝ)|=(5519665873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4773988587/10000000000 : ℝ)|^2071 ≤ (299578734303/800000000000 : ℝ)^1559
        have hw : |(4773988587/10000000000 : ℝ)|=(4773988587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2651119379/10000000000 : ℝ)|^2071 ≤ (2142813877537/12500000000000 : ℝ)^1559
        have hw : |(-2651119379/10000000000 : ℝ)|=(2651119379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1091_s0_3 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4205147801/10000000000 : ℝ)*x 0 + (3123560639/10000000000 : ℝ)*x 1 + (2834338329/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4205147801/10000000000 : ℝ)^2071 ≤ (3163917451523/10000000000000 : ℝ)^1559 := by
    have hnat : (4205147801 : ℕ)^2071*10000000000000^1559 ≤ 3163917451523^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4205147801 10000000000 3163917451523 10000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3123560639/10000000000 : ℝ)^2071 ≤ (21314987045439/100000000000000 : ℝ)^1559 := by
    have hnat : (3123560639 : ℕ)^2071*100000000000000^1559 ≤ 21314987045439^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3123560639 10000000000 21314987045439 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2834338329/5000000000 : ℝ)^2071 ≤ (47045838428811/100000000000000 : ℝ)^1559 := by
    have hnat : (2834338329 : ℕ)^2071*100000000000000^1559 ≤ 47045838428811^1559*5000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2834338329 5000000000 47045838428811 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4205147801/10000000000 : ℝ), (3123560639/10000000000 : ℝ), (2834338329/5000000000 : ℝ)] ![(3163917451523/10000000000000 : ℝ), (21314987045439/100000000000000 : ℝ), (47045838428811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4205147801/10000000000 : ℝ)|^2071 ≤ (3163917451523/10000000000000 : ℝ)^1559
        have hw : |(4205147801/10000000000 : ℝ)|=(4205147801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3123560639/10000000000 : ℝ)|^2071 ≤ (21314987045439/100000000000000 : ℝ)^1559
        have hw : |(3123560639/10000000000 : ℝ)|=(3123560639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2834338329/5000000000 : ℝ)|^2071 ≤ (47045838428811/100000000000000 : ℝ)^1559
        have hw : |(2834338329/5000000000 : ℝ)|=(2834338329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1091_s0_4 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-119584733/625000000 : ℝ)*x 0 + (4807345587/10000000000 : ℝ)*x 1 + (3015833267/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (119584733/625000000 : ℝ)^2071 ≤ (11115428129291/100000000000000 : ℝ)^1559 := by
    have hnat : (119584733 : ℕ)^2071*100000000000000^1559 ≤ 11115428129291^1559*625000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      119584733 625000000 11115428129291 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4807345587/10000000000 : ℝ)^2071 ≤ (18897662309351/50000000000000 : ℝ)^1559 := by
    have hnat : (4807345587 : ℕ)^2071*50000000000000^1559 ≤ 18897662309351^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4807345587 10000000000 18897662309351 50000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3015833267/5000000000 : ℝ)^2071 ≤ (51089247236823/100000000000000 : ℝ)^1559 := by
    have hnat : (3015833267 : ℕ)^2071*100000000000000^1559 ≤ 51089247236823^1559*5000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3015833267 5000000000 51089247236823 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-119584733/625000000 : ℝ), (4807345587/10000000000 : ℝ), (3015833267/5000000000 : ℝ)] ![(11115428129291/100000000000000 : ℝ), (18897662309351/50000000000000 : ℝ), (51089247236823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-119584733/625000000 : ℝ)|^2071 ≤ (11115428129291/100000000000000 : ℝ)^1559
        have hw : |(-119584733/625000000 : ℝ)|=(119584733/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4807345587/10000000000 : ℝ)|^2071 ≤ (18897662309351/50000000000000 : ℝ)^1559
        have hw : |(4807345587/10000000000 : ℝ)|=(4807345587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3015833267/5000000000 : ℝ)|^2071 ≤ (51089247236823/100000000000000 : ℝ)^1559
        have hw : |(3015833267/5000000000 : ℝ)|=(3015833267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1091_s0_5 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5168806317/10000000000 : ℝ)*x 0 + (-696721849/5000000000 : ℝ)*x 1 + (6031665951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5168806317/10000000000 : ℝ)^2071 ≤ (1664650729273/4000000000000 : ℝ)^1559 := by
    have hnat : (5168806317 : ℕ)^2071*4000000000000^1559 ≤ 1664650729273^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5168806317 10000000000 1664650729273 4000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (696721849/5000000000 : ℝ)^2071 ≤ (7294491075423/100000000000000 : ℝ)^1559 := by
    have hnat : (696721849 : ℕ)^2071*100000000000000^1559 ≤ 7294491075423^1559*5000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      696721849 5000000000 7294491075423 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6031665951/10000000000 : ℝ)^2071 ≤ (51089240676961/100000000000000 : ℝ)^1559 := by
    have hnat : (6031665951 : ℕ)^2071*100000000000000^1559 ≤ 51089240676961^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6031665951 10000000000 51089240676961 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5168806317/10000000000 : ℝ), (-696721849/5000000000 : ℝ), (6031665951/10000000000 : ℝ)] ![(1664650729273/4000000000000 : ℝ), (7294491075423/100000000000000 : ℝ), (51089240676961/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5168806317/10000000000 : ℝ)|^2071 ≤ (1664650729273/4000000000000 : ℝ)^1559
        have hw : |(5168806317/10000000000 : ℝ)|=(5168806317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-696721849/5000000000 : ℝ)|^2071 ≤ (7294491075423/100000000000000 : ℝ)^1559
        have hw : |(-696721849/5000000000 : ℝ)|=(696721849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6031665951/10000000000 : ℝ)|^2071 ≤ (51089240676961/100000000000000 : ℝ)^1559
        have hw : |(6031665951/10000000000 : ℝ)|=(6031665951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1091_s0_6 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5168806867/10000000000 : ℝ)*x 0 + (3015833343/5000000000 : ℝ)*x 1 + (-1393441663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5168806867/10000000000 : ℝ)^2071 ≤ (10404068528607/25000000000000 : ℝ)^1559 := by
    have hnat : (5168806867 : ℕ)^2071*25000000000000^1559 ≤ 10404068528607^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5168806867 10000000000 10404068528607 25000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3015833343/5000000000 : ℝ)^2071 ≤ (51089248947113/100000000000000 : ℝ)^1559 := by
    have hnat : (3015833343 : ℕ)^2071*100000000000000^1559 ≤ 51089248947113^1559*5000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3015833343 5000000000 51089248947113 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1393441663/10000000000 : ℝ)^2071 ≤ (3647238461939/50000000000000 : ℝ)^1559 := by
    have hnat : (1393441663 : ℕ)^2071*50000000000000^1559 ≤ 3647238461939^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1393441663 10000000000 3647238461939 50000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5168806867/10000000000 : ℝ), (3015833343/5000000000 : ℝ), (-1393441663/10000000000 : ℝ)] ![(10404068528607/25000000000000 : ℝ), (51089248947113/100000000000000 : ℝ), (3647238461939/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5168806867/10000000000 : ℝ)|^2071 ≤ (10404068528607/25000000000000 : ℝ)^1559
        have hw : |(5168806867/10000000000 : ℝ)|=(5168806867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3015833343/5000000000 : ℝ)|^2071 ≤ (51089248947113/100000000000000 : ℝ)^1559
        have hw : |(3015833343/5000000000 : ℝ)|=(3015833343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1393441663/10000000000 : ℝ)|^2071 ≤ (3647238461939/50000000000000 : ℝ)^1559
        have hw : |(-1393441663/10000000000 : ℝ)|=(1393441663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1091_s0_7 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4215580227/10000000000 : ℝ)*x 0 + (2801488021/5000000000 : ℝ)*x 1 + (1595781989/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4215580227/10000000000 : ℝ)^2071 ≤ (31743487882233/100000000000000 : ℝ)^1559 := by
    have hnat : (4215580227 : ℕ)^2071*100000000000000^1559 ≤ 31743487882233^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4215580227 10000000000 31743487882233 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2801488021/5000000000 : ℝ)^2071 ≤ (23161439886419/50000000000000 : ℝ)^1559 := by
    have hnat : (2801488021 : ℕ)^2071*50000000000000^1559 ≤ 23161439886419^1559*5000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2801488021 5000000000 23161439886419 50000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1595781989/5000000000 : ℝ)^2071 ≤ (2193363233097/10000000000000 : ℝ)^1559 := by
    have hnat : (1595781989 : ℕ)^2071*10000000000000^1559 ≤ 2193363233097^1559*5000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1595781989 5000000000 2193363233097 10000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4215580227/10000000000 : ℝ), (2801488021/5000000000 : ℝ), (1595781989/5000000000 : ℝ)] ![(31743487882233/100000000000000 : ℝ), (23161439886419/50000000000000 : ℝ), (2193363233097/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4215580227/10000000000 : ℝ)|^2071 ≤ (31743487882233/100000000000000 : ℝ)^1559
        have hw : |(4215580227/10000000000 : ℝ)|=(4215580227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2801488021/5000000000 : ℝ)|^2071 ≤ (23161439886419/50000000000000 : ℝ)^1559
        have hw : |(2801488021/5000000000 : ℝ)|=(2801488021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1595781989/5000000000 : ℝ)|^2071 ≤ (2193363233097/10000000000000 : ℝ)^1559
        have hw : |(1595781989/5000000000 : ℝ)|=(1595781989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1091_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29695923/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (101/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7003/25000 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
  have base45 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [sign1]
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
  have hpowlo : (0 : ℝ) ^ (8283/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8283 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8283*1^2048 ≤ 0^2048*1^8283 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8283 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8283 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8283/2048 : ℝ) ≤ (1228932600060095831/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8283 ≤ (1228932600060095831/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8283*50000000000000000000^2048 ≤ 1228932600060095831^2048*5^8283 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1228932600060095831 50000000000000000000 8283 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1228932600060095831/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8283 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8283/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8283 := by
      have hnat : (1 : ℕ)^2048*1^8283 ≤ 1^8283*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8283 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8283 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (51228932600060095831/50000000000000000000 : ℝ) ≤ (2515054327969959/2500000000000000 : ℝ) ^ (8283/2048 : ℝ) := by
    have hpowers : (51228932600060095831/50000000000000000000 : ℝ)^2048 ≤ (2515054327969959/2500000000000000 : ℝ)^8283 := by
      have hnat : (51228932600060095831 : ℕ)^2048*2500000000000000^8283 ≤ 2515054327969959^8283*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51228932600060095831 50000000000000000000 2515054327969959 2500000000000000 2048 8283 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2515054327969959/2500000000000000 : ℝ)) (X := (51228932600060095831/50000000000000000000 : ℝ)) (by norm_num) 8283 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (26228932600060095831/25000000000000000000 : ℝ) ≤ (1265054327969959/1250000000000000 : ℝ) ^ (8283/2048 : ℝ) := by
    have hpowers : (26228932600060095831/25000000000000000000 : ℝ)^2048 ≤ (1265054327969959/1250000000000000 : ℝ)^8283 := by
      have hnat : (26228932600060095831 : ℕ)^2048*1250000000000000^8283 ≤ 1265054327969959^8283*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26228932600060095831 25000000000000000000 1265054327969959 1250000000000000 2048 8283 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1265054327969959/1250000000000000 : ℝ)) (X := (26228932600060095831/25000000000000000000 : ℝ)) (by norm_num) 8283 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(15054327969959/1000000000000000 : ℝ)*(0 : ℝ))^(8283/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(15054327969959/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1228932600060095831/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(15054327969959/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8283/2048 : ℝ) := by
    rw [show (1 : ℝ)+(15054327969959/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2515054327969959/2500000000000000 : ℝ) by norm_num, show 1+(1228932600060095831/50000000000000000000 : ℝ)+(0 : ℝ)=(51228932600060095831/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1228932600060095831/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(15054327969959/1000000000000000 : ℝ)*(2/5 : ℝ))^(8283/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(15054327969959/1000000000000000 : ℝ)*(2/5 : ℝ)=(1265054327969959/1250000000000000 : ℝ) by norm_num, show 1+2*(1228932600060095831/50000000000000000000 : ℝ)=(26228932600060095831/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(15054327969959/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8283/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (15054327969959/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(15054327969959/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8283/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (15054327969959/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(15054327969959/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8283/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (15054327969959/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-477014427/2500000000 : ℝ)*X 0 0+(3033096453/5000000000 : ℝ)*X 0 1+(596748553/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1379916423/2500000000 : ℝ)*X 1 0+(-1325559853/5000000000 : ℝ)*X 1 1+(4773988507/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5519665873/10000000000 : ℝ)*X 2 0+(4773988587/10000000000 : ℝ)*X 2 1+(-2651119379/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4205147801/10000000000 : ℝ)*X 0 0+(3123560639/10000000000 : ℝ)*X 0 1+(2834338329/5000000000 : ℝ)*X 0 2+(4205147801/10000000000 : ℝ)*X 1 0+(3123560639/10000000000 : ℝ)*X 1 1+(2834338329/5000000000 : ℝ)*X 1 2+(4205147801/10000000000 : ℝ)*X 2 0+(3123560639/10000000000 : ℝ)*X 2 1+(2834338329/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-119584733/625000000 : ℝ)*X 0 0+(4807345587/10000000000 : ℝ)*X 0 1+(3015833267/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5168806317/10000000000 : ℝ)*X 1 0+(-696721849/5000000000 : ℝ)*X 1 1+(6031665951/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5168806867/10000000000 : ℝ)*X 2 0+(3015833343/5000000000 : ℝ)*X 2 1+(-1393441663/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4215580227/10000000000 : ℝ)*X 0 0+(2801488021/5000000000 : ℝ)*X 0 1+(1595781989/5000000000 : ℝ)*X 0 2+(4215580227/10000000000 : ℝ)*X 1 0+(2801488021/5000000000 : ℝ)*X 1 1+(1595781989/5000000000 : ℝ)*X 1 2+(4215580227/10000000000 : ℝ)*X 2 0+(2801488021/5000000000 : ℝ)*X 2 1+(1595781989/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2008097286664458960303/781250000000000000000000000 : ℝ) := by norm_num
    linear_combination (9496591/50000000000000 : ℝ)*(base1) + (312344051/50000000000000 : ℝ)*(base19) + (144041831/25000000000000 : ℝ)*(base23) + (73897531/100000000000000 : ℝ)*(base24) + (160514647/100000000000000 : ℝ)*(upper3) + (36462058750089/6250000000000 : ℝ)*(major0) + (36462058750089/6250000000000 : ℝ)*(major1) + (36462058750089/6250000000000 : ℝ)*(major2) + (773873380224497/100000000000000 : ℝ)*(sp0) + (38693701749937/5000000000000 : ℝ)*(sp1) + (386937004810993/50000000000000 : ℝ)*(sp2) + (49113749211831/12500000000000 : ℝ)*(sp3) + (1298455527/100000000000000 : ℝ)*(sp4) + (224389871/20000000000000 : ℝ)*(sp7) + (78582226927437/20000000000000 : ℝ)*(f.failure) + (386937329843421/50000000000000 : ℝ)*(f.sum) + (3320377057137/1562500000000000000000000000 : ℝ)*base66 + (3797598254899/6250000000000000000000000000 : ℝ)*base68 + (10296198923649/6250000000000000000000000000 : ℝ)*base70 + (9229848879899/6250000000000000000000000000 : ℝ)*base72 + (8687164867399/3125000000000000000000000000 : ℝ)*base74 + (30465105386149/6250000000000000000000000000 : ℝ)*base76 + (7561053007601/6250000000000000000000000000 : ℝ)*base77 + (12950863301351/6250000000000000000000000000 : ℝ)*base79 + (13454200298649/3125000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (260649/400000000000000000000 : ℝ)*base90 + (260649/400000000000000000000 : ℝ)*base92 + (260649/400000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (33068928370784136928869/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1167918199/100000000000000 : ℝ)*(base19) + (50473353/3125000000000 : ℝ)*(base23) + (163661333/50000000000000 : ℝ)*(base39) + (293179577/100000000000000 : ℝ)*(base45) + (122671351/100000000000000 : ℝ)*(upper3) + (336030871/100000000000000 : ℝ)*(upper5) + (307867353731909/50000000000000 : ℝ)*(major0) + (307867353731909/50000000000000 : ℝ)*(major1) + (19241699379411/3125000000000 : ℝ)*(major2) + (626529101/100000000000000 : ℝ)*(sp2) + (6381060737901/781250000000 : ℝ)*(sp4) + (816774606533129/100000000000000 : ℝ)*(sp5) + (816773860097597/100000000000000 : ℝ)*(sp6) + (414693092694117/100000000000000 : ℝ)*(sp7) + (414693092694117/100000000000000 : ℝ)*(f.failure) + (408388050886997/50000000000000 : ℝ)*(f.sum) + (6010764159623/10000000000000000000000000000 : ℝ)*base65 + (14601606542101/3125000000000000000000000000 : ℝ)*base68 + (65980037178269/50000000000000000000000000000 : ℝ)*base70 + (4092125298351/3125000000000000000000000000 : ℝ)*base72 + (6525796810377/10000000000000000000000000000 : ℝ)*base74 + (17646713528269/50000000000000000000000000000 : ℝ)*base76 + (44985974828269/50000000000000000000000000000 : ℝ)*base78 + (306834745428269/50000000000000000000000000000 : ℝ)*base80 + (221099058321731/25000000000000000000000000000 : ℝ)*base81 + (984991/2000000000000000000000 : ℝ)*base89 + (984991/2000000000000000000000 : ℝ)*base91 + (984991/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1091_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29695923/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (101/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7003/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1091_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1091_s1_0 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-52909881/250000000 : ℝ)*x 0 + (571536529/1000000000 : ℝ)*x 1 + (4991412779/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (52909881/250000000 : ℝ)^2071 ≤ (12709024070167/100000000000000 : ℝ)^1559 := by
    have hnat : (52909881 : ℕ)^2071*100000000000000^1559 ≤ 12709024070167^1559*250000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52909881 250000000 12709024070167 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (571536529/1000000000 : ℝ)^2071 ≤ (47561269446199/100000000000000 : ℝ)^1559 := by
    have hnat : (571536529 : ℕ)^2071*100000000000000^1559 ≤ 47561269446199^1559*1000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      571536529 1000000000 47561269446199 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4991412779/10000000000 : ℝ)^2071 ≤ (1241553327197/3125000000000 : ℝ)^1559 := by
    have hnat : (4991412779 : ℕ)^2071*3125000000000^1559 ≤ 1241553327197^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4991412779 10000000000 1241553327197 3125000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-52909881/250000000 : ℝ), (571536529/1000000000 : ℝ), (4991412779/10000000000 : ℝ)] ![(12709024070167/100000000000000 : ℝ), (47561269446199/100000000000000 : ℝ), (1241553327197/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-52909881/250000000 : ℝ)|^2071 ≤ (12709024070167/100000000000000 : ℝ)^1559
        have hw : |(-52909881/250000000 : ℝ)|=(52909881/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(571536529/1000000000 : ℝ)|^2071 ≤ (47561269446199/100000000000000 : ℝ)^1559
        have hw : |(571536529/1000000000 : ℝ)|=(571536529/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4991412779/10000000000 : ℝ)|^2071 ≤ (1241553327197/3125000000000 : ℝ)^1559
        have hw : |(4991412779/10000000000 : ℝ)|=(4991412779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1091_s1_1 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5421932401/10000000000 : ℝ)*x 0 + (-2508112849/10000000000 : ℝ)*x 1 + (4991412989/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5421932401/10000000000 : ℝ)^2071 ≤ (44345151591297/100000000000000 : ℝ)^1559 := by
    have hnat : (5421932401 : ℕ)^2071*100000000000000^1559 ≤ 44345151591297^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5421932401 10000000000 44345151591297 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2508112849/10000000000 : ℝ)^2071 ≤ (7962569854107/50000000000000 : ℝ)^1559 := by
    have hnat : (2508112849 : ℕ)^2071*50000000000000^1559 ≤ 7962569854107^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2508112849 10000000000 7962569854107 50000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4991412989/10000000000 : ℝ)^2071 ≤ (1589188347631/4000000000000 : ℝ)^1559 := by
    have hnat : (4991412989 : ℕ)^2071*4000000000000^1559 ≤ 1589188347631^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4991412989 10000000000 1589188347631 4000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5421932401/10000000000 : ℝ), (-2508112849/10000000000 : ℝ), (4991412989/10000000000 : ℝ)] ![(44345151591297/100000000000000 : ℝ), (7962569854107/50000000000000 : ℝ), (1589188347631/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5421932401/10000000000 : ℝ)|^2071 ≤ (44345151591297/100000000000000 : ℝ)^1559
        have hw : |(5421932401/10000000000 : ℝ)|=(5421932401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2508112849/10000000000 : ℝ)|^2071 ≤ (7962569854107/50000000000000 : ℝ)^1559
        have hw : |(-2508112849/10000000000 : ℝ)|=(2508112849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4991412989/10000000000 : ℝ)|^2071 ≤ (1589188347631/4000000000000 : ℝ)^1559
        have hw : |(4991412989/10000000000 : ℝ)|=(4991412989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1091_s1_2 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2710966657/5000000000 : ℝ)*x 0 + (4991412057/10000000000 : ℝ)*x 1 + (-2508112841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2710966657/5000000000 : ℝ)^2071 ≤ (22172580755479/50000000000000 : ℝ)^1559 := by
    have hnat : (2710966657 : ℕ)^2071*50000000000000^1559 ≤ 22172580755479^1559*5000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2710966657 5000000000 22172580755479 50000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4991412057/10000000000 : ℝ)^2071 ≤ (2483106177257/6250000000000 : ℝ)^1559 := by
    have hnat : (4991412057 : ℕ)^2071*6250000000000^1559 ≤ 2483106177257^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4991412057 10000000000 2483106177257 6250000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2508112841/10000000000 : ℝ)^2071 ≤ (15925139640737/100000000000000 : ℝ)^1559 := by
    have hnat : (2508112841 : ℕ)^2071*100000000000000^1559 ≤ 15925139640737^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2508112841 10000000000 15925139640737 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2710966657/5000000000 : ℝ), (4991412057/10000000000 : ℝ), (-2508112841/10000000000 : ℝ)] ![(22172580755479/50000000000000 : ℝ), (2483106177257/6250000000000 : ℝ), (15925139640737/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2710966657/5000000000 : ℝ)|^2071 ≤ (22172580755479/50000000000000 : ℝ)^1559
        have hw : |(2710966657/5000000000 : ℝ)|=(2710966657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4991412057/10000000000 : ℝ)|^2071 ≤ (2483106177257/6250000000000 : ℝ)^1559
        have hw : |(4991412057/10000000000 : ℝ)|=(4991412057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2508112841/10000000000 : ℝ)|^2071 ≤ (15925139640737/100000000000000 : ℝ)^1559
        have hw : |(-2508112841/10000000000 : ℝ)|=(2508112841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1091_s1_3 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2160862517/5000000000 : ℝ)*x 0 + (3667357333/10000000000 : ℝ)*x 1 + (5093247141/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2160862517/5000000000 : ℝ)^2071 ≤ (16404811175679/50000000000000 : ℝ)^1559 := by
    have hnat : (2160862517 : ℕ)^2071*50000000000000^1559 ≤ 16404811175679^1559*5000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2160862517 5000000000 16404811175679 50000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3667357333/10000000000 : ℝ)^2071 ≤ (6595079246409/25000000000000 : ℝ)^1559 := by
    have hnat : (3667357333 : ℕ)^2071*25000000000000^1559 ≤ 6595079246409^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3667357333 10000000000 6595079246409 25000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5093247141/10000000000 : ℝ)^2071 ≤ (20405030322931/50000000000000 : ℝ)^1559 := by
    have hnat : (5093247141 : ℕ)^2071*50000000000000^1559 ≤ 20405030322931^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5093247141 10000000000 20405030322931 50000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2160862517/5000000000 : ℝ), (3667357333/10000000000 : ℝ), (5093247141/10000000000 : ℝ)] ![(16404811175679/50000000000000 : ℝ), (6595079246409/25000000000000 : ℝ), (20405030322931/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2160862517/5000000000 : ℝ)|^2071 ≤ (16404811175679/50000000000000 : ℝ)^1559
        have hw : |(2160862517/5000000000 : ℝ)|=(2160862517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3667357333/10000000000 : ℝ)|^2071 ≤ (6595079246409/25000000000000 : ℝ)^1559
        have hw : |(3667357333/10000000000 : ℝ)|=(3667357333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5093247141/10000000000 : ℝ)|^2071 ≤ (20405030322931/50000000000000 : ℝ)^1559
        have hw : |(5093247141/10000000000 : ℝ)|=(5093247141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1091_s1_4 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2117279177/10000000000 : ℝ)*x 0 + (5001491351/10000000000 : ℝ)*x 1 + (5705081051/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2117279177/10000000000 : ℝ)^2071 ≤ (12716075878577/100000000000000 : ℝ)^1559 := by
    have hnat : (2117279177 : ℕ)^2071*100000000000000^1559 ≤ 12716075878577^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117279177 10000000000 12716075878577 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5001491351/10000000000 : ℝ)^2071 ≤ (39836309307753/100000000000000 : ℝ)^1559 := by
    have hnat : (5001491351 : ℕ)^2071*100000000000000^1559 ≤ 39836309307753^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5001491351 10000000000 39836309307753 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5705081051/10000000000 : ℝ)^2071 ≤ (23723807399907/50000000000000 : ℝ)^1559 := by
    have hnat : (5705081051 : ℕ)^2071*50000000000000^1559 ≤ 23723807399907^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5705081051 10000000000 23723807399907 50000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2117279177/10000000000 : ℝ), (5001491351/10000000000 : ℝ), (5705081051/10000000000 : ℝ)] ![(12716075878577/100000000000000 : ℝ), (39836309307753/100000000000000 : ℝ), (23723807399907/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2117279177/10000000000 : ℝ)|^2071 ≤ (12716075878577/100000000000000 : ℝ)^1559
        have hw : |(-2117279177/10000000000 : ℝ)|=(2117279177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5001491351/10000000000 : ℝ)|^2071 ≤ (39836309307753/100000000000000 : ℝ)^1559
        have hw : |(5001491351/10000000000 : ℝ)|=(5001491351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5705081051/10000000000 : ℝ)|^2071 ≤ (23723807399907/50000000000000 : ℝ)^1559
        have hw : |(5705081051/10000000000 : ℝ)|=(5705081051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1091_s1_5 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5236804937/10000000000 : ℝ)*x 0 + (-1794441743/10000000000 : ℝ)*x 1 + (5705083503/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5236804937/10000000000 : ℝ)^2071 ≤ (10586280913099/25000000000000 : ℝ)^1559 := by
    have hnat : (5236804937 : ℕ)^2071*25000000000000^1559 ≤ 10586280913099^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5236804937 10000000000 10586280913099 25000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1794441743/10000000000 : ℝ)^2071 ≤ (1020723443529/10000000000000 : ℝ)^1559 := by
    have hnat : (1794441743 : ℕ)^2071*10000000000000^1559 ≤ 1020723443529^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1794441743 10000000000 1020723443529 10000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5705083503/10000000000 : ℝ)^2071 ≤ (47447641889691/100000000000000 : ℝ)^1559 := by
    have hnat : (5705083503 : ℕ)^2071*100000000000000^1559 ≤ 47447641889691^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5705083503 10000000000 47447641889691 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5236804937/10000000000 : ℝ), (-1794441743/10000000000 : ℝ), (5705083503/10000000000 : ℝ)] ![(10586280913099/25000000000000 : ℝ), (1020723443529/10000000000000 : ℝ), (47447641889691/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5236804937/10000000000 : ℝ)|^2071 ≤ (10586280913099/25000000000000 : ℝ)^1559
        have hw : |(5236804937/10000000000 : ℝ)|=(5236804937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1794441743/10000000000 : ℝ)|^2071 ≤ (1020723443529/10000000000000 : ℝ)^1559
        have hw : |(-1794441743/10000000000 : ℝ)|=(1794441743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5705083503/10000000000 : ℝ)|^2071 ≤ (47447641889691/100000000000000 : ℝ)^1559
        have hw : |(5705083503/10000000000 : ℝ)|=(5705083503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1091_s1_6 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5236802847/10000000000 : ℝ)*x 0 + (2852542929/5000000000 : ℝ)*x 1 + (-1794441271/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5236802847/10000000000 : ℝ)^2071 ≤ (42345101202349/100000000000000 : ℝ)^1559 := by
    have hnat : (5236802847 : ℕ)^2071*100000000000000^1559 ≤ 42345101202349^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5236802847 10000000000 42345101202349 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2852542929/5000000000 : ℝ)^2071 ≤ (4744766790791/10000000000000 : ℝ)^1559 := by
    have hnat : (2852542929 : ℕ)^2071*10000000000000^1559 ≤ 4744766790791^1559*5000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2852542929 5000000000 4744766790791 10000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1794441271/10000000000 : ℝ)^2071 ≤ (637951929293/6250000000000 : ℝ)^1559 := by
    have hnat : (1794441271 : ℕ)^2071*6250000000000^1559 ≤ 637951929293^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1794441271 10000000000 637951929293 6250000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5236802847/10000000000 : ℝ), (2852542929/5000000000 : ℝ), (-1794441271/10000000000 : ℝ)] ![(42345101202349/100000000000000 : ℝ), (4744766790791/10000000000000 : ℝ), (637951929293/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5236802847/10000000000 : ℝ)|^2071 ≤ (42345101202349/100000000000000 : ℝ)^1559
        have hw : |(5236802847/10000000000 : ℝ)|=(5236802847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2852542929/5000000000 : ℝ)|^2071 ≤ (4744766790791/10000000000000 : ℝ)^1559
        have hw : |(2852542929/5000000000 : ℝ)|=(2852542929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1794441271/10000000000 : ℝ)|^2071 ≤ (637951929293/6250000000000 : ℝ)^1559
        have hw : |(-1794441271/10000000000 : ℝ)|=(1794441271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1091_s1_7 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2161730301/5000000000 : ℝ)*x 0 + (2536696631/5000000000 : ℝ)*x 1 + (921902049/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2161730301/5000000000 : ℝ)^2071 ≤ (1313085071867/4000000000000 : ℝ)^1559 := by
    have hnat : (2161730301 : ℕ)^2071*4000000000000^1559 ≤ 1313085071867^1559*5000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2161730301 5000000000 1313085071867 4000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2536696631/5000000000 : ℝ)^2071 ≤ (5074858820251/12500000000000 : ℝ)^1559 := by
    have hnat : (2536696631 : ℕ)^2071*12500000000000^1559 ≤ 5074858820251^1559*5000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2536696631 5000000000 5074858820251 12500000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (921902049/2500000000 : ℝ)^2071 ≤ (26574002629131/100000000000000 : ℝ)^1559 := by
    have hnat : (921902049 : ℕ)^2071*100000000000000^1559 ≤ 26574002629131^1559*2500000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      921902049 2500000000 26574002629131 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2161730301/5000000000 : ℝ), (2536696631/5000000000 : ℝ), (921902049/2500000000 : ℝ)] ![(1313085071867/4000000000000 : ℝ), (5074858820251/12500000000000 : ℝ), (26574002629131/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2161730301/5000000000 : ℝ)|^2071 ≤ (1313085071867/4000000000000 : ℝ)^1559
        have hw : |(2161730301/5000000000 : ℝ)|=(2161730301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2536696631/5000000000 : ℝ)|^2071 ≤ (5074858820251/12500000000000 : ℝ)^1559
        have hw : |(2536696631/5000000000 : ℝ)|=(2536696631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(921902049/2500000000 : ℝ)|^2071 ≤ (26574002629131/100000000000000 : ℝ)^1559
        have hw : |(921902049/2500000000 : ℝ)|=(921902049/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1091_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29695923/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7003/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (101/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5359/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20673/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7003/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (101/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7003/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (101/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7003/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (101/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7003/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (101/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7003/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (101/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7003/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (101/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (101/50000 : ℝ) ^ (8283/2048 : ℝ) ≤ (252756627/20000000000000000000 : ℝ) := by
    have hpowers : (101/50000 : ℝ)^8283 ≤ (252756627/20000000000000000000 : ℝ)^2048 := by
      have hnat : (101 : ℕ)^8283*20000000000000000000^2048 ≤ 252756627^2048*50000^8283 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101 50000 252756627 20000000000000000000 8283 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (101/50000 : ℝ)) (X := (252756627/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8283 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7003/25000 : ℝ) ^ (8283/2048 : ℝ) ≤ (581861984388593123/100000000000000000000 : ℝ) := by
    have hpowers : (7003/25000 : ℝ)^8283 ≤ (581861984388593123/100000000000000000000 : ℝ)^2048 := by
      have hnat : (7003 : ℕ)^8283*100000000000000000000^2048 ≤ 581861984388593123^2048*25000^8283 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7003 25000 581861984388593123 100000000000000000000 8283 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7003/25000 : ℝ)) (X := (581861984388593123/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8283 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000000000252756627/10000000000000000000 : ℝ) ≤ (2000000000012499/2000000000000000 : ℝ) ^ (8283/2048 : ℝ) := by
    have hpowers : (10000000000252756627/10000000000000000000 : ℝ)^2048 ≤ (2000000000012499/2000000000000000 : ℝ)^8283 := by
      have hnat : (10000000000252756627 : ℕ)^2048*2000000000000000^8283 ≤ 2000000000012499^8283*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000000000252756627 10000000000000000000 2000000000012499 2000000000000000 2048 8283 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000000000012499/2000000000000000 : ℝ)) (X := (10000000000252756627/10000000000000000000 : ℝ)) (by norm_num) 8283 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50290930992826188129/50000000000000000000 : ℝ) ≤ (5007177668080017/5000000000000000 : ℝ) ^ (8283/2048 : ℝ) := by
    have hpowers : (50290930992826188129/50000000000000000000 : ℝ)^2048 ≤ (5007177668080017/5000000000000000 : ℝ)^8283 := by
      have hnat : (50290930992826188129 : ℕ)^2048*5000000000000000^8283 ≤ 5007177668080017^8283*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50290930992826188129 50000000000000000000 5007177668080017 5000000000000000 2048 8283 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5007177668080017/5000000000000000 : ℝ)) (X := (50290930992826188129/50000000000000000000 : ℝ)) (by norm_num) 8283 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50581861984388593123/50000000000000000000 : ℝ) ≤ (10028710672257573/10000000000000000 : ℝ) ^ (8283/2048 : ℝ) := by
    have hpowers : (50581861984388593123/50000000000000000000 : ℝ)^2048 ≤ (10028710672257573/10000000000000000 : ℝ)^8283 := by
      have hnat : (50581861984388593123 : ℕ)^2048*10000000000000000^8283 ≤ 10028710672257573^8283*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50581861984388593123 50000000000000000000 10028710672257573 10000000000000000 2048 8283 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10028710672257573/10000000000000000 : ℝ)) (X := (50581861984388593123/50000000000000000000 : ℝ)) (by norm_num) 8283 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(252756627/20000000000000000000 : ℝ) ≤ ((15449677802553032233/15450000000000000000 : ℝ)+2*(1595037344171/309000000000000 : ℝ)*(101/50000 : ℝ))^(8283/2048 : ℝ) := by
    rw [show (15449677802553032233/15450000000000000000 : ℝ)+2*(1595037344171/309000000000000 : ℝ)*(101/50000 : ℝ)=(2000000000012499/2000000000000000 : ℝ) by norm_num, show 1+2*(252756627/20000000000000000000 : ℝ)=(10000000000252756627/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(581861984388593123/100000000000000000000 : ℝ)+(252756627/20000000000000000000 : ℝ) ≤ ((15449677802553032233/15450000000000000000 : ℝ)+(1595037344171/309000000000000 : ℝ)*((7003/25000 : ℝ)+(101/50000 : ℝ)))^(8283/2048 : ℝ) := by
    rw [show (15449677802553032233/15450000000000000000 : ℝ)+(1595037344171/309000000000000 : ℝ)*((7003/25000 : ℝ)+(101/50000 : ℝ))=(5007177668080017/5000000000000000 : ℝ) by norm_num, show 1+(581861984388593123/100000000000000000000 : ℝ)+(252756627/20000000000000000000 : ℝ)=(50290930992826188129/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(581861984388593123/100000000000000000000 : ℝ) ≤ ((15449677802553032233/15450000000000000000 : ℝ)+2*(1595037344171/309000000000000 : ℝ)*(7003/25000 : ℝ))^(8283/2048 : ℝ) := by
    rw [show (15449677802553032233/15450000000000000000 : ℝ)+2*(1595037344171/309000000000000 : ℝ)*(7003/25000 : ℝ)=(10028710672257573/10000000000000000 : ℝ) by norm_num, show 1+2*(581861984388593123/100000000000000000000 : ℝ)=(50581861984388593123/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (15449677802553032233/15450000000000000000 : ℝ)*(X 1 0+X 2 0)+(1595037344171/309000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8283/2048 : ℝ)) (lo := (101/50000 : ℝ)) (hi := (7003/25000 : ℝ)) (c := (15449677802553032233/15450000000000000000 : ℝ)) (alpha := (1595037344171/309000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (15449677802553032233/15450000000000000000 : ℝ)*(X 0 1+X 2 1)+(1595037344171/309000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8283/2048 : ℝ)) (lo := (101/50000 : ℝ)) (hi := (7003/25000 : ℝ)) (c := (15449677802553032233/15450000000000000000 : ℝ)) (alpha := (1595037344171/309000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (15449677802553032233/15450000000000000000 : ℝ)*(X 0 2+X 1 2)+(1595037344171/309000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8283/2048 : ℝ)) (lo := (101/50000 : ℝ)) (hi := (7003/25000 : ℝ)) (c := (15449677802553032233/15450000000000000000 : ℝ)) (alpha := (1595037344171/309000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-52909881/250000000 : ℝ)*X 0 0+(571536529/1000000000 : ℝ)*X 0 1+(4991412779/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5421932401/10000000000 : ℝ)*X 1 0+(-2508112849/10000000000 : ℝ)*X 1 1+(4991412989/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2710966657/5000000000 : ℝ)*X 2 0+(4991412057/10000000000 : ℝ)*X 2 1+(-2508112841/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2160862517/5000000000 : ℝ)*X 0 0+(3667357333/10000000000 : ℝ)*X 0 1+(5093247141/10000000000 : ℝ)*X 0 2+(2160862517/5000000000 : ℝ)*X 1 0+(3667357333/10000000000 : ℝ)*X 1 1+(5093247141/10000000000 : ℝ)*X 1 2+(2160862517/5000000000 : ℝ)*X 2 0+(3667357333/10000000000 : ℝ)*X 2 1+(5093247141/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2117279177/10000000000 : ℝ)*X 0 0+(5001491351/10000000000 : ℝ)*X 0 1+(5705081051/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5236804937/10000000000 : ℝ)*X 1 0+(-1794441743/10000000000 : ℝ)*X 1 1+(5705083503/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5236802847/10000000000 : ℝ)*X 2 0+(2852542929/5000000000 : ℝ)*X 2 1+(-1794441271/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2161730301/5000000000 : ℝ)*X 0 0+(2536696631/5000000000 : ℝ)*X 0 1+(921902049/2500000000 : ℝ)*X 0 2+(2161730301/5000000000 : ℝ)*X 1 0+(2536696631/5000000000 : ℝ)*X 1 1+(921902049/2500000000 : ℝ)*X 1 2+(2161730301/5000000000 : ℝ)*X 2 0+(2536696631/5000000000 : ℝ)*X 2 1+(921902049/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (407784723805181173790428443/64375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (166823829/100000000000000 : ℝ)*(base1) + (253786859/20000000000000 : ℝ)*(base19) + (750767203/50000000000000 : ℝ)*(base23) + (100153673/100000000000000 : ℝ)*(upper3) + (41431729/25000000000000 : ℝ)*(upper5) + (520660074665371/50000000000000 : ℝ)*(major0) + (520660074665371/50000000000000 : ℝ)*(major1) + (520660074665371/50000000000000 : ℝ)*(major2) + (690655775176801/50000000000000 : ℝ)*(sp0) + (690658428206533/50000000000000 : ℝ)*(sp1) + (276263324762591/20000000000000 : ℝ)*(sp2) + (701319114087771/100000000000000 : ℝ)*(sp3) + (1685454397/25000000000000 : ℝ)*(sp4) + (1340625927/50000000000000 : ℝ)*(sp7) + (350660981081727/50000000000000 : ℝ)*(f.failure) + (1381318125347361/100000000000000 : ℝ)*(f.sum) + (15507365110091/7725000000000000000000000000 : ℝ)*base65 + (7117093910603546557/772500000000000000000000000000000 : ℝ)*base68 + (2750377224801453443/772500000000000000000000000000000 : ℝ)*base69 + (871530544756046557/772500000000000000000000000000000 : ℝ)*base72 + (926180738221/1931250000000000000000000000 : ℝ)*base74 + (334145231078546557/772500000000000000000000000000000 : ℝ)*base76 + (279897054346046557/772500000000000000000000000000000 : ℝ)*base78 + (4336744716361046557/772500000000000000000000000000000 : ℝ)*base80 + (38807840940941/7725000000000000000000000000 : ℝ)*base81 + (1699021/1000000000000000000000 : ℝ)*base89 + (1699021/1000000000000000000000 : ℝ)*base91 + (1699021/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (131607309601988869584780663/32187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3025601039/100000000000000 : ℝ)*(base19) + (3111252869/100000000000000 : ℝ)*(base23) + (149067179/50000000000000 : ℝ)*(upper2) + (540598329/100000000000000 : ℝ)*(upper3) + (586478861/100000000000000 : ℝ)*(upper5) + (267861558149211/25000000000000 : ℝ)*(major0) + (267861558149211/25000000000000 : ℝ)*(major1) + (267861558149211/25000000000000 : ℝ)*(major2) + (3879136269/25000000000000 : ℝ)*(sp1) + (17880401379/100000000000000 : ℝ)*(sp2) + (88830041047233/6250000000000 : ℝ)*(sp4) + (1421262114609613/100000000000000 : ℝ)*(sp5) + (35531491627537/2500000000000 : ℝ)*(sp6) + (721611672145597/100000000000000 : ℝ)*(sp7) + (721611672145597/100000000000000 : ℝ)*(f.failure) + (88830041047233/6250000000000 : ℝ)*(f.sum) + (393831536787/321875000000000000000000000 : ℝ)*base66 + (18004820621022721/128750000000000000000000000000000 : ℝ)*base67 + (822442631121477279/128750000000000000000000000000000 : ℝ)*base70 + (545232694162727279/128750000000000000000000000000000 : ℝ)*base72 + (7623619206229/2575000000000000000000000000 : ℝ)*base73 + (334917414402727279/128750000000000000000000000000000 : ℝ)*base76 + (696138857946477279/128750000000000000000000000000000 : ℝ)*base78 + (434060623435227279/128750000000000000000000000000000 : ℝ)*base80 + (6281673730921/2575000000000000000000000000 : ℝ)*base82 + (13301031/2000000000000000000000 : ℝ)*base89 + (13301031/2000000000000000000000 : ℝ)*base91 + (13301031/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1091_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29695923/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7003/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (101/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5359/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20673/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1091_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1091_s2_0 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2172414799/10000000000 : ℝ)*x 0 + (345050397/625000000 : ℝ)*x 1 + (1030080731/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2172414799/10000000000 : ℝ)^2071 ≤ (13157833153409/100000000000000 : ℝ)^1559 := by
    have hnat : (2172414799 : ℕ)^2071*100000000000000^1559 ≤ 13157833153409^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2172414799 10000000000 13157833153409 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (345050397/625000000 : ℝ)^2071 ≤ (45422611720053/100000000000000 : ℝ)^1559 := by
    have hnat : (345050397 : ℕ)^2071*100000000000000^1559 ≤ 45422611720053^1559*625000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      345050397 625000000 45422611720053 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1030080731/2000000000 : ℝ)^2071 ≤ (4141955511119/10000000000000 : ℝ)^1559 := by
    have hnat : (1030080731 : ℕ)^2071*10000000000000^1559 ≤ 4141955511119^1559*2000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030080731 2000000000 4141955511119 10000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2172414799/10000000000 : ℝ), (345050397/625000000 : ℝ), (1030080731/2000000000 : ℝ)] ![(13157833153409/100000000000000 : ℝ), (45422611720053/100000000000000 : ℝ), (4141955511119/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2172414799/10000000000 : ℝ)|^2071 ≤ (13157833153409/100000000000000 : ℝ)^1559
        have hw : |(-2172414799/10000000000 : ℝ)|=(2172414799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(345050397/625000000 : ℝ)|^2071 ≤ (45422611720053/100000000000000 : ℝ)^1559
        have hw : |(345050397/625000000 : ℝ)|=(345050397/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1030080731/2000000000 : ℝ)|^2071 ≤ (4141955511119/10000000000000 : ℝ)^1559
        have hw : |(1030080731/2000000000 : ℝ)|=(1030080731/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1091_s2_1 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5376091399/10000000000 : ℝ)*x 0 + (-2365383077/10000000000 : ℝ)*x 1 + (2575202137/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5376091399/10000000000 : ℝ)^2071 ≤ (21923893067109/50000000000000 : ℝ)^1559 := by
    have hnat : (5376091399 : ℕ)^2071*50000000000000^1559 ≤ 21923893067109^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376091399 10000000000 21923893067109 50000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2365383077/10000000000 : ℝ)^2071 ≤ (14732652119877/100000000000000 : ℝ)^1559 := by
    have hnat : (2365383077 : ℕ)^2071*100000000000000^1559 ≤ 14732652119877^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2365383077 10000000000 14732652119877 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2575202137/5000000000 : ℝ)^2071 ≤ (20709780862021/50000000000000 : ℝ)^1559 := by
    have hnat : (2575202137 : ℕ)^2071*50000000000000^1559 ≤ 20709780862021^1559*5000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2575202137 5000000000 20709780862021 50000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5376091399/10000000000 : ℝ), (-2365383077/10000000000 : ℝ), (2575202137/5000000000 : ℝ)] ![(21923893067109/50000000000000 : ℝ), (14732652119877/100000000000000 : ℝ), (20709780862021/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5376091399/10000000000 : ℝ)|^2071 ≤ (21923893067109/50000000000000 : ℝ)^1559
        have hw : |(5376091399/10000000000 : ℝ)|=(5376091399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2365383077/10000000000 : ℝ)|^2071 ≤ (14732652119877/100000000000000 : ℝ)^1559
        have hw : |(-2365383077/10000000000 : ℝ)|=(2365383077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2575202137/5000000000 : ℝ)|^2071 ≤ (20709780862021/50000000000000 : ℝ)^1559
        have hw : |(2575202137/5000000000 : ℝ)|=(2575202137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1091_s2_2 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5376091509/10000000000 : ℝ)*x 0 + (1030080829/2000000000 : ℝ)*x 1 + (-23653831/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5376091509/10000000000 : ℝ)^2071 ≤ (4384778732603/10000000000000 : ℝ)^1559 := by
    have hnat : (5376091509 : ℕ)^2071*10000000000000^1559 ≤ 4384778732603^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376091509 10000000000 4384778732603 10000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1030080829/2000000000 : ℝ)^2071 ≤ (41419560345919/100000000000000 : ℝ)^1559 := by
    have hnat : (1030080829 : ℕ)^2071*100000000000000^1559 ≤ 41419560345919^1559*2000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030080829 2000000000 41419560345919 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (23653831/100000000 : ℝ)^2071 ≤ (7366326155089/50000000000000 : ℝ)^1559 := by
    have hnat : (23653831 : ℕ)^2071*50000000000000^1559 ≤ 7366326155089^1559*100000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23653831 100000000 7366326155089 50000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5376091509/10000000000 : ℝ), (1030080829/2000000000 : ℝ), (-23653831/100000000 : ℝ)] ![(4384778732603/10000000000000 : ℝ), (41419560345919/100000000000000 : ℝ), (7366326155089/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5376091509/10000000000 : ℝ)|^2071 ≤ (4384778732603/10000000000000 : ℝ)^1559
        have hw : |(5376091509/10000000000 : ℝ)|=(5376091509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1030080829/2000000000 : ℝ)|^2071 ≤ (41419560345919/100000000000000 : ℝ)^1559
        have hw : |(1030080829/2000000000 : ℝ)|=(1030080829/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-23653831/100000000 : ℝ)|^2071 ≤ (7366326155089/50000000000000 : ℝ)^1559
        have hw : |(-23653831/100000000 : ℝ)|=(23653831/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1091_s2_3 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (436001917/1000000000 : ℝ)*x 0 + (4010547813/10000000000 : ℝ)*x 1 + (1185022171/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (436001917/1000000000 : ℝ)^2071 ≤ (33196381468043/100000000000000 : ℝ)^1559 := by
    have hnat : (436001917 : ℕ)^2071*100000000000000^1559 ≤ 33196381468043^1559*1000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436001917 1000000000 33196381468043 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4010547813/10000000000 : ℝ)^2071 ≤ (29709105946261/100000000000000 : ℝ)^1559 := by
    have hnat : (4010547813 : ℕ)^2071*100000000000000^1559 ≤ 29709105946261^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4010547813 10000000000 29709105946261 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1185022171/2500000000 : ℝ)^2071 ≤ (37094512562023/100000000000000 : ℝ)^1559 := by
    have hnat : (1185022171 : ℕ)^2071*100000000000000^1559 ≤ 37094512562023^1559*2500000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1185022171 2500000000 37094512562023 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(436001917/1000000000 : ℝ), (4010547813/10000000000 : ℝ), (1185022171/2500000000 : ℝ)] ![(33196381468043/100000000000000 : ℝ), (29709105946261/100000000000000 : ℝ), (37094512562023/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(436001917/1000000000 : ℝ)|^2071 ≤ (33196381468043/100000000000000 : ℝ)^1559
        have hw : |(436001917/1000000000 : ℝ)|=(436001917/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4010547813/10000000000 : ℝ)|^2071 ≤ (29709105946261/100000000000000 : ℝ)^1559
        have hw : |(4010547813/10000000000 : ℝ)|=(4010547813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1185022171/2500000000 : ℝ)|^2071 ≤ (37094512562023/100000000000000 : ℝ)^1559
        have hw : |(1185022171/2500000000 : ℝ)|=(1185022171/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1091_s2_4 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2172532503/10000000000 : ℝ)*x 0 + (5153051093/10000000000 : ℝ)*x 1 + (5518131533/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2172532503/10000000000 : ℝ)^2071 ≤ (822423762411/6250000000000 : ℝ)^1559 := by
    have hnat : (2172532503 : ℕ)^2071*6250000000000^1559 ≤ 822423762411^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2172532503 10000000000 822423762411 6250000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5153051093/10000000000 : ℝ)^2071 ≤ (41447840398593/100000000000000 : ℝ)^1559 := by
    have hnat : (5153051093 : ℕ)^2071*100000000000000^1559 ≤ 41447840398593^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5153051093 10000000000 41447840398593 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5518131533/10000000000 : ℝ)^2071 ≤ (9078675878263/20000000000000 : ℝ)^1559 := by
    have hnat : (5518131533 : ℕ)^2071*20000000000000^1559 ≤ 9078675878263^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5518131533 10000000000 9078675878263 20000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2172532503/10000000000 : ℝ), (5153051093/10000000000 : ℝ), (5518131533/10000000000 : ℝ)] ![(822423762411/6250000000000 : ℝ), (41447840398593/100000000000000 : ℝ), (9078675878263/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2172532503/10000000000 : ℝ)|^2071 ≤ (822423762411/6250000000000 : ℝ)^1559
        have hw : |(-2172532503/10000000000 : ℝ)|=(2172532503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5153051093/10000000000 : ℝ)|^2071 ≤ (41447840398593/100000000000000 : ℝ)^1559
        have hw : |(5153051093/10000000000 : ℝ)|=(5153051093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5518131533/10000000000 : ℝ)|^2071 ≤ (9078675878263/20000000000000 : ℝ)^1559
        have hw : |(5518131533/10000000000 : ℝ)|=(5518131533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1091_s2_5 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5282434811/10000000000 : ℝ)*x 0 + (-998827841/5000000000 : ℝ)*x 1 + (5518131623/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5282434811/10000000000 : ℝ)^2071 ≤ (42835963707923/100000000000000 : ℝ)^1559 := by
    have hnat : (5282434811 : ℕ)^2071*100000000000000^1559 ≤ 42835963707923^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282434811 10000000000 42835963707923 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (998827841/5000000000 : ℝ)^2071 ≤ (2942663974687/25000000000000 : ℝ)^1559 := by
    have hnat : (998827841 : ℕ)^2071*25000000000000^1559 ≤ 2942663974687^1559*5000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      998827841 5000000000 2942663974687 25000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5518131623/10000000000 : ℝ)^2071 ≤ (45393380374821/100000000000000 : ℝ)^1559 := by
    have hnat : (5518131623 : ℕ)^2071*100000000000000^1559 ≤ 45393380374821^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5518131623 10000000000 45393380374821 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5282434811/10000000000 : ℝ), (-998827841/5000000000 : ℝ), (5518131623/10000000000 : ℝ)] ![(42835963707923/100000000000000 : ℝ), (2942663974687/25000000000000 : ℝ), (45393380374821/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5282434811/10000000000 : ℝ)|^2071 ≤ (42835963707923/100000000000000 : ℝ)^1559
        have hw : |(5282434811/10000000000 : ℝ)|=(5282434811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-998827841/5000000000 : ℝ)|^2071 ≤ (2942663974687/25000000000000 : ℝ)^1559
        have hw : |(-998827841/5000000000 : ℝ)|=(998827841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5518131623/10000000000 : ℝ)|^2071 ≤ (45393380374821/100000000000000 : ℝ)^1559
        have hw : |(5518131623/10000000000 : ℝ)|=(5518131623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1091_s2_6 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5282434999/10000000000 : ℝ)*x 0 + (5518131541/10000000000 : ℝ)*x 1 + (-998827769/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5282434999/10000000000 : ℝ)^2071 ≤ (8567193146623/20000000000000 : ℝ)^1559 := by
    have hnat : (5282434999 : ℕ)^2071*20000000000000^1559 ≤ 8567193146623^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282434999 10000000000 8567193146623 20000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5518131541/10000000000 : ℝ)^2071 ≤ (22696689739369/50000000000000 : ℝ)^1559 := by
    have hnat : (5518131541 : ℕ)^2071*50000000000000^1559 ≤ 22696689739369^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5518131541 10000000000 22696689739369 50000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (998827769/5000000000 : ℝ)^2071 ≤ (11770654771611/100000000000000 : ℝ)^1559 := by
    have hnat : (998827769 : ℕ)^2071*100000000000000^1559 ≤ 11770654771611^1559*5000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      998827769 5000000000 11770654771611 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5282434999/10000000000 : ℝ), (5518131541/10000000000 : ℝ), (-998827769/5000000000 : ℝ)] ![(8567193146623/20000000000000 : ℝ), (22696689739369/50000000000000 : ℝ), (11770654771611/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5282434999/10000000000 : ℝ)|^2071 ≤ (8567193146623/20000000000000 : ℝ)^1559
        have hw : |(5282434999/10000000000 : ℝ)|=(5282434999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5518131541/10000000000 : ℝ)|^2071 ≤ (22696689739369/50000000000000 : ℝ)^1559
        have hw : |(5518131541/10000000000 : ℝ)|=(5518131541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-998827769/5000000000 : ℝ)|^2071 ≤ (11770654771611/100000000000000 : ℝ)^1559
        have hw : |(-998827769/5000000000 : ℝ)|=(998827769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1091_s2_7 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1090062817/2500000000 : ℝ)*x 0 + (4734875019/10000000000 : ℝ)*x 1 + (803162991/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1090062817/2500000000 : ℝ)^2071 ≤ (3319872900007/10000000000000 : ℝ)^1559 := by
    have hnat : (1090062817 : ℕ)^2071*10000000000000^1559 ≤ 3319872900007^1559*2500000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090062817 2500000000 3319872900007 10000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4734875019/10000000000 : ℝ)^2071 ≤ (1481612889051/4000000000000 : ℝ)^1559 := by
    have hnat : (4734875019 : ℕ)^2071*4000000000000^1559 ≤ 1481612889051^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4734875019 10000000000 1481612889051 4000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (803162991/2000000000 : ℝ)^2071 ≤ (7440237188557/25000000000000 : ℝ)^1559 := by
    have hnat : (803162991 : ℕ)^2071*25000000000000^1559 ≤ 7440237188557^1559*2000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      803162991 2000000000 7440237188557 25000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1090062817/2500000000 : ℝ), (4734875019/10000000000 : ℝ), (803162991/2000000000 : ℝ)] ![(3319872900007/10000000000000 : ℝ), (1481612889051/4000000000000 : ℝ), (7440237188557/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1090062817/2500000000 : ℝ)|^2071 ≤ (3319872900007/10000000000000 : ℝ)^1559
        have hw : |(1090062817/2500000000 : ℝ)|=(1090062817/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4734875019/10000000000 : ℝ)|^2071 ≤ (1481612889051/4000000000000 : ℝ)^1559
        have hw : |(4734875019/10000000000 : ℝ)|=(4734875019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(803162991/2000000000 : ℝ)|^2071 ≤ (7440237188557/25000000000000 : ℝ)^1559
        have hw : |(803162991/2000000000 : ℝ)|=(803162991/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1091_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29695923/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20673/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5359/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (8833/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (833/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20673/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5359/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20673/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5359/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20673/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5359/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20673/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5359/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20673/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5359/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20673/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5359/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5359/100000 : ℝ) ^ (8283/2048 : ℝ) ≤ (90526069658069/12500000000000000000 : ℝ) := by
    have hpowers : (5359/100000 : ℝ)^8283 ≤ (90526069658069/12500000000000000000 : ℝ)^2048 := by
      have hnat : (5359 : ℕ)^8283*12500000000000000000^2048 ≤ 90526069658069^2048*100000^8283 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5359 100000 90526069658069 12500000000000000000 8283 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5359/100000 : ℝ)) (X := (90526069658069/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8283 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (20673/100000 : ℝ) ^ (8283/2048 : ℝ) ≤ (34058454102157127/20000000000000000000 : ℝ) := by
    have hpowers : (20673/100000 : ℝ)^8283 ≤ (34058454102157127/20000000000000000000 : ℝ)^2048 := by
      have hnat : (20673 : ℕ)^8283*20000000000000000000^2048 ≤ 34058454102157127^2048*100000^8283 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20673 100000 34058454102157127 20000000000000000000 8283 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20673/100000 : ℝ)) (X := (34058454102157127/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8283 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250090526069658069/6250000000000000000 : ℝ) ≤ (400001432496477/400000000000000 : ℝ) ^ (8283/2048 : ℝ) := by
    have hpowers : (6250090526069658069/6250000000000000000 : ℝ)^2048 ≤ (400001432496477/400000000000000 : ℝ)^8283 := by
      have hnat : (6250090526069658069 : ℕ)^2048*400000000000000^8283 ≤ 400001432496477^8283*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250090526069658069 6250000000000000000 400001432496477 400000000000000 2048 8283 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400001432496477/400000000000000 : ℝ)) (X := (6250090526069658069/6250000000000000000 : ℝ)) (by norm_num) 8283 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100171016479068050187/100000000000000000000 : ℝ) ≤ (2000845144361669/2000000000000000 : ℝ) ^ (8283/2048 : ℝ) := by
    have hpowers : (100171016479068050187/100000000000000000000 : ℝ)^2048 ≤ (2000845144361669/2000000000000000 : ℝ)^8283 := by
      have hnat : (100171016479068050187 : ℕ)^2048*2000000000000000^8283 ≤ 2000845144361669^8283*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100171016479068050187 100000000000000000000 2000845144361669 2000000000000000 2048 8283 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000845144361669/2000000000000000 : ℝ)) (X := (100171016479068050187/100000000000000000000 : ℝ)) (by norm_num) 8283 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10034058454102157127/10000000000000000000 : ℝ) ≤ (2001683126240953/2000000000000000 : ℝ) ^ (8283/2048 : ℝ) := by
    have hpowers : (10034058454102157127/10000000000000000000 : ℝ)^2048 ≤ (2001683126240953/2000000000000000 : ℝ)^8283 := by
      have hnat : (10034058454102157127 : ℕ)^2048*2000000000000000^8283 ≤ 2001683126240953^8283*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10034058454102157127 10000000000000000000 2001683126240953 2000000000000000 2048 8283 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2001683126240953/2000000000000000 : ℝ)) (X := (10034058454102157127/10000000000000000000 : ℝ)) (by norm_num) 8283 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(90526069658069/12500000000000000000 : ℝ) ≤ ((805766531486133631/806000000000000000 : ℝ)+2*(11026077359/4030000000000 : ℝ)*(5359/100000 : ℝ))^(8283/2048 : ℝ) := by
    rw [show (805766531486133631/806000000000000000 : ℝ)+2*(11026077359/4030000000000 : ℝ)*(5359/100000 : ℝ)=(400001432496477/400000000000000 : ℝ) by norm_num, show 1+2*(90526069658069/12500000000000000000 : ℝ)=(6250090526069658069/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34058454102157127/20000000000000000000 : ℝ)+(90526069658069/12500000000000000000 : ℝ) ≤ ((805766531486133631/806000000000000000 : ℝ)+(11026077359/4030000000000 : ℝ)*((20673/100000 : ℝ)+(5359/100000 : ℝ)))^(8283/2048 : ℝ) := by
    rw [show (805766531486133631/806000000000000000 : ℝ)+(11026077359/4030000000000 : ℝ)*((20673/100000 : ℝ)+(5359/100000 : ℝ))=(2000845144361669/2000000000000000 : ℝ) by norm_num, show 1+(34058454102157127/20000000000000000000 : ℝ)+(90526069658069/12500000000000000000 : ℝ)=(100171016479068050187/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34058454102157127/20000000000000000000 : ℝ) ≤ ((805766531486133631/806000000000000000 : ℝ)+2*(11026077359/4030000000000 : ℝ)*(20673/100000 : ℝ))^(8283/2048 : ℝ) := by
    rw [show (805766531486133631/806000000000000000 : ℝ)+2*(11026077359/4030000000000 : ℝ)*(20673/100000 : ℝ)=(2001683126240953/2000000000000000 : ℝ) by norm_num, show 1+2*(34058454102157127/20000000000000000000 : ℝ)=(10034058454102157127/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (805766531486133631/806000000000000000 : ℝ)*(X 1 0+X 2 0)+(11026077359/4030000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8283/2048 : ℝ)) (lo := (5359/100000 : ℝ)) (hi := (20673/100000 : ℝ)) (c := (805766531486133631/806000000000000000 : ℝ)) (alpha := (11026077359/4030000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (805766531486133631/806000000000000000 : ℝ)*(X 0 1+X 2 1)+(11026077359/4030000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8283/2048 : ℝ)) (lo := (5359/100000 : ℝ)) (hi := (20673/100000 : ℝ)) (c := (805766531486133631/806000000000000000 : ℝ)) (alpha := (11026077359/4030000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (805766531486133631/806000000000000000 : ℝ)*(X 0 2+X 1 2)+(11026077359/4030000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8283/2048 : ℝ)) (lo := (5359/100000 : ℝ)) (hi := (20673/100000 : ℝ)) (c := (805766531486133631/806000000000000000 : ℝ)) (alpha := (11026077359/4030000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2172414799/10000000000 : ℝ)*X 0 0+(345050397/625000000 : ℝ)*X 0 1+(1030080731/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5376091399/10000000000 : ℝ)*X 1 0+(-2365383077/10000000000 : ℝ)*X 1 1+(2575202137/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5376091509/10000000000 : ℝ)*X 2 0+(1030080829/2000000000 : ℝ)*X 2 1+(-23653831/100000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((436001917/1000000000 : ℝ)*X 0 0+(4010547813/10000000000 : ℝ)*X 0 1+(1185022171/2500000000 : ℝ)*X 0 2+(436001917/1000000000 : ℝ)*X 1 0+(4010547813/10000000000 : ℝ)*X 1 1+(1185022171/2500000000 : ℝ)*X 1 2+(436001917/1000000000 : ℝ)*X 2 0+(4010547813/10000000000 : ℝ)*X 2 1+(1185022171/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2172532503/10000000000 : ℝ)*X 0 0+(5153051093/10000000000 : ℝ)*X 0 1+(5518131533/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5282434811/10000000000 : ℝ)*X 1 0+(-998827841/5000000000 : ℝ)*X 1 1+(5518131623/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5282434999/10000000000 : ℝ)*X 2 0+(5518131541/10000000000 : ℝ)*X 2 1+(-998827769/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1090062817/2500000000 : ℝ)*X 0 0+(4734875019/10000000000 : ℝ)*X 0 1+(803162991/2000000000 : ℝ)*X 0 2+(1090062817/2500000000 : ℝ)*X 1 0+(4734875019/10000000000 : ℝ)*X 1 1+(803162991/2000000000 : ℝ)*X 1 2+(1090062817/2500000000 : ℝ)*X 2 0+(4734875019/10000000000 : ℝ)*X 2 1+(803162991/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6421178508704205688375467/1550000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (605447147/100000000000000 : ℝ)*(base19) + (31788501/5000000000000 : ℝ)*(base23) + (4682213/6250000000000 : ℝ)*(upper3) + (13395777/100000000000000 : ℝ)*(upper4) + (54254689/100000000000000 : ℝ)*(upper5) + (2035259219098747/100000000000000 : ℝ)*(major0) + (2035259219098747/100000000000000 : ℝ)*(major1) + (2035259219098747/100000000000000 : ℝ)*(major2) + (539954943037949/20000000000000 : ℝ)*(sp0) + (134989230085221/5000000000000 : ℝ)*(sp1) + (674946142845387/25000000000000 : ℝ)*(sp2) + (685364464889891/50000000000000 : ℝ)*(sp3) + (5245980911/50000000000000 : ℝ)*(sp4) + (4163176277/100000000000000 : ℝ)*(sp7) + (685366546478029/50000000000000 : ℝ)*(f.failure) + (168736575446973/6250000000000 : ℝ)*(f.sum) + (604559604019/403000000000000000000000000 : ℝ)*base66 + (611730071567739643/80600000000000000000000000000000 : ℝ)*base68 + (163302928973139643/80600000000000000000000000000000 : ℝ)*base70 + (67663364527660357/80600000000000000000000000000000 : ℝ)*base71 + (2649497359321/403000000000000000000000000 : ℝ)*base74 + (387035631280539643/80600000000000000000000000000000 : ℝ)*base76 + (53219899043539643/80600000000000000000000000000000 : ℝ)*base78 + (1703302704352139643/80600000000000000000000000000000 : ℝ)*base80 + (192204777277/403000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (375767/1000000000000000000000 : ℝ)*base89 + (375767/1000000000000000000000 : ℝ)*base91 + (375767/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1242438046402443379251/201500000000000000000000000 : ℝ) := by norm_num
    linear_combination (243475301/20000000000000 : ℝ)*(base19) + (1435134863/100000000000000 : ℝ)*(base23) + (173775561/100000000000000 : ℝ)*(upper3) + (3807773/10000000000000 : ℝ)*(lower4) + (118483259/100000000000000 : ℝ)*(upper5) + (206491334007121/10000000000000 : ℝ)*(major0) + (206491334007121/10000000000000 : ℝ)*(major1) + (206491334007121/10000000000000 : ℝ)*(major2) + (10782136821/100000000000000 : ℝ)*(sp1) + (13500189137/100000000000000 : ℝ)*(sp2) + (1369560767516511/50000000000000 : ℝ)*(sp4) + (171194345969981/6250000000000 : ℝ)*(sp5) + (1369553299854511/50000000000000 : ℝ)*(sp6) + (695352469788937/50000000000000 : ℝ)*(sp7) + (695352469788937/50000000000000 : ℝ)*(f.failure) + (1369560767516511/50000000000000 : ℝ)*(f.sum) + (489512805941/201500000000000000000000000 : ℝ)*base65 + (30599877375733649/8060000000000000000000000000000 : ℝ)*base68 + (33069991272373649/8060000000000000000000000000000 : ℝ)*base70 + (23575722007366351/8060000000000000000000000000000 : ℝ)*base71 + (293853334171/403000000000000000000000000 : ℝ)*base74 + (25603504170533649/8060000000000000000000000000000 : ℝ)*base76 + (15493487078806351/8060000000000000000000000000000 : ℝ)*base77 + (22587718293006351/8060000000000000000000000000000 : ℝ)*base79 + (382201778111/201500000000000000000000000 : ℝ)*base82 + (596149/1000000000000000000000 : ℝ)*base90 + (596149/1000000000000000000000 : ℝ)*base92 + (596149/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1091_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29695923/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20673/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5359/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8833/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (833/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1091_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1091_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29695923/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8833/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (833/5000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1091_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1091_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1091_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29695923/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8833/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (833/5000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1091_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
