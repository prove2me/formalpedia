-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1091_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:57:08.57252+00:00
-- url     : https://prove2.me/submissions/d8d89572-ef37-4c02-8878-4cd1614552fe

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
theorem support_rectangle_w1091_s3_0 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1093553393/5000000000 : ℝ)*x 0 + (5434672579/10000000000 : ℝ)*x 1 + (130675849/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1093553393/5000000000 : ℝ)^2071 ≤ (132761747557/1000000000000 : ℝ)^1559 := by
    have hnat : (1093553393 : ℕ)^2071*1000000000000^1559 ≤ 132761747557^1559*5000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093553393 5000000000 132761747557 1000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5434672579/10000000000 : ℝ)^2071 ≤ (11120906456661/25000000000000 : ℝ)^1559 := by
    have hnat : (5434672579 : ℕ)^2071*25000000000000^1559 ≤ 11120906456661^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434672579 10000000000 11120906456661 25000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (130675849/250000000 : ℝ)^2071 ≤ (1320006231533/3125000000000 : ℝ)^1559 := by
    have hnat : (130675849 : ℕ)^2071*3125000000000^1559 ≤ 1320006231533^1559*250000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130675849 250000000 1320006231533 3125000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1093553393/5000000000 : ℝ), (5434672579/10000000000 : ℝ), (130675849/250000000 : ℝ)] ![(132761747557/1000000000000 : ℝ), (11120906456661/25000000000000 : ℝ), (1320006231533/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1093553393/5000000000 : ℝ)|^2071 ≤ (132761747557/1000000000000 : ℝ)^1559
        have hw : |(-1093553393/5000000000 : ℝ)|=(1093553393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5434672579/10000000000 : ℝ)|^2071 ≤ (11120906456661/25000000000000 : ℝ)^1559
        have hw : |(5434672579/10000000000 : ℝ)|=(5434672579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(130675849/250000000 : ℝ)|^2071 ≤ (1320006231533/3125000000000 : ℝ)^1559
        have hw : |(130675849/250000000 : ℝ)|=(130675849/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1091_s3_1 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2677526569/5000000000 : ℝ)*x 0 + (-2293369157/10000000000 : ℝ)*x 1 + (2613516931/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677526569/5000000000 : ℝ)^2071 ≤ (872399809547/2000000000000 : ℝ)^1559 := by
    have hnat : (2677526569 : ℕ)^2071*2000000000000^1559 ≤ 872399809547^1559*5000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677526569 5000000000 872399809547 2000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2293369157/10000000000 : ℝ)^2071 ≤ (14139811151397/100000000000000 : ℝ)^1559 := by
    have hnat : (2293369157 : ℕ)^2071*100000000000000^1559 ≤ 14139811151397^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2293369157 10000000000 14139811151397 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2613516931/5000000000 : ℝ)^2071 ≤ (42240198357019/100000000000000 : ℝ)^1559 := by
    have hnat : (2613516931 : ℕ)^2071*100000000000000^1559 ≤ 42240198357019^1559*5000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2613516931 5000000000 42240198357019 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677526569/5000000000 : ℝ), (-2293369157/10000000000 : ℝ), (2613516931/5000000000 : ℝ)] ![(872399809547/2000000000000 : ℝ), (14139811151397/100000000000000 : ℝ), (42240198357019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677526569/5000000000 : ℝ)|^2071 ≤ (872399809547/2000000000000 : ℝ)^1559
        have hw : |(2677526569/5000000000 : ℝ)|=(2677526569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2293369157/10000000000 : ℝ)|^2071 ≤ (14139811151397/100000000000000 : ℝ)^1559
        have hw : |(-2293369157/10000000000 : ℝ)|=(2293369157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2613516931/5000000000 : ℝ)|^2071 ≤ (42240198357019/100000000000000 : ℝ)^1559
        have hw : |(2613516931/5000000000 : ℝ)|=(2613516931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1091_s3_2 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (214202121/400000000 : ℝ)*x 0 + (2613517151/5000000000 : ℝ)*x 1 + (-2293368731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214202121/400000000 : ℝ)^2071 ≤ (4361998925461/10000000000000 : ℝ)^1559 := by
    have hnat : (214202121 : ℕ)^2071*10000000000000^1559 ≤ 4361998925461^1559*400000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214202121 400000000 4361998925461 10000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2613517151/5000000000 : ℝ)^2071 ≤ (42240203080447/100000000000000 : ℝ)^1559 := by
    have hnat : (2613517151 : ℕ)^2071*100000000000000^1559 ≤ 42240203080447^1559*5000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2613517151 5000000000 42240203080447 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2293368731/10000000000 : ℝ)^2071 ≤ (7069903831149/50000000000000 : ℝ)^1559 := by
    have hnat : (2293368731 : ℕ)^2071*50000000000000^1559 ≤ 7069903831149^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2293368731 10000000000 7069903831149 50000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214202121/400000000 : ℝ), (2613517151/5000000000 : ℝ), (-2293368731/10000000000 : ℝ)] ![(4361998925461/10000000000000 : ℝ), (42240203080447/100000000000000 : ℝ), (7069903831149/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214202121/400000000 : ℝ)|^2071 ≤ (4361998925461/10000000000000 : ℝ)^1559
        have hw : |(214202121/400000000 : ℝ)|=(214202121/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2613517151/5000000000 : ℝ)|^2071 ≤ (42240203080447/100000000000000 : ℝ)^1559
        have hw : |(2613517151/5000000000 : ℝ)|=(2613517151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2293368731/10000000000 : ℝ)|^2071 ≤ (7069903831149/50000000000000 : ℝ)^1559
        have hw : |(-2293368731/10000000000 : ℝ)|=(2293368731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1091_s3_3 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4369298217/10000000000 : ℝ)*x 0 + (2084814111/5000000000 : ℝ)*x 1 + (4578590763/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4369298217/10000000000 : ℝ)^2071 ≤ (1331610616949/4000000000000 : ℝ)^1559 := by
    have hnat : (4369298217 : ℕ)^2071*4000000000000^1559 ≤ 1331610616949^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4369298217 10000000000 1331610616949 4000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2084814111/5000000000 : ℝ)^2071 ≤ (15642326850623/50000000000000 : ℝ)^1559 := by
    have hnat : (2084814111 : ℕ)^2071*50000000000000^1559 ≤ 15642326850623^1559*5000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084814111 5000000000 15642326850623 50000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4578590763/10000000000 : ℝ)^2071 ≤ (7085016170209/20000000000000 : ℝ)^1559 := by
    have hnat : (4578590763 : ℕ)^2071*20000000000000^1559 ≤ 7085016170209^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4578590763 10000000000 7085016170209 20000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4369298217/10000000000 : ℝ), (2084814111/5000000000 : ℝ), (4578590763/10000000000 : ℝ)] ![(1331610616949/4000000000000 : ℝ), (15642326850623/50000000000000 : ℝ), (7085016170209/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4369298217/10000000000 : ℝ)|^2071 ≤ (1331610616949/4000000000000 : ℝ)^1559
        have hw : |(4369298217/10000000000 : ℝ)|=(4369298217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2084814111/5000000000 : ℝ)|^2071 ≤ (15642326850623/50000000000000 : ℝ)^1559
        have hw : |(2084814111/5000000000 : ℝ)|=(2084814111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4578590763/10000000000 : ℝ)|^2071 ≤ (7085016170209/20000000000000 : ℝ)^1559
        have hw : |(4578590763/10000000000 : ℝ)|=(4578590763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1091_s3_4 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-437425541/2000000000 : ℝ)*x 0 + (5227869701/10000000000 : ℝ)*x 1 + (169807247/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (437425541/2000000000 : ℝ)^2071 ≤ (13276343441513/100000000000000 : ℝ)^1559 := by
    have hnat : (437425541 : ℕ)^2071*100000000000000^1559 ≤ 13276343441513^1559*2000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437425541 2000000000 13276343441513 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5227869701/10000000000 : ℝ)^2071 ≤ (42249171377387/100000000000000 : ℝ)^1559 := by
    have hnat : (5227869701 : ℕ)^2071*100000000000000^1559 ≤ 42249171377387^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5227869701 10000000000 42249171377387 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169807247/312500000 : ℝ)^2071 ≤ (44474485159827/100000000000000 : ℝ)^1559 := by
    have hnat : (169807247 : ℕ)^2071*100000000000000^1559 ≤ 44474485159827^1559*312500000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169807247 312500000 44474485159827 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-437425541/2000000000 : ℝ), (5227869701/10000000000 : ℝ), (169807247/312500000 : ℝ)] ![(13276343441513/100000000000000 : ℝ), (42249171377387/100000000000000 : ℝ), (44474485159827/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-437425541/2000000000 : ℝ)|^2071 ≤ (13276343441513/100000000000000 : ℝ)^1559
        have hw : |(-437425541/2000000000 : ℝ)|=(437425541/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5227869701/10000000000 : ℝ)|^2071 ≤ (42249171377387/100000000000000 : ℝ)^1559
        have hw : |(5227869701/10000000000 : ℝ)|=(5227869701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169807247/312500000 : ℝ)|^2071 ≤ (44474485159827/100000000000000 : ℝ)^1559
        have hw : |(169807247/312500000 : ℝ)|=(169807247/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1091_s3_5 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1325662139/2500000000 : ℝ)*x 0 + (-2086570981/10000000000 : ℝ)*x 1 + (679229023/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325662139/2500000000 : ℝ)^2071 ≤ (43053848909749/100000000000000 : ℝ)^1559 := by
    have hnat : (1325662139 : ℕ)^2071*100000000000000^1559 ≤ 43053848909749^1559*2500000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325662139 2500000000 43053848909749 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2086570981/10000000000 : ℝ)^2071 ≤ (2494332572201/20000000000000 : ℝ)^1559 := by
    have hnat : (2086570981 : ℕ)^2071*20000000000000^1559 ≤ 2494332572201^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086570981 10000000000 2494332572201 20000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (679229023/1250000000 : ℝ)^2071 ≤ (1389827756381/3125000000000 : ℝ)^1559 := by
    have hnat : (679229023 : ℕ)^2071*3125000000000^1559 ≤ 1389827756381^1559*1250000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      679229023 1250000000 1389827756381 3125000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1325662139/2500000000 : ℝ), (-2086570981/10000000000 : ℝ), (679229023/1250000000 : ℝ)] ![(43053848909749/100000000000000 : ℝ), (2494332572201/20000000000000 : ℝ), (1389827756381/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1325662139/2500000000 : ℝ)|^2071 ≤ (43053848909749/100000000000000 : ℝ)^1559
        have hw : |(1325662139/2500000000 : ℝ)|=(1325662139/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2086570981/10000000000 : ℝ)|^2071 ≤ (2494332572201/20000000000000 : ℝ)^1559
        have hw : |(-2086570981/10000000000 : ℝ)|=(2086570981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(679229023/1250000000 : ℝ)|^2071 ≤ (1389827756381/3125000000000 : ℝ)^1559
        have hw : |(679229023/1250000000 : ℝ)|=(679229023/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1091_s3_6 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (53026487/100000000 : ℝ)*x 0 + (5433831929/10000000000 : ℝ)*x 1 + (-16301337/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53026487/100000000 : ℝ)^2071 ≤ (43053850462907/100000000000000 : ℝ)^1559 := by
    have hnat : (53026487 : ℕ)^2071*100000000000000^1559 ≤ 43053850462907^1559*100000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53026487 100000000 43053850462907 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5433831929/10000000000 : ℝ)^2071 ≤ (22237242715823/50000000000000 : ℝ)^1559 := by
    have hnat : (5433831929 : ℕ)^2071*50000000000000^1559 ≤ 22237242715823^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433831929 10000000000 22237242715823 50000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (16301337/78125000 : ℝ)^2071 ≤ (6235832045859/50000000000000 : ℝ)^1559 := by
    have hnat : (16301337 : ℕ)^2071*50000000000000^1559 ≤ 6235832045859^1559*78125000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16301337 78125000 6235832045859 50000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53026487/100000000 : ℝ), (5433831929/10000000000 : ℝ), (-16301337/78125000 : ℝ)] ![(43053850462907/100000000000000 : ℝ), (22237242715823/50000000000000 : ℝ), (6235832045859/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53026487/100000000 : ℝ)|^2071 ≤ (43053850462907/100000000000000 : ℝ)^1559
        have hw : |(53026487/100000000 : ℝ)|=(53026487/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5433831929/10000000000 : ℝ)|^2071 ≤ (22237242715823/50000000000000 : ℝ)^1559
        have hw : |(5433831929/10000000000 : ℝ)|=(5433831929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-16301337/78125000 : ℝ)|^2071 ≤ (6235832045859/50000000000000 : ℝ)^1559
        have hw : |(-16301337/78125000 : ℝ)|=(16301337/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1091_s3_7 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4369338973/10000000000 : ℝ)*x 0 + (572118193/1250000000 : ℝ)*x 1 + (2085641593/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4369338973/10000000000 : ℝ)^2071 ≤ (33290677931153/100000000000000 : ℝ)^1559 := by
    have hnat : (4369338973 : ℕ)^2071*100000000000000^1559 ≤ 33290677931153^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4369338973 10000000000 33290677931153 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (572118193/1250000000 : ℝ)^2071 ≤ (17704086058481/50000000000000 : ℝ)^1559 := by
    have hnat : (572118193 : ℕ)^2071*50000000000000^1559 ≤ 17704086058481^1559*1250000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      572118193 1250000000 17704086058481 50000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2085641593/5000000000 : ℝ)^2071 ≤ (31301149937023/100000000000000 : ℝ)^1559 := by
    have hnat : (2085641593 : ℕ)^2071*100000000000000^1559 ≤ 31301149937023^1559*5000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085641593 5000000000 31301149937023 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4369338973/10000000000 : ℝ), (572118193/1250000000 : ℝ), (2085641593/5000000000 : ℝ)] ![(33290677931153/100000000000000 : ℝ), (17704086058481/50000000000000 : ℝ), (31301149937023/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4369338973/10000000000 : ℝ)|^2071 ≤ (33290677931153/100000000000000 : ℝ)^1559
        have hw : |(4369338973/10000000000 : ℝ)|=(4369338973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(572118193/1250000000 : ℝ)|^2071 ≤ (17704086058481/50000000000000 : ℝ)^1559
        have hw : |(572118193/1250000000 : ℝ)|=(572118193/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2085641593/5000000000 : ℝ)|^2071 ≤ (31301149937023/100000000000000 : ℝ)^1559
        have hw : |(2085641593/5000000000 : ℝ)|=(2085641593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1091_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29695923/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (833/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8833/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5239/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14871/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (833/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8833/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (833/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8833/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (833/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8833/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (833/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8833/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (833/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8833/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (833/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8833/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8833/100000 : ℝ) ^ (8283/2048 : ℝ) ≤ (273259158968527/5000000000000000000 : ℝ) := by
    have hpowers : (8833/100000 : ℝ)^8283 ≤ (273259158968527/5000000000000000000 : ℝ)^2048 := by
      have hnat : (8833 : ℕ)^8283*5000000000000000000^2048 ≤ 273259158968527^2048*100000^8283 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8833 100000 273259158968527 5000000000000000000 8283 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8833/100000 : ℝ)) (X := (273259158968527/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8283 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (833/5000 : ℝ) ^ (8283/2048 : ℝ) ≤ (2845615400729967/4000000000000000000 : ℝ) := by
    have hpowers : (833/5000 : ℝ)^8283 ≤ (2845615400729967/4000000000000000000 : ℝ)^2048 := by
      have hnat : (833 : ℕ)^8283*4000000000000000000^2048 ≤ 2845615400729967^2048*5000^8283 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        833 5000 2845615400729967 4000000000000000000 8283 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (833/5000 : ℝ)) (X := (2845615400729967/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8283 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500273259158968527/2500000000000000000 : ℝ) ≤ (5000135122959371/5000000000000000 : ℝ) ^ (8283/2048 : ℝ) := by
    have hpowers : (2500273259158968527/2500000000000000000 : ℝ)^2048 ≤ (5000135122959371/5000000000000000 : ℝ)^8283 := by
      have hnat : (2500273259158968527 : ℕ)^2048*5000000000000000^8283 ≤ 5000135122959371^8283*2500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500273259158968527 2500000000000000000 5000135122959371 5000000000000000 2048 8283 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000135122959371/5000000000000000 : ℝ)) (X := (2500273259158968527/2500000000000000000 : ℝ)) (by norm_num) 8283 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20015321113639523943/20000000000000000000 : ℝ) ≤ (5000946776466507/5000000000000000 : ℝ) ^ (8283/2048 : ℝ) := by
    have hpowers : (20015321113639523943/20000000000000000000 : ℝ)^2048 ≤ (5000946776466507/5000000000000000 : ℝ)^8283 := by
      have hnat : (20015321113639523943 : ℕ)^2048*5000000000000000^8283 ≤ 5000946776466507^8283*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20015321113639523943 20000000000000000000 5000946776466507 5000000000000000 2048 8283 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000946776466507/5000000000000000 : ℝ)) (X := (20015321113639523943/20000000000000000000 : ℝ)) (by norm_num) 8283 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (2002845615400729967/2000000000000000000 : ℝ) ≤ (5001758429973643/5000000000000000 : ℝ) ^ (8283/2048 : ℝ) := by
    have hpowers : (2002845615400729967/2000000000000000000 : ℝ)^2048 ≤ (5001758429973643/5000000000000000 : ℝ)^8283 := by
      have hnat : (2002845615400729967 : ℕ)^2048*5000000000000000^8283 ≤ 5001758429973643^8283*2000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2002845615400729967 2000000000000000000 5001758429973643 5000000000000000 2048 8283 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001758429973643/5000000000000000 : ℝ)) (X := (2002845615400729967/2000000000000000000 : ℝ)) (by norm_num) 8283 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(273259158968527/5000000000000000000 : ℝ) ≤ ((39121718936545932241/39135000000000000000 : ℝ)+2*(12682086049/6114843750000 : ℝ)*(8833/100000 : ℝ))^(8283/2048 : ℝ) := by
    rw [show (39121718936545932241/39135000000000000000 : ℝ)+2*(12682086049/6114843750000 : ℝ)*(8833/100000 : ℝ)=(5000135122959371/5000000000000000 : ℝ) by norm_num, show 1+2*(273259158968527/5000000000000000000 : ℝ)=(2500273259158968527/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2845615400729967/4000000000000000000 : ℝ)+(273259158968527/5000000000000000000 : ℝ) ≤ ((39121718936545932241/39135000000000000000 : ℝ)+(12682086049/6114843750000 : ℝ)*((833/5000 : ℝ)+(8833/100000 : ℝ)))^(8283/2048 : ℝ) := by
    rw [show (39121718936545932241/39135000000000000000 : ℝ)+(12682086049/6114843750000 : ℝ)*((833/5000 : ℝ)+(8833/100000 : ℝ))=(5000946776466507/5000000000000000 : ℝ) by norm_num, show 1+(2845615400729967/4000000000000000000 : ℝ)+(273259158968527/5000000000000000000 : ℝ)=(20015321113639523943/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2845615400729967/4000000000000000000 : ℝ) ≤ ((39121718936545932241/39135000000000000000 : ℝ)+2*(12682086049/6114843750000 : ℝ)*(833/5000 : ℝ))^(8283/2048 : ℝ) := by
    rw [show (39121718936545932241/39135000000000000000 : ℝ)+2*(12682086049/6114843750000 : ℝ)*(833/5000 : ℝ)=(5001758429973643/5000000000000000 : ℝ) by norm_num, show 1+2*(2845615400729967/4000000000000000000 : ℝ)=(2002845615400729967/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (39121718936545932241/39135000000000000000 : ℝ)*(X 1 0+X 2 0)+(12682086049/6114843750000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8283/2048 : ℝ)) (lo := (8833/100000 : ℝ)) (hi := (833/5000 : ℝ)) (c := (39121718936545932241/39135000000000000000 : ℝ)) (alpha := (12682086049/6114843750000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (39121718936545932241/39135000000000000000 : ℝ)*(X 0 1+X 2 1)+(12682086049/6114843750000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8283/2048 : ℝ)) (lo := (8833/100000 : ℝ)) (hi := (833/5000 : ℝ)) (c := (39121718936545932241/39135000000000000000 : ℝ)) (alpha := (12682086049/6114843750000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (39121718936545932241/39135000000000000000 : ℝ)*(X 0 2+X 1 2)+(12682086049/6114843750000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8283/2048 : ℝ)) (lo := (8833/100000 : ℝ)) (hi := (833/5000 : ℝ)) (c := (39121718936545932241/39135000000000000000 : ℝ)) (alpha := (12682086049/6114843750000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1093553393/5000000000 : ℝ)*X 0 0+(5434672579/10000000000 : ℝ)*X 0 1+(130675849/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2677526569/5000000000 : ℝ)*X 1 0+(-2293369157/10000000000 : ℝ)*X 1 1+(2613516931/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((214202121/400000000 : ℝ)*X 2 0+(2613517151/5000000000 : ℝ)*X 2 1+(-2293368731/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4369298217/10000000000 : ℝ)*X 0 0+(2084814111/5000000000 : ℝ)*X 0 1+(4578590763/10000000000 : ℝ)*X 0 2+(4369298217/10000000000 : ℝ)*X 1 0+(2084814111/5000000000 : ℝ)*X 1 1+(4578590763/10000000000 : ℝ)*X 1 2+(4369298217/10000000000 : ℝ)*X 2 0+(2084814111/5000000000 : ℝ)*X 2 1+(4578590763/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-437425541/2000000000 : ℝ)*X 0 0+(5227869701/10000000000 : ℝ)*X 0 1+(169807247/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1325662139/2500000000 : ℝ)*X 1 0+(-2086570981/10000000000 : ℝ)*X 1 1+(679229023/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((53026487/100000000 : ℝ)*X 2 0+(5433831929/10000000000 : ℝ)*X 2 1+(-16301337/78125000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4369338973/10000000000 : ℝ)*X 0 0+(572118193/1250000000 : ℝ)*X 0 1+(2085641593/5000000000 : ℝ)*X 0 2+(4369338973/10000000000 : ℝ)*X 1 0+(572118193/1250000000 : ℝ)*X 1 1+(2085641593/5000000000 : ℝ)*X 1 2+(4369338973/10000000000 : ℝ)*X 2 0+(572118193/1250000000 : ℝ)*X 2 1+(2085641593/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (27611639843743834393514323/20382812500000000000000000000000 : ℝ) := by norm_num
    linear_combination (34471141/5000000000000 : ℝ)*(base19) + (289781351/100000000000000 : ℝ)*(base23) + (10898659/6250000000000 : ℝ)*(lower2) + (40012203/100000000000000 : ℝ)*(upper5) + (226915940018027/6250000000000 : ℝ)*(major0) + (226915940018027/6250000000000 : ℝ)*(major1) + (226915940018027/6250000000000 : ℝ)*(major2) + (4816072372100837/100000000000000 : ℝ)*(sp0) + (2351604156487/48828125000 : ℝ)*(sp1) + (2408044267220087/50000000000000 : ℝ)*(sp2) + (61130406566731/2500000000000 : ℝ)*(sp3) + (16452120687/100000000000000 : ℝ)*(sp4) + (2822313329/100000000000000 : ℝ)*(sp5) + (4948530987/100000000000000 : ℝ)*(sp7) + (1222610605600113/50000000000000 : ℝ)*(f.failure) + (192643552968861/4000000000000 : ℝ)*(f.sum) + (113554063876693/19567500000000000000000000000 : ℝ)*base66 + (873561344737478993/244593750000000000000000000000000 : ℝ)*base68 + (2754541301256353993/244593750000000000000000000000000 : ℝ)*base70 + (854922768996072743/244593750000000000000000000000000 : ℝ)*base72 + (79384621575859/39135000000000000000000000000 : ℝ)*base73 + (3527888055823853993/244593750000000000000000000000000 : ℝ)*base76 + (2941530902181260243/244593750000000000000000000000000 : ℝ)*base78 + (5187068823191416493/244593750000000000000000000000000 : ℝ)*base80 + (31826779726019/9783750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (4439299/1000000000000000000000 : ℝ)*base89 + (4439299/1000000000000000000000 : ℝ)*base91 + (4439299/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (267022969700691032697194571/32612500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (300539869/20000000000000 : ℝ)*(base19) + (59306901/3125000000000 : ℝ)*(base23) + (30774449/12500000000000 : ℝ)*(upper3) + (28906883/25000000000000 : ℝ)*(lower4) + (83436143/100000000000000 : ℝ)*(upper5) + (366018004693869/10000000000000 : ℝ)*(major0) + (366018004693869/10000000000000 : ℝ)*(major1) + (366018004693869/10000000000000 : ℝ)*(major2) + (2784883573/10000000000000 : ℝ)*(sp1) + (16212072183/50000000000000 : ℝ)*(sp2) + (2427626860369393/50000000000000 : ℝ)*(sp4) + (9482860096101/195312500000 : ℝ)*(sp5) + (1213804849693397/25000000000000 : ℝ)*(sp6) + (154069131263351/6250000000000 : ℝ)*(sp7) + (154069131263351/6250000000000 : ℝ)*(f.failure) + (2427626860369393/50000000000000 : ℝ)*(f.sum) + (1187360053203/260900000000000000000000000 : ℝ)*base66 + (93771292873010143/130450000000000000000000000000000 : ℝ)*base67 + (298390071409510143/130450000000000000000000000000000 : ℝ)*base69 + (53140437072510143/130450000000000000000000000000000 : ℝ)*base71 + (765339326243/1304500000000000000000000000 : ℝ)*base74 + (1643531380186289857/130450000000000000000000000000000 : ℝ)*base76 + (275181712170410143/130450000000000000000000000000000 : ℝ)*base77 + (702527854273910143/130450000000000000000000000000000 : ℝ)*base79 + (9079986263923/1304500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1517973/125000000000000000000 : ℝ)*base89 + (1517973/125000000000000000000 : ℝ)*base91 + (1517973/125000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1091_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29695923/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (833/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8833/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5239/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14871/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1091_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1091_s4_0 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2190546471/10000000000 : ℝ)*x 0 + (1351115249/2500000000 : ℝ)*x 1 + (2627498807/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2190546471/10000000000 : ℝ)^2071 ≤ (13303918669839/100000000000000 : ℝ)^1559 := by
    have hnat : (2190546471 : ℕ)^2071*100000000000000^1559 ≤ 13303918669839^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2190546471 10000000000 13303918669839 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1351115249/2500000000 : ℝ)^2071 ≤ (44155426909927/100000000000000 : ℝ)^1559 := by
    have hnat : (1351115249 : ℕ)^2071*100000000000000^1559 ≤ 44155426909927^1559*2500000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351115249 2500000000 44155426909927 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2627498807/5000000000 : ℝ)^2071 ≤ (10635163602693/25000000000000 : ℝ)^1559 := by
    have hnat : (2627498807 : ℕ)^2071*25000000000000^1559 ≤ 10635163602693^1559*5000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627498807 5000000000 10635163602693 25000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2190546471/10000000000 : ℝ), (1351115249/2500000000 : ℝ), (2627498807/5000000000 : ℝ)] ![(13303918669839/100000000000000 : ℝ), (44155426909927/100000000000000 : ℝ), (10635163602693/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2190546471/10000000000 : ℝ)|^2071 ≤ (13303918669839/100000000000000 : ℝ)^1559
        have hw : |(-2190546471/10000000000 : ℝ)|=(2190546471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1351115249/2500000000 : ℝ)|^2071 ≤ (44155426909927/100000000000000 : ℝ)^1559
        have hw : |(1351115249/2500000000 : ℝ)|=(1351115249/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2627498807/5000000000 : ℝ)|^2071 ≤ (10635163602693/25000000000000 : ℝ)^1559
        have hw : |(2627498807/5000000000 : ℝ)|=(2627498807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1091_s4_1 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (66844361/125000000 : ℝ)*x 0 + (-566636417/2500000000 : ℝ)*x 1 + (5254997423/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66844361/125000000 : ℝ)^2071 ≤ (21769403883787/50000000000000 : ℝ)^1559 := by
    have hnat : (66844361 : ℕ)^2071*50000000000000^1559 ≤ 21769403883787^1559*125000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66844361 125000000 21769403883787 50000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (566636417/2500000000 : ℝ)^2071 ≤ (3480134963173/25000000000000 : ℝ)^1559 := by
    have hnat : (566636417 : ℕ)^2071*25000000000000^1559 ≤ 3480134963173^1559*2500000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      566636417 2500000000 3480134963173 25000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5254997423/10000000000 : ℝ)^2071 ≤ (21270326178389/50000000000000 : ℝ)^1559 := by
    have hnat : (5254997423 : ℕ)^2071*50000000000000^1559 ≤ 21270326178389^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254997423 10000000000 21270326178389 50000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66844361/125000000 : ℝ), (-566636417/2500000000 : ℝ), (5254997423/10000000000 : ℝ)] ![(21769403883787/50000000000000 : ℝ), (3480134963173/25000000000000 : ℝ), (21270326178389/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66844361/125000000 : ℝ)|^2071 ≤ (21769403883787/50000000000000 : ℝ)^1559
        have hw : |(66844361/125000000 : ℝ)|=(66844361/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-566636417/2500000000 : ℝ)|^2071 ≤ (3480134963173/25000000000000 : ℝ)^1559
        have hw : |(-566636417/2500000000 : ℝ)|=(566636417/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5254997423/10000000000 : ℝ)|^2071 ≤ (21270326178389/50000000000000 : ℝ)^1559
        have hw : |(5254997423/10000000000 : ℝ)|=(5254997423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1091_s4_2 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1336887289/2500000000 : ℝ)*x 0 + (1050999471/2000000000 : ℝ)*x 1 + (-141659087/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336887289/2500000000 : ℝ)^2071 ≤ (8707762150543/20000000000000 : ℝ)^1559 := by
    have hnat : (1336887289 : ℕ)^2071*20000000000000^1559 ≤ 8707762150543^1559*2500000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336887289 2500000000 8707762150543 20000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1050999471/2000000000 : ℝ)^2071 ≤ (21270325812757/50000000000000 : ℝ)^1559 := by
    have hnat : (1050999471 : ℕ)^2071*50000000000000^1559 ≤ 21270325812757^1559*2000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050999471 2000000000 21270325812757 50000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (141659087/625000000 : ℝ)^2071 ≤ (6960268800433/50000000000000 : ℝ)^1559 := by
    have hnat : (141659087 : ℕ)^2071*50000000000000^1559 ≤ 6960268800433^1559*625000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      141659087 625000000 6960268800433 50000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336887289/2500000000 : ℝ), (1050999471/2000000000 : ℝ), (-141659087/625000000 : ℝ)] ![(8707762150543/20000000000000 : ℝ), (21270325812757/50000000000000 : ℝ), (6960268800433/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336887289/2500000000 : ℝ)|^2071 ≤ (8707762150543/20000000000000 : ℝ)^1559
        have hw : |(1336887289/2500000000 : ℝ)|=(1336887289/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1050999471/2000000000 : ℝ)|^2071 ≤ (21270325812757/50000000000000 : ℝ)^1559
        have hw : |(1050999471/2000000000 : ℝ)|=(1050999471/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-141659087/625000000 : ℝ)|^2071 ≤ (6960268800433/50000000000000 : ℝ)^1559
        have hw : |(-141659087/625000000 : ℝ)|=(141659087/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1091_s4_3 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4371347167/10000000000 : ℝ)*x 0 + (10566627/25000000 : ℝ)*x 1 + (1130258229/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4371347167/10000000000 : ℝ)^2071 ≤ (16655502606803/50000000000000 : ℝ)^1559 := by
    have hnat : (4371347167 : ℕ)^2071*50000000000000^1559 ≤ 16655502606803^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4371347167 10000000000 16655502606803 50000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (10566627/25000000 : ℝ)^2071 ≤ (31107690239/97656250000 : ℝ)^1559 := by
    have hnat : (10566627 : ℕ)^2071*97656250000^1559 ≤ 31107690239^1559*25000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10566627 25000000 31107690239 97656250000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1130258229/2500000000 : ℝ)^2071 ≤ (8708679990817/25000000000000 : ℝ)^1559 := by
    have hnat : (1130258229 : ℕ)^2071*25000000000000^1559 ≤ 8708679990817^1559*2500000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1130258229 2500000000 8708679990817 25000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4371347167/10000000000 : ℝ), (10566627/25000000 : ℝ), (1130258229/2500000000 : ℝ)] ![(16655502606803/50000000000000 : ℝ), (31107690239/97656250000 : ℝ), (8708679990817/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4371347167/10000000000 : ℝ)|^2071 ≤ (16655502606803/50000000000000 : ℝ)^1559
        have hw : |(4371347167/10000000000 : ℝ)|=(4371347167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(10566627/25000000 : ℝ)|^2071 ≤ (31107690239/97656250000 : ℝ)^1559
        have hw : |(10566627/25000000 : ℝ)|=(10566627/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1130258229/2500000000 : ℝ)|^2071 ≤ (8708679990817/25000000000000 : ℝ)^1559
        have hw : |(1130258229/2500000000 : ℝ)|=(1130258229/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1091_s4_4 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-547638693/2500000000 : ℝ)*x 0 + (5255431083/10000000000 : ℝ)*x 1 + (5404025319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (547638693/2500000000 : ℝ)^2071 ≤ (13303985641609/100000000000000 : ℝ)^1559 := by
    have hnat : (547638693 : ℕ)^2071*100000000000000^1559 ≤ 13303985641609^1559*2500000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547638693 2500000000 13303985641609 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5255431083/10000000000 : ℝ)^2071 ≤ (42545315952253/100000000000000 : ℝ)^1559 := by
    have hnat : (5255431083 : ℕ)^2071*100000000000000^1559 ≤ 42545315952253^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255431083 10000000000 42545315952253 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5404025319/10000000000 : ℝ)^2071 ≤ (11037674599281/25000000000000 : ℝ)^1559 := by
    have hnat : (5404025319 : ℕ)^2071*25000000000000^1559 ≤ 11037674599281^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404025319 10000000000 11037674599281 25000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-547638693/2500000000 : ℝ), (5255431083/10000000000 : ℝ), (5404025319/10000000000 : ℝ)] ![(13303985641609/100000000000000 : ℝ), (42545315952253/100000000000000 : ℝ), (11037674599281/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-547638693/2500000000 : ℝ)|^2071 ≤ (13303985641609/100000000000000 : ℝ)^1559
        have hw : |(-547638693/2500000000 : ℝ)|=(547638693/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5255431083/10000000000 : ℝ)|^2071 ≤ (42545315952253/100000000000000 : ℝ)^1559
        have hw : |(5255431083/10000000000 : ℝ)|=(5255431083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5404025319/10000000000 : ℝ)|^2071 ≤ (11037674599281/25000000000000 : ℝ)^1559
        have hw : |(5404025319/10000000000 : ℝ)|=(5404025319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1091_s4_5 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2654914927/5000000000 : ℝ)*x 0 + (-1058758851/5000000000 : ℝ)*x 1 + (5404025351/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2654914927/5000000000 : ℝ)^2071 ≤ (4313132230887/10000000000000 : ℝ)^1559 := by
    have hnat : (2654914927 : ℕ)^2071*10000000000000^1559 ≤ 4313132230887^1559*5000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2654914927 5000000000 4313132230887 10000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1058758851/5000000000 : ℝ)^2071 ≤ (12717978931677/100000000000000 : ℝ)^1559 := by
    have hnat : (1058758851 : ℕ)^2071*100000000000000^1559 ≤ 12717978931677^1559*5000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058758851 5000000000 12717978931677 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5404025351/10000000000 : ℝ)^2071 ≤ (5518837343053/12500000000000 : ℝ)^1559 := by
    have hnat : (5404025351 : ℕ)^2071*12500000000000^1559 ≤ 5518837343053^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404025351 10000000000 5518837343053 12500000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2654914927/5000000000 : ℝ), (-1058758851/5000000000 : ℝ), (5404025351/10000000000 : ℝ)] ![(4313132230887/10000000000000 : ℝ), (12717978931677/100000000000000 : ℝ), (5518837343053/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2654914927/5000000000 : ℝ)|^2071 ≤ (4313132230887/10000000000000 : ℝ)^1559
        have hw : |(2654914927/5000000000 : ℝ)|=(2654914927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1058758851/5000000000 : ℝ)|^2071 ≤ (12717978931677/100000000000000 : ℝ)^1559
        have hw : |(-1058758851/5000000000 : ℝ)|=(1058758851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5404025351/10000000000 : ℝ)|^2071 ≤ (5518837343053/12500000000000 : ℝ)^1559
        have hw : |(5404025351/10000000000 : ℝ)|=(5404025351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1091_s4_6 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1327457533/2500000000 : ℝ)*x 0 + (5404025349/10000000000 : ℝ)*x 1 + (-2117517329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1327457533/2500000000 : ℝ)^2071 ≤ (43131325308661/100000000000000 : ℝ)^1559 := by
    have hnat : (1327457533 : ℕ)^2071*100000000000000^1559 ≤ 43131325308661^1559*2500000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327457533 2500000000 43131325308661 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5404025349/10000000000 : ℝ)^2071 ≤ (44150698722717/100000000000000 : ℝ)^1559 := by
    have hnat : (5404025349 : ℕ)^2071*100000000000000^1559 ≤ 44150698722717^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404025349 10000000000 44150698722717 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2117517329/10000000000 : ℝ)^2071 ≤ (1271797595567/10000000000000 : ℝ)^1559 := by
    have hnat : (2117517329 : ℕ)^2071*10000000000000^1559 ≤ 1271797595567^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117517329 10000000000 1271797595567 10000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1327457533/2500000000 : ℝ), (5404025349/10000000000 : ℝ), (-2117517329/10000000000 : ℝ)] ![(43131325308661/100000000000000 : ℝ), (44150698722717/100000000000000 : ℝ), (1271797595567/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1327457533/2500000000 : ℝ)|^2071 ≤ (43131325308661/100000000000000 : ℝ)^1559
        have hw : |(1327457533/2500000000 : ℝ)|=(1327457533/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5404025349/10000000000 : ℝ)|^2071 ≤ (44150698722717/100000000000000 : ℝ)^1559
        have hw : |(5404025349/10000000000 : ℝ)|=(5404025349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2117517329/10000000000 : ℝ)|^2071 ≤ (1271797595567/10000000000000 : ℝ)^1559
        have hw : |(-2117517329/10000000000 : ℝ)|=(2117517329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1091_s4_7 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4371362307/10000000000 : ℝ)*x 0 + (4520178927/10000000000 : ℝ)*x 1 + (4227508519/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4371362307/10000000000 : ℝ)^2071 ≤ (832778961873/2500000000000 : ℝ)^1559 := by
    have hnat : (4371362307 : ℕ)^2071*2500000000000^1559 ≤ 832778961873^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4371362307 10000000000 832778961873 2500000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4520178927/10000000000 : ℝ)^2071 ≤ (4353247404817/12500000000000 : ℝ)^1559 := by
    have hnat : (4520178927 : ℕ)^2071*12500000000000^1559 ≤ 4353247404817^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4520178927 10000000000 4353247404817 12500000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4227508519/10000000000 : ℝ)^2071 ≤ (3982857783369/12500000000000 : ℝ)^1559 := by
    have hnat : (4227508519 : ℕ)^2071*12500000000000^1559 ≤ 3982857783369^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227508519 10000000000 3982857783369 12500000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4371362307/10000000000 : ℝ), (4520178927/10000000000 : ℝ), (4227508519/10000000000 : ℝ)] ![(832778961873/2500000000000 : ℝ), (4353247404817/12500000000000 : ℝ), (3982857783369/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4371362307/10000000000 : ℝ)|^2071 ≤ (832778961873/2500000000000 : ℝ)^1559
        have hw : |(4371362307/10000000000 : ℝ)|=(4371362307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4520178927/10000000000 : ℝ)|^2071 ≤ (4353247404817/12500000000000 : ℝ)^1559
        have hw : |(4520178927/10000000000 : ℝ)|=(4520178927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4227508519/10000000000 : ℝ)|^2071 ≤ (3982857783369/12500000000000 : ℝ)^1559
        have hw : |(4227508519/10000000000 : ℝ)|=(4227508519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1091_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29695923/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14871/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5239/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (443/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14239/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14871/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5239/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14871/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5239/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14871/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5239/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14871/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5239/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14871/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5239/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14871/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5239/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5239/50000 : ℝ) ^ (8283/2048 : ℝ) ≤ (436155161127147/4000000000000000000 : ℝ) := by
    have hpowers : (5239/50000 : ℝ)^8283 ≤ (436155161127147/4000000000000000000 : ℝ)^2048 := by
      have hnat : (5239 : ℕ)^8283*4000000000000000000^2048 ≤ 436155161127147^2048*50000^8283 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5239 50000 436155161127147 4000000000000000000 8283 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5239/50000 : ℝ)) (X := (436155161127147/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8283 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14871/100000 : ℝ) ^ (8283/2048 : ℝ) ≤ (2246750248238487/5000000000000000000 : ℝ) := by
    have hpowers : (14871/100000 : ℝ)^8283 ≤ (2246750248238487/5000000000000000000 : ℝ)^2048 := by
      have hnat : (14871 : ℕ)^8283*5000000000000000000^2048 ≤ 2246750248238487^2048*100000^8283 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14871 100000 2246750248238487 5000000000000000000 8283 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14871/100000 : ℝ)) (X := (2246750248238487/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8283 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000436155161127147/2000000000000000000 : ℝ) ≤ (5000269580002109/5000000000000000 : ℝ) ^ (8283/2048 : ℝ) := by
    have hpowers : (2000436155161127147/2000000000000000000 : ℝ)^2048 ≤ (5000269580002109/5000000000000000 : ℝ)^8283 := by
      have hnat : (2000436155161127147 : ℕ)^2048*5000000000000000^8283 ≤ 5000269580002109^8283*2000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000436155161127147 2000000000000000000 5000269580002109 5000000000000000 2048 8283 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000269580002109/5000000000000000 : ℝ)) (X := (2000436155161127147/2000000000000000000 : ℝ)) (by norm_num) 8283 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20011167776798589683/20000000000000000000 : ℝ) ≤ (10001380345387759/10000000000000000 : ℝ) ^ (8283/2048 : ℝ) := by
    have hpowers : (20011167776798589683/20000000000000000000 : ℝ)^2048 ≤ (10001380345387759/10000000000000000 : ℝ)^8283 := by
      have hnat : (20011167776798589683 : ℕ)^2048*10000000000000000^8283 ≤ 10001380345387759^8283*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20011167776798589683 20000000000000000000 10001380345387759 10000000000000000 2048 8283 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001380345387759/10000000000000000 : ℝ)) (X := (20011167776798589683/20000000000000000000 : ℝ)) (by norm_num) 8283 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (2502246750248238487/2500000000000000000 : ℝ) ≤ (100022215307713/100000000000000 : ℝ) ^ (8283/2048 : ℝ) := by
    have hpowers : (2502246750248238487/2500000000000000000 : ℝ)^2048 ≤ (100022215307713/100000000000000 : ℝ)^8283 := by
      have hnat : (2502246750248238487 : ℕ)^2048*100000000000000^8283 ≤ 100022215307713^8283*2500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2502246750248238487 2500000000000000000 100022215307713 100000000000000 2048 8283 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (100022215307713/100000000000000 : ℝ)) (X := (2502246750248238487/2500000000000000000 : ℝ)) (by norm_num) 8283 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(436155161127147/4000000000000000000 : ℝ) ≤ ((21957370324500522239/21965000000000000000 : ℝ)+2*(841185383541/439300000000000 : ℝ)*(5239/50000 : ℝ))^(8283/2048 : ℝ) := by
    rw [show (21957370324500522239/21965000000000000000 : ℝ)+2*(841185383541/439300000000000 : ℝ)*(5239/50000 : ℝ)=(5000269580002109/5000000000000000 : ℝ) by norm_num, show 1+2*(436155161127147/4000000000000000000 : ℝ)=(2000436155161127147/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2246750248238487/5000000000000000000 : ℝ)+(436155161127147/4000000000000000000 : ℝ) ≤ ((21957370324500522239/21965000000000000000 : ℝ)+(841185383541/439300000000000 : ℝ)*((14871/100000 : ℝ)+(5239/50000 : ℝ)))^(8283/2048 : ℝ) := by
    rw [show (21957370324500522239/21965000000000000000 : ℝ)+(841185383541/439300000000000 : ℝ)*((14871/100000 : ℝ)+(5239/50000 : ℝ))=(10001380345387759/10000000000000000 : ℝ) by norm_num, show 1+(2246750248238487/5000000000000000000 : ℝ)+(436155161127147/4000000000000000000 : ℝ)=(20011167776798589683/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2246750248238487/5000000000000000000 : ℝ) ≤ ((21957370324500522239/21965000000000000000 : ℝ)+2*(841185383541/439300000000000 : ℝ)*(14871/100000 : ℝ))^(8283/2048 : ℝ) := by
    rw [show (21957370324500522239/21965000000000000000 : ℝ)+2*(841185383541/439300000000000 : ℝ)*(14871/100000 : ℝ)=(100022215307713/100000000000000 : ℝ) by norm_num, show 1+2*(2246750248238487/5000000000000000000 : ℝ)=(2502246750248238487/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (21957370324500522239/21965000000000000000 : ℝ)*(X 1 0+X 2 0)+(841185383541/439300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8283/2048 : ℝ)) (lo := (5239/50000 : ℝ)) (hi := (14871/100000 : ℝ)) (c := (21957370324500522239/21965000000000000000 : ℝ)) (alpha := (841185383541/439300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (21957370324500522239/21965000000000000000 : ℝ)*(X 0 1+X 2 1)+(841185383541/439300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8283/2048 : ℝ)) (lo := (5239/50000 : ℝ)) (hi := (14871/100000 : ℝ)) (c := (21957370324500522239/21965000000000000000 : ℝ)) (alpha := (841185383541/439300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (21957370324500522239/21965000000000000000 : ℝ)*(X 0 2+X 1 2)+(841185383541/439300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8283/2048 : ℝ)) (lo := (5239/50000 : ℝ)) (hi := (14871/100000 : ℝ)) (c := (21957370324500522239/21965000000000000000 : ℝ)) (alpha := (841185383541/439300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2190546471/10000000000 : ℝ)*X 0 0+(1351115249/2500000000 : ℝ)*X 0 1+(2627498807/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((66844361/125000000 : ℝ)*X 1 0+(-566636417/2500000000 : ℝ)*X 1 1+(5254997423/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336887289/2500000000 : ℝ)*X 2 0+(1050999471/2000000000 : ℝ)*X 2 1+(-141659087/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4371347167/10000000000 : ℝ)*X 0 0+(10566627/25000000 : ℝ)*X 0 1+(1130258229/2500000000 : ℝ)*X 0 2+(4371347167/10000000000 : ℝ)*X 1 0+(10566627/25000000 : ℝ)*X 1 1+(1130258229/2500000000 : ℝ)*X 1 2+(4371347167/10000000000 : ℝ)*X 2 0+(10566627/25000000 : ℝ)*X 2 1+(1130258229/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-547638693/2500000000 : ℝ)*X 0 0+(5255431083/10000000000 : ℝ)*X 0 1+(5404025319/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2654914927/5000000000 : ℝ)*X 1 0+(-1058758851/5000000000 : ℝ)*X 1 1+(5404025351/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1327457533/2500000000 : ℝ)*X 2 0+(5404025349/10000000000 : ℝ)*X 2 1+(-2117517329/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4371362307/10000000000 : ℝ)*X 0 0+(4520178927/10000000000 : ℝ)*X 0 1+(4227508519/10000000000 : ℝ)*X 0 2+(4371362307/10000000000 : ℝ)*X 1 0+(4520178927/10000000000 : ℝ)*X 1 1+(4227508519/10000000000 : ℝ)*X 1 2+(4371362307/10000000000 : ℝ)*X 2 0+(4520178927/10000000000 : ℝ)*X 2 1+(4227508519/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2804879384369361769287872283/1098250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (79383779/50000000000000 : ℝ)*(base8) + (36087979/25000000000000 : ℝ)*(base21) + (34292021/100000000000000 : ℝ)*(base29) + (63699697/25000000000000 : ℝ)*(lower2) + (12791887/100000000000000 : ℝ)*(upper4) + (5043765714617/100000000000 : ℝ)*(major0) + (5043765748909021/100000000000000 : ℝ)*(major1) + (2521882874454511/50000000000000 : ℝ)*(major2) + (6690589694695883/100000000000000 : ℝ)*(sp0) + (1672646409473063/25000000000000 : ℝ)*(sp1) + (1338117934963901/20000000000000 : ℝ)*(sp2) + (212308805420713/6250000000000 : ℝ)*(sp3) + (65332487/1562500000000 : ℝ)*(sp5) + (672491401/100000000000000 : ℝ)*(sp7) + (424617694902851/12500000000000 : ℝ)*(f.failure) + (3345294926731721/50000000000000 : ℝ)*(f.sum) + (107602344134763/43930000000000000000000000000 : ℝ)*base65 + (26313243995574181981/2196500000000000000000000000000000 : ℝ)*base68 + (2035027341949145129/1098250000000000000000000000000000 : ℝ)*base69 + (14529780690124937/2196500000000000000000000000000 : ℝ)*base72 + (23003759379531/5491250000000000000000000000 : ℝ)*base74 + (2454965429043620129/1098250000000000000000000000000000 : ℝ)*base75 + (50851712814983987/2196500000000000000000000000000 : ℝ)*base78 + (713127192919338347/95500000000000000000000000000000 : ℝ)*base80 + (346501285415549/43930000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (3276473/250000000000000000000 : ℝ)*base89 + (3276473/250000000000000000000 : ℝ)*base91 + (776473/250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4112554531729523433681203259/1098250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (103609879/100000000000000 : ℝ)*(base19) + (514681589/100000000000000 : ℝ)*(base23) + (69154009/100000000000000 : ℝ)*(upper3) + (36575121/100000000000000 : ℝ)*(upper4) + (16008607/25000000000000 : ℝ)*(upper5) + (5073280389416909/100000000000000 : ℝ)*(major0) + (5073280389416909/100000000000000 : ℝ)*(major1) + (5073280389416909/100000000000000 : ℝ)*(major2) + (2245564969/12500000000000 : ℝ)*(sp2) + (253972461/12500000000000 : ℝ)*(sp3) + (210304412103181/3125000000000 : ℝ)*(sp4) + (6729741083691913/100000000000000 : ℝ)*(sp5) + (6729722708100451/100000000000000 : ℝ)*(sp6) + (854204358732721/25000000000000 : ℝ)*(sp7) + (3416819466710571/100000000000000 : ℝ)*(f.failure) + (210304412103181/3125000000000 : ℝ)*(f.sum) + (123665589139869/21965000000000000000000000000 : ℝ)*base65 + (49441375620750410749/2196500000000000000000000000000000 : ℝ)*base68 + (22373576751182410749/2196500000000000000000000000000000 : ℝ)*base70 + (9242726961313410749/2196500000000000000000000000000000 : ℝ)*base72 + (132677076951261/21965000000000000000000000000 : ℝ)*base74 + (33935106692329910749/2196500000000000000000000000000000 : ℝ)*base76 + (32898478755216410749/2196500000000000000000000000000000 : ℝ)*base78 + (33778546234669910749/2196500000000000000000000000000000 : ℝ)*base80 + (17541738660551/5491250000000000000000000000 : ℝ)*base81 + (297967/2000000000000000000000 : ℝ)*base90 + (297967/2000000000000000000000 : ℝ)*base92 + (297967/2000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1091_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29695923/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14871/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5239/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (443/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14239/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1091_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1091_s5_0 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2191309851/10000000000 : ℝ)*x 0 + (2698143057/5000000000 : ℝ)*x 1 + (5262671503/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2191309851/10000000000 : ℝ)^2071 ≤ (3327519476021/25000000000000 : ℝ)^1559 := by
    have hnat : (2191309851 : ℕ)^2071*25000000000000^1559 ≤ 3327519476021^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2191309851 10000000000 3327519476021 25000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2698143057/5000000000 : ℝ)^2071 ≤ (8813344743277/20000000000000 : ℝ)^1559 := by
    have hnat : (2698143057 : ℕ)^2071*20000000000000^1559 ≤ 8813344743277^1559*5000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698143057 5000000000 8813344743277 20000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5262671503/10000000000 : ℝ)^2071 ≤ (42623198358277/100000000000000 : ℝ)^1559 := by
    have hnat : (5262671503 : ℕ)^2071*100000000000000^1559 ≤ 42623198358277^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262671503 10000000000 42623198358277 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2191309851/10000000000 : ℝ), (2698143057/5000000000 : ℝ), (5262671503/10000000000 : ℝ)] ![(3327519476021/25000000000000 : ℝ), (8813344743277/20000000000000 : ℝ), (42623198358277/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2191309851/10000000000 : ℝ)|^2071 ≤ (3327519476021/25000000000000 : ℝ)^1559
        have hw : |(-2191309851/10000000000 : ℝ)|=(2191309851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2698143057/5000000000 : ℝ)|^2071 ≤ (8813344743277/20000000000000 : ℝ)^1559
        have hw : |(2698143057/5000000000 : ℝ)|=(2698143057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5262671503/10000000000 : ℝ)|^2071 ≤ (42623198358277/100000000000000 : ℝ)^1559
        have hw : |(5262671503/10000000000 : ℝ)|=(5262671503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1091_s5_1 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5345507957/10000000000 : ℝ)*x 0 + (-1129564801/5000000000 : ℝ)*x 1 + (657833941/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345507957/10000000000 : ℝ)^2071 ≤ (43516735083241/100000000000000 : ℝ)^1559 := by
    have hnat : (5345507957 : ℕ)^2071*100000000000000^1559 ≤ 43516735083241^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345507957 10000000000 43516735083241 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1129564801/5000000000 : ℝ)^2071 ≤ (13860066283599/100000000000000 : ℝ)^1559 := by
    have hnat : (1129564801 : ℕ)^2071*100000000000000^1559 ≤ 13860066283599^1559*5000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1129564801 5000000000 13860066283599 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (657833941/1250000000 : ℝ)^2071 ≤ (42623198627253/100000000000000 : ℝ)^1559 := by
    have hnat : (657833941 : ℕ)^2071*100000000000000^1559 ≤ 42623198627253^1559*1250000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657833941 1250000000 42623198627253 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345507957/10000000000 : ℝ), (-1129564801/5000000000 : ℝ), (657833941/1250000000 : ℝ)] ![(43516735083241/100000000000000 : ℝ), (13860066283599/100000000000000 : ℝ), (42623198627253/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345507957/10000000000 : ℝ)|^2071 ≤ (43516735083241/100000000000000 : ℝ)^1559
        have hw : |(5345507957/10000000000 : ℝ)|=(5345507957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1129564801/5000000000 : ℝ)|^2071 ≤ (13860066283599/100000000000000 : ℝ)^1559
        have hw : |(-1129564801/5000000000 : ℝ)|=(1129564801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(657833941/1250000000 : ℝ)|^2071 ≤ (42623198627253/100000000000000 : ℝ)^1559
        have hw : |(657833941/1250000000 : ℝ)|=(657833941/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1091_s5_2 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5345507963/10000000000 : ℝ)*x 0 + (5262671517/10000000000 : ℝ)*x 1 + (-282391201/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345507963/10000000000 : ℝ)^2071 ≤ (1359897973379/3125000000000 : ℝ)^1559 := by
    have hnat : (5345507963 : ℕ)^2071*3125000000000^1559 ≤ 1359897973379^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345507963 10000000000 1359897973379 3125000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5262671517/10000000000 : ℝ)^2071 ≤ (42623198508903/100000000000000 : ℝ)^1559 := by
    have hnat : (5262671517 : ℕ)^2071*100000000000000^1559 ≤ 42623198508903^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262671517 10000000000 42623198508903 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (282391201/1250000000 : ℝ)^2071 ≤ (13860066332499/100000000000000 : ℝ)^1559 := by
    have hnat : (282391201 : ℕ)^2071*100000000000000^1559 ≤ 13860066332499^1559*1250000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      282391201 1250000000 13860066332499 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345507963/10000000000 : ℝ), (5262671517/10000000000 : ℝ), (-282391201/1250000000 : ℝ)] ![(1359897973379/3125000000000 : ℝ), (42623198508903/100000000000000 : ℝ), (13860066332499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345507963/10000000000 : ℝ)|^2071 ≤ (1359897973379/3125000000000 : ℝ)^1559
        have hw : |(5345507963/10000000000 : ℝ)|=(5345507963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5262671517/10000000000 : ℝ)|^2071 ≤ (42623198508903/100000000000000 : ℝ)^1559
        have hw : |(5262671517/10000000000 : ℝ)|=(5262671517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-282391201/1250000000 : ℝ)|^2071 ≤ (13860066332499/100000000000000 : ℝ)^1559
        have hw : |(-282391201/1250000000 : ℝ)|=(282391201/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1091_s5_3 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2185894923/5000000000 : ℝ)*x 0 + (4242200799/10000000000 : ℝ)*x 1 + (140792721/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2185894923/5000000000 : ℝ)^2071 ≤ (33315486498607/100000000000000 : ℝ)^1559 := by
    have hnat : (2185894923 : ℕ)^2071*100000000000000^1559 ≤ 33315486498607^1559*5000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185894923 5000000000 33315486498607 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4242200799/10000000000 : ℝ)^2071 ≤ (32010049810839/100000000000000 : ℝ)^1559 := by
    have hnat : (4242200799 : ℕ)^2071*100000000000000^1559 ≤ 32010049810839^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4242200799 10000000000 32010049810839 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (140792721/312500000 : ℝ)^2071 ≤ (6934892736369/20000000000000 : ℝ)^1559 := by
    have hnat : (140792721 : ℕ)^2071*20000000000000^1559 ≤ 6934892736369^1559*312500000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140792721 312500000 6934892736369 20000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2185894923/5000000000 : ℝ), (4242200799/10000000000 : ℝ), (140792721/312500000 : ℝ)] ![(33315486498607/100000000000000 : ℝ), (32010049810839/100000000000000 : ℝ), (6934892736369/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2185894923/5000000000 : ℝ)|^2071 ≤ (33315486498607/100000000000000 : ℝ)^1559
        have hw : |(2185894923/5000000000 : ℝ)|=(2185894923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4242200799/10000000000 : ℝ)|^2071 ≤ (32010049810839/100000000000000 : ℝ)^1559
        have hw : |(4242200799/10000000000 : ℝ)|=(4242200799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(140792721/312500000 : ℝ)|^2071 ≤ (6934892736369/20000000000000 : ℝ)^1559
        have hw : |(140792721/312500000 : ℝ)|=(140792721/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1091_s5_4 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-219131551/1000000000 : ℝ)*x 0 + (2631509157/5000000000 : ℝ)*x 1 + (5395937931/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (219131551/1000000000 : ℝ)^2071 ≤ (3327530891409/25000000000000 : ℝ)^1559 := by
    have hnat : (219131551 : ℕ)^2071*25000000000000^1559 ≤ 3327530891409^1559*1000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219131551 1000000000 3327530891409 25000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2631509157/5000000000 : ℝ)^2071 ≤ (10656732438523/25000000000000 : ℝ)^1559 := by
    have hnat : (2631509157 : ℕ)^2071*25000000000000^1559 ≤ 10656732438523^1559*5000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631509157 5000000000 10656732438523 25000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5395937931/10000000000 : ℝ)^2071 ≤ (8812589333267/20000000000000 : ℝ)^1559 := by
    have hnat : (5395937931 : ℕ)^2071*20000000000000^1559 ≤ 8812589333267^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395937931 10000000000 8812589333267 20000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-219131551/1000000000 : ℝ), (2631509157/5000000000 : ℝ), (5395937931/10000000000 : ℝ)] ![(3327530891409/25000000000000 : ℝ), (10656732438523/25000000000000 : ℝ), (8812589333267/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-219131551/1000000000 : ℝ)|^2071 ≤ (3327530891409/25000000000000 : ℝ)^1559
        have hw : |(-219131551/1000000000 : ℝ)|=(219131551/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2631509157/5000000000 : ℝ)|^2071 ≤ (10656732438523/25000000000000 : ℝ)^1559
        have hw : |(2631509157/5000000000 : ℝ)|=(2631509157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5395937931/10000000000 : ℝ)|^2071 ≤ (8812589333267/20000000000000 : ℝ)^1559
        have hw : |(5395937931/10000000000 : ℝ)|=(5395937931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1091_s5_5 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1327946831/2500000000 : ℝ)*x 0 + (-1062931557/5000000000 : ℝ)*x 1 + (5395938023/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1327946831/2500000000 : ℝ)^2071 ≤ (43152445890317/100000000000000 : ℝ)^1559 := by
    have hnat : (1327946831 : ℕ)^2071*100000000000000^1559 ≤ 43152445890317^1559*2500000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327946831 2500000000 43152445890317 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1062931557/5000000000 : ℝ)^2071 ≤ (3196151608721/25000000000000 : ℝ)^1559 := by
    have hnat : (1062931557 : ℕ)^2071*25000000000000^1559 ≤ 3196151608721^1559*5000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062931557 5000000000 3196151608721 25000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5395938023/10000000000 : ℝ)^2071 ≤ (4406294766433/10000000000000 : ℝ)^1559 := by
    have hnat : (5395938023 : ℕ)^2071*10000000000000^1559 ≤ 4406294766433^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395938023 10000000000 4406294766433 10000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1327946831/2500000000 : ℝ), (-1062931557/5000000000 : ℝ), (5395938023/10000000000 : ℝ)] ![(43152445890317/100000000000000 : ℝ), (3196151608721/25000000000000 : ℝ), (4406294766433/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1327946831/2500000000 : ℝ)|^2071 ≤ (43152445890317/100000000000000 : ℝ)^1559
        have hw : |(1327946831/2500000000 : ℝ)|=(1327946831/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1062931557/5000000000 : ℝ)|^2071 ≤ (3196151608721/25000000000000 : ℝ)^1559
        have hw : |(-1062931557/5000000000 : ℝ)|=(1062931557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5395938023/10000000000 : ℝ)|^2071 ≤ (4406294766433/10000000000000 : ℝ)^1559
        have hw : |(5395938023/10000000000 : ℝ)|=(5395938023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1091_s5_6 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1327946837/2500000000 : ℝ)*x 0 + (5395937961/10000000000 : ℝ)*x 1 + (-425172633/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1327946837/2500000000 : ℝ)^2071 ≤ (43152446149323/100000000000000 : ℝ)^1559 := by
    have hnat : (1327946837 : ℕ)^2071*100000000000000^1559 ≤ 43152446149323^1559*2500000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327946837 2500000000 43152446149323 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5395937961/10000000000 : ℝ)^2071 ≤ (44062946991769/100000000000000 : ℝ)^1559 := by
    have hnat : (5395937961 : ℕ)^2071*100000000000000^1559 ≤ 44062946991769^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395937961 10000000000 44062946991769 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (425172633/2000000000 : ℝ)^2071 ≤ (12784606842317/100000000000000 : ℝ)^1559 := by
    have hnat : (425172633 : ℕ)^2071*100000000000000^1559 ≤ 12784606842317^1559*2000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425172633 2000000000 12784606842317 100000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1327946837/2500000000 : ℝ), (5395937961/10000000000 : ℝ), (-425172633/2000000000 : ℝ)] ![(43152446149323/100000000000000 : ℝ), (44062946991769/100000000000000 : ℝ), (12784606842317/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1327946837/2500000000 : ℝ)|^2071 ≤ (43152446149323/100000000000000 : ℝ)^1559
        have hw : |(1327946837/2500000000 : ℝ)|=(1327946837/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5395937961/10000000000 : ℝ)|^2071 ≤ (44062946991769/100000000000000 : ℝ)^1559
        have hw : |(5395937961/10000000000 : ℝ)|=(5395937961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-425172633/2000000000 : ℝ)|^2071 ≤ (12784606842317/100000000000000 : ℝ)^1559
        have hw : |(-425172633/2000000000 : ℝ)|=(425172633/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1091_s5_7 (p : ℝ) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2185900407/5000000000 : ℝ)*x 0 + (2252341949/5000000000 : ℝ)*x 1 + (4242886497/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2185900407/5000000000 : ℝ)^2071 ≤ (3331559753069/10000000000000 : ℝ)^1559 := by
    have hnat : (2185900407 : ℕ)^2071*10000000000000^1559 ≤ 3331559753069^1559*5000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185900407 5000000000 3331559753069 10000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2252341949/5000000000 : ℝ)^2071 ≤ (866686980049/2500000000000 : ℝ)^1559 := by
    have hnat : (2252341949 : ℕ)^2071*2500000000000^1559 ≤ 866686980049^1559*5000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252341949 5000000000 866686980049 2500000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4242886497/10000000000 : ℝ)^2071 ≤ (8004230810239/25000000000000 : ℝ)^1559 := by
    have hnat : (4242886497 : ℕ)^2071*25000000000000^1559 ≤ 8004230810239^1559*10000000000^2071 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4242886497 10000000000 8004230810239 25000000000000 2071 1559 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2071/512 : ℝ)) 2071 1559 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2185900407/5000000000 : ℝ), (2252341949/5000000000 : ℝ), (4242886497/10000000000 : ℝ)] ![(3331559753069/10000000000000 : ℝ), (866686980049/2500000000000 : ℝ), (8004230810239/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2185900407/5000000000 : ℝ)|^2071 ≤ (3331559753069/10000000000000 : ℝ)^1559
        have hw : |(2185900407/5000000000 : ℝ)|=(2185900407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2252341949/5000000000 : ℝ)|^2071 ≤ (866686980049/2500000000000 : ℝ)^1559
        have hw : |(2252341949/5000000000 : ℝ)|=(2252341949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4242886497/10000000000 : ℝ)|^2071 ≤ (8004230810239/25000000000000 : ℝ)^1559
        have hw : |(4242886497/10000000000 : ℝ)|=(4242886497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1091_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29695923/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14239/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (443/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (5619/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3517/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14239/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (443/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14239/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (443/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14239/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (443/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14239/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (443/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14239/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (443/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14239/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (443/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (443/4000 : ℝ) ^ (8283/2048 : ℝ) ≤ (6821528558684023/50000000000000000000 : ℝ) := by
    have hpowers : (443/4000 : ℝ)^8283 ≤ (6821528558684023/50000000000000000000 : ℝ)^2048 := by
      have hnat : (443 : ℕ)^8283*50000000000000000000^2048 ≤ 6821528558684023^2048*4000^8283 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        443 4000 6821528558684023 50000000000000000000 8283 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (443/4000 : ℝ)) (X := (6821528558684023/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8283 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14239/100000 : ℝ) ^ (8283/2048 : ℝ) ≤ (37696758873894169/100000000000000000000 : ℝ) := by
    have hpowers : (14239/100000 : ℝ)^8283 ≤ (37696758873894169/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14239 : ℕ)^8283*100000000000000000000^2048 ≤ 37696758873894169^2048*100000^8283 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14239 100000 37696758873894169 100000000000000000000 8283 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14239/100000 : ℝ)) (X := (37696758873894169/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8283 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006821528558684023/25000000000000000000 : ℝ) ≤ (10000674589205861/10000000000000000 : ℝ) ^ (8283/2048 : ℝ) := by
    have hpowers : (25006821528558684023/25000000000000000000 : ℝ)^2048 ≤ (10000674589205861/10000000000000000 : ℝ)^8283 := by
      have hnat : (25006821528558684023 : ℕ)^2048*10000000000000000^8283 ≤ 10000674589205861^8283*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006821528558684023 25000000000000000000 10000674589205861 10000000000000000 2048 8283 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000674589205861/10000000000000000 : ℝ)) (X := (25006821528558684023/25000000000000000000 : ℝ)) (by norm_num) 8283 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20010267963198252443/20000000000000000000 : ℝ) ≤ (2000253829849923/2000000000000000 : ℝ) ^ (8283/2048 : ℝ) := by
    have hpowers : (20010267963198252443/20000000000000000000 : ℝ)^2048 ≤ (2000253829849923/2000000000000000 : ℝ)^8283 := by
      have hnat : (20010267963198252443 : ℕ)^2048*2000000000000000^8283 ≤ 2000253829849923^8283*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20010267963198252443 20000000000000000000 2000253829849923 2000000000000000 2048 8283 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000253829849923/2000000000000000 : ℝ)) (X := (20010267963198252443/20000000000000000000 : ℝ)) (by norm_num) 8283 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50037696758873894169/50000000000000000000 : ℝ) ≤ (10001863709293369/10000000000000000 : ℝ) ^ (8283/2048 : ℝ) := by
    have hpowers : (50037696758873894169/50000000000000000000 : ℝ)^2048 ≤ (10001863709293369/10000000000000000 : ℝ)^8283 := by
      have hnat : (50037696758873894169 : ℕ)^2048*10000000000000000^8283 ≤ 10001863709293369^8283*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50037696758873894169 50000000000000000000 10001863709293369 10000000000000000 2048 8283 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001863709293369/10000000000000000 : ℝ)) (X := (50037696758873894169/50000000000000000000 : ℝ)) (by norm_num) 8283 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6821528558684023/50000000000000000000 : ℝ) ≤ ((1976810305954887069/1977500000000000000 : ℝ)+2*(297280021877/158200000000000 : ℝ)*(443/4000 : ℝ))^(8283/2048 : ℝ) := by
    rw [show (1976810305954887069/1977500000000000000 : ℝ)+2*(297280021877/158200000000000 : ℝ)*(443/4000 : ℝ)=(10000674589205861/10000000000000000 : ℝ) by norm_num, show 1+2*(6821528558684023/50000000000000000000 : ℝ)=(25006821528558684023/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(37696758873894169/100000000000000000000 : ℝ)+(6821528558684023/50000000000000000000 : ℝ) ≤ ((1976810305954887069/1977500000000000000 : ℝ)+(297280021877/158200000000000 : ℝ)*((14239/100000 : ℝ)+(443/4000 : ℝ)))^(8283/2048 : ℝ) := by
    rw [show (1976810305954887069/1977500000000000000 : ℝ)+(297280021877/158200000000000 : ℝ)*((14239/100000 : ℝ)+(443/4000 : ℝ))=(2000253829849923/2000000000000000 : ℝ) by norm_num, show 1+(37696758873894169/100000000000000000000 : ℝ)+(6821528558684023/50000000000000000000 : ℝ)=(20010267963198252443/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(37696758873894169/100000000000000000000 : ℝ) ≤ ((1976810305954887069/1977500000000000000 : ℝ)+2*(297280021877/158200000000000 : ℝ)*(14239/100000 : ℝ))^(8283/2048 : ℝ) := by
    rw [show (1976810305954887069/1977500000000000000 : ℝ)+2*(297280021877/158200000000000 : ℝ)*(14239/100000 : ℝ)=(10001863709293369/10000000000000000 : ℝ) by norm_num, show 1+2*(37696758873894169/100000000000000000000 : ℝ)=(50037696758873894169/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1976810305954887069/1977500000000000000 : ℝ)*(X 1 0+X 2 0)+(297280021877/158200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8283/2048 : ℝ)) (lo := (443/4000 : ℝ)) (hi := (14239/100000 : ℝ)) (c := (1976810305954887069/1977500000000000000 : ℝ)) (alpha := (297280021877/158200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1976810305954887069/1977500000000000000 : ℝ)*(X 0 1+X 2 1)+(297280021877/158200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8283/2048 : ℝ)) (lo := (443/4000 : ℝ)) (hi := (14239/100000 : ℝ)) (c := (1976810305954887069/1977500000000000000 : ℝ)) (alpha := (297280021877/158200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1976810305954887069/1977500000000000000 : ℝ)*(X 0 2+X 1 2)+(297280021877/158200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8283/2048 : ℝ)) (lo := (443/4000 : ℝ)) (hi := (14239/100000 : ℝ)) (c := (1976810305954887069/1977500000000000000 : ℝ)) (alpha := (297280021877/158200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2191309851/10000000000 : ℝ)*X 0 0+(2698143057/5000000000 : ℝ)*X 0 1+(5262671503/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345507957/10000000000 : ℝ)*X 1 0+(-1129564801/5000000000 : ℝ)*X 1 1+(657833941/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345507963/10000000000 : ℝ)*X 2 0+(5262671517/10000000000 : ℝ)*X 2 1+(-282391201/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2185894923/5000000000 : ℝ)*X 0 0+(4242200799/10000000000 : ℝ)*X 0 1+(140792721/312500000 : ℝ)*X 0 2+(2185894923/5000000000 : ℝ)*X 1 0+(4242200799/10000000000 : ℝ)*X 1 1+(140792721/312500000 : ℝ)*X 1 2+(2185894923/5000000000 : ℝ)*X 2 0+(4242200799/10000000000 : ℝ)*X 2 1+(140792721/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-219131551/1000000000 : ℝ)*X 0 0+(2631509157/5000000000 : ℝ)*X 0 1+(5395937931/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1327946831/2500000000 : ℝ)*X 1 0+(-1062931557/5000000000 : ℝ)*X 1 1+(5395938023/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1327946837/2500000000 : ℝ)*X 2 0+(5395937961/10000000000 : ℝ)*X 2 1+(-425172633/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2185900407/5000000000 : ℝ)*X 0 0+(2252341949/5000000000 : ℝ)*X 0 1+(4242886497/10000000000 : ℝ)*X 0 2+(2185900407/5000000000 : ℝ)*X 1 0+(2252341949/5000000000 : ℝ)*X 1 1+(4242886497/10000000000 : ℝ)*X 1 2+(2185900407/5000000000 : ℝ)*X 2 0+(2252341949/5000000000 : ℝ)*X 2 1+(4242886497/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1091_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (53711347265341166365636137/7062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (377208947/25000000000000 : ℝ)*(base19) + (1394871339/100000000000000 : ℝ)*(base23) + (65410363/100000000000000 : ℝ)*(lower2) + (208201229/100000000000000 : ℝ)*(upper3) + (27209807/25000000000000 : ℝ)*(upper5) + (2821053265943187/50000000000000 : ℝ)*(major0) + (2821053265943187/50000000000000 : ℝ)*(major1) + (45136852255091/800000000000 : ℝ)*(major2) + (3742126715024193/50000000000000 : ℝ)*(sp0) + (374214566904233/5000000000000 : ℝ)*(sp1) + (7484291452049109/100000000000000 : ℝ)*(sp2) + (1899949061197869/50000000000000 : ℝ)*(sp3) + (19708436031/50000000000000 : ℝ)*(sp4) + (21840951671/100000000000000 : ℝ)*(sp7) + (3799919963347409/100000000000000 : ℝ)*(f.failure) + (29235518933283/390625000000 : ℝ)*(f.sum) + (19730029747647/15820000000000000000000000000 : ℝ)*base66 + (272322708720167653/98875000000000000000000000000000 : ℝ)*base67 + (28716342263972079/1582000000000000000000000000000 : ℝ)*base69 + (1606918526751082347/98875000000000000000000000000000 : ℝ)*base72 + (18144525048127/15820000000000000000000000000 : ℝ)*base74 + (13368389709227921/1582000000000000000000000000000 : ℝ)*base76 + (388354031822438597/98875000000000000000000000000000 : ℝ)*base78 + (579729072525438597/98875000000000000000000000000000 : ℝ)*base80 + (6937170258103/1977500000000000000000000000 : ℝ)*base82 + (86493/2000000000000000000000 : ℝ)*base90 + (86493/2000000000000000000000 : ℝ)*base92 + (20086493/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (249453218268194605099209501/49437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1138374927/100000000000000 : ℝ)*(base19) + (598458243/50000000000000 : ℝ)*(base23) + (529899/2500000000000 : ℝ)*(upper2) + (17748503/12500000000000 : ℝ)*(upper3) + (32089699/20000000000000 : ℝ)*(upper5) + (2835772937208157/50000000000000 : ℝ)*(major0) + (2835772937208157/50000000000000 : ℝ)*(major1) + (2835772937208157/50000000000000 : ℝ)*(major2) + (33867598463/100000000000000 : ℝ)*(sp1) + (31448932679/100000000000000 : ℝ)*(sp2) + (7523344422473637/100000000000000 : ℝ)*(sp4) + (940413677062531/12500000000000 : ℝ)*(sp5) + (940413972078059/12500000000000 : ℝ)*(sp6) + (76394943163293/2000000000000 : ℝ)*(sp7) + (76394943163293/2000000000000 : ℝ)*(f.failure) + (7523344422473637/100000000000000 : ℝ)*(f.sum) + (3156133616039/3955000000000000000000000000 : ℝ)*base65 + (121163334846984333/98875000000000000000000000000000 : ℝ)*base67 + (762895467123359333/98875000000000000000000000000000 : ℝ)*base69 + (1322558079900109333/98875000000000000000000000000000 : ℝ)*base71 + (1542155130721/3955000000000000000000000000 : ℝ)*base74 + (2005897808090515667/98875000000000000000000000000000 : ℝ)*base76 + (36525927823640667/98875000000000000000000000000000 : ℝ)*base78 + (514982695466109333/98875000000000000000000000000000 : ℝ)*base79 + (9856369878899/3955000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (245561/40000000000000000000 : ℝ)*base90 + (245561/40000000000000000000 : ℝ)*base92 + (245561/40000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1091_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29695923/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14239/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (443/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5619/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3517/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1091_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1091_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29695923/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (833/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8833/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5619/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3517/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1091_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1091_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1091_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8283/2048 : ℝ) ≤ p) (hpb : p ≤ (2071/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29695923/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (833/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8833/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5619/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3517/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1091_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
