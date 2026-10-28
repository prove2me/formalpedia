-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1043_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:49:27.883975+00:00
-- url     : https://prove2.me/submissions/71a75826-7881-4ccd-8db7-8e78c1eb7f7c

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
theorem support_rectangle_w1043_s9_0 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1107572533/5000000000 : ℝ)*x 0 + (539473609/1000000000 : ℝ)*x 1 + (5264041617/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1107572533/5000000000 : ℝ)^2059 ≤ (1345099498677/10000000000000 : ℝ)^1547 := by
    have hnat : (1107572533 : ℕ)^2059*10000000000000^1547 ≤ 1345099498677^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1107572533 5000000000 1345099498677 10000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539473609/1000000000 : ℝ)^2059 ≤ (5497588509299/12500000000000 : ℝ)^1547 := by
    have hnat : (539473609 : ℕ)^2059*12500000000000^1547 ≤ 5497588509299^1547*1000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539473609 1000000000 5497588509299 12500000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264041617/10000000000 : ℝ)^2059 ≤ (10642074230417/25000000000000 : ℝ)^1547 := by
    have hnat : (5264041617 : ℕ)^2059*25000000000000^1547 ≤ 10642074230417^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264041617 10000000000 10642074230417 25000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1107572533/5000000000 : ℝ), (539473609/1000000000 : ℝ), (5264041617/10000000000 : ℝ)] ![(1345099498677/10000000000000 : ℝ), (5497588509299/12500000000000 : ℝ), (10642074230417/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1107572533/5000000000 : ℝ)|^2059 ≤ (1345099498677/10000000000000 : ℝ)^1547
        have hw : |(-1107572533/5000000000 : ℝ)|=(1107572533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539473609/1000000000 : ℝ)|^2059 ≤ (5497588509299/12500000000000 : ℝ)^1547
        have hw : |(539473609/1000000000 : ℝ)|=(539473609/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264041617/10000000000 : ℝ)|^2059 ≤ (10642074230417/25000000000000 : ℝ)^1547
        have hw : |(5264041617/10000000000 : ℝ)|=(5264041617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s9_1 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5345022299/10000000000 : ℝ)*x 0 + (-142591343/625000000 : ℝ)*x 1 + (1052808307/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345022299/10000000000 : ℝ)^2059 ≤ (43442102584319/100000000000000 : ℝ)^1547 := by
    have hnat : (5345022299 : ℕ)^2059*100000000000000^1547 ≤ 43442102584319^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345022299 10000000000 43442102584319 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (142591343/625000000 : ℝ)^2059 ≤ (1398960135517/10000000000000 : ℝ)^1547 := by
    have hnat : (142591343 : ℕ)^2059*10000000000000^1547 ≤ 1398960135517^1547*625000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      142591343 625000000 1398960135517 10000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052808307/2000000000 : ℝ)^2059 ≤ (42568296039103/100000000000000 : ℝ)^1547 := by
    have hnat : (1052808307 : ℕ)^2059*100000000000000^1547 ≤ 42568296039103^1547*2000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052808307 2000000000 42568296039103 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345022299/10000000000 : ℝ), (-142591343/625000000 : ℝ), (1052808307/2000000000 : ℝ)] ![(43442102584319/100000000000000 : ℝ), (1398960135517/10000000000000 : ℝ), (42568296039103/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345022299/10000000000 : ℝ)|^2059 ≤ (43442102584319/100000000000000 : ℝ)^1547
        have hw : |(5345022299/10000000000 : ℝ)|=(5345022299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-142591343/625000000 : ℝ)|^2059 ≤ (1398960135517/10000000000000 : ℝ)^1547
        have hw : |(-142591343/625000000 : ℝ)|=(142591343/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052808307/2000000000 : ℝ)|^2059 ≤ (42568296039103/100000000000000 : ℝ)^1547
        have hw : |(1052808307/2000000000 : ℝ)|=(1052808307/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s9_2 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5345022267/10000000000 : ℝ)*x 0 + (5264041593/10000000000 : ℝ)*x 1 + (-1140730727/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345022267/10000000000 : ℝ)^2059 ≤ (43442102238159/100000000000000 : ℝ)^1547 := by
    have hnat : (5345022267 : ℕ)^2059*100000000000000^1547 ≤ 43442102238159^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345022267 10000000000 43442102238159 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264041593/10000000000 : ℝ)^2059 ≤ (42568296663357/100000000000000 : ℝ)^1547 := by
    have hnat : (5264041593 : ℕ)^2059*100000000000000^1547 ≤ 42568296663357^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264041593 10000000000 42568296663357 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1140730727/5000000000 : ℝ)^2059 ≤ (13989601077687/100000000000000 : ℝ)^1547 := by
    have hnat : (1140730727 : ℕ)^2059*100000000000000^1547 ≤ 13989601077687^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1140730727 5000000000 13989601077687 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345022267/10000000000 : ℝ), (5264041593/10000000000 : ℝ), (-1140730727/5000000000 : ℝ)] ![(43442102238159/100000000000000 : ℝ), (42568296663357/100000000000000 : ℝ), (13989601077687/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345022267/10000000000 : ℝ)|^2059 ≤ (43442102238159/100000000000000 : ℝ)^1547
        have hw : |(5345022267/10000000000 : ℝ)|=(5345022267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264041593/10000000000 : ℝ)|^2059 ≤ (42568296663357/100000000000000 : ℝ)^1547
        have hw : |(5264041593/10000000000 : ℝ)|=(5264041593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1140730727/5000000000 : ℝ)|^2059 ≤ (13989601077687/100000000000000 : ℝ)^1547
        have hw : |(-1140730727/5000000000 : ℝ)|=(1140730727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s9_3 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4378811373/10000000000 : ℝ)*x 0 + (2126607423/5000000000 : ℝ)*x 1 + (450818909/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4378811373/10000000000 : ℝ)^2059 ≤ (33316422919171/100000000000000 : ℝ)^1547 := by
    have hnat : (4378811373 : ℕ)^2059*100000000000000^1547 ≤ 33316422919171^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4378811373 10000000000 33316422919171 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2126607423/5000000000 : ℝ)^2059 ≤ (3205061995707/10000000000000 : ℝ)^1547 := by
    have hnat : (2126607423 : ℕ)^2059*10000000000000^1547 ≤ 3205061995707^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126607423 5000000000 3205061995707 10000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (450818909/1000000000 : ℝ)^2059 ≤ (4329119638821/12500000000000 : ℝ)^1547 := by
    have hnat : (450818909 : ℕ)^2059*12500000000000^1547 ≤ 4329119638821^1547*1000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450818909 1000000000 4329119638821 12500000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4378811373/10000000000 : ℝ), (2126607423/5000000000 : ℝ), (450818909/1000000000 : ℝ)] ![(33316422919171/100000000000000 : ℝ), (3205061995707/10000000000000 : ℝ), (4329119638821/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4378811373/10000000000 : ℝ)|^2059 ≤ (33316422919171/100000000000000 : ℝ)^1547
        have hw : |(4378811373/10000000000 : ℝ)|=(4378811373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2126607423/5000000000 : ℝ)|^2059 ≤ (3205061995707/10000000000000 : ℝ)^1547
        have hw : |(2126607423/5000000000 : ℝ)|=(2126607423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(450818909/1000000000 : ℝ)|^2059 ≤ (4329119638821/12500000000000 : ℝ)^1547
        have hw : |(450818909/1000000000 : ℝ)|=(450818909/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s9_4 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1107574531/5000000000 : ℝ)*x 0 + (5264369383/10000000000 : ℝ)*x 1 + (539440799/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1107574531/5000000000 : ℝ)^2059 ≤ (1681378410301/12500000000000 : ℝ)^1547 := by
    have hnat : (1107574531 : ℕ)^2059*12500000000000^1547 ≤ 1681378410301^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1107574531 5000000000 1681378410301 12500000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264369383/10000000000 : ℝ)^2059 ≤ (21285912350331/50000000000000 : ℝ)^1547 := by
    have hnat : (5264369383 : ℕ)^2059*50000000000000^1547 ≤ 21285912350331^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264369383 10000000000 21285912350331 50000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539440799/1000000000 : ℝ)^2059 ≤ (43977147993177/100000000000000 : ℝ)^1547 := by
    have hnat : (539440799 : ℕ)^2059*100000000000000^1547 ≤ 43977147993177^1547*1000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539440799 1000000000 43977147993177 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1107574531/5000000000 : ℝ), (5264369383/10000000000 : ℝ), (539440799/1000000000 : ℝ)] ![(1681378410301/12500000000000 : ℝ), (21285912350331/50000000000000 : ℝ), (43977147993177/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1107574531/5000000000 : ℝ)|^2059 ≤ (1681378410301/12500000000000 : ℝ)^1547
        have hw : |(-1107574531/5000000000 : ℝ)|=(1107574531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264369383/10000000000 : ℝ)|^2059 ≤ (21285912350331/50000000000000 : ℝ)^1547
        have hw : |(5264369383/10000000000 : ℝ)|=(5264369383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539440799/1000000000 : ℝ)|^2059 ≤ (43977147993177/100000000000000 : ℝ)^1547
        have hw : |(539440799/1000000000 : ℝ)|=(539440799/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s9_5 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (212486591/400000000 : ℝ)*x 0 + (-1075546583/5000000000 : ℝ)*x 1 + (2697204113/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212486591/400000000 : ℝ)^2059 ≤ (2692939251601/6250000000000 : ℝ)^1547 := by
    have hnat : (212486591 : ℕ)^2059*6250000000000^1547 ≤ 2692939251601^1547*400000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212486591 400000000 2692939251601 6250000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1075546583/5000000000 : ℝ)^2059 ≤ (2587164281353/20000000000000 : ℝ)^1547 := by
    have hnat : (1075546583 : ℕ)^2059*20000000000000^1547 ≤ 2587164281353^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075546583 5000000000 2587164281353 20000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697204113/5000000000 : ℝ)^2059 ≤ (10994287638473/25000000000000 : ℝ)^1547 := by
    have hnat : (2697204113 : ℕ)^2059*25000000000000^1547 ≤ 10994287638473^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697204113 5000000000 10994287638473 25000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212486591/400000000 : ℝ), (-1075546583/5000000000 : ℝ), (2697204113/5000000000 : ℝ)] ![(2692939251601/6250000000000 : ℝ), (2587164281353/20000000000000 : ℝ), (10994287638473/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212486591/400000000 : ℝ)|^2059 ≤ (2692939251601/6250000000000 : ℝ)^1547
        have hw : |(212486591/400000000 : ℝ)|=(212486591/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1075546583/5000000000 : ℝ)|^2059 ≤ (2587164281353/20000000000000 : ℝ)^1547
        have hw : |(-1075546583/5000000000 : ℝ)|=(1075546583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697204113/5000000000 : ℝ)|^2059 ≤ (10994287638473/25000000000000 : ℝ)^1547
        have hw : |(2697204113/5000000000 : ℝ)|=(2697204113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s9_6 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312163129/10000000000 : ℝ)*x 0 + (5394408439/10000000000 : ℝ)*x 1 + (-1075547549/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312163129/10000000000 : ℝ)^2059 ≤ (21543505128147/50000000000000 : ℝ)^1547 := by
    have hnat : (5312163129 : ℕ)^2059*50000000000000^1547 ≤ 21543505128147^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312163129 10000000000 21543505128147 50000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394408439/10000000000 : ℝ)^2059 ≤ (21988576432523/50000000000000 : ℝ)^1547 := by
    have hnat : (5394408439 : ℕ)^2059*50000000000000^1547 ≤ 21988576432523^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394408439 10000000000 21988576432523 50000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1075547549/5000000000 : ℝ)^2059 ≤ (101061225549/781250000000 : ℝ)^1547 := by
    have hnat : (1075547549 : ℕ)^2059*781250000000^1547 ≤ 101061225549^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075547549 5000000000 101061225549 781250000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312163129/10000000000 : ℝ), (5394408439/10000000000 : ℝ), (-1075547549/5000000000 : ℝ)] ![(21543505128147/50000000000000 : ℝ), (21988576432523/50000000000000 : ℝ), (101061225549/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312163129/10000000000 : ℝ)|^2059 ≤ (21543505128147/50000000000000 : ℝ)^1547
        have hw : |(5312163129/10000000000 : ℝ)|=(5312163129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394408439/10000000000 : ℝ)|^2059 ≤ (21988576432523/50000000000000 : ℝ)^1547
        have hw : |(5394408439/10000000000 : ℝ)|=(5394408439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1075547549/5000000000 : ℝ)|^2059 ≤ (101061225549/781250000000 : ℝ)^1547
        have hw : |(-1075547549/5000000000 : ℝ)|=(1075547549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s9_7 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4378820101/10000000000 : ℝ)*x 0 + (2253775347/5000000000 : ℝ)*x 1 + (2126928409/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4378820101/10000000000 : ℝ)^2059 ≤ (16658255652541/50000000000000 : ℝ)^1547 := by
    have hnat : (4378820101 : ℕ)^2059*50000000000000^1547 ≤ 16658255652541^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4378820101 10000000000 16658255652541 50000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2253775347/5000000000 : ℝ)^2059 ≤ (4328303726527/12500000000000 : ℝ)^1547 := by
    have hnat : (2253775347 : ℕ)^2059*12500000000000^1547 ≤ 4328303726527^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253775347 5000000000 4328303726527 12500000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2126928409/5000000000 : ℝ)^2059 ≤ (16028529431497/50000000000000 : ℝ)^1547 := by
    have hnat : (2126928409 : ℕ)^2059*50000000000000^1547 ≤ 16028529431497^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126928409 5000000000 16028529431497 50000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4378820101/10000000000 : ℝ), (2253775347/5000000000 : ℝ), (2126928409/5000000000 : ℝ)] ![(16658255652541/50000000000000 : ℝ), (4328303726527/12500000000000 : ℝ), (16028529431497/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4378820101/10000000000 : ℝ)|^2059 ≤ (16658255652541/50000000000000 : ℝ)^1547
        have hw : |(4378820101/10000000000 : ℝ)|=(4378820101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2253775347/5000000000 : ℝ)|^2059 ≤ (4328303726527/12500000000000 : ℝ)^1547
        have hw : |(2253775347/5000000000 : ℝ)|=(2253775347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2126928409/5000000000 : ℝ)|^2059 ≤ (16028529431497/50000000000000 : ℝ)^1547
        have hw : |(2126928409/5000000000 : ℝ)|=(2126928409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1043_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147545813/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13989/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11219/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (561/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3497/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13989/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11219/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13989/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11219/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13989/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11219/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13989/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11219/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13989/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11219/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13989/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11219/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11219/100000 : ℝ) ^ (8235/2048 : ℝ) ≤ (3026211908775883/20000000000000000000 : ℝ) := by
    have hpowers : (11219/100000 : ℝ)^8235 ≤ (3026211908775883/20000000000000000000 : ℝ)^2048 := by
      have hnat : (11219 : ℕ)^8235*20000000000000000000^2048 ≤ 3026211908775883^2048*100000^8235 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11219 100000 3026211908775883 20000000000000000000 8235 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11219/100000 : ℝ)) (X := (3026211908775883/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8235 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (13989/100000 : ℝ) ^ (8235/2048 : ℝ) ≤ (36746124110812039/100000000000000000000 : ℝ) := by
    have hpowers : (13989/100000 : ℝ)^8235 ≤ (36746124110812039/100000000000000000000 : ℝ)^2048 := by
      have hnat : (13989 : ℕ)^8235*100000000000000000000^2048 ≤ 36746124110812039^2048*100000^8235 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13989 100000 36746124110812039 100000000000000000000 8235 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13989/100000 : ℝ)) (X := (36746124110812039/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8235 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10003026211908775883/10000000000000000000 : ℝ) ≤ (5000376258503839/5000000000000000 : ℝ) ^ (8235/2048 : ℝ) := by
    have hpowers : (10003026211908775883/10000000000000000000 : ℝ)^2048 ≤ (5000376258503839/5000000000000000 : ℝ)^8235 := by
      have hnat : (10003026211908775883 : ℕ)^2048*5000000000000000^8235 ≤ 5000376258503839^8235*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10003026211908775883 10000000000000000000 5000376258503839 5000000000000000 2048 8235 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000376258503839/5000000000000000 : ℝ)) (X := (10003026211908775883/10000000000000000000 : ℝ)) (by norm_num) 8235 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50025938591827345727/50000000000000000000 : ℝ) ≤ (10001289906177027/10000000000000000 : ℝ) ^ (8235/2048 : ℝ) := by
    have hpowers : (50025938591827345727/50000000000000000000 : ℝ)^2048 ≤ (10001289906177027/10000000000000000 : ℝ)^8235 := by
      have hnat : (50025938591827345727 : ℕ)^2048*10000000000000000^8235 ≤ 10001289906177027^8235*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025938591827345727 50000000000000000000 10001289906177027 10000000000000000 2048 8235 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001289906177027/10000000000000000 : ℝ)) (X := (50025938591827345727/50000000000000000000 : ℝ)) (by norm_num) 8235 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036746124110812039/50000000000000000000 : ℝ) ≤ (1250228411918297/1250000000000000 : ℝ) ^ (8235/2048 : ℝ) := by
    have hpowers : (50036746124110812039/50000000000000000000 : ℝ)^2048 ≤ (1250228411918297/1250000000000000 : ℝ)^8235 := by
      have hnat : (50036746124110812039 : ℕ)^2048*1250000000000000^8235 ≤ 1250228411918297^8235*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036746124110812039 50000000000000000000 1250228411918297 1250000000000000 2048 8235 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250228411918297/1250000000000000 : ℝ)) (X := (50036746124110812039/50000000000000000000 : ℝ)) (by norm_num) 8235 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3026211908775883/20000000000000000000 : ℝ) ≤ ((13845013266964707599/13850000000000000000 : ℝ)+2*(537389169349/277000000000000 : ℝ)*(11219/100000 : ℝ))^(8235/2048 : ℝ) := by
    rw [show (13845013266964707599/13850000000000000000 : ℝ)+2*(537389169349/277000000000000 : ℝ)*(11219/100000 : ℝ)=(5000376258503839/5000000000000000 : ℝ) by norm_num, show 1+2*(3026211908775883/20000000000000000000 : ℝ)=(10003026211908775883/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36746124110812039/100000000000000000000 : ℝ)+(3026211908775883/20000000000000000000 : ℝ) ≤ ((13845013266964707599/13850000000000000000 : ℝ)+(537389169349/277000000000000 : ℝ)*((13989/100000 : ℝ)+(11219/100000 : ℝ)))^(8235/2048 : ℝ) := by
    rw [show (13845013266964707599/13850000000000000000 : ℝ)+(537389169349/277000000000000 : ℝ)*((13989/100000 : ℝ)+(11219/100000 : ℝ))=(10001289906177027/10000000000000000 : ℝ) by norm_num, show 1+(36746124110812039/100000000000000000000 : ℝ)+(3026211908775883/20000000000000000000 : ℝ)=(50025938591827345727/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36746124110812039/100000000000000000000 : ℝ) ≤ ((13845013266964707599/13850000000000000000 : ℝ)+2*(537389169349/277000000000000 : ℝ)*(13989/100000 : ℝ))^(8235/2048 : ℝ) := by
    rw [show (13845013266964707599/13850000000000000000 : ℝ)+2*(537389169349/277000000000000 : ℝ)*(13989/100000 : ℝ)=(1250228411918297/1250000000000000 : ℝ) by norm_num, show 1+2*(36746124110812039/100000000000000000000 : ℝ)=(50036746124110812039/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13845013266964707599/13850000000000000000 : ℝ)*(X 1 0+X 2 0)+(537389169349/277000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8235/2048 : ℝ)) (lo := (11219/100000 : ℝ)) (hi := (13989/100000 : ℝ)) (c := (13845013266964707599/13850000000000000000 : ℝ)) (alpha := (537389169349/277000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13845013266964707599/13850000000000000000 : ℝ)*(X 0 1+X 2 1)+(537389169349/277000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8235/2048 : ℝ)) (lo := (11219/100000 : ℝ)) (hi := (13989/100000 : ℝ)) (c := (13845013266964707599/13850000000000000000 : ℝ)) (alpha := (537389169349/277000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13845013266964707599/13850000000000000000 : ℝ)*(X 0 2+X 1 2)+(537389169349/277000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8235/2048 : ℝ)) (lo := (11219/100000 : ℝ)) (hi := (13989/100000 : ℝ)) (c := (13845013266964707599/13850000000000000000 : ℝ)) (alpha := (537389169349/277000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1107572533/5000000000 : ℝ)*X 0 0+(539473609/1000000000 : ℝ)*X 0 1+(5264041617/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s9_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345022299/10000000000 : ℝ)*X 1 0+(-142591343/625000000 : ℝ)*X 1 1+(1052808307/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s9_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345022267/10000000000 : ℝ)*X 2 0+(5264041593/10000000000 : ℝ)*X 2 1+(-1140730727/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s9_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4378811373/10000000000 : ℝ)*X 0 0+(2126607423/5000000000 : ℝ)*X 0 1+(450818909/1000000000 : ℝ)*X 0 2+(4378811373/10000000000 : ℝ)*X 1 0+(2126607423/5000000000 : ℝ)*X 1 1+(450818909/1000000000 : ℝ)*X 1 2+(4378811373/10000000000 : ℝ)*X 2 0+(2126607423/5000000000 : ℝ)*X 2 1+(450818909/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s9_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1107574531/5000000000 : ℝ)*X 0 0+(5264369383/10000000000 : ℝ)*X 0 1+(539440799/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s9_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((212486591/400000000 : ℝ)*X 1 0+(-1075546583/5000000000 : ℝ)*X 1 1+(2697204113/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s9_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312163129/10000000000 : ℝ)*X 2 0+(5394408439/10000000000 : ℝ)*X 2 1+(-1075547549/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s9_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4378820101/10000000000 : ℝ)*X 0 0+(2253775347/5000000000 : ℝ)*X 0 1+(2126928409/5000000000 : ℝ)*X 0 2+(4378820101/10000000000 : ℝ)*X 1 0+(2253775347/5000000000 : ℝ)*X 1 1+(2126928409/5000000000 : ℝ)*X 1 2+(4378820101/10000000000 : ℝ)*X 2 0+(2253775347/5000000000 : ℝ)*X 2 1+(2126928409/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s9_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3073708303332481521534751503/692500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (157222923/25000000000000 : ℝ)*(base19) + (226681469/50000000000000 : ℝ)*(base23) + (69335843/100000000000000 : ℝ)*(lower2) + (35634277/50000000000000 : ℝ)*(upper3) + (151563/800000000000 : ℝ)*(upper5) + (57867208130681/1000000000000 : ℝ)*(major0) + (57867208130681/1000000000000 : ℝ)*(major1) + (5786720813068101/100000000000000 : ℝ)*(major2) + (1912861628624961/25000000000000 : ℝ)*(sp0) + (3825729226248607/50000000000000 : ℝ)*(sp1) + (478216164251623/6250000000000 : ℝ)*(sp2) + (980493201012583/25000000000000 : ℝ)*(sp3) + (6283444531/50000000000000 : ℝ)*(sp4) + (959274469/10000000000000 : ℝ)*(sp7) + (3921982396795021/100000000000000 : ℝ)*(f.failure) + (3825729540694453/50000000000000 : ℝ)*(f.sum) + (277705757887451/27700000000000000000000000000 : ℝ)*base66 + (149579914197569419/13850000000000000000000000000000 : ℝ)*base67 + (3191882017104199499/1385000000000000000000000000000000 : ℝ)*base69 + (65217133027330581/13850000000000000000000000000000 : ℝ)*base72 + (80546557106851/27700000000000000000000000000 : ℝ)*base74 + (2201094065734199499/1385000000000000000000000000000000 : ℝ)*base75 + (39847462021505081/13850000000000000000000000000000 : ℝ)*base78 + (55691752408594919/13850000000000000000000000000000 : ℝ)*base79 + (782193404009/138500000000000000000000000 : ℝ)*base82 + (32202927/10000000000000000000000 : ℝ)*base90 + (32202927/10000000000000000000000 : ℝ)*base92 + (132202927/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3224263788037715215285048503/346250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (32571043/10000000000000 : ℝ)*(base19) + (24942073/100000000000000 : ℝ)*(lower1) + (109095683/25000000000000 : ℝ)*(upper2) + (174259021/25000000000000 : ℝ)*(lower3) + (909306707/100000000000000 : ℝ)*(lower4) + (35670853/10000000000000 : ℝ)*(lower5) + (2907923156982899/50000000000000 : ℝ)*(major0) + (2907923156982899/50000000000000 : ℝ)*(major1) + (2907923156982899/50000000000000 : ℝ)*(major2) + (76981798259/100000000000000 : ℝ)*(sp1) + (7689969949602721/100000000000000 : ℝ)*(sp4) + (7689892642094033/100000000000000 : ℝ)*(sp5) + (7689969949602721/100000000000000 : ℝ)*(sp6) + (1970861183965213/50000000000000 : ℝ)*(sp7) + (1970861183965213/50000000000000 : ℝ)*(f.failure) + (7689969949602721/100000000000000 : ℝ)*(f.sum) + (25591672155949/6925000000000000000000000000 : ℝ)*base66 + (987753554718399501/692500000000000000000000000000000 : ℝ)*base67 + (2971600286449100499/692500000000000000000000000000000 : ℝ)*base70 + (8223155189369100499/692500000000000000000000000000000 : ℝ)*base72 + (47758672627801/6925000000000000000000000000 : ℝ)*base73 + (934610617198399501/692500000000000000000000000000000 : ℝ)*base75 + (33762284417021600499/692500000000000000000000000000000 : ℝ)*base78 + (2761352373161600499/692500000000000000000000000000000 : ℝ)*base80 + (12103267003501/6925000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (15803169/5000000000000000000000 : ℝ)*base89 + (15803169/5000000000000000000000 : ℝ)*base91 + (15803169/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1043_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147545813/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13989/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11219/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (561/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3497/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1043_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1043_box_0 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2084882081/10000000000 : ℝ)*x 0 + (672209647/1250000000 : ℝ)*x 1 + (5377677079/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2084882081/10000000000 : ℝ)^2059 ≤ (6204296798689/50000000000000 : ℝ)^1547 := by
    have hnat : (2084882081 : ℕ)^2059*50000000000000^1547 ≤ 6204296798689^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084882081 10000000000 6204296798689 50000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (672209647/1250000000 : ℝ)^2059 ≤ (43795703720183/100000000000000 : ℝ)^1547 := by
    have hnat : (672209647 : ℕ)^2059*100000000000000^1547 ≤ 43795703720183^1547*1250000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672209647 1250000000 43795703720183 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5377677079/10000000000 : ℝ)^2059 ≤ (43795702668767/100000000000000 : ℝ)^1547 := by
    have hnat : (5377677079 : ℕ)^2059*100000000000000^1547 ≤ 43795702668767^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377677079 10000000000 43795702668767 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2084882081/10000000000 : ℝ), (672209647/1250000000 : ℝ), (5377677079/10000000000 : ℝ)] ![(6204296798689/50000000000000 : ℝ), (43795703720183/100000000000000 : ℝ), (43795702668767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2084882081/10000000000 : ℝ)|^2059 ≤ (6204296798689/50000000000000 : ℝ)^1547
        have hw : |(-2084882081/10000000000 : ℝ)|=(2084882081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(672209647/1250000000 : ℝ)|^2059 ≤ (43795703720183/100000000000000 : ℝ)^1547
        have hw : |(672209647/1250000000 : ℝ)|=(672209647/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5377677079/10000000000 : ℝ)|^2059 ≤ (43795702668767/100000000000000 : ℝ)^1547
        have hw : |(5377677079/10000000000 : ℝ)|=(5377677079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_box_1 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2647468421/5000000000 : ℝ)*x 0 + (-1098413603/5000000000 : ℝ)*x 1 + (1344419261/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647468421/5000000000 : ℝ)^2059 ≤ (1340660765611/3125000000000 : ℝ)^1547 := by
    have hnat : (2647468421 : ℕ)^2059*3125000000000^1547 ≤ 1340660765611^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647468421 5000000000 1340660765611 3125000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1098413603/5000000000 : ℝ)^2059 ≤ (6651576600939/50000000000000 : ℝ)^1547 := by
    have hnat : (1098413603 : ℕ)^2059*50000000000000^1547 ≤ 6651576600939^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098413603 5000000000 6651576600939 50000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1344419261/2500000000 : ℝ)^2059 ≤ (4379570228939/10000000000000 : ℝ)^1547 := by
    have hnat : (1344419261 : ℕ)^2059*10000000000000^1547 ≤ 4379570228939^1547*2500000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344419261 2500000000 4379570228939 10000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647468421/5000000000 : ℝ), (-1098413603/5000000000 : ℝ), (1344419261/2500000000 : ℝ)] ![(1340660765611/3125000000000 : ℝ), (6651576600939/50000000000000 : ℝ), (4379570228939/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647468421/5000000000 : ℝ)|^2059 ≤ (1340660765611/3125000000000 : ℝ)^1547
        have hw : |(2647468421/5000000000 : ℝ)|=(2647468421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1098413603/5000000000 : ℝ)|^2059 ≤ (6651576600939/50000000000000 : ℝ)^1547
        have hw : |(-1098413603/5000000000 : ℝ)|=(1098413603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1344419261/2500000000 : ℝ)|^2059 ≤ (4379570228939/10000000000000 : ℝ)^1547
        have hw : |(1344419261/2500000000 : ℝ)|=(1344419261/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_box_2 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (264746841/500000000 : ℝ)*x 0 + (1344419267/2500000000 : ℝ)*x 1 + (-2196827203/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (264746841/500000000 : ℝ)^2059 ≤ (42901144262307/100000000000000 : ℝ)^1547 := by
    have hnat : (264746841 : ℕ)^2059*100000000000000^1547 ≤ 42901144262307^1547*500000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264746841 500000000 42901144262307 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1344419267/2500000000 : ℝ)^2059 ≤ (21897851274767/50000000000000 : ℝ)^1547 := by
    have hnat : (1344419267 : ℕ)^2059*50000000000000^1547 ≤ 21897851274767^1547*2500000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344419267 2500000000 21897851274767 50000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2196827203/10000000000 : ℝ)^2059 ≤ (6651576588849/50000000000000 : ℝ)^1547 := by
    have hnat : (2196827203 : ℕ)^2059*50000000000000^1547 ≤ 6651576588849^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2196827203 10000000000 6651576588849 50000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(264746841/500000000 : ℝ), (1344419267/2500000000 : ℝ), (-2196827203/10000000000 : ℝ)] ![(42901144262307/100000000000000 : ℝ), (21897851274767/50000000000000 : ℝ), (6651576588849/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(264746841/500000000 : ℝ)|^2059 ≤ (42901144262307/100000000000000 : ℝ)^1547
        have hw : |(264746841/500000000 : ℝ)|=(264746841/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1344419267/2500000000 : ℝ)|^2059 ≤ (21897851274767/50000000000000 : ℝ)^1547
        have hw : |(1344419267/2500000000 : ℝ)|=(1344419267/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2196827203/10000000000 : ℝ)|^2059 ≤ (6651576588849/50000000000000 : ℝ)^1547
        have hw : |(-2196827203/10000000000 : ℝ)|=(2196827203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_box_3 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2243732793/5000000000 : ℝ)*x 0 + (1081666063/2500000000 : ℝ)*x 1 + (4326664133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2243732793/5000000000 : ℝ)^2059 ≤ (17210612715517/50000000000000 : ℝ)^1547 := by
    have hnat : (2243732793 : ℕ)^2059*50000000000000^1547 ≤ 17210612715517^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2243732793 5000000000 17210612715517 50000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081666063/2500000000 : ℝ)^2059 ≤ (16394693937107/50000000000000 : ℝ)^1547 := by
    have hnat : (1081666063 : ℕ)^2059*50000000000000^1547 ≤ 16394693937107^1547*2500000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081666063 2500000000 16394693937107 50000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4326664133/10000000000 : ℝ)^2059 ≤ (6557877334781/20000000000000 : ℝ)^1547 := by
    have hnat : (4326664133 : ℕ)^2059*20000000000000^1547 ≤ 6557877334781^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4326664133 10000000000 6557877334781 20000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2243732793/5000000000 : ℝ), (1081666063/2500000000 : ℝ), (4326664133/10000000000 : ℝ)] ![(17210612715517/50000000000000 : ℝ), (16394693937107/50000000000000 : ℝ), (6557877334781/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2243732793/5000000000 : ℝ)|^2059 ≤ (17210612715517/50000000000000 : ℝ)^1547
        have hw : |(2243732793/5000000000 : ℝ)|=(2243732793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1081666063/2500000000 : ℝ)|^2059 ≤ (16394693937107/50000000000000 : ℝ)^1547
        have hw : |(1081666063/2500000000 : ℝ)|=(1081666063/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4326664133/10000000000 : ℝ)|^2059 ≤ (6557877334781/20000000000000 : ℝ)^1547
        have hw : |(4326664133/10000000000 : ℝ)|=(4326664133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_box_4 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2346795979/10000000000 : ℝ)*x 0 + (1319934909/2500000000 : ℝ)*x 1 + (5279739537/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2346795979/10000000000 : ℝ)^2059 ≤ (581013010997/4000000000000 : ℝ)^1547 := by
    have hnat : (2346795979 : ℕ)^2059*4000000000000^1547 ≤ 581013010997^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2346795979 10000000000 581013010997 4000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1319934909/2500000000 : ℝ)^2059 ≤ (5342167236047/12500000000000 : ℝ)^1547 := by
    have hnat : (1319934909 : ℕ)^2059*12500000000000^1547 ≤ 5342167236047^1547*2500000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319934909 2500000000 5342167236047 12500000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5279739537/10000000000 : ℝ)^2059 ≤ (42737336821789/100000000000000 : ℝ)^1547 := by
    have hnat : (5279739537 : ℕ)^2059*100000000000000^1547 ≤ 42737336821789^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279739537 10000000000 42737336821789 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2346795979/10000000000 : ℝ), (1319934909/2500000000 : ℝ), (5279739537/10000000000 : ℝ)] ![(581013010997/4000000000000 : ℝ), (5342167236047/12500000000000 : ℝ), (42737336821789/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2346795979/10000000000 : ℝ)|^2059 ≤ (581013010997/4000000000000 : ℝ)^1547
        have hw : |(-2346795979/10000000000 : ℝ)|=(2346795979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1319934909/2500000000 : ℝ)|^2059 ≤ (5342167236047/12500000000000 : ℝ)^1547
        have hw : |(1319934909/2500000000 : ℝ)|=(1319934909/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5279739537/10000000000 : ℝ)|^2059 ≤ (42737336821789/100000000000000 : ℝ)^1547
        have hw : |(5279739537/10000000000 : ℝ)|=(5279739537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_box_5 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2682142773/5000000000 : ℝ)*x 0 + (-1117521931/5000000000 : ℝ)*x 1 + (5279739591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2682142773/5000000000 : ℝ)^2059 ≤ (43650607148039/100000000000000 : ℝ)^1547 := by
    have hnat : (2682142773 : ℕ)^2059*100000000000000^1547 ≤ 43650607148039^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2682142773 5000000000 43650607148039 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1117521931/5000000000 : ℝ)^2059 ≤ (13612055432801/100000000000000 : ℝ)^1547 := by
    have hnat : (1117521931 : ℕ)^2059*100000000000000^1547 ≤ 13612055432801^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1117521931 5000000000 13612055432801 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5279739591/10000000000 : ℝ)^2059 ≤ (10684334350891/25000000000000 : ℝ)^1547 := by
    have hnat : (5279739591 : ℕ)^2059*25000000000000^1547 ≤ 10684334350891^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279739591 10000000000 10684334350891 25000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2682142773/5000000000 : ℝ), (-1117521931/5000000000 : ℝ), (5279739591/10000000000 : ℝ)] ![(43650607148039/100000000000000 : ℝ), (13612055432801/100000000000000 : ℝ), (10684334350891/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2682142773/5000000000 : ℝ)|^2059 ≤ (43650607148039/100000000000000 : ℝ)^1547
        have hw : |(2682142773/5000000000 : ℝ)|=(2682142773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1117521931/5000000000 : ℝ)|^2059 ≤ (13612055432801/100000000000000 : ℝ)^1547
        have hw : |(-1117521931/5000000000 : ℝ)|=(1117521931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5279739591/10000000000 : ℝ)|^2059 ≤ (10684334350891/25000000000000 : ℝ)^1547
        have hw : |(5279739591/10000000000 : ℝ)|=(5279739591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_box_6 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2682142929/5000000000 : ℝ)*x 0 + (1319934863/2500000000 : ℝ)*x 1 + (-2235043631/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2682142929/5000000000 : ℝ)^2059 ≤ (10912652631781/25000000000000 : ℝ)^1547 := by
    have hnat : (2682142929 : ℕ)^2059*25000000000000^1547 ≤ 10912652631781^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2682142929 5000000000 10912652631781 25000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1319934863/2500000000 : ℝ)^2059 ≤ (42737335906033/100000000000000 : ℝ)^1547 := by
    have hnat : (1319934863 : ℕ)^2059*100000000000000^1547 ≤ 42737335906033^1547*2500000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319934863 2500000000 42737335906033 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2235043631/10000000000 : ℝ)^2059 ≤ (13612053560327/100000000000000 : ℝ)^1547 := by
    have hnat : (2235043631 : ℕ)^2059*100000000000000^1547 ≤ 13612053560327^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2235043631 10000000000 13612053560327 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2682142929/5000000000 : ℝ), (1319934863/2500000000 : ℝ), (-2235043631/10000000000 : ℝ)] ![(10912652631781/25000000000000 : ℝ), (42737335906033/100000000000000 : ℝ), (13612053560327/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2682142929/5000000000 : ℝ)|^2059 ≤ (10912652631781/25000000000000 : ℝ)^1547
        have hw : |(2682142929/5000000000 : ℝ)|=(2682142929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1319934863/2500000000 : ℝ)|^2059 ≤ (42737335906033/100000000000000 : ℝ)^1547
        have hw : |(1319934863/2500000000 : ℝ)|=(1319934863/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2235043631/10000000000 : ℝ)|^2059 ≤ (13612053560327/100000000000000 : ℝ)^1547
        have hw : |(-2235043631/10000000000 : ℝ)|=(2235043631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_box_7 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4269839233/10000000000 : ℝ)*x 0 + (4435455581/10000000000 : ℝ)*x 1 + (4435455847/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4269839233/10000000000 : ℝ)^2059 ≤ (8054366062743/25000000000000 : ℝ)^1547 := by
    have hnat : (4269839233 : ℕ)^2059*25000000000000^1547 ≤ 8054366062743^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4269839233 10000000000 8054366062743 25000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4435455581/10000000000 : ℝ)^2059 ≤ (2118204156961/6250000000000 : ℝ)^1547 := by
    have hnat : (4435455581 : ℕ)^2059*6250000000000^1547 ≤ 2118204156961^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4435455581 10000000000 2118204156961 6250000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4435455847/10000000000 : ℝ)^2059 ≤ (33891269216563/100000000000000 : ℝ)^1547 := by
    have hnat : (4435455847 : ℕ)^2059*100000000000000^1547 ≤ 33891269216563^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4435455847 10000000000 33891269216563 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4269839233/10000000000 : ℝ), (4435455581/10000000000 : ℝ), (4435455847/10000000000 : ℝ)] ![(8054366062743/25000000000000 : ℝ), (2118204156961/6250000000000 : ℝ), (33891269216563/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4269839233/10000000000 : ℝ)|^2059 ≤ (8054366062743/25000000000000 : ℝ)^1547
        have hw : |(4269839233/10000000000 : ℝ)|=(4269839233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4435455581/10000000000 : ℝ)|^2059 ≤ (2118204156961/6250000000000 : ℝ)^1547
        have hw : |(4435455581/10000000000 : ℝ)|=(4435455581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4435455847/10000000000 : ℝ)|^2059 ≤ (33891269216563/100000000000000 : ℝ)^1547
        have hw : |(4435455847/10000000000 : ℝ)|=(4435455847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_box_8 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2292148461/10000000000 : ℝ)*x 0 + (651666101/1250000000 : ℝ)*x 1 + (1346818653/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2292148461/10000000000 : ℝ)^2059 ≤ (1759611032871/12500000000000 : ℝ)^1547 := by
    have hnat : (2292148461 : ℕ)^2059*12500000000000^1547 ≤ 1759611032871^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2292148461 10000000000 1759611032871 12500000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (651666101/1250000000 : ℝ)^2059 ≤ (42023347429729/100000000000000 : ℝ)^1547 := by
    have hnat : (651666101 : ℕ)^2059*100000000000000^1547 ≤ 42023347429729^1547*1250000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      651666101 1250000000 42023347429729 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1346818653/2500000000 : ℝ)^2059 ≤ (175599057189/400000000000 : ℝ)^1547 := by
    have hnat : (1346818653 : ℕ)^2059*400000000000^1547 ≤ 175599057189^1547*2500000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346818653 2500000000 175599057189 400000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2292148461/10000000000 : ℝ), (651666101/1250000000 : ℝ), (1346818653/2500000000 : ℝ)] ![(1759611032871/12500000000000 : ℝ), (42023347429729/100000000000000 : ℝ), (175599057189/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2292148461/10000000000 : ℝ)|^2059 ≤ (1759611032871/12500000000000 : ℝ)^1547
        have hw : |(-2292148461/10000000000 : ℝ)|=(2292148461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(651666101/1250000000 : ℝ)|^2059 ≤ (42023347429729/100000000000000 : ℝ)^1547
        have hw : |(651666101/1250000000 : ℝ)|=(651666101/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1346818653/2500000000 : ℝ)|^2059 ≤ (175599057189/400000000000 : ℝ)^1547
        have hw : |(1346818653/2500000000 : ℝ)|=(1346818653/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_box_9 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5288136853/10000000000 : ℝ)*x 0 + (-274126427/1250000000 : ℝ)*x 1 + (2693637223/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288136853/10000000000 : ℝ)^2059 ≤ (21413914988959/50000000000000 : ℝ)^1547 := by
    have hnat : (5288136853 : ℕ)^2059*50000000000000^1547 ≤ 21413914988959^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288136853 10000000000 21413914988959 50000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (274126427/1250000000 : ℝ)^2059 ≤ (1659050938531/12500000000000 : ℝ)^1547 := by
    have hnat : (274126427 : ℕ)^2059*12500000000000^1547 ≤ 1659050938531^1547*1250000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274126427 1250000000 1659050938531 12500000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2693637223/5000000000 : ℝ)^2059 ≤ (21949881248429/50000000000000 : ℝ)^1547 := by
    have hnat : (2693637223 : ℕ)^2059*50000000000000^1547 ≤ 21949881248429^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693637223 5000000000 21949881248429 50000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288136853/10000000000 : ℝ), (-274126427/1250000000 : ℝ), (2693637223/5000000000 : ℝ)] ![(21413914988959/50000000000000 : ℝ), (1659050938531/12500000000000 : ℝ), (21949881248429/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288136853/10000000000 : ℝ)|^2059 ≤ (21413914988959/50000000000000 : ℝ)^1547
        have hw : |(5288136853/10000000000 : ℝ)|=(5288136853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-274126427/1250000000 : ℝ)|^2059 ≤ (1659050938531/12500000000000 : ℝ)^1547
        have hw : |(-274126427/1250000000 : ℝ)|=(274126427/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2693637223/5000000000 : ℝ)|^2059 ≤ (21949881248429/50000000000000 : ℝ)^1547
        have hw : |(2693637223/5000000000 : ℝ)|=(2693637223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_box_10 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2644068569/5000000000 : ℝ)*x 0 + (1077454913/2000000000 : ℝ)*x 1 + (-1096505437/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644068569/5000000000 : ℝ)^2059 ≤ (42827833050011/100000000000000 : ℝ)^1547 := by
    have hnat : (2644068569 : ℕ)^2059*100000000000000^1547 ≤ 42827833050011^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644068569 5000000000 42827833050011 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1077454913/2000000000 : ℝ)^2059 ≤ (43899763787501/100000000000000 : ℝ)^1547 := by
    have hnat : (1077454913 : ℕ)^2059*100000000000000^1547 ≤ 43899763787501^1547*2000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077454913 2000000000 43899763787501 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1096505437/5000000000 : ℝ)^2059 ≤ (1659050392793/12500000000000 : ℝ)^1547 := by
    have hnat : (1096505437 : ℕ)^2059*12500000000000^1547 ≤ 1659050392793^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1096505437 5000000000 1659050392793 12500000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644068569/5000000000 : ℝ), (1077454913/2000000000 : ℝ), (-1096505437/5000000000 : ℝ)] ![(42827833050011/100000000000000 : ℝ), (43899763787501/100000000000000 : ℝ), (1659050392793/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644068569/5000000000 : ℝ)|^2059 ≤ (42827833050011/100000000000000 : ℝ)^1547
        have hw : |(2644068569/5000000000 : ℝ)|=(2644068569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1077454913/2000000000 : ℝ)|^2059 ≤ (43899763787501/100000000000000 : ℝ)^1547
        have hw : |(1077454913/2000000000 : ℝ)|=(1077454913/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1096505437/5000000000 : ℝ)|^2059 ≤ (1659050392793/12500000000000 : ℝ)^1547
        have hw : |(-1096505437/5000000000 : ℝ)|=(1096505437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_box_11 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4508518463/10000000000 : ℝ)*x 0 + (2157998559/5000000000 : ℝ)*x 1 + (2157998677/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4508518463/10000000000 : ℝ)^2059 ≤ (34636324913963/100000000000000 : ℝ)^1547 := by
    have hnat : (4508518463 : ℕ)^2059*100000000000000^1547 ≤ 34636324913963^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4508518463 10000000000 34636324913963 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2157998559/5000000000 : ℝ)^2059 ≤ (6536367269579/20000000000000 : ℝ)^1547 := by
    have hnat : (2157998559 : ℕ)^2059*20000000000000^1547 ≤ 6536367269579^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2157998559 5000000000 6536367269579 20000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2157998677/5000000000 : ℝ)^2059 ≤ (8170459681599/25000000000000 : ℝ)^1547 := by
    have hnat : (2157998677 : ℕ)^2059*25000000000000^1547 ≤ 8170459681599^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2157998677 5000000000 8170459681599 25000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4508518463/10000000000 : ℝ), (2157998559/5000000000 : ℝ), (2157998677/5000000000 : ℝ)] ![(34636324913963/100000000000000 : ℝ), (6536367269579/20000000000000 : ℝ), (8170459681599/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4508518463/10000000000 : ℝ)|^2059 ≤ (34636324913963/100000000000000 : ℝ)^1547
        have hw : |(4508518463/10000000000 : ℝ)|=(4508518463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2157998559/5000000000 : ℝ)|^2059 ≤ (6536367269579/20000000000000 : ℝ)^1547
        have hw : |(2157998559/5000000000 : ℝ)|=(2157998559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2157998677/5000000000 : ℝ)|^2059 ≤ (8170459681599/25000000000000 : ℝ)^1547
        have hw : |(2157998677/5000000000 : ℝ)|=(2157998677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_box_12 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-427982741/2000000000 : ℝ)*x 0 + (5442734201/10000000000 : ℝ)*x 1 + (2635875537/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (427982741/2000000000 : ℝ)^2059 ≤ (1605802416711/12500000000000 : ℝ)^1547 := by
    have hnat : (427982741 : ℕ)^2059*12500000000000^1547 ≤ 1605802416711^1547*2000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427982741 2000000000 1605802416711 12500000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5442734201/10000000000 : ℝ)^2059 ≤ (44502286815611/100000000000000 : ℝ)^1547 := by
    have hnat : (5442734201 : ℕ)^2059*100000000000000^1547 ≤ 44502286815611^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5442734201 10000000000 44502286815611 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2635875537/5000000000 : ℝ)^2059 ≤ (21325646922293/50000000000000 : ℝ)^1547 := by
    have hnat : (2635875537 : ℕ)^2059*50000000000000^1547 ≤ 21325646922293^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2635875537 5000000000 21325646922293 50000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-427982741/2000000000 : ℝ), (5442734201/10000000000 : ℝ), (2635875537/5000000000 : ℝ)] ![(1605802416711/12500000000000 : ℝ), (44502286815611/100000000000000 : ℝ), (21325646922293/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-427982741/2000000000 : ℝ)|^2059 ≤ (1605802416711/12500000000000 : ℝ)^1547
        have hw : |(-427982741/2000000000 : ℝ)|=(427982741/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5442734201/10000000000 : ℝ)|^2059 ≤ (44502286815611/100000000000000 : ℝ)^1547
        have hw : |(5442734201/10000000000 : ℝ)|=(5442734201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2635875537/5000000000 : ℝ)|^2059 ≤ (21325646922293/50000000000000 : ℝ)^1547
        have hw : |(2635875537/5000000000 : ℝ)|=(2635875537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_box_13 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5369939611/10000000000 : ℝ)*x 0 + (-55952547/250000000 : ℝ)*x 1 + (5271751387/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369939611/10000000000 : ℝ)^2059 ≤ (43711853603061/100000000000000 : ℝ)^1547 := by
    have hnat : (5369939611 : ℕ)^2059*100000000000000^1547 ≤ 43711853603061^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369939611 10000000000 43711853603061 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (55952547/250000000 : ℝ)^2059 ≤ (6818424585703/50000000000000 : ℝ)^1547 := by
    have hnat : (55952547 : ℕ)^2059*50000000000000^1547 ≤ 6818424585703^1547*250000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55952547 250000000 6818424585703 50000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5271751387/10000000000 : ℝ)^2059 ≤ (21325648607517/50000000000000 : ℝ)^1547 := by
    have hnat : (5271751387 : ℕ)^2059*50000000000000^1547 ≤ 21325648607517^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271751387 10000000000 21325648607517 50000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369939611/10000000000 : ℝ), (-55952547/250000000 : ℝ), (5271751387/10000000000 : ℝ)] ![(43711853603061/100000000000000 : ℝ), (6818424585703/50000000000000 : ℝ), (21325648607517/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369939611/10000000000 : ℝ)|^2059 ≤ (43711853603061/100000000000000 : ℝ)^1547
        have hw : |(5369939611/10000000000 : ℝ)|=(5369939611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-55952547/250000000 : ℝ)|^2059 ≤ (6818424585703/50000000000000 : ℝ)^1547
        have hw : |(-55952547/250000000 : ℝ)|=(55952547/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5271751387/10000000000 : ℝ)|^2059 ≤ (21325648607517/50000000000000 : ℝ)^1547
        have hw : |(5271751387/10000000000 : ℝ)|=(5271751387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_box_14 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1342484777/2500000000 : ℝ)*x 0 + (5271751669/10000000000 : ℝ)*x 1 + (-69940693/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1342484777/2500000000 : ℝ)^2059 ≤ (43711848153471/100000000000000 : ℝ)^1547 := by
    have hnat : (1342484777 : ℕ)^2059*100000000000000^1547 ≤ 43711848153471^1547*2500000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342484777 2500000000 43711848153471 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5271751669/10000000000 : ℝ)^2059 ≤ (10662825062917/25000000000000 : ℝ)^1547 := by
    have hnat : (5271751669 : ℕ)^2059*25000000000000^1547 ≤ 10662825062917^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271751669 10000000000 10662825062917 25000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (69940693/312500000 : ℝ)^2059 ≤ (3409212892963/25000000000000 : ℝ)^1547 := by
    have hnat : (69940693 : ℕ)^2059*25000000000000^1547 ≤ 3409212892963^1547*312500000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69940693 312500000 3409212892963 25000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1342484777/2500000000 : ℝ), (5271751669/10000000000 : ℝ), (-69940693/312500000 : ℝ)] ![(43711848153471/100000000000000 : ℝ), (10662825062917/25000000000000 : ℝ), (3409212892963/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1342484777/2500000000 : ℝ)|^2059 ≤ (43711848153471/100000000000000 : ℝ)^1547
        have hw : |(1342484777/2500000000 : ℝ)|=(1342484777/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5271751669/10000000000 : ℝ)|^2059 ≤ (10662825062917/25000000000000 : ℝ)^1547
        have hw : |(5271751669/10000000000 : ℝ)|=(5271751669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-69940693/312500000 : ℝ)|^2059 ≤ (3409212892963/25000000000000 : ℝ)^1547
        have hw : |(-69940693/312500000 : ℝ)|=(69940693/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_box_15 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4251857851/10000000000 : ℝ)*x 0 + (4444325219/10000000000 : ℝ)*x 1 + (4444324293/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4251857851/10000000000 : ℝ)^2059 ≤ (32037010510591/100000000000000 : ℝ)^1547 := by
    have hnat : (4251857851 : ℕ)^2059*100000000000000^1547 ≤ 32037010510591^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4251857851 10000000000 32037010510591 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4444325219/10000000000 : ℝ)^2059 ≤ (33981499453769/100000000000000 : ℝ)^1547 := by
    have hnat : (4444325219 : ℕ)^2059*100000000000000^1547 ≤ 33981499453769^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4444325219 10000000000 33981499453769 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4444324293/10000000000 : ℝ)^2059 ≤ (33981490030237/100000000000000 : ℝ)^1547 := by
    have hnat : (4444324293 : ℕ)^2059*100000000000000^1547 ≤ 33981490030237^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4444324293 10000000000 33981490030237 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4251857851/10000000000 : ℝ), (4444325219/10000000000 : ℝ), (4444324293/10000000000 : ℝ)] ![(32037010510591/100000000000000 : ℝ), (33981499453769/100000000000000 : ℝ), (33981490030237/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4251857851/10000000000 : ℝ)|^2059 ≤ (32037010510591/100000000000000 : ℝ)^1547
        have hw : |(4251857851/10000000000 : ℝ)|=(4251857851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4444325219/10000000000 : ℝ)|^2059 ≤ (33981499453769/100000000000000 : ℝ)^1547
        have hw : |(4444325219/10000000000 : ℝ)|=(4444325219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4444324293/10000000000 : ℝ)|^2059 ≤ (33981490030237/100000000000000 : ℝ)^1547
        have hw : |(4444324293/10000000000 : ℝ)|=(4444324293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1043_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147545813/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3497/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (561/5000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62223/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(7403/12500 : ℝ) ∧ (159/200 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (829/1000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3497/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (561/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3497/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (561/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3497/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (561/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3497/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (561/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3497/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (561/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3497/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (561/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (561/5000 : ℝ) ^ (8235/2048 : ℝ) ≤ (3027296677889303/20000000000000000000 : ℝ) := by
    have hpowers : (561/5000 : ℝ)^8235 ≤ (3027296677889303/20000000000000000000 : ℝ)^2048 := by
      have hnat : (561 : ℕ)^8235*20000000000000000000^2048 ≤ 3027296677889303^2048*5000^8235 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        561 5000 3027296677889303 20000000000000000000 8235 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (561/5000 : ℝ)) (X := (3027296677889303/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8235 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3497/25000 : ℝ) ^ (8235/2048 : ℝ) ≤ (36735562950761709/100000000000000000000 : ℝ) := by
    have hpowers : (3497/25000 : ℝ)^8235 ≤ (36735562950761709/100000000000000000000 : ℝ)^2048 := by
      have hnat : (3497 : ℕ)^8235*100000000000000000000^2048 ≤ 36735562950761709^2048*25000^8235 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3497 25000 36735562950761709 100000000000000000000 8235 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3497/25000 : ℝ)) (X := (36735562950761709/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8235 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10003027296677889303/10000000000000000000 : ℝ) ≤ (10000752786722563/10000000000000000 : ℝ) ^ (8235/2048 : ℝ) := by
    have hpowers : (10003027296677889303/10000000000000000000 : ℝ)^2048 ≤ (10000752786722563/10000000000000000 : ℝ)^8235 := by
      have hnat : (10003027296677889303 : ℕ)^2048*10000000000000000^8235 ≤ 10000752786722563^8235*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10003027296677889303 10000000000000000000 10000752786722563 10000000000000000 2048 8235 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000752786722563/10000000000000000 : ℝ)) (X := (10003027296677889303/10000000000000000000 : ℝ)) (by norm_num) 8235 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (3126621001448131507/3125000000000000000 : ℝ) ≤ (10001289778464563/10000000000000000 : ℝ) ^ (8235/2048 : ℝ) := by
    have hpowers : (3126621001448131507/3125000000000000000 : ℝ)^2048 ≤ (10001289778464563/10000000000000000 : ℝ)^8235 := by
      have hnat : (3126621001448131507 : ℕ)^2048*10000000000000000^8235 ≤ 10001289778464563^8235*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126621001448131507 3125000000000000000 10001289778464563 10000000000000000 2048 8235 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001289778464563/10000000000000000 : ℝ)) (X := (3126621001448131507/3125000000000000000 : ℝ)) (by norm_num) 8235 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036735562950761709/50000000000000000000 : ℝ) ≤ (10001826770206563/10000000000000000 : ℝ) ^ (8235/2048 : ℝ) := by
    have hpowers : (50036735562950761709/50000000000000000000 : ℝ)^2048 ≤ (10001826770206563/10000000000000000 : ℝ)^8235 := by
      have hnat : (50036735562950761709 : ℕ)^2048*10000000000000000^8235 ≤ 10001826770206563^8235*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036735562950761709 50000000000000000000 10001826770206563 10000000000000000 2048 8235 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001826770206563/10000000000000000 : ℝ)) (X := (50036735562950761709/50000000000000000000 : ℝ)) (by norm_num) 8235 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3027296677889303/20000000000000000000 : ℝ) ≤ ((1729377101184848399/1730000000000000000 : ℝ)+2*(268495871/138400000000 : ℝ)*(561/5000 : ℝ))^(8235/2048 : ℝ) := by
    rw [show (1729377101184848399/1730000000000000000 : ℝ)+2*(268495871/138400000000 : ℝ)*(561/5000 : ℝ)=(10000752786722563/10000000000000000 : ℝ) by norm_num, show 1+2*(3027296677889303/20000000000000000000 : ℝ)=(10003027296677889303/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36735562950761709/100000000000000000000 : ℝ)+(3027296677889303/20000000000000000000 : ℝ) ≤ ((1729377101184848399/1730000000000000000 : ℝ)+(268495871/138400000000 : ℝ)*((3497/25000 : ℝ)+(561/5000 : ℝ)))^(8235/2048 : ℝ) := by
    rw [show (1729377101184848399/1730000000000000000 : ℝ)+(268495871/138400000000 : ℝ)*((3497/25000 : ℝ)+(561/5000 : ℝ))=(10001289778464563/10000000000000000 : ℝ) by norm_num, show 1+(36735562950761709/100000000000000000000 : ℝ)+(3027296677889303/20000000000000000000 : ℝ)=(3126621001448131507/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36735562950761709/100000000000000000000 : ℝ) ≤ ((1729377101184848399/1730000000000000000 : ℝ)+2*(268495871/138400000000 : ℝ)*(3497/25000 : ℝ))^(8235/2048 : ℝ) := by
    rw [show (1729377101184848399/1730000000000000000 : ℝ)+2*(268495871/138400000000 : ℝ)*(3497/25000 : ℝ)=(10001826770206563/10000000000000000 : ℝ) by norm_num, show 1+2*(36735562950761709/100000000000000000000 : ℝ)=(50036735562950761709/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1729377101184848399/1730000000000000000 : ℝ)*(X 1 0+X 2 0)+(268495871/138400000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8235/2048 : ℝ)) (lo := (561/5000 : ℝ)) (hi := (3497/25000 : ℝ)) (c := (1729377101184848399/1730000000000000000 : ℝ)) (alpha := (268495871/138400000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1729377101184848399/1730000000000000000 : ℝ)*(X 0 1+X 2 1)+(268495871/138400000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8235/2048 : ℝ)) (lo := (561/5000 : ℝ)) (hi := (3497/25000 : ℝ)) (c := (1729377101184848399/1730000000000000000 : ℝ)) (alpha := (268495871/138400000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1729377101184848399/1730000000000000000 : ℝ)*(X 0 2+X 1 2)+(268495871/138400000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8235/2048 : ℝ)) (lo := (561/5000 : ℝ)) (hi := (3497/25000 : ℝ)) (c := (1729377101184848399/1730000000000000000 : ℝ)) (alpha := (268495871/138400000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2084882081/10000000000 : ℝ)*X 0 0+(672209647/1250000000 : ℝ)*X 0 1+(5377677079/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2647468421/5000000000 : ℝ)*X 1 0+(-1098413603/5000000000 : ℝ)*X 1 1+(1344419261/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((264746841/500000000 : ℝ)*X 2 0+(1344419267/2500000000 : ℝ)*X 2 1+(-2196827203/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2243732793/5000000000 : ℝ)*X 0 0+(1081666063/2500000000 : ℝ)*X 0 1+(4326664133/10000000000 : ℝ)*X 0 2+(2243732793/5000000000 : ℝ)*X 1 0+(1081666063/2500000000 : ℝ)*X 1 1+(4326664133/10000000000 : ℝ)*X 1 2+(2243732793/5000000000 : ℝ)*X 2 0+(1081666063/2500000000 : ℝ)*X 2 1+(4326664133/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2346795979/10000000000 : ℝ)*X 0 0+(1319934909/2500000000 : ℝ)*X 0 1+(5279739537/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2682142773/5000000000 : ℝ)*X 1 0+(-1117521931/5000000000 : ℝ)*X 1 1+(5279739591/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2682142929/5000000000 : ℝ)*X 2 0+(1319934863/2500000000 : ℝ)*X 2 1+(-2235043631/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4269839233/10000000000 : ℝ)*X 0 0+(4435455581/10000000000 : ℝ)*X 0 1+(4435455847/10000000000 : ℝ)*X 0 2+(4269839233/10000000000 : ℝ)*X 1 0+(4435455581/10000000000 : ℝ)*X 1 1+(4435455847/10000000000 : ℝ)*X 1 2+(4269839233/10000000000 : ℝ)*X 2 0+(4435455581/10000000000 : ℝ)*X 2 1+(4435455847/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2292148461/10000000000 : ℝ)*X 0 0+(651666101/1250000000 : ℝ)*X 0 1+(1346818653/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5288136853/10000000000 : ℝ)*X 1 0+(-274126427/1250000000 : ℝ)*X 1 1+(2693637223/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2644068569/5000000000 : ℝ)*X 2 0+(1077454913/2000000000 : ℝ)*X 2 1+(-1096505437/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4508518463/10000000000 : ℝ)*X 0 0+(2157998559/5000000000 : ℝ)*X 0 1+(2157998677/5000000000 : ℝ)*X 0 2+(4508518463/10000000000 : ℝ)*X 1 0+(2157998559/5000000000 : ℝ)*X 1 1+(2157998677/5000000000 : ℝ)*X 1 2+(4508518463/10000000000 : ℝ)*X 2 0+(2157998559/5000000000 : ℝ)*X 2 1+(2157998677/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-427982741/2000000000 : ℝ)*X 0 0+(5442734201/10000000000 : ℝ)*X 0 1+(2635875537/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5369939611/10000000000 : ℝ)*X 1 0+(-55952547/250000000 : ℝ)*X 1 1+(5271751387/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1342484777/2500000000 : ℝ)*X 2 0+(5271751669/10000000000 : ℝ)*X 2 1+(-69940693/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4251857851/10000000000 : ℝ)*X 0 0+(4444325219/10000000000 : ℝ)*X 0 1+(4444324293/10000000000 : ℝ)*X 0 2+(4251857851/10000000000 : ℝ)*X 1 0+(4444325219/10000000000 : ℝ)*X 1 1+(4444324293/10000000000 : ℝ)*X 1 2+(4251857851/10000000000 : ℝ)*X 2 0+(4444325219/10000000000 : ℝ)*X 2 1+(4444324293/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62223/100000 : ℝ) ≤ (-21528468316378901229019869/34600000000000000000000000 : ℝ) := by norm_num
    linear_combination (143249567/100000000000000 : ℝ)*(upper0) + (178699551/100000000000000 : ℝ)*(lower2) + (16457003/50000000000000 : ℝ)*(upper5) + (383706657757447/10000000000000 : ℝ)*(major0) + (383706657757447/10000000000000 : ℝ)*(major1) + (383706657757447/10000000000000 : ℝ)*(major2) + (2377164297/100000000000000 : ℝ)*(sp3) + (5094277924584171/100000000000000 : ℝ)*(sp4) + (2547137883448247/50000000000000 : ℝ)*(sp5) + (5094240816436739/100000000000000 : ℝ)*(sp6) + (1300295478451863/50000000000000 : ℝ)*(sp7) + (2232061637/100000000000000 : ℝ)*(sp8) + (877949863/20000000000000 : ℝ)*(sp13) + (3934020907/10000000000000 : ℝ)*(sp14) + (1300296667034011/50000000000000 : ℝ)*(f.failure) + (5094280156645809/100000000000000 : ℝ)*(f.sum) + (195865421733/43250000000000000000000000 : ℝ)*base66 + (1441486891156177353/17300000000000000000000000000000 : ℝ)*base67 + (34734703105422647/17300000000000000000000000000000 : ℝ)*base70 + (122609085891077353/17300000000000000000000000000000 : ℝ)*base71 + (1191800124411/43250000000000000000000000 : ℝ)*base73 + (124039295857822647/17300000000000000000000000000000 : ℝ)*base76 + (12984065799822647/17300000000000000000000000000000 : ℝ)*base78 + (149326978932377353/17300000000000000000000000000000 : ℝ)*base79 + (31936923757/10812500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (48354057/5000000000000000000000 : ℝ)*base90 + (48354057/5000000000000000000000 : ℝ)*base92 + (48354057/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (7403/12500 : ℝ) ≤ (51230664317241791783125326454803/86500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6658801/100000000000000 : ℝ)*(upper3) + (3534151/20000000000000 : ℝ)*(upper4) + (39405413/100000000000000 : ℝ)*(lower5) + (1949804309726583/50000000000000 : ℝ)*(major0) + (1949804309726583/50000000000000 : ℝ)*(major1) + (3899608619453167/100000000000000 : ℝ)*(major2) + (5136491760337459/100000000000000 : ℝ)*(sp0) + (1284116522578661/25000000000000 : ℝ)*(sp1) + (5136492140717977/100000000000000 : ℝ)*(sp2) + (1321490071539709/50000000000000 : ℝ)*(sp3) + (1478258547/100000000000000 : ℝ)*(sp6) + (1409676109/100000000000000 : ℝ)*(sp7) + (371727813/20000000000000 : ℝ)*(sp8) + (688216547/2500000000000 : ℝ)*(sp9) + (330372694094441/12500000000000 : ℝ)*(f.failure) + (1284123404744131/25000000000000 : ℝ)*(f.sum) + (1208861974529/346000000000000000000000000 : ℝ)*base65 + (496378271216959383/86500000000000000000000000000000 : ℝ)*base68 + (1454208300266429633/173000000000000000000000000000000 : ℝ)*base69 + (134537635552959383/86500000000000000000000000000000 : ℝ)*base72 + (570124965409/346000000000000000000000000 : ℝ)*base73 + (1772730576191429633/173000000000000000000000000000000 : ℝ)*base75 + (166450915756290617/86500000000000000000000000000000 : ℝ)*base77 + (347505488434709383/86500000000000000000000000000000 : ℝ)*base80 + (542193847567/173000000000000000000000000 : ℝ)*base82 + (21125533/1250000000000000000000 : ℝ)*base89 + (21125533/1250000000000000000000 : ℝ)*base91 + (8625533/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (159/200 : ℝ) ≤ (34384615865731991639794865772903/43250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (167432529/100000000000000 : ℝ)*(upper0) + (7779511/6250000000000 : ℝ)*(lower3) + (323379821/100000000000000 : ℝ)*(upper4) + (4367900741468467/100000000000000 : ℝ)*(major0) + (4367900741468467/100000000000000 : ℝ)*(major1) + (1091975185367117/25000000000000 : ℝ)*(major2) + (150649433/125000000000 : ℝ)*(sp1) + (710293299/200000000000 : ℝ)*(sp2) + (117735674499/100000000000000 : ℝ)*(sp3) + (8055747659/100000000000000 : ℝ)*(sp4) + (5748923602196871/100000000000000 : ℝ)*(sp8) + (5748811138398131/100000000000000 : ℝ)*(sp9) + (574857651129503/10000000000000 : ℝ)*(sp10) + (740062855495997/25000000000000 : ℝ)*(sp11) + (370046144707311/12500000000000 : ℝ)*(f.failure) + (574893165794453/10000000000000 : ℝ)*(f.sum) + (898274309189/346000000000000000000000000 : ℝ)*base65 + (1351730238631934333/173000000000000000000000000000000 : ℝ)*base67 + (625436182459820683/43250000000000000000000000000000 : ℝ)*base69 + (30421256010934333/173000000000000000000000000000000 : ℝ)*base71 + (19665694469769/346000000000000000000000000 : ℝ)*base73 + (486963994274070683/43250000000000000000000000000000 : ℝ)*base75 + (479196475342434333/173000000000000000000000000000000 : ℝ)*base77 + (11554456092210434333/173000000000000000000000000000000 : ℝ)*base79 + (107433493051/86500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (11038843/1250000000000000000000 : ℝ)*base89 + (11038843/1250000000000000000000 : ℝ)*base91 + (1461157/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-829/1000 : ℝ) ≤ (-35853076229427846083146023497859/43250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (103569107/100000000000000 : ℝ)*(lower0) + (4200177/100000000000000 : ℝ)*(upper1) + (440890367/100000000000000 : ℝ)*(upper3) + (110621197/100000000000000 : ℝ)*(lower4) + (2201150919628847/50000000000000 : ℝ)*(major0) + (2201150919628847/50000000000000 : ℝ)*(major1) + (2201150919628847/50000000000000 : ℝ)*(major2) + (7146481033/100000000000000 : ℝ)*(sp4) + (324653038219/100000000000000 : ℝ)*(sp5) + (219439066823/100000000000000 : ℝ)*(sp7) + (2924272133316727/50000000000000 : ℝ)*(sp12) + (1462056690019067/25000000000000 : ℝ)*(sp13) + (5848551413114487/100000000000000 : ℝ)*(sp14) + (2983465255027271/100000000000000 : ℝ)*(sp15) + (1491842347047047/50000000000000 : ℝ)*(f.failure) + (5848551413114487/100000000000000 : ℝ)*(f.sum) + (237638827669/173000000000000000000000000 : ℝ)*base66 + (607658506033665953/86500000000000000000000000000000 : ℝ)*base67 + (1624108016531834047/86500000000000000000000000000000 : ℝ)*base70 + (653690783031665953/86500000000000000000000000000000 : ℝ)*base71 + (174434071953/43250000000000000000000000 : ℝ)*base74 + (889349408153834047/86500000000000000000000000000000 : ℝ)*base76 + (1541083619830665953/86500000000000000000000000000000 : ℝ)*base77 + (239043551507165953/86500000000000000000000000000000 : ℝ)*base79 + (498188239353/86500000000000000000000000 : ℝ)*base82 + (1135789/5000000000000000000000 : ℝ)*base90 + (1135789/5000000000000000000000 : ℝ)*base92 + (1135789/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1043_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147545813/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3497/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (561/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(7403/12500 : ℝ) else (159/200 : ℝ) ≤ X j i ∧ X j i ≤ (829/1000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1043_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1043_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147545813/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13989/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11219/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(7403/12500 : ℝ) else (159/200 : ℝ) ≤ X j i ∧ X j i ≤ (829/1000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1043_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1043_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147545813/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13989/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11219/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(7403/12500 : ℝ) else (159/200 : ℝ) ≤ X j i ∧ X j i ≤ (829/1000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1043_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
