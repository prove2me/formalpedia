-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1112_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:05:46.361447+00:00
-- url     : https://prove2.me/submissions/91d7d366-49cf-4276-af7f-35ad774f8910

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
theorem support_rectangle_w1112_box_0 (p : ℝ) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-256677209/1250000000 : ℝ)*x 0 + (1344184191/2500000000 : ℝ)*x 1 + (1344184169/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (256677209/1250000000 : ℝ)^8305 ≤ (1223043475237/10000000000000 : ℝ)^6257 := by
    have hnat : (256677209 : ℕ)^8305*10000000000000^6257 ≤ 1223043475237^6257*1250000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256677209 1250000000 1223043475237 10000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1344184191/2500000000 : ℝ)^8305 ≤ (43884783094633/100000000000000 : ℝ)^6257 := by
    have hnat : (1344184191 : ℕ)^8305*100000000000000^6257 ≤ 43884783094633^6257*2500000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344184191 2500000000 43884783094633 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1344184169/2500000000 : ℝ)^8305 ≤ (8776956428257/20000000000000 : ℝ)^6257 := by
    have hnat : (1344184169 : ℕ)^8305*20000000000000^6257 ≤ 8776956428257^6257*2500000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344184169 2500000000 8776956428257 20000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8305/2048 : ℝ)) 8305 6257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-256677209/1250000000 : ℝ), (1344184191/2500000000 : ℝ), (1344184169/2500000000 : ℝ)] ![(1223043475237/10000000000000 : ℝ), (43884783094633/100000000000000 : ℝ), (8776956428257/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-256677209/1250000000 : ℝ)|^8305 ≤ (1223043475237/10000000000000 : ℝ)^6257
        have hw : |(-256677209/1250000000 : ℝ)|=(256677209/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1344184191/2500000000 : ℝ)|^8305 ≤ (43884783094633/100000000000000 : ℝ)^6257
        have hw : |(1344184191/2500000000 : ℝ)|=(1344184191/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1344184169/2500000000 : ℝ)|^8305 ≤ (8776956428257/20000000000000 : ℝ)^6257
        have hw : |(1344184169/2500000000 : ℝ)|=(1344184169/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1112_box_1 (p : ℝ) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5295691833/10000000000 : ℝ)*x 0 + (-2163252077/10000000000 : ℝ)*x 1 + (268836841/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295691833/10000000000 : ℝ)^8305 ≤ (43008956338037/100000000000000 : ℝ)^6257 := by
    have hnat : (5295691833 : ℕ)^8305*100000000000000^6257 ≤ 43008956338037^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295691833 10000000000 43008956338037 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2163252077/10000000000 : ℝ)^8305 ≤ (13106259942571/100000000000000 : ℝ)^6257 := by
    have hnat : (2163252077 : ℕ)^8305*100000000000000^6257 ≤ 13106259942571^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2163252077 10000000000 13106259942571 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (268836841/500000000 : ℝ)^8305 ≤ (43884783701309/100000000000000 : ℝ)^6257 := by
    have hnat : (268836841 : ℕ)^8305*100000000000000^6257 ≤ 43884783701309^6257*500000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268836841 500000000 43884783701309 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8305/2048 : ℝ)) 8305 6257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295691833/10000000000 : ℝ), (-2163252077/10000000000 : ℝ), (268836841/500000000 : ℝ)] ![(43008956338037/100000000000000 : ℝ), (13106259942571/100000000000000 : ℝ), (43884783701309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295691833/10000000000 : ℝ)|^8305 ≤ (43008956338037/100000000000000 : ℝ)^6257
        have hw : |(5295691833/10000000000 : ℝ)|=(5295691833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2163252077/10000000000 : ℝ)|^8305 ≤ (13106259942571/100000000000000 : ℝ)^6257
        have hw : |(-2163252077/10000000000 : ℝ)|=(2163252077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(268836841/500000000 : ℝ)|^8305 ≤ (43884783701309/100000000000000 : ℝ)^6257
        have hw : |(268836841/500000000 : ℝ)|=(268836841/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1112_box_2 (p : ℝ) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5295691951/10000000000 : ℝ)*x 0 + (1344184151/2500000000 : ℝ)*x 1 + (-2163252211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295691951/10000000000 : ℝ)^8305 ≤ (860179152201/2000000000000 : ℝ)^6257 := by
    have hnat : (5295691951 : ℕ)^8305*2000000000000^6257 ≤ 860179152201^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295691951 10000000000 860179152201 2000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1344184151/2500000000 : ℝ)^8305 ≤ (43884781361273/100000000000000 : ℝ)^6257 := by
    have hnat : (1344184151 : ℕ)^8305*100000000000000^6257 ≤ 43884781361273^6257*2500000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344184151 2500000000 43884781361273 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2163252211/10000000000 : ℝ)^8305 ≤ (13106261020153/100000000000000 : ℝ)^6257 := by
    have hnat : (2163252211 : ℕ)^8305*100000000000000^6257 ≤ 13106261020153^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2163252211 10000000000 13106261020153 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8305/2048 : ℝ)) 8305 6257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295691951/10000000000 : ℝ), (1344184151/2500000000 : ℝ), (-2163252211/10000000000 : ℝ)] ![(860179152201/2000000000000 : ℝ), (43884781361273/100000000000000 : ℝ), (13106261020153/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295691951/10000000000 : ℝ)|^8305 ≤ (860179152201/2000000000000 : ℝ)^6257
        have hw : |(5295691951/10000000000 : ℝ)|=(5295691951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1344184151/2500000000 : ℝ)|^8305 ≤ (43884781361273/100000000000000 : ℝ)^6257
        have hw : |(1344184151/2500000000 : ℝ)|=(1344184151/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2163252211/10000000000 : ℝ)|^8305 ≤ (13106261020153/100000000000000 : ℝ)^6257
        have hw : |(-2163252211/10000000000 : ℝ)|=(2163252211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1112_box_3 (p : ℝ) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4476795799/10000000000 : ℝ)*x 0 + (269819347/625000000 : ℝ)*x 1 + (2158554989/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4476795799/10000000000 : ℝ)^8305 ≤ (34413131781317/100000000000000 : ℝ)^6257 := by
    have hnat : (4476795799 : ℕ)^8305*100000000000000^6257 ≤ 34413131781317^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4476795799 10000000000 34413131781317 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269819347/625000000 : ℝ)^8305 ≤ (2049589496937/6250000000000 : ℝ)^6257 := by
    have hnat : (269819347 : ℕ)^8305*6250000000000^6257 ≤ 2049589496937^6257*625000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269819347 625000000 2049589496937 6250000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2158554989/5000000000 : ℝ)^8305 ≤ (32793436246127/100000000000000 : ℝ)^6257 := by
    have hnat : (2158554989 : ℕ)^8305*100000000000000^6257 ≤ 32793436246127^6257*5000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158554989 5000000000 32793436246127 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8305/2048 : ℝ)) 8305 6257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4476795799/10000000000 : ℝ), (269819347/625000000 : ℝ), (2158554989/5000000000 : ℝ)] ![(34413131781317/100000000000000 : ℝ), (2049589496937/6250000000000 : ℝ), (32793436246127/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4476795799/10000000000 : ℝ)|^8305 ≤ (34413131781317/100000000000000 : ℝ)^6257
        have hw : |(4476795799/10000000000 : ℝ)|=(4476795799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269819347/625000000 : ℝ)|^8305 ≤ (2049589496937/6250000000000 : ℝ)^6257
        have hw : |(269819347/625000000 : ℝ)|=(269819347/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2158554989/5000000000 : ℝ)|^8305 ≤ (32793436246127/100000000000000 : ℝ)^6257
        have hw : |(2158554989/5000000000 : ℝ)|=(2158554989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1112_box_4 (p : ℝ) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-577651451/2500000000 : ℝ)*x 0 + (660092757/1250000000 : ℝ)*x 1 + (5280742827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (577651451/2500000000 : ℝ)^8305 ≤ (14304240456479/100000000000000 : ℝ)^6257 := by
    have hnat : (577651451 : ℕ)^8305*100000000000000^6257 ≤ 14304240456479^6257*2500000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      577651451 2500000000 14304240456479 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (660092757/1250000000 : ℝ)^8305 ≤ (42847875612811/100000000000000 : ℝ)^6257 := by
    have hnat : (660092757 : ℕ)^8305*100000000000000^6257 ≤ 42847875612811^6257*1250000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660092757 1250000000 42847875612811 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5280742827/10000000000 : ℝ)^8305 ≤ (4284788391633/10000000000000 : ℝ)^6257 := by
    have hnat : (5280742827 : ℕ)^8305*10000000000000^6257 ≤ 4284788391633^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280742827 10000000000 4284788391633 10000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8305/2048 : ℝ)) 8305 6257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-577651451/2500000000 : ℝ), (660092757/1250000000 : ℝ), (5280742827/10000000000 : ℝ)] ![(14304240456479/100000000000000 : ℝ), (42847875612811/100000000000000 : ℝ), (4284788391633/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-577651451/2500000000 : ℝ)|^8305 ≤ (14304240456479/100000000000000 : ℝ)^6257
        have hw : |(-577651451/2500000000 : ℝ)|=(577651451/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(660092757/1250000000 : ℝ)|^8305 ≤ (42847875612811/100000000000000 : ℝ)^6257
        have hw : |(660092757/1250000000 : ℝ)|=(660092757/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5280742827/10000000000 : ℝ)|^8305 ≤ (4284788391633/10000000000000 : ℝ)^6257
        have hw : |(5280742827/10000000000 : ℝ)|=(5280742827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1112_box_5 (p : ℝ) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2681778983/5000000000 : ℝ)*x 0 + (-440184459/2000000000 : ℝ)*x 1 + (26403713/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681778983/5000000000 : ℝ)^8305 ≤ (10935516982491/25000000000000 : ℝ)^6257 := by
    have hnat : (2681778983 : ℕ)^8305*25000000000000^6257 ≤ 10935516982491^6257*5000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681778983 5000000000 10935516982491 25000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (440184459/2000000000 : ℝ)^8305 ≤ (6705025295483/50000000000000 : ℝ)^6257 := by
    have hnat : (440184459 : ℕ)^8305*50000000000000^6257 ≤ 6705025295483^6257*2000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      440184459 2000000000 6705025295483 50000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (26403713/50000000 : ℝ)^8305 ≤ (8569576294317/20000000000000 : ℝ)^6257 := by
    have hnat : (26403713 : ℕ)^8305*20000000000000^6257 ≤ 8569576294317^6257*50000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26403713 50000000 8569576294317 20000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8305/2048 : ℝ)) 8305 6257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681778983/5000000000 : ℝ), (-440184459/2000000000 : ℝ), (26403713/50000000 : ℝ)] ![(10935516982491/25000000000000 : ℝ), (6705025295483/50000000000000 : ℝ), (8569576294317/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681778983/5000000000 : ℝ)|^8305 ≤ (10935516982491/25000000000000 : ℝ)^6257
        have hw : |(2681778983/5000000000 : ℝ)|=(2681778983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-440184459/2000000000 : ℝ)|^8305 ≤ (6705025295483/50000000000000 : ℝ)^6257
        have hw : |(-440184459/2000000000 : ℝ)|=(440184459/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(26403713/50000000 : ℝ)|^8305 ≤ (8569576294317/20000000000000 : ℝ)^6257
        have hw : |(26403713/50000000 : ℝ)|=(26403713/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1112_box_6 (p : ℝ) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5363557861/10000000000 : ℝ)*x 0 + (5280742361/10000000000 : ℝ)*x 1 + (-1100461377/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5363557861/10000000000 : ℝ)^8305 ≤ (546775834917/1250000000000 : ℝ)^6257 := by
    have hnat : (5363557861 : ℕ)^8305*1250000000000^6257 ≤ 546775834917^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363557861 10000000000 546775834917 1250000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5280742361/10000000000 : ℝ)^8305 ≤ (42847878897601/100000000000000 : ℝ)^6257 := by
    have hnat : (5280742361 : ℕ)^8305*100000000000000^6257 ≤ 42847878897601^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280742361 10000000000 42847878897601 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1100461377/5000000000 : ℝ)^8305 ≤ (13410054302999/100000000000000 : ℝ)^6257 := by
    have hnat : (1100461377 : ℕ)^8305*100000000000000^6257 ≤ 13410054302999^6257*5000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100461377 5000000000 13410054302999 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8305/2048 : ℝ)) 8305 6257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5363557861/10000000000 : ℝ), (5280742361/10000000000 : ℝ), (-1100461377/5000000000 : ℝ)] ![(546775834917/1250000000000 : ℝ), (42847878897601/100000000000000 : ℝ), (13410054302999/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5363557861/10000000000 : ℝ)|^8305 ≤ (546775834917/1250000000000 : ℝ)^6257
        have hw : |(5363557861/10000000000 : ℝ)|=(5363557861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5280742361/10000000000 : ℝ)|^8305 ≤ (42847878897601/100000000000000 : ℝ)^6257
        have hw : |(5280742361/10000000000 : ℝ)|=(5280742361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1100461377/5000000000 : ℝ)|^8305 ≤ (13410054302999/100000000000000 : ℝ)^6257
        have hw : |(-1100461377/5000000000 : ℝ)|=(1100461377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1112_box_7 (p : ℝ) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2130346721/5000000000 : ℝ)*x 0 + (88502797/200000000 : ℝ)*x 1 + (35401119/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2130346721/5000000000 : ℝ)^8305 ≤ (32225837855077/100000000000000 : ℝ)^6257 := by
    have hnat : (2130346721 : ℕ)^8305*100000000000000^6257 ≤ 32225837855077^6257*5000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2130346721 5000000000 32225837855077 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (88502797/200000000 : ℝ)^8305 ≤ (16943540470317/50000000000000 : ℝ)^6257 := by
    have hnat : (88502797 : ℕ)^8305*50000000000000^6257 ≤ 16943540470317^6257*200000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88502797 200000000 16943540470317 50000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (35401119/80000000 : ℝ)^8305 ≤ (33887081194743/100000000000000 : ℝ)^6257 := by
    have hnat : (35401119 : ℕ)^8305*100000000000000^6257 ≤ 33887081194743^6257*80000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35401119 80000000 33887081194743 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8305/2048 : ℝ)) 8305 6257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2130346721/5000000000 : ℝ), (88502797/200000000 : ℝ), (35401119/80000000 : ℝ)] ![(32225837855077/100000000000000 : ℝ), (16943540470317/50000000000000 : ℝ), (33887081194743/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2130346721/5000000000 : ℝ)|^8305 ≤ (32225837855077/100000000000000 : ℝ)^6257
        have hw : |(2130346721/5000000000 : ℝ)|=(2130346721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(88502797/200000000 : ℝ)|^8305 ≤ (16943540470317/50000000000000 : ℝ)^6257
        have hw : |(88502797/200000000 : ℝ)|=(88502797/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(35401119/80000000 : ℝ)|^8305 ≤ (33887081194743/100000000000000 : ℝ)^6257
        have hw : |(35401119/80000000 : ℝ)|=(35401119/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1112_box_8 (p : ℝ) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-451371831/2000000000 : ℝ)*x 0 + (5215515019/10000000000 : ℝ)*x 1 + (269317173/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (451371831/2000000000 : ℝ)^8305 ≤ (13864295188997/100000000000000 : ℝ)^6257 := by
    have hnat : (451371831 : ℕ)^8305*100000000000000^6257 ≤ 13864295188997^6257*2000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451371831 2000000000 13864295188997 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5215515019/10000000000 : ℝ)^8305 ≤ (42146817170659/100000000000000 : ℝ)^6257 := by
    have hnat : (5215515019 : ℕ)^8305*100000000000000^6257 ≤ 42146817170659^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215515019 10000000000 42146817170659 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269317173/500000000 : ℝ)^8305 ≤ (10997221906463/25000000000000 : ℝ)^6257 := by
    have hnat : (269317173 : ℕ)^8305*25000000000000^6257 ≤ 10997221906463^6257*500000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269317173 500000000 10997221906463 25000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8305/2048 : ℝ)) 8305 6257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-451371831/2000000000 : ℝ), (5215515019/10000000000 : ℝ), (269317173/500000000 : ℝ)] ![(13864295188997/100000000000000 : ℝ), (42146817170659/100000000000000 : ℝ), (10997221906463/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-451371831/2000000000 : ℝ)|^8305 ≤ (13864295188997/100000000000000 : ℝ)^6257
        have hw : |(-451371831/2000000000 : ℝ)|=(451371831/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5215515019/10000000000 : ℝ)|^8305 ≤ (42146817170659/100000000000000 : ℝ)^6257
        have hw : |(5215515019/10000000000 : ℝ)|=(5215515019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269317173/500000000 : ℝ)|^8305 ≤ (10997221906463/25000000000000 : ℝ)^6257
        have hw : |(269317173/500000000 : ℝ)|=(269317173/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1112_box_9 (p : ℝ) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5288896653/10000000000 : ℝ)*x 0 + (-2159412353/10000000000 : ℝ)*x 1 + (2693171727/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288896653/10000000000 : ℝ)^8305 ≤ (21467860607933/50000000000000 : ℝ)^6257 := by
    have hnat : (5288896653 : ℕ)^8305*50000000000000^6257 ≤ 21467860607933^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288896653 10000000000 21467860607933 50000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2159412353/10000000000 : ℝ)^8305 ≤ (13075391201879/100000000000000 : ℝ)^6257 := by
    have hnat : (2159412353 : ℕ)^8305*100000000000000^6257 ≤ 13075391201879^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2159412353 10000000000 13075391201879 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2693171727/5000000000 : ℝ)^8305 ≤ (43988887560813/100000000000000 : ℝ)^6257 := by
    have hnat : (2693171727 : ℕ)^8305*100000000000000^6257 ≤ 43988887560813^6257*5000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693171727 5000000000 43988887560813 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8305/2048 : ℝ)) 8305 6257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288896653/10000000000 : ℝ), (-2159412353/10000000000 : ℝ), (2693171727/5000000000 : ℝ)] ![(21467860607933/50000000000000 : ℝ), (13075391201879/100000000000000 : ℝ), (43988887560813/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288896653/10000000000 : ℝ)|^8305 ≤ (21467860607933/50000000000000 : ℝ)^6257
        have hw : |(5288896653/10000000000 : ℝ)|=(5288896653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2159412353/10000000000 : ℝ)|^8305 ≤ (13075391201879/100000000000000 : ℝ)^6257
        have hw : |(-2159412353/10000000000 : ℝ)|=(2159412353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2693171727/5000000000 : ℝ)|^8305 ≤ (43988887560813/100000000000000 : ℝ)^6257
        have hw : |(2693171727/5000000000 : ℝ)|=(2693171727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1112_box_10 (p : ℝ) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2644448379/5000000000 : ℝ)*x 0 + (5386343439/10000000000 : ℝ)*x 1 + (-2159412233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644448379/5000000000 : ℝ)^8305 ≤ (42935722347267/100000000000000 : ℝ)^6257 := by
    have hnat : (2644448379 : ℕ)^8305*100000000000000^6257 ≤ 42935722347267^6257*5000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644448379 5000000000 42935722347267 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5386343439/10000000000 : ℝ)^8305 ≤ (5498610924777/12500000000000 : ℝ)^6257 := by
    have hnat : (5386343439 : ℕ)^8305*12500000000000^6257 ≤ 5498610924777^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386343439 10000000000 5498610924777 12500000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2159412233/10000000000 : ℝ)^8305 ≤ (6537695118721/50000000000000 : ℝ)^6257 := by
    have hnat : (2159412233 : ℕ)^8305*50000000000000^6257 ≤ 6537695118721^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2159412233 10000000000 6537695118721 50000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8305/2048 : ℝ)) 8305 6257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644448379/5000000000 : ℝ), (5386343439/10000000000 : ℝ), (-2159412233/10000000000 : ℝ)] ![(42935722347267/100000000000000 : ℝ), (5498610924777/12500000000000 : ℝ), (6537695118721/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644448379/5000000000 : ℝ)|^8305 ≤ (42935722347267/100000000000000 : ℝ)^6257
        have hw : |(2644448379/5000000000 : ℝ)|=(2644448379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5386343439/10000000000 : ℝ)|^8305 ≤ (5498610924777/12500000000000 : ℝ)^6257
        have hw : |(5386343439/10000000000 : ℝ)|=(5386343439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2159412233/10000000000 : ℝ)|^8305 ≤ (6537695118721/50000000000000 : ℝ)^6257
        have hw : |(-2159412233/10000000000 : ℝ)|=(2159412233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1112_box_11 (p : ℝ) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2249074703/5000000000 : ℝ)*x 0 + (4306292387/10000000000 : ℝ)*x 1 + (269143277/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2249074703/5000000000 : ℝ)^8305 ≤ (6926234756897/20000000000000 : ℝ)^6257 := by
    have hnat : (2249074703 : ℕ)^8305*20000000000000^6257 ≤ 6926234756897^6257*5000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2249074703 5000000000 6926234756897 20000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4306292387/10000000000 : ℝ)^8305 ≤ (32684412871739/100000000000000 : ℝ)^6257 := by
    have hnat : (4306292387 : ℕ)^8305*100000000000000^6257 ≤ 32684412871739^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4306292387 10000000000 32684412871739 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269143277/625000000 : ℝ)^8305 ≤ (16342206662539/50000000000000 : ℝ)^6257 := by
    have hnat : (269143277 : ℕ)^8305*50000000000000^6257 ≤ 16342206662539^6257*625000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269143277 625000000 16342206662539 50000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8305/2048 : ℝ)) 8305 6257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2249074703/5000000000 : ℝ), (4306292387/10000000000 : ℝ), (269143277/625000000 : ℝ)] ![(6926234756897/20000000000000 : ℝ), (32684412871739/100000000000000 : ℝ), (16342206662539/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2249074703/5000000000 : ℝ)|^8305 ≤ (6926234756897/20000000000000 : ℝ)^6257
        have hw : |(2249074703/5000000000 : ℝ)|=(2249074703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4306292387/10000000000 : ℝ)|^8305 ≤ (32684412871739/100000000000000 : ℝ)^6257
        have hw : |(4306292387/10000000000 : ℝ)|=(4306292387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269143277/625000000 : ℝ)|^8305 ≤ (16342206662539/50000000000000 : ℝ)^6257
        have hw : |(269143277/625000000 : ℝ)|=(269143277/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1112_box_12 (p : ℝ) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1053751297/5000000000 : ℝ)*x 0 + (170020749/312500000 : ℝ)*x 1 + (5272717451/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1053751297/5000000000 : ℝ)^8305 ≤ (506393761261/4000000000000 : ℝ)^6257 := by
    have hnat : (1053751297 : ℕ)^8305*4000000000000^6257 ≤ 506393761261^6257*5000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053751297 5000000000 506393761261 4000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (170020749/312500000 : ℝ)^8305 ≤ (2786167641729/6250000000000 : ℝ)^6257 := by
    have hnat : (170020749 : ℕ)^8305*6250000000000^6257 ≤ 2786167641729^6257*312500000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170020749 312500000 2786167641729 6250000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5272717451/10000000000 : ℝ)^8305 ≤ (42761473685509/100000000000000 : ℝ)^6257 := by
    have hnat : (5272717451 : ℕ)^8305*100000000000000^6257 ≤ 42761473685509^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5272717451 10000000000 42761473685509 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8305/2048 : ℝ)) 8305 6257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1053751297/5000000000 : ℝ), (170020749/312500000 : ℝ), (5272717451/10000000000 : ℝ)] ![(506393761261/4000000000000 : ℝ), (2786167641729/6250000000000 : ℝ), (42761473685509/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1053751297/5000000000 : ℝ)|^8305 ≤ (506393761261/4000000000000 : ℝ)^6257
        have hw : |(-1053751297/5000000000 : ℝ)|=(1053751297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(170020749/312500000 : ℝ)|^8305 ≤ (2786167641729/6250000000000 : ℝ)^6257
        have hw : |(170020749/312500000 : ℝ)|=(170020749/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5272717451/10000000000 : ℝ)|^8305 ≤ (42761473685509/100000000000000 : ℝ)^6257
        have hw : |(5272717451/10000000000 : ℝ)|=(5272717451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1112_box_13 (p : ℝ) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1073845849/2000000000 : ℝ)*x 0 + (-1102006901/5000000000 : ℝ)*x 1 + (5272717383/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073845849/2000000000 : ℝ)^8305 ≤ (2190173450113/5000000000000 : ℝ)^6257 := by
    have hnat : (1073845849 : ℕ)^8305*5000000000000^6257 ≤ 2190173450113^6257*2000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073845849 2000000000 2190173450113 5000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1102006901/5000000000 : ℝ)^8305 ≤ (537402321191/4000000000000 : ℝ)^6257 := by
    have hnat : (1102006901 : ℕ)^8305*4000000000000^6257 ≤ 537402321191^6257*5000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102006901 5000000000 537402321191 4000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5272717383/10000000000 : ℝ)^8305 ≤ (42761472953527/100000000000000 : ℝ)^6257 := by
    have hnat : (5272717383 : ℕ)^8305*100000000000000^6257 ≤ 42761472953527^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5272717383 10000000000 42761472953527 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8305/2048 : ℝ)) 8305 6257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073845849/2000000000 : ℝ), (-1102006901/5000000000 : ℝ), (5272717383/10000000000 : ℝ)] ![(2190173450113/5000000000000 : ℝ), (537402321191/4000000000000 : ℝ), (42761472953527/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073845849/2000000000 : ℝ)|^8305 ≤ (2190173450113/5000000000000 : ℝ)^6257
        have hw : |(1073845849/2000000000 : ℝ)|=(1073845849/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1102006901/5000000000 : ℝ)|^8305 ≤ (537402321191/4000000000000 : ℝ)^6257
        have hw : |(-1102006901/5000000000 : ℝ)|=(1102006901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5272717383/10000000000 : ℝ)|^8305 ≤ (42761472953527/100000000000000 : ℝ)^6257
        have hw : |(5272717383/10000000000 : ℝ)|=(5272717383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1112_box_14 (p : ℝ) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (671153597/1250000000 : ℝ)*x 0 + (1318179383/2500000000 : ℝ)*x 1 + (-275501779/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (671153597/1250000000 : ℝ)^8305 ≤ (43803463923673/100000000000000 : ℝ)^6257 := by
    have hnat : (671153597 : ℕ)^8305*100000000000000^6257 ≤ 43803463923673^6257*1250000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671153597 1250000000 43803463923673 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1318179383/2500000000 : ℝ)^8305 ≤ (42761474557429/100000000000000 : ℝ)^6257 := by
    have hnat : (1318179383 : ℕ)^8305*100000000000000^6257 ≤ 42761474557429^6257*2500000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318179383 2500000000 42761474557429 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (275501779/1250000000 : ℝ)^8305 ≤ (13435061508877/100000000000000 : ℝ)^6257 := by
    have hnat : (275501779 : ℕ)^8305*100000000000000^6257 ≤ 13435061508877^6257*1250000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275501779 1250000000 13435061508877 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8305/2048 : ℝ)) 8305 6257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(671153597/1250000000 : ℝ), (1318179383/2500000000 : ℝ), (-275501779/1250000000 : ℝ)] ![(43803463923673/100000000000000 : ℝ), (42761474557429/100000000000000 : ℝ), (13435061508877/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(671153597/1250000000 : ℝ)|^8305 ≤ (43803463923673/100000000000000 : ℝ)^6257
        have hw : |(671153597/1250000000 : ℝ)|=(671153597/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1318179383/2500000000 : ℝ)|^8305 ≤ (42761474557429/100000000000000 : ℝ)^6257
        have hw : |(1318179383/2500000000 : ℝ)|=(1318179383/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-275501779/1250000000 : ℝ)|^8305 ≤ (13435061508877/100000000000000 : ℝ)^6257
        have hw : |(-275501779/1250000000 : ℝ)|=(275501779/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1112_box_15 (p : ℝ) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2121198387/5000000000 : ℝ)*x 0 + (2217083077/5000000000 : ℝ)*x 1 + (4434166109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2121198387/5000000000 : ℝ)^8305 ≤ (801057096941/2500000000000 : ℝ)^6257 := by
    have hnat : (2121198387 : ℕ)^8305*2500000000000^6257 ≤ 801057096941^6257*5000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121198387 5000000000 801057096941 2500000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2217083077/5000000000 : ℝ)^8305 ≤ (33978858284527/100000000000000 : ℝ)^6257 := by
    have hnat : (2217083077 : ℕ)^8305*100000000000000^6257 ≤ 33978858284527^6257*5000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2217083077 5000000000 33978858284527 100000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4434166109/10000000000 : ℝ)^8305 ≤ (1359154313073/4000000000000 : ℝ)^6257 := by
    have hnat : (4434166109 : ℕ)^8305*4000000000000^6257 ≤ 1359154313073^6257*10000000000^8305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4434166109 10000000000 1359154313073 4000000000000 8305 6257 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8305/2048 : ℝ)) 8305 6257 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2121198387/5000000000 : ℝ), (2217083077/5000000000 : ℝ), (4434166109/10000000000 : ℝ)] ![(801057096941/2500000000000 : ℝ), (33978858284527/100000000000000 : ℝ), (1359154313073/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2121198387/5000000000 : ℝ)|^8305 ≤ (801057096941/2500000000000 : ℝ)^6257
        have hw : |(2121198387/5000000000 : ℝ)|=(2121198387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2217083077/5000000000 : ℝ)|^8305 ≤ (33978858284527/100000000000000 : ℝ)^6257
        have hw : |(2217083077/5000000000 : ℝ)|=(2217083077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4434166109/10000000000 : ℝ)|^8305 ≤ (1359154313073/4000000000000 : ℝ)^6257
        have hw : |(4434166109/10000000000 : ℝ)|=(4434166109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1112_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148888709/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14031/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5657/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(15557/25000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(2371/4000 : ℝ) ∧ (19929/25000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (83057/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14031/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5657/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14031/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5657/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14031/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5657/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14031/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5657/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14031/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5657/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14031/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5657/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5657/50000 : ℝ) ^ (519/128 : ℝ) ≤ (14544852860014477/100000000000000000000 : ℝ) := by
    have hpowers : (5657/50000 : ℝ)^519 ≤ (14544852860014477/100000000000000000000 : ℝ)^128 := by
      have hnat : (5657 : ℕ)^519*100000000000000000000^128 ≤ 14544852860014477^128*50000^519 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5657 50000 14544852860014477 100000000000000000000 519 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5657/50000 : ℝ)) (X := (14544852860014477/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 519 128 (by norm_num) hpowers
    exact h
  have hpowhi : (14031/100000 : ℝ) ^ (519/128 : ℝ) ≤ (1392422072344579/4000000000000000000 : ℝ) := by
    have hpowers : (14031/100000 : ℝ)^519 ≤ (1392422072344579/4000000000000000000 : ℝ)^128 := by
      have hnat : (14031 : ℕ)^519*4000000000000000000^128 ≤ 1392422072344579^128*100000^519 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14031 100000 1392422072344579 4000000000000000000 519 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14031/100000 : ℝ)) (X := (1392422072344579/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 519 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014544852860014477/50000000000000000000 : ℝ) ≤ (4883162771179/4882812500000 : ℝ) ^ (519/128 : ℝ) := by
    have hpowers : (50014544852860014477/50000000000000000000 : ℝ)^128 ≤ (4883162771179/4882812500000 : ℝ)^519 := by
      have hnat : (50014544852860014477 : ℕ)^128*4882812500000^519 ≤ 4883162771179^519*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014544852860014477 50000000000000000000 4883162771179 4882812500000 128 519 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (4883162771179/4882812500000 : ℝ)) (X := (50014544852860014477/50000000000000000000 : ℝ)) (by norm_num) 519 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (12506169425583578619/12500000000000000000 : ℝ) ≤ (10001217016882587/10000000000000000 : ℝ) ^ (519/128 : ℝ) := by
    have hpowers : (12506169425583578619/12500000000000000000 : ℝ)^128 ≤ (10001217016882587/10000000000000000 : ℝ)^519 := by
      have hnat : (12506169425583578619 : ℕ)^128*10000000000000000^519 ≤ 10001217016882587^519*12500000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506169425583578619 12500000000000000000 10001217016882587 10000000000000000 128 519 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001217016882587/10000000000000000 : ℝ)) (X := (12506169425583578619/12500000000000000000 : ℝ)) (by norm_num) 519 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (2001392422072344579/2000000000000000000 : ℝ) ≤ (5000858339195291/5000000000000000 : ℝ) ^ (519/128 : ℝ) := by
    have hpowers : (2001392422072344579/2000000000000000000 : ℝ)^128 ≤ (5000858339195291/5000000000000000 : ℝ)^519 := by
      have hnat : (2001392422072344579 : ℕ)^128*5000000000000000^519 ≤ 5000858339195291^519*2000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2001392422072344579 2000000000000000000 5000858339195291 5000000000000000 128 519 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000858339195291/5000000000000000 : ℝ)) (X := (2001392422072344579/2000000000000000000 : ℝ)) (by norm_num) 519 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14544852860014477/100000000000000000000 : ℝ) ≤ ((27490529062702283/27500000000000000 : ℝ)+2*(404584217/220000000000 : ℝ)*(5657/50000 : ℝ))^(519/128 : ℝ) := by
    rw [show (27490529062702283/27500000000000000 : ℝ)+2*(404584217/220000000000 : ℝ)*(5657/50000 : ℝ)=(4883162771179/4882812500000 : ℝ) by norm_num, show 1+2*(14544852860014477/100000000000000000000 : ℝ)=(50014544852860014477/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1392422072344579/4000000000000000000 : ℝ)+(14544852860014477/100000000000000000000 : ℝ) ≤ ((27490529062702283/27500000000000000 : ℝ)+(404584217/220000000000 : ℝ)*((14031/100000 : ℝ)+(5657/50000 : ℝ)))^(519/128 : ℝ) := by
    rw [show (27490529062702283/27500000000000000 : ℝ)+(404584217/220000000000 : ℝ)*((14031/100000 : ℝ)+(5657/50000 : ℝ))=(10001217016882587/10000000000000000 : ℝ) by norm_num, show 1+(1392422072344579/4000000000000000000 : ℝ)+(14544852860014477/100000000000000000000 : ℝ)=(12506169425583578619/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1392422072344579/4000000000000000000 : ℝ) ≤ ((27490529062702283/27500000000000000 : ℝ)+2*(404584217/220000000000 : ℝ)*(14031/100000 : ℝ))^(519/128 : ℝ) := by
    rw [show (27490529062702283/27500000000000000 : ℝ)+2*(404584217/220000000000 : ℝ)*(14031/100000 : ℝ)=(5000858339195291/5000000000000000 : ℝ) by norm_num, show 1+2*(1392422072344579/4000000000000000000 : ℝ)=(2001392422072344579/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27490529062702283/27500000000000000 : ℝ)*(X 1 0+X 2 0)+(404584217/220000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (519/128 : ℝ)) (lo := (5657/50000 : ℝ)) (hi := (14031/100000 : ℝ)) (c := (27490529062702283/27500000000000000 : ℝ)) (alpha := (404584217/220000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27490529062702283/27500000000000000 : ℝ)*(X 0 1+X 2 1)+(404584217/220000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (519/128 : ℝ)) (lo := (5657/50000 : ℝ)) (hi := (14031/100000 : ℝ)) (c := (27490529062702283/27500000000000000 : ℝ)) (alpha := (404584217/220000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27490529062702283/27500000000000000 : ℝ)*(X 0 2+X 1 2)+(404584217/220000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (519/128 : ℝ)) (lo := (5657/50000 : ℝ)) (hi := (14031/100000 : ℝ)) (c := (27490529062702283/27500000000000000 : ℝ)) (alpha := (404584217/220000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-256677209/1250000000 : ℝ)*X 0 0+(1344184191/2500000000 : ℝ)*X 0 1+(1344184169/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1112_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5295691833/10000000000 : ℝ)*X 1 0+(-2163252077/10000000000 : ℝ)*X 1 1+(268836841/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1112_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5295691951/10000000000 : ℝ)*X 2 0+(1344184151/2500000000 : ℝ)*X 2 1+(-2163252211/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1112_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4476795799/10000000000 : ℝ)*X 0 0+(269819347/625000000 : ℝ)*X 0 1+(2158554989/5000000000 : ℝ)*X 0 2+(4476795799/10000000000 : ℝ)*X 1 0+(269819347/625000000 : ℝ)*X 1 1+(2158554989/5000000000 : ℝ)*X 1 2+(4476795799/10000000000 : ℝ)*X 2 0+(269819347/625000000 : ℝ)*X 2 1+(2158554989/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1112_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-577651451/2500000000 : ℝ)*X 0 0+(660092757/1250000000 : ℝ)*X 0 1+(5280742827/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1112_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2681778983/5000000000 : ℝ)*X 1 0+(-440184459/2000000000 : ℝ)*X 1 1+(26403713/50000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1112_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5363557861/10000000000 : ℝ)*X 2 0+(5280742361/10000000000 : ℝ)*X 2 1+(-1100461377/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1112_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2130346721/5000000000 : ℝ)*X 0 0+(88502797/200000000 : ℝ)*X 0 1+(35401119/80000000 : ℝ)*X 0 2+(2130346721/5000000000 : ℝ)*X 1 0+(88502797/200000000 : ℝ)*X 1 1+(35401119/80000000 : ℝ)*X 1 2+(2130346721/5000000000 : ℝ)*X 2 0+(88502797/200000000 : ℝ)*X 2 1+(35401119/80000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1112_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-451371831/2000000000 : ℝ)*X 0 0+(5215515019/10000000000 : ℝ)*X 0 1+(269317173/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1112_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5288896653/10000000000 : ℝ)*X 1 0+(-2159412353/10000000000 : ℝ)*X 1 1+(2693171727/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1112_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2644448379/5000000000 : ℝ)*X 2 0+(5386343439/10000000000 : ℝ)*X 2 1+(-2159412233/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1112_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2249074703/5000000000 : ℝ)*X 0 0+(4306292387/10000000000 : ℝ)*X 0 1+(269143277/625000000 : ℝ)*X 0 2+(2249074703/5000000000 : ℝ)*X 1 0+(4306292387/10000000000 : ℝ)*X 1 1+(269143277/625000000 : ℝ)*X 1 2+(2249074703/5000000000 : ℝ)*X 2 0+(4306292387/10000000000 : ℝ)*X 2 1+(269143277/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1112_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1053751297/5000000000 : ℝ)*X 0 0+(170020749/312500000 : ℝ)*X 0 1+(5272717451/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1112_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1073845849/2000000000 : ℝ)*X 1 0+(-1102006901/5000000000 : ℝ)*X 1 1+(5272717383/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1112_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((671153597/1250000000 : ℝ)*X 2 0+(1318179383/2500000000 : ℝ)*X 2 1+(-275501779/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1112_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2121198387/5000000000 : ℝ)*X 0 0+(2217083077/5000000000 : ℝ)*X 0 1+(4434166109/10000000000 : ℝ)*X 0 2+(2121198387/5000000000 : ℝ)*X 1 0+(2217083077/5000000000 : ℝ)*X 1 1+(4434166109/10000000000 : ℝ)*X 1 2+(2121198387/5000000000 : ℝ)*X 2 0+(2217083077/5000000000 : ℝ)*X 2 1+(4434166109/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1112_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-15557/25000 : ℝ) ≤ (-835547997795677085147405009/1342773437500000000000000000 : ℝ) := by norm_num
    linear_combination (74467959/50000000000000 : ℝ)*(lower0) + (18573919/50000000000000 : ℝ)*(lower3) + (67735529/25000000000000 : ℝ)*(lower4) + (973783794082023/25000000000000 : ℝ)*(major0) + (973783794082023/25000000000000 : ℝ)*(major1) + (973783794082023/25000000000000 : ℝ)*(major2) + (6441560283/100000000000000 : ℝ)*(sp1) + (1197730953/3125000000000 : ℝ)*(sp2) + (9986628211/100000000000000 : ℝ)*(sp3) + (2597424935435827/50000000000000 : ℝ)*(sp4) + (5194867030117513/100000000000000 : ℝ)*(sp5) + (51948351442873/1000000000000 : ℝ)*(sp6) + (327016092550567/12500000000000 : ℝ)*(sp7) + (23600806141/100000000000000 : ℝ)*(sp12) + (654034681758187/25000000000000 : ℝ)*(f.failure) + (1298718367919449/25000000000000 : ℝ)*(f.sum) + (14596805723/11000000000000000000000000 : ℝ)*base65 + (3437501166233509/687500000000000000000000000000 : ℝ)*base67 + (3704377925421009/687500000000000000000000000000 : ℝ)*base69 + (7577332869108509/687500000000000000000000000000 : ℝ)*base71 + (80598153221/5500000000000000000000000 : ℝ)*base74 + (30321955358509/687500000000000000000000000000 : ℝ)*base75 + (8655995826046009/687500000000000000000000000000 : ℝ)*base77 + (15923408239516491/687500000000000000000000000000 : ℝ)*base80 + (24175578721/5500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (12610583/2500000000000000000000 : ℝ)*base89 + (12610583/2500000000000000000000 : ℝ)*base91 + (12610583/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (2371/4000 : ℝ) ≤ (20376755925800493165875211387/34375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (47214743/100000000000000 : ℝ)*(upper0) + (47076459/50000000000000 : ℝ)*(upper2) + (3281997/50000000000000 : ℝ)*(upper3) + (29446721/100000000000000 : ℝ)*(upper4) + (36713663/50000000000000 : ℝ)*(upper5) + (197938827594837/5000000000000 : ℝ)*(major0) + (197938827594837/5000000000000 : ℝ)*(major1) + (197938827594837/5000000000000 : ℝ)*(major2) + (2619455419585869/50000000000000 : ℝ)*(sp0) + (2619451832061441/50000000000000 : ℝ)*(sp1) + (5238796300758313/100000000000000 : ℝ)*(sp2) + (20772523329283/781250000000 : ℝ)*(sp3) + (896881107/12500000000000 : ℝ)*(sp5) + (7158650839/6250000000000 : ℝ)*(sp10) + (20772523329283/781250000000 : ℝ)*(f.failure) + (2619455419585869/50000000000000 : ℝ)*(f.sum) + (637408743/550000000000000000000000 : ℝ)*base66 + (1443929554037871/137500000000000000000000000000 : ℝ)*base67 + (1150569113037871/137500000000000000000000000000 : ℝ)*base69 + (1369733303062871/137500000000000000000000000000 : ℝ)*base71 + (28492382387/5500000000000000000000000 : ℝ)*base74 + (814090394637871/137500000000000000000000000000 : ℝ)*base75 + (1554820890775371/137500000000000000000000000000 : ℝ)*base77 + (8082336969912129/137500000000000000000000000000 : ℝ)*base80 + (8106436973/11000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (359353/78125000000000000000 : ℝ)*base90 + (359353/78125000000000000000 : ℝ)*base92 + (359353/78125000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (19929/25000 : ℝ) ≤ (548062830908313734537847055647/687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1006031/100000000000000 : ℝ)*(lower1) + (20991751/25000000000000 : ℝ)*(lower3) + (3692643/6250000000000 : ℝ)*(upper4) + (2213413864306699/50000000000000 : ℝ)*(major0) + (2213413864306699/50000000000000 : ℝ)*(major1) + (2213413864306699/50000000000000 : ℝ)*(major2) + (526528749/10000000000000 : ℝ)*(sp0) + (87967254277/100000000000000 : ℝ)*(sp1) + (4223010001/5000000000000 : ℝ)*(sp2) + (76927872507/100000000000000 : ℝ)*(sp3) + (5853831352027377/100000000000000 : ℝ)*(sp8) + (5853748650060591/100000000000000 : ℝ)*(sp9) + (5853752157114847/100000000000000 : ℝ)*(sp10) + (2973169168722633/100000000000000 : ℝ)*(sp11) + (148662304829757/5000000000000 : ℝ)*(f.failure) + (5853836617314867/100000000000000 : ℝ)*(f.sum) + (724069877/1100000000000000000000000 : ℝ)*base66 + (18202457832618817/1375000000000000000000000000000 : ℝ)*base67 + (458445002118817/1375000000000000000000000000000 : ℝ)*base69 + (3537139036743817/1375000000000000000000000000000 : ℝ)*base71 + (60235242653/11000000000000000000000000 : ℝ)*base73 + (28683464910368817/1375000000000000000000000000000 : ℝ)*base75 + (13759324386493817/1375000000000000000000000000000 : ℝ)*base77 + (17310751921368817/1375000000000000000000000000000 : ℝ)*base79 + (40540091547/440000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (5486287/500000000000000000000 : ℝ)*base90 + (5486287/500000000000000000000 : ℝ)*base92 + (5486287/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-83057/100000 : ℝ) ≤ (-913600538027474669013171/1100000000000000000000000 : ℝ) := by norm_num
    linear_combination (2147721/3125000000000 : ℝ)*(lower0) + (47597411/25000000000000 : ℝ)*(upper3) + (298327281/100000000000000 : ℝ)*(lower4) + (1115401236369161/25000000000000 : ℝ)*(major0) + (1115401236369161/25000000000000 : ℝ)*(major1) + (1115401236369161/25000000000000 : ℝ)*(major2) + (161504627/100000000000000 : ℝ)*(sp0) + (36223129497/12500000000000 : ℝ)*(sp5) + (323433205089/100000000000000 : ℝ)*(sp6) + (78108635469/50000000000000 : ℝ)*(sp7) + (297714531859973/5000000000000 : ℝ)*(sp12) + (5954001013668111/100000000000000 : ℝ)*(sp13) + (2976983682749499/50000000000000 : ℝ)*(sp14) + (1498223869883481/50000000000000 : ℝ)*(sp15) + (29966039570379/1000000000000 : ℝ)*(f.failure) + (5954290798704087/100000000000000 : ℝ)*(f.sum) + (8648277537/2750000000000000000000000 : ℝ)*base65 + (7795702935369563/687500000000000000000000000000 : ℝ)*base67 + (4722552927380437/687500000000000000000000000000 : ℝ)*base70 + (8640288133557063/687500000000000000000000000000 : ℝ)*base71 + (233147746091/5500000000000000000000000 : ℝ)*base73 + (2394591853067937/687500000000000000000000000000 : ℝ)*base76 + (8492179963182063/687500000000000000000000000000 : ℝ)*base77 + (18444827147567937/687500000000000000000000000000 : ℝ)*base80 + (11528435439/5500000000000000000000000 : ℝ)*base82 + (49289/100000000000000000000 : ℝ)*base90 + (49289/100000000000000000000 : ℝ)*base92 + (49289/100000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1112_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148888709/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14031/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5657/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15557/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(2371/4000 : ℝ) else (19929/25000 : ℝ) ≤ X j i ∧ X j i ≤ (83057/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1112_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1112_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148888709/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14031/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5657/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15557/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(2371/4000 : ℝ) else (19929/25000 : ℝ) ≤ X j i ∧ X j i ≤ (83057/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1112_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (519/128 : ℝ) ≤ p) (hpb : p ≤ (8305/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148888709/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14031/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5657/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15557/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(2371/4000 : ℝ) else (19929/25000 : ℝ) ≤ X j i ∧ X j i ≤ (83057/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1112_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
