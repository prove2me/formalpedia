-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1511_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:55:35.620466+00:00
-- url     : https://prove2.me/submissions/128ee9aa-e707-4d82-bd5b-0a44f38a631b

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
theorem support_rectangle_w1511_s3_0 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1868992531/10000000000 : ℝ)*x 0 + (2718337821/5000000000 : ℝ)*x 1 + (5214606059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1868992531/10000000000 : ℝ)^4519 ≤ (5716969579371/50000000000000 : ℝ)^3495 := by
    have hnat : (1868992531 : ℕ)^4519*50000000000000^3495 ≤ 5716969579371^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1868992531 10000000000 5716969579371 50000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2718337821/5000000000 : ℝ)^4519 ≤ (11369170393343/25000000000000 : ℝ)^3495 := by
    have hnat : (2718337821 : ℕ)^4519*25000000000000^3495 ≤ 11369170393343^3495*5000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718337821 5000000000 11369170393343 25000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5214606059/10000000000 : ℝ)^4519 ≤ (1723575170229/4000000000000 : ℝ)^3495 := by
    have hnat : (5214606059 : ℕ)^4519*4000000000000^3495 ≤ 1723575170229^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5214606059 10000000000 1723575170229 4000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1868992531/10000000000 : ℝ), (2718337821/5000000000 : ℝ), (5214606059/10000000000 : ℝ)] ![(5716969579371/50000000000000 : ℝ), (11369170393343/25000000000000 : ℝ), (1723575170229/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1868992531/10000000000 : ℝ)|^4519 ≤ (5716969579371/50000000000000 : ℝ)^3495
        have hw : |(-1868992531/10000000000 : ℝ)|=(1868992531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2718337821/5000000000 : ℝ)|^4519 ≤ (11369170393343/25000000000000 : ℝ)^3495
        have hw : |(2718337821/5000000000 : ℝ)|=(2718337821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5214606059/10000000000 : ℝ)|^4519 ≤ (1723575170229/4000000000000 : ℝ)^3495
        have hw : |(5214606059/10000000000 : ℝ)|=(5214606059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1511_s3_1 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338128121/2500000000 : ℝ)*x 0 + (-1982806483/10000000000 : ℝ)*x 1 + (1042921231/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338128121/2500000000 : ℝ)^4519 ≤ (22284239345803/50000000000000 : ℝ)^3495 := by
    have hnat : (1338128121 : ℕ)^4519*50000000000000^3495 ≤ 22284239345803^3495*2500000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338128121 2500000000 22284239345803 50000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1982806483/10000000000 : ℝ)^4519 ≤ (12342141017143/100000000000000 : ℝ)^3495 := by
    have hnat : (1982806483 : ℕ)^4519*100000000000000^3495 ≤ 12342141017143^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1982806483 10000000000 12342141017143 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1042921231/2000000000 : ℝ)^4519 ≤ (10772345070353/25000000000000 : ℝ)^3495 := by
    have hnat : (1042921231 : ℕ)^4519*25000000000000^3495 ≤ 10772345070353^3495*2000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042921231 2000000000 10772345070353 25000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338128121/2500000000 : ℝ), (-1982806483/10000000000 : ℝ), (1042921231/2000000000 : ℝ)] ![(22284239345803/50000000000000 : ℝ), (12342141017143/100000000000000 : ℝ), (10772345070353/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338128121/2500000000 : ℝ)|^4519 ≤ (22284239345803/50000000000000 : ℝ)^3495
        have hw : |(1338128121/2500000000 : ℝ)|=(1338128121/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1982806483/10000000000 : ℝ)|^4519 ≤ (12342141017143/100000000000000 : ℝ)^3495
        have hw : |(-1982806483/10000000000 : ℝ)|=(1982806483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1042921231/2000000000 : ℝ)|^4519 ≤ (10772345070353/25000000000000 : ℝ)^3495
        have hw : |(1042921231/2000000000 : ℝ)|=(1042921231/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1511_s3_2 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352512599/10000000000 : ℝ)*x 0 + (260730303/500000000 : ℝ)*x 1 + (-396561291/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352512599/10000000000 : ℝ)^4519 ≤ (44568479929727/100000000000000 : ℝ)^3495 := by
    have hnat : (5352512599 : ℕ)^4519*100000000000000^3495 ≤ 44568479929727^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352512599 10000000000 44568479929727 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (260730303/500000000 : ℝ)^4519 ≤ (43089379266409/100000000000000 : ℝ)^3495 := by
    have hnat : (260730303 : ℕ)^4519*100000000000000^3495 ≤ 43089379266409^3495*500000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260730303 500000000 43089379266409 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (396561291/2000000000 : ℝ)^4519 ≤ (1234214079179/10000000000000 : ℝ)^3495 := by
    have hnat : (396561291 : ℕ)^4519*10000000000000^3495 ≤ 1234214079179^3495*2000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      396561291 2000000000 1234214079179 10000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352512599/10000000000 : ℝ), (260730303/500000000 : ℝ), (-396561291/2000000000 : ℝ)] ![(44568479929727/100000000000000 : ℝ), (43089379266409/100000000000000 : ℝ), (1234214079179/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352512599/10000000000 : ℝ)|^4519 ≤ (44568479929727/100000000000000 : ℝ)^3495
        have hw : |(5352512599/10000000000 : ℝ)|=(5352512599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(260730303/500000000 : ℝ)|^4519 ≤ (43089379266409/100000000000000 : ℝ)^3495
        have hw : |(260730303/500000000 : ℝ)|=(260730303/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-396561291/2000000000 : ℝ)|^4519 ≤ (1234214079179/10000000000000 : ℝ)^3495
        have hw : |(-396561291/2000000000 : ℝ)|=(396561291/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1511_s3_3 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2134961501/5000000000 : ℝ)*x 0 + (2012308613/5000000000 : ℝ)*x 1 + (4527824561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2134961501/5000000000 : ℝ)^4519 ≤ (33276436884021/100000000000000 : ℝ)^3495 := by
    have hnat : (2134961501 : ℕ)^4519*100000000000000^3495 ≤ 33276436884021^3495*5000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2134961501 5000000000 33276436884021 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2012308613/5000000000 : ℝ)^4519 ≤ (30825692553141/100000000000000 : ℝ)^3495 := by
    have hnat : (2012308613 : ℕ)^4519*100000000000000^3495 ≤ 30825692553141^3495*5000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2012308613 5000000000 30825692553141 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4527824561/10000000000 : ℝ)^4519 ≤ (3589787054997/10000000000000 : ℝ)^3495 := by
    have hnat : (4527824561 : ℕ)^4519*10000000000000^3495 ≤ 3589787054997^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4527824561 10000000000 3589787054997 10000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2134961501/5000000000 : ℝ), (2012308613/5000000000 : ℝ), (4527824561/10000000000 : ℝ)] ![(33276436884021/100000000000000 : ℝ), (30825692553141/100000000000000 : ℝ), (3589787054997/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2134961501/5000000000 : ℝ)|^4519 ≤ (33276436884021/100000000000000 : ℝ)^3495
        have hw : |(2134961501/5000000000 : ℝ)|=(2134961501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2012308613/5000000000 : ℝ)|^4519 ≤ (30825692553141/100000000000000 : ℝ)^3495
        have hw : |(2012308613/5000000000 : ℝ)|=(2012308613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4527824561/10000000000 : ℝ)|^4519 ≤ (3589787054997/10000000000000 : ℝ)^3495
        have hw : |(4527824561/10000000000 : ℝ)|=(4527824561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1511_s3_4 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-934511867/5000000000 : ℝ)*x 0 + (5215782089/10000000000 : ℝ)*x 1 + (5435490997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (934511867/5000000000 : ℝ)^4519 ≤ (11434185979047/100000000000000 : ℝ)^3495 := by
    have hnat : (934511867 : ℕ)^4519*100000000000000^3495 ≤ 11434185979047^3495*5000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      934511867 5000000000 11434185979047 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5215782089/10000000000 : ℝ)^4519 ≤ (10775486166273/25000000000000 : ℝ)^3495 := by
    have hnat : (5215782089 : ℕ)^4519*25000000000000^3495 ≤ 10775486166273^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215782089 10000000000 10775486166273 25000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5435490997/10000000000 : ℝ)^4519 ≤ (1136596733481/2500000000000 : ℝ)^3495 := by
    have hnat : (5435490997 : ℕ)^4519*2500000000000^3495 ≤ 1136596733481^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435490997 10000000000 1136596733481 2500000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-934511867/5000000000 : ℝ), (5215782089/10000000000 : ℝ), (5435490997/10000000000 : ℝ)] ![(11434185979047/100000000000000 : ℝ), (10775486166273/25000000000000 : ℝ), (1136596733481/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-934511867/5000000000 : ℝ)|^4519 ≤ (11434185979047/100000000000000 : ℝ)^3495
        have hw : |(-934511867/5000000000 : ℝ)|=(934511867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5215782089/10000000000 : ℝ)|^4519 ≤ (10775486166273/25000000000000 : ℝ)^3495
        have hw : |(5215782089/10000000000 : ℝ)|=(5215782089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5435490997/10000000000 : ℝ)|^4519 ≤ (1136596733481/2500000000000 : ℝ)^3495
        have hw : |(5435490997/10000000000 : ℝ)|=(5435490997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1511_s3_5 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647111837/5000000000 : ℝ)*x 0 + (-1761921441/10000000000 : ℝ)*x 1 + (5435491163/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647111837/5000000000 : ℝ)^4519 ≤ (43941929338007/100000000000000 : ℝ)^3495 := by
    have hnat : (2647111837 : ℕ)^4519*100000000000000^3495 ≤ 43941929338007^3495*5000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647111837 5000000000 43941929338007 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1761921441/10000000000 : ℝ)^4519 ≤ (10594199523773/100000000000000 : ℝ)^3495 := by
    have hnat : (1761921441 : ℕ)^4519*100000000000000^3495 ≤ 10594199523773^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1761921441 10000000000 10594199523773 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5435491163/10000000000 : ℝ)^4519 ≤ (22731935567257/50000000000000 : ℝ)^3495 := by
    have hnat : (5435491163 : ℕ)^4519*50000000000000^3495 ≤ 22731935567257^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435491163 10000000000 22731935567257 50000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647111837/5000000000 : ℝ), (-1761921441/10000000000 : ℝ), (5435491163/10000000000 : ℝ)] ![(43941929338007/100000000000000 : ℝ), (10594199523773/100000000000000 : ℝ), (22731935567257/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647111837/5000000000 : ℝ)|^4519 ≤ (43941929338007/100000000000000 : ℝ)^3495
        have hw : |(2647111837/5000000000 : ℝ)|=(2647111837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1761921441/10000000000 : ℝ)|^4519 ≤ (10594199523773/100000000000000 : ℝ)^3495
        have hw : |(-1761921441/10000000000 : ℝ)|=(1761921441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5435491163/10000000000 : ℝ)|^4519 ≤ (22731935567257/50000000000000 : ℝ)^3495
        have hw : |(5435491163/10000000000 : ℝ)|=(5435491163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1511_s3_6 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (42353791/80000000 : ℝ)*x 0 + (5435490921/10000000000 : ℝ)*x 1 + (-3523843/20000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42353791/80000000 : ℝ)^4519 ≤ (5492741436887/12500000000000 : ℝ)^3495 := by
    have hnat : (42353791 : ℕ)^4519*12500000000000^3495 ≤ 5492741436887^3495*80000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42353791 80000000 5492741436887 12500000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5435490921/10000000000 : ℝ)^4519 ≤ (45463868517307/100000000000000 : ℝ)^3495 := by
    have hnat : (5435490921 : ℕ)^4519*100000000000000^3495 ≤ 45463868517307^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435490921 10000000000 45463868517307 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3523843/20000000 : ℝ)^4519 ≤ (5297099991237/50000000000000 : ℝ)^3495 := by
    have hnat : (3523843 : ℕ)^4519*50000000000000^3495 ≤ 5297099991237^3495*20000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3523843 20000000 5297099991237 50000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42353791/80000000 : ℝ), (5435490921/10000000000 : ℝ), (-3523843/20000000 : ℝ)] ![(5492741436887/12500000000000 : ℝ), (45463868517307/100000000000000 : ℝ), (5297099991237/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42353791/80000000 : ℝ)|^4519 ≤ (5492741436887/12500000000000 : ℝ)^3495
        have hw : |(42353791/80000000 : ℝ)|=(42353791/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5435490921/10000000000 : ℝ)|^4519 ≤ (45463868517307/100000000000000 : ℝ)^3495
        have hw : |(5435490921/10000000000 : ℝ)|=(5435490921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3523843/20000000 : ℝ)|^4519 ≤ (5297099991237/50000000000000 : ℝ)^3495
        have hw : |(-3523843/20000000 : ℝ)|=(3523843/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1511_s3_7 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2134997281/5000000000 : ℝ)*x 0 + (2262579977/5000000000 : ℝ)*x 1 + (4027302103/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2134997281/5000000000 : ℝ)^4519 ≤ (33277157963827/100000000000000 : ℝ)^3495 := by
    have hnat : (2134997281 : ℕ)^4519*100000000000000^3495 ≤ 33277157963827^3495*5000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2134997281 5000000000 33277157963827 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2262579977/5000000000 : ℝ)^4519 ≤ (1793527875709/5000000000000 : ℝ)^3495 := by
    have hnat : (2262579977 : ℕ)^4519*5000000000000^3495 ≤ 1793527875709^3495*5000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2262579977 5000000000 1793527875709 5000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4027302103/10000000000 : ℝ)^4519 ≤ (7713071126787/25000000000000 : ℝ)^3495 := by
    have hnat : (4027302103 : ℕ)^4519*25000000000000^3495 ≤ 7713071126787^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4027302103 10000000000 7713071126787 25000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2134997281/5000000000 : ℝ), (2262579977/5000000000 : ℝ), (4027302103/10000000000 : ℝ)] ![(33277157963827/100000000000000 : ℝ), (1793527875709/5000000000000 : ℝ), (7713071126787/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2134997281/5000000000 : ℝ)|^4519 ≤ (33277157963827/100000000000000 : ℝ)^3495
        have hw : |(2134997281/5000000000 : ℝ)|=(2134997281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2262579977/5000000000 : ℝ)|^4519 ≤ (1793527875709/5000000000000 : ℝ)^3495
        have hw : |(2262579977/5000000000 : ℝ)|=(2262579977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4027302103/10000000000 : ℝ)|^4519 ≤ (7713071126787/25000000000000 : ℝ)^3495
        have hw : |(4027302103/10000000000 : ℝ)|=(4027302103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1511_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163299369/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4/25 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2087/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (339/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15551/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4/25 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2087/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4/25 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2087/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4/25 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2087/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4/25 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2087/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4/25 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2087/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4/25 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2087/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2087/20000 : ℝ) ^ (4517/1024 : ℝ) ≤ (4682091056024417/100000000000000000000 : ℝ) := by
    have hpowers : (2087/20000 : ℝ)^4517 ≤ (4682091056024417/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2087 : ℕ)^4517*100000000000000000000^1024 ≤ 4682091056024417^1024*20000^4517 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2087 20000 4682091056024417 100000000000000000000 4517 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2087/20000 : ℝ)) (X := (4682091056024417/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4517 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4/25 : ℝ) ^ (4517/1024 : ℝ) ≤ (30850878876554711/100000000000000000000 : ℝ) := by
    have hpowers : (4/25 : ℝ)^4517 ≤ (30850878876554711/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4 : ℕ)^4517*100000000000000000000^1024 ≤ 30850878876554711^1024*25^4517 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4 25 30850878876554711 100000000000000000000 4517 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4/25 : ℝ)) (X := (30850878876554711/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4517 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004682091056024417/50000000000000000000 : ℝ) ≤ (5000106138757131/5000000000000000 : ℝ) ^ (4517/1024 : ℝ) := by
    have hpowers : (50004682091056024417/50000000000000000000 : ℝ)^1024 ≤ (5000106138757131/5000000000000000 : ℝ)^4517 := by
      have hnat : (50004682091056024417 : ℕ)^1024*5000000000000000^4517 ≤ 5000106138757131^4517*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004682091056024417 50000000000000000000 5000106138757131 5000000000000000 1024 4517 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000106138757131/5000000000000000 : ℝ)) (X := (50004682091056024417/50000000000000000000 : ℝ)) (by norm_num) 4517 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12504441621241572391/12500000000000000000 : ℝ) ≤ (5000402709356651/5000000000000000 : ℝ) ^ (4517/1024 : ℝ) := by
    have hpowers : (12504441621241572391/12500000000000000000 : ℝ)^1024 ≤ (5000402709356651/5000000000000000 : ℝ)^4517 := by
      have hnat : (12504441621241572391 : ℕ)^1024*5000000000000000^4517 ≤ 5000402709356651^4517*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12504441621241572391 12500000000000000000 5000402709356651 5000000000000000 1024 4517 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000402709356651/5000000000000000 : ℝ)) (X := (12504441621241572391/12500000000000000000 : ℝ)) (by norm_num) 4517 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50030850878876554711/50000000000000000000 : ℝ) ≤ (5000699279956171/5000000000000000 : ℝ) ^ (4517/1024 : ℝ) := by
    have hpowers : (50030850878876554711/50000000000000000000 : ℝ)^1024 ≤ (5000699279956171/5000000000000000 : ℝ)^4517 := by
      have hnat : (50030850878876554711 : ℕ)^1024*5000000000000000^4517 ≤ 5000699279956171^4517*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030850878876554711 50000000000000000000 5000699279956171 5000000000000000 1024 4517 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000699279956171/5000000000000000 : ℝ)) (X := (50030850878876554711/50000000000000000000 : ℝ)) (by norm_num) 4517 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4682091056024417/100000000000000000000 : ℝ) ≤ ((5563880246754290323/5565000000000000000 : ℝ)+2*(1853566247/1739062500000 : ℝ)*(2087/20000 : ℝ))^(4517/1024 : ℝ) := by
    rw [show (5563880246754290323/5565000000000000000 : ℝ)+2*(1853566247/1739062500000 : ℝ)*(2087/20000 : ℝ)=(5000106138757131/5000000000000000 : ℝ) by norm_num, show 1+2*(4682091056024417/100000000000000000000 : ℝ)=(50004682091056024417/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30850878876554711/100000000000000000000 : ℝ)+(4682091056024417/100000000000000000000 : ℝ) ≤ ((5563880246754290323/5565000000000000000 : ℝ)+(1853566247/1739062500000 : ℝ)*((4/25 : ℝ)+(2087/20000 : ℝ)))^(4517/1024 : ℝ) := by
    rw [show (5563880246754290323/5565000000000000000 : ℝ)+(1853566247/1739062500000 : ℝ)*((4/25 : ℝ)+(2087/20000 : ℝ))=(5000402709356651/5000000000000000 : ℝ) by norm_num, show 1+(30850878876554711/100000000000000000000 : ℝ)+(4682091056024417/100000000000000000000 : ℝ)=(12504441621241572391/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30850878876554711/100000000000000000000 : ℝ) ≤ ((5563880246754290323/5565000000000000000 : ℝ)+2*(1853566247/1739062500000 : ℝ)*(4/25 : ℝ))^(4517/1024 : ℝ) := by
    rw [show (5563880246754290323/5565000000000000000 : ℝ)+2*(1853566247/1739062500000 : ℝ)*(4/25 : ℝ)=(5000699279956171/5000000000000000 : ℝ) by norm_num, show 1+2*(30850878876554711/100000000000000000000 : ℝ)=(50030850878876554711/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5563880246754290323/5565000000000000000 : ℝ)*(X 1 0+X 2 0)+(1853566247/1739062500000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4517/1024 : ℝ)) (lo := (2087/20000 : ℝ)) (hi := (4/25 : ℝ)) (c := (5563880246754290323/5565000000000000000 : ℝ)) (alpha := (1853566247/1739062500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5563880246754290323/5565000000000000000 : ℝ)*(X 0 1+X 2 1)+(1853566247/1739062500000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4517/1024 : ℝ)) (lo := (2087/20000 : ℝ)) (hi := (4/25 : ℝ)) (c := (5563880246754290323/5565000000000000000 : ℝ)) (alpha := (1853566247/1739062500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5563880246754290323/5565000000000000000 : ℝ)*(X 0 2+X 1 2)+(1853566247/1739062500000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4517/1024 : ℝ)) (lo := (2087/20000 : ℝ)) (hi := (4/25 : ℝ)) (c := (5563880246754290323/5565000000000000000 : ℝ)) (alpha := (1853566247/1739062500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1868992531/10000000000 : ℝ)*X 0 0+(2718337821/5000000000 : ℝ)*X 0 1+(5214606059/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338128121/2500000000 : ℝ)*X 1 0+(-1982806483/10000000000 : ℝ)*X 1 1+(1042921231/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352512599/10000000000 : ℝ)*X 2 0+(260730303/500000000 : ℝ)*X 2 1+(-396561291/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2134961501/5000000000 : ℝ)*X 0 0+(2012308613/5000000000 : ℝ)*X 0 1+(4527824561/10000000000 : ℝ)*X 0 2+(2134961501/5000000000 : ℝ)*X 1 0+(2012308613/5000000000 : ℝ)*X 1 1+(4527824561/10000000000 : ℝ)*X 1 2+(2134961501/5000000000 : ℝ)*X 2 0+(2012308613/5000000000 : ℝ)*X 2 1+(4527824561/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-934511867/5000000000 : ℝ)*X 0 0+(5215782089/10000000000 : ℝ)*X 0 1+(5435490997/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2647111837/5000000000 : ℝ)*X 1 0+(-1761921441/10000000000 : ℝ)*X 1 1+(5435491163/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((42353791/80000000 : ℝ)*X 2 0+(5435490921/10000000000 : ℝ)*X 2 1+(-3523843/20000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2134997281/5000000000 : ℝ)*X 0 0+(2262579977/5000000000 : ℝ)*X 0 1+(4027302103/10000000000 : ℝ)*X 0 2+(2134997281/5000000000 : ℝ)*X 1 0+(2262579977/5000000000 : ℝ)*X 1 1+(4027302103/10000000000 : ℝ)*X 1 2+(2134997281/5000000000 : ℝ)*X 2 0+(2262579977/5000000000 : ℝ)*X 2 1+(4027302103/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15699762294256367239443/1855000000000000000000000000 : ℝ) := by norm_num
    linear_combination (116985501/6250000000000 : ℝ)*(base19) + (1785191439/100000000000000 : ℝ)*(base23) + (321848107/100000000000000 : ℝ)*(upper3) + (98126411/100000000000000 : ℝ)*(upper4) + (46972569/20000000000000 : ℝ)*(upper5) + (3245214009127551/100000000000000 : ℝ)*(major0) + (3245214009127551/100000000000000 : ℝ)*(major1) + (3245214009127551/100000000000000 : ℝ)*(major2) + (4503120834264311/100000000000000 : ℝ)*(sp0) + (2251573449987737/50000000000000 : ℝ)*(sp1) + (1125786746638013/25000000000000 : ℝ)*(sp2) + (1987264803628177/100000000000000 : ℝ)*(sp3) + (27937479179/100000000000000 : ℝ)*(sp4) + (7080383651/50000000000000 : ℝ)*(sp7) + (993639482197739/50000000000000 : ℝ)*(f.failure) + (450314877174349/10000000000000 : ℝ)*(f.sum) + (9371711370369/1855000000000000000000000000 : ℝ)*base66 + (454470086439037009/185500000000000000000000000000000 : ℝ)*base68 + (949845696584962991/185500000000000000000000000000000 : ℝ)*base69 + (598310086669537009/185500000000000000000000000000000 : ℝ)*base72 + (263514061247/57968750000000000000000000 : ℝ)*base74 + (1173942559525962991/185500000000000000000000000000000 : ℝ)*base75 + (2086110189955537009/185500000000000000000000000000000 : ℝ)*base78 + (172075172302462991/185500000000000000000000000000000 : ℝ)*base79 + (7736856813471/1855000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (38073309/5000000000000000000000 : ℝ)*base90 + (38073309/5000000000000000000000 : ℝ)*base92 + (38073309/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (30205605450112479713939829/3312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (281396261/20000000000000 : ℝ)*(base19) + (349903007/20000000000000 : ℝ)*(base23) + (52425693/25000000000000 : ℝ)*(upper3) + (75937559/100000000000000 : ℝ)*(lower4) + (169531419/100000000000000 : ℝ)*(upper5) + (820010183705587/25000000000000 : ℝ)*(major0) + (820010183705587/25000000000000 : ℝ)*(major1) + (820010183705587/25000000000000 : ℝ)*(major2) + (575038549/2500000000000 : ℝ)*(sp1) + (12695087677/50000000000000 : ℝ)*(sp2) + (2275737640674989/50000000000000 : ℝ)*(sp4) + (4551450872826713/100000000000000 : ℝ)*(sp5) + (4551448141659589/100000000000000 : ℝ)*(sp6) + (1004302942169467/50000000000000 : ℝ)*(sp7) + (1004302942169467/50000000000000 : ℝ)*(f.failure) + (2275737640674989/50000000000000 : ℝ)*(f.sum) + (118790943013/49687500000000000000000000 : ℝ)*base66 + (227658512579545057/19875000000000000000000000000000 : ℝ)*base68 + (184168697230795057/19875000000000000000000000000000 : ℝ)*base70 + (85872568715545057/19875000000000000000000000000000 : ℝ)*base72 + (1901108132473/795000000000000000000000000 : ℝ)*base74 + (125009824671670057/19875000000000000000000000000000 : ℝ)*base76 + (123570280568170057/19875000000000000000000000000000 : ℝ)*base78 + (75022341836170057/19875000000000000000000000000000 : ℝ)*base80 + (230338002641/99375000000000000000000000 : ℝ)*base82 + (52166323/5000000000000000000000 : ℝ)*base89 + (52166323/5000000000000000000000 : ℝ)*base91 + (52166323/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1511_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163299369/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4/25 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2087/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (339/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15551/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1511_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1511_s4_0 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-934717299/5000000000 : ℝ)*x 0 + (2716883739/5000000000 : ℝ)*x 1 + (1043444451/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (934717299/5000000000 : ℝ)^4519 ≤ (11437436086141/100000000000000 : ℝ)^3495 := by
    have hnat : (934717299 : ℕ)^4519*100000000000000^3495 ≤ 11437436086141^3495*5000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      934717299 5000000000 11437436086141 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2716883739/5000000000 : ℝ)^4519 ≤ (45445230508041/100000000000000 : ℝ)^3495 := by
    have hnat : (2716883739 : ℕ)^4519*100000000000000^3495 ≤ 45445230508041^3495*5000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716883739 5000000000 45445230508041 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043444451/2000000000 : ℝ)^4519 ≤ (43117333392507/100000000000000 : ℝ)^3495 := by
    have hnat : (1043444451 : ℕ)^4519*100000000000000^3495 ≤ 43117333392507^3495*2000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043444451 2000000000 43117333392507 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-934717299/5000000000 : ℝ), (2716883739/5000000000 : ℝ), (1043444451/2000000000 : ℝ)] ![(11437436086141/100000000000000 : ℝ), (45445230508041/100000000000000 : ℝ), (43117333392507/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-934717299/5000000000 : ℝ)|^4519 ≤ (11437436086141/100000000000000 : ℝ)^3495
        have hw : |(-934717299/5000000000 : ℝ)|=(934717299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2716883739/5000000000 : ℝ)|^4519 ≤ (45445230508041/100000000000000 : ℝ)^3495
        have hw : |(2716883739/5000000000 : ℝ)|=(2716883739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043444451/2000000000 : ℝ)|^4519 ≤ (43117333392507/100000000000000 : ℝ)^3495
        have hw : |(1043444451/2000000000 : ℝ)|=(1043444451/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1511_s4_1 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675876071/5000000000 : ℝ)*x 0 + (-990175169/5000000000 : ℝ)*x 1 + (5217221977/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675876071/5000000000 : ℝ)^4519 ≤ (4456029281441/10000000000000 : ℝ)^3495 := by
    have hnat : (2675876071 : ℕ)^4519*10000000000000^3495 ≤ 4456029281441^3495*5000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675876071 5000000000 4456029281441 10000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (990175169/5000000000 : ℝ)^4519 ≤ (1540297094991/12500000000000 : ℝ)^3495 := by
    have hnat : (990175169 : ℕ)^4519*12500000000000^3495 ≤ 1540297094991^3495*5000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      990175169 5000000000 1540297094991 12500000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5217221977/10000000000 : ℝ)^4519 ≤ (862346608437/2000000000000 : ℝ)^3495 := by
    have hnat : (5217221977 : ℕ)^4519*2000000000000^3495 ≤ 862346608437^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217221977 10000000000 862346608437 2000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675876071/5000000000 : ℝ), (-990175169/5000000000 : ℝ), (5217221977/10000000000 : ℝ)] ![(4456029281441/10000000000000 : ℝ), (1540297094991/12500000000000 : ℝ), (862346608437/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675876071/5000000000 : ℝ)|^4519 ≤ (4456029281441/10000000000000 : ℝ)^3495
        have hw : |(2675876071/5000000000 : ℝ)|=(2675876071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-990175169/5000000000 : ℝ)|^4519 ≤ (1540297094991/12500000000000 : ℝ)^3495
        have hw : |(-990175169/5000000000 : ℝ)|=(990175169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5217221977/10000000000 : ℝ)|^4519 ≤ (862346608437/2000000000000 : ℝ)^3495
        have hw : |(5217221977/10000000000 : ℝ)|=(5217221977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1511_s4_2 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (133793797/250000000 : ℝ)*x 0 + (1304305569/2500000000 : ℝ)*x 1 + (-198035029/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133793797/250000000 : ℝ)^4519 ≤ (11140072498441/25000000000000 : ℝ)^3495 := by
    have hnat : (133793797 : ℕ)^4519*25000000000000^3495 ≤ 11140072498441^3495*250000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133793797 250000000 11140072498441 25000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1304305569/2500000000 : ℝ)^4519 ≤ (43117333616909/100000000000000 : ℝ)^3495 := by
    have hnat : (1304305569 : ℕ)^4519*100000000000000^3495 ≤ 43117333616909^3495*2500000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304305569 2500000000 43117333616909 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (198035029/1000000000 : ℝ)^4519 ≤ (3080594093437/25000000000000 : ℝ)^3495 := by
    have hnat : (198035029 : ℕ)^4519*25000000000000^3495 ≤ 3080594093437^3495*1000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      198035029 1000000000 3080594093437 25000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(133793797/250000000 : ℝ), (1304305569/2500000000 : ℝ), (-198035029/1000000000 : ℝ)] ![(11140072498441/25000000000000 : ℝ), (43117333616909/100000000000000 : ℝ), (3080594093437/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(133793797/250000000 : ℝ)|^4519 ≤ (11140072498441/25000000000000 : ℝ)^3495
        have hw : |(133793797/250000000 : ℝ)|=(133793797/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1304305569/2500000000 : ℝ)|^4519 ≤ (43117333616909/100000000000000 : ℝ)^3495
        have hw : |(1304305569/2500000000 : ℝ)|=(1304305569/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-198035029/1000000000 : ℝ)|^4519 ≤ (3080594093437/25000000000000 : ℝ)^3495
        have hw : |(-198035029/1000000000 : ℝ)|=(198035029/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1511_s4_3 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2135099967/5000000000 : ℝ)*x 0 + (403084469/1000000000 : ℝ)*x 1 + (180861341/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2135099967/5000000000 : ℝ)^4519 ≤ (16639613715067/50000000000000 : ℝ)^3495 := by
    have hnat : (2135099967 : ℕ)^4519*50000000000000^3495 ≤ 16639613715067^3495*5000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2135099967 5000000000 16639613715067 50000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (403084469/1000000000 : ℝ)^4519 ≤ (15443689733663/50000000000000 : ℝ)^3495 := by
    have hnat : (403084469 : ℕ)^4519*50000000000000^3495 ≤ 15443689733663^3495*1000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      403084469 1000000000 15443689733663 50000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (180861341/400000000 : ℝ)^4519 ≤ (35833393079321/100000000000000 : ℝ)^3495 := by
    have hnat : (180861341 : ℕ)^4519*100000000000000^3495 ≤ 35833393079321^3495*400000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      180861341 400000000 35833393079321 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2135099967/5000000000 : ℝ), (403084469/1000000000 : ℝ), (180861341/400000000 : ℝ)] ![(16639613715067/50000000000000 : ℝ), (15443689733663/50000000000000 : ℝ), (35833393079321/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2135099967/5000000000 : ℝ)|^4519 ≤ (16639613715067/50000000000000 : ℝ)^3495
        have hw : |(2135099967/5000000000 : ℝ)|=(2135099967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(403084469/1000000000 : ℝ)|^4519 ≤ (15443689733663/50000000000000 : ℝ)^3495
        have hw : |(403084469/1000000000 : ℝ)|=(403084469/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(180861341/400000000 : ℝ)|^4519 ≤ (35833393079321/100000000000000 : ℝ)^3495
        have hw : |(180861341/400000000 : ℝ)|=(180861341/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1511_s4_4 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-934731999/5000000000 : ℝ)*x 0 + (1043668103/2000000000 : ℝ)*x 1 + (5432640887/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (934731999/5000000000 : ℝ)^4519 ≤ (5718834330267/50000000000000 : ℝ)^3495 := by
    have hnat : (934731999 : ℕ)^4519*50000000000000^3495 ≤ 5718834330267^3495*5000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      934731999 5000000000 5718834330267 50000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043668103/2000000000 : ℝ)^4519 ≤ (21564641644497/50000000000000 : ℝ)^3495 := by
    have hnat : (1043668103 : ℕ)^4519*50000000000000^3495 ≤ 21564641644497^3495*2000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043668103 2000000000 21564641644497 50000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5432640887/10000000000 : ℝ)^4519 ≤ (45433048033639/100000000000000 : ℝ)^3495 := by
    have hnat : (5432640887 : ℕ)^4519*100000000000000^3495 ≤ 45433048033639^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432640887 10000000000 45433048033639 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-934731999/5000000000 : ℝ), (1043668103/2000000000 : ℝ), (5432640887/10000000000 : ℝ)] ![(5718834330267/50000000000000 : ℝ), (21564641644497/50000000000000 : ℝ), (45433048033639/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-934731999/5000000000 : ℝ)|^4519 ≤ (5718834330267/50000000000000 : ℝ)^3495
        have hw : |(-934731999/5000000000 : ℝ)|=(934731999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043668103/2000000000 : ℝ)|^4519 ≤ (21564641644497/50000000000000 : ℝ)^3495
        have hw : |(1043668103/2000000000 : ℝ)|=(1043668103/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5432640887/10000000000 : ℝ)|^4519 ≤ (45433048033639/100000000000000 : ℝ)^3495
        have hw : |(5432640887/10000000000 : ℝ)|=(5432640887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1511_s4_5 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294914441/10000000000 : ℝ)*x 0 + (-352986349/2000000000 : ℝ)*x 1 + (42442507/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294914441/10000000000 : ℝ)^4519 ≤ (21974671321599/50000000000000 : ℝ)^3495 := by
    have hnat : (5294914441 : ℕ)^4519*50000000000000^3495 ≤ 21974671321599^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294914441 10000000000 21974671321599 50000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (352986349/2000000000 : ℝ)^4519 ≤ (2654402304853/25000000000000 : ℝ)^3495 := by
    have hnat : (352986349 : ℕ)^4519*25000000000000^3495 ≤ 2654402304853^3495*2000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      352986349 2000000000 2654402304853 25000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42442507/78125000 : ℝ)^4519 ≤ (22716524065479/50000000000000 : ℝ)^3495 := by
    have hnat : (42442507 : ℕ)^4519*50000000000000^3495 ≤ 22716524065479^3495*78125000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42442507 78125000 22716524065479 50000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294914441/10000000000 : ℝ), (-352986349/2000000000 : ℝ), (42442507/78125000 : ℝ)] ![(21974671321599/50000000000000 : ℝ), (2654402304853/25000000000000 : ℝ), (22716524065479/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294914441/10000000000 : ℝ)|^4519 ≤ (21974671321599/50000000000000 : ℝ)^3495
        have hw : |(5294914441/10000000000 : ℝ)|=(5294914441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-352986349/2000000000 : ℝ)|^4519 ≤ (2654402304853/25000000000000 : ℝ)^3495
        have hw : |(-352986349/2000000000 : ℝ)|=(352986349/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(42442507/78125000 : ℝ)|^4519 ≤ (22716524065479/50000000000000 : ℝ)^3495
        have hw : |(42442507/78125000 : ℝ)|=(42442507/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1511_s4_6 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (661864319/1250000000 : ℝ)*x 0 + (5432640839/10000000000 : ℝ)*x 1 + (-1764931671/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661864319/1250000000 : ℝ)^4519 ≤ (5493667979309/12500000000000 : ℝ)^3495 := by
    have hnat : (661864319 : ℕ)^4519*12500000000000^3495 ≤ 5493667979309^3495*1250000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661864319 1250000000 5493667979309 12500000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5432640839/10000000000 : ℝ)^4519 ≤ (45433047514603/100000000000000 : ℝ)^3495 := by
    have hnat : (5432640839 : ℕ)^4519*100000000000000^3495 ≤ 45433047514603^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432640839 10000000000 45433047514603 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1764931671/10000000000 : ℝ)^4519 ≤ (5308804321903/50000000000000 : ℝ)^3495 := by
    have hnat : (1764931671 : ℕ)^4519*50000000000000^3495 ≤ 5308804321903^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1764931671 10000000000 5308804321903 50000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661864319/1250000000 : ℝ), (5432640839/10000000000 : ℝ), (-1764931671/10000000000 : ℝ)] ![(5493667979309/12500000000000 : ℝ), (45433047514603/100000000000000 : ℝ), (5308804321903/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661864319/1250000000 : ℝ)|^4519 ≤ (5493667979309/12500000000000 : ℝ)^3495
        have hw : |(661864319/1250000000 : ℝ)|=(661864319/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5432640839/10000000000 : ℝ)|^4519 ≤ (45433047514603/100000000000000 : ℝ)^3495
        have hw : |(5432640839/10000000000 : ℝ)|=(5432640839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1764931671/10000000000 : ℝ)|^4519 ≤ (5308804321903/50000000000000 : ℝ)^3495
        have hw : |(-1764931671/10000000000 : ℝ)|=(1764931671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1511_s4_7 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (133445839/312500000 : ℝ)*x 0 + (180759957/400000000 : ℝ)*x 1 + (806679509/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133445839/312500000 : ℝ)^4519 ≤ (33279901706871/100000000000000 : ℝ)^3495 := by
    have hnat : (133445839 : ℕ)^4519*100000000000000^3495 ≤ 33279901706871^3495*312500000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133445839 312500000 33279901706871 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (180759957/400000000 : ℝ)^4519 ≤ (8951855782533/25000000000000 : ℝ)^3495 := by
    have hnat : (180759957 : ℕ)^4519*25000000000000^3495 ≤ 8951855782533^3495*400000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      180759957 400000000 8951855782533 25000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (806679509/2000000000 : ℝ)^4519 ≤ (1545633758051/5000000000000 : ℝ)^3495 := by
    have hnat : (806679509 : ℕ)^4519*5000000000000^3495 ≤ 1545633758051^3495*2000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      806679509 2000000000 1545633758051 5000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(133445839/312500000 : ℝ), (180759957/400000000 : ℝ), (806679509/2000000000 : ℝ)] ![(33279901706871/100000000000000 : ℝ), (8951855782533/25000000000000 : ℝ), (1545633758051/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(133445839/312500000 : ℝ)|^4519 ≤ (33279901706871/100000000000000 : ℝ)^3495
        have hw : |(133445839/312500000 : ℝ)|=(133445839/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(180759957/400000000 : ℝ)|^4519 ≤ (8951855782533/25000000000000 : ℝ)^3495
        have hw : |(180759957/400000000 : ℝ)|=(180759957/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(806679509/2000000000 : ℝ)|^4519 ≤ (1545633758051/5000000000000 : ℝ)^3495
        have hw : |(806679509/2000000000 : ℝ)|=(806679509/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1511_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163299369/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15551/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (339/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (1363/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1549/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15551/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (339/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15551/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (339/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15551/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (339/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15551/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (339/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15551/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (339/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15551/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (339/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (339/3125 : ℝ) ^ (4517/1024 : ℝ) ≤ (5556474243033317/100000000000000000000 : ℝ) := by
    have hpowers : (339/3125 : ℝ)^4517 ≤ (5556474243033317/100000000000000000000 : ℝ)^1024 := by
      have hnat : (339 : ℕ)^4517*100000000000000000000^1024 ≤ 5556474243033317^1024*3125^4517 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        339 3125 5556474243033317 100000000000000000000 4517 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (339/3125 : ℝ)) (X := (5556474243033317/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4517 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15551/100000 : ℝ) ^ (4517/1024 : ℝ) ≤ (13605315437767763/50000000000000000000 : ℝ) := by
    have hpowers : (15551/100000 : ℝ)^4517 ≤ (13605315437767763/50000000000000000000 : ℝ)^1024 := by
      have hnat : (15551 : ℕ)^4517*50000000000000000000^1024 ≤ 13605315437767763^1024*100000^4517 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15551 100000 13605315437767763 50000000000000000000 4517 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15551/100000 : ℝ)) (X := (13605315437767763/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4517 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005556474243033317/50000000000000000000 : ℝ) ≤ (10000251918758417/10000000000000000 : ℝ) ^ (4517/1024 : ℝ) := by
    have hpowers : (50005556474243033317/50000000000000000000 : ℝ)^1024 ≤ (10000251918758417/10000000000000000 : ℝ)^4517 := by
      have hnat : (50005556474243033317 : ℕ)^1024*10000000000000000^4517 ≤ 10000251918758417^4517*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005556474243033317 50000000000000000000 10000251918758417 10000000000000000 1024 4517 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000251918758417/10000000000000000 : ℝ)) (X := (50005556474243033317/50000000000000000000 : ℝ)) (by norm_num) 4517 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100032767105118568843/100000000000000000000 : ℝ) ≤ (62504642083439/62500000000000 : ℝ) ^ (4517/1024 : ℝ) := by
    have hpowers : (100032767105118568843/100000000000000000000 : ℝ)^1024 ≤ (62504642083439/62500000000000 : ℝ)^4517 := by
      have hnat : (100032767105118568843 : ℕ)^1024*62500000000000^4517 ≤ 62504642083439^4517*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100032767105118568843 100000000000000000000 62504642083439 62500000000000 1024 4517 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (62504642083439/62500000000000 : ℝ)) (X := (100032767105118568843/100000000000000000000 : ℝ)) (by norm_num) 4517 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25013605315437767763/25000000000000000000 : ℝ) ≤ (10001233547942063/10000000000000000 : ℝ) ^ (4517/1024 : ℝ) := by
    have hpowers : (25013605315437767763/25000000000000000000 : ℝ)^1024 ≤ (10001233547942063/10000000000000000 : ℝ)^4517 := by
      have hnat : (25013605315437767763 : ℕ)^1024*10000000000000000^4517 ≤ 10001233547942063^4517*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013605315437767763 25000000000000000000 10001233547942063 10000000000000000 1024 4517 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001233547942063/10000000000000000 : ℝ)) (X := (25013605315437767763/25000000000000000000 : ℝ)) (by norm_num) 4517 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5556474243033317/100000000000000000000 : ℝ) ≤ ((47020536060536643343/47030000000000000000 : ℝ)+2*(490814591823/470300000000000 : ℝ)*(339/3125 : ℝ))^(4517/1024 : ℝ) := by
    rw [show (47020536060536643343/47030000000000000000 : ℝ)+2*(490814591823/470300000000000 : ℝ)*(339/3125 : ℝ)=(10000251918758417/10000000000000000 : ℝ) by norm_num, show 1+2*(5556474243033317/100000000000000000000 : ℝ)=(50005556474243033317/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13605315437767763/50000000000000000000 : ℝ)+(5556474243033317/100000000000000000000 : ℝ) ≤ ((47020536060536643343/47030000000000000000 : ℝ)+(490814591823/470300000000000 : ℝ)*((15551/100000 : ℝ)+(339/3125 : ℝ)))^(4517/1024 : ℝ) := by
    rw [show (47020536060536643343/47030000000000000000 : ℝ)+(490814591823/470300000000000 : ℝ)*((15551/100000 : ℝ)+(339/3125 : ℝ))=(62504642083439/62500000000000 : ℝ) by norm_num, show 1+(13605315437767763/50000000000000000000 : ℝ)+(5556474243033317/100000000000000000000 : ℝ)=(100032767105118568843/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13605315437767763/50000000000000000000 : ℝ) ≤ ((47020536060536643343/47030000000000000000 : ℝ)+2*(490814591823/470300000000000 : ℝ)*(15551/100000 : ℝ))^(4517/1024 : ℝ) := by
    rw [show (47020536060536643343/47030000000000000000 : ℝ)+2*(490814591823/470300000000000 : ℝ)*(15551/100000 : ℝ)=(10001233547942063/10000000000000000 : ℝ) by norm_num, show 1+2*(13605315437767763/50000000000000000000 : ℝ)=(25013605315437767763/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (47020536060536643343/47030000000000000000 : ℝ)*(X 1 0+X 2 0)+(490814591823/470300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4517/1024 : ℝ)) (lo := (339/3125 : ℝ)) (hi := (15551/100000 : ℝ)) (c := (47020536060536643343/47030000000000000000 : ℝ)) (alpha := (490814591823/470300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (47020536060536643343/47030000000000000000 : ℝ)*(X 0 1+X 2 1)+(490814591823/470300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4517/1024 : ℝ)) (lo := (339/3125 : ℝ)) (hi := (15551/100000 : ℝ)) (c := (47020536060536643343/47030000000000000000 : ℝ)) (alpha := (490814591823/470300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (47020536060536643343/47030000000000000000 : ℝ)*(X 0 2+X 1 2)+(490814591823/470300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4517/1024 : ℝ)) (lo := (339/3125 : ℝ)) (hi := (15551/100000 : ℝ)) (c := (47020536060536643343/47030000000000000000 : ℝ)) (alpha := (490814591823/470300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-934717299/5000000000 : ℝ)*X 0 0+(2716883739/5000000000 : ℝ)*X 0 1+(1043444451/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675876071/5000000000 : ℝ)*X 1 0+(-990175169/5000000000 : ℝ)*X 1 1+(5217221977/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((133793797/250000000 : ℝ)*X 2 0+(1304305569/2500000000 : ℝ)*X 2 1+(-198035029/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2135099967/5000000000 : ℝ)*X 0 0+(403084469/1000000000 : ℝ)*X 0 1+(180861341/400000000 : ℝ)*X 0 2+(2135099967/5000000000 : ℝ)*X 1 0+(403084469/1000000000 : ℝ)*X 1 1+(180861341/400000000 : ℝ)*X 1 2+(2135099967/5000000000 : ℝ)*X 2 0+(403084469/1000000000 : ℝ)*X 2 1+(180861341/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-934731999/5000000000 : ℝ)*X 0 0+(1043668103/2000000000 : ℝ)*X 0 1+(5432640887/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5294914441/10000000000 : ℝ)*X 1 0+(-352986349/2000000000 : ℝ)*X 1 1+(42442507/78125000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((661864319/1250000000 : ℝ)*X 2 0+(5432640839/10000000000 : ℝ)*X 2 1+(-1764931671/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((133445839/312500000 : ℝ)*X 0 0+(180759957/400000000 : ℝ)*X 0 1+(806679509/2000000000 : ℝ)*X 0 2+(133445839/312500000 : ℝ)*X 1 0+(180759957/400000000 : ℝ)*X 1 1+(806679509/2000000000 : ℝ)*X 1 2+(133445839/312500000 : ℝ)*X 2 0+(180759957/400000000 : ℝ)*X 2 1+(806679509/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (231416763440309542417161/23515000000000000000000000000 : ℝ) := by norm_num
    linear_combination (902069363/50000000000000 : ℝ)*(base19) + (1378774397/100000000000000 : ℝ)*(base23) + (53326123/50000000000000 : ℝ)*(lower2) + (107742763/50000000000000 : ℝ)*(upper3) + (78285173/100000000000000 : ℝ)*(upper5) + (415999947833423/12500000000000 : ℝ)*(major0) + (415999947833423/12500000000000 : ℝ)*(major1) + (415999947833423/12500000000000 : ℝ)*(major2) + (461800019276233/10000000000000 : ℝ)*(sp0) + (2309011240923091/50000000000000 : ℝ)*(sp1) + (288626431700657/6250000000000 : ℝ)*(sp2) + (2037962147579303/100000000000000 : ℝ)*(sp3) + (24093222579/100000000000000 : ℝ)*(sp4) + (12403729211/100000000000000 : ℝ)*(sp7) + (1018987275654257/50000000000000 : ℝ)*(f.failure) + (4618024285984909/100000000000000 : ℝ)*(f.sum) + (740231560453/5878750000000000000000000000 : ℝ)*base65 + (1687768116574996911/587875000000000000000000000000000 : ℝ)*base68 + (5428664015321121911/587875000000000000000000000000000 : ℝ)*base70 + (1904063712223503089/587875000000000000000000000000000 : ℝ)*base71 + (40901156026403/23515000000000000000000000000 : ℝ)*base74 + (3980098943682253089/587875000000000000000000000000000 : ℝ)*base75 + (423359013805003089/587875000000000000000000000000000 : ℝ)*base77 + (3793403146457621911/587875000000000000000000000000000 : ℝ)*base80 + (9971492868909/11757500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (30263833/5000000000000000000000 : ℝ)*base89 + (30263833/5000000000000000000000 : ℝ)*base91 + (30263833/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2742613097160806530515094791/470300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (768706879/100000000000000 : ℝ)*(base19) + (73451583/6250000000000 : ℝ)*(base23) + (81026469/100000000000000 : ℝ)*(upper3) + (142666599/100000000000000 : ℝ)*(lower4) + (47586287/25000000000000 : ℝ)*(upper5) + (672564956015807/20000000000000 : ℝ)*(major0) + (672564956015807/20000000000000 : ℝ)*(major1) + (672564956015807/20000000000000 : ℝ)*(major2) + (3182975797/25000000000000 : ℝ)*(sp1) + (16388911433/100000000000000 : ℝ)*(sp2) + (466634883039677/10000000000000 : ℝ)*(sp4) + (291645958111669/6250000000000 : ℝ)*(sp5) + (466633126626001/10000000000000 : ℝ)*(sp6) + (1029650267686899/50000000000000 : ℝ)*(sp7) + (1029650267686899/50000000000000 : ℝ)*(f.failure) + (466634883039677/10000000000000 : ℝ)*(f.sum) + (7591691887371/4703000000000000000000000000 : ℝ)*base66 + (4044680365025422801/940600000000000000000000000000000 : ℝ)*base67 + (7359112842705422801/940600000000000000000000000000000 : ℝ)*base69 + (2772174451167022801/940600000000000000000000000000000 : ℝ)*base71 + (8347673940583/4703000000000000000000000000 : ℝ)*base73 + (11645733236223422801/940600000000000000000000000000000 : ℝ)*base75 + (1172318822127022801/940600000000000000000000000000000 : ℝ)*base77 + (11248647961896622801/940600000000000000000000000000000 : ℝ)*base79 + (7937043234271/4703000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (53733269/5000000000000000000000 : ℝ)*base90 + (53733269/5000000000000000000000 : ℝ)*base92 + (53733269/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1511_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163299369/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15551/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (339/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1363/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1511_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1511_s5_0 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1869490053/10000000000 : ℝ)*x 0 + (2716703529/5000000000 : ℝ)*x 1 + (1043509187/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1869490053/10000000000 : ℝ)^4519 ≤ (11437874774553/100000000000000 : ℝ)^3495 := by
    have hnat : (1869490053 : ℕ)^4519*100000000000000^3495 ≤ 11437874774553^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1869490053 10000000000 11437874774553 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2716703529/5000000000 : ℝ)^4519 ≤ (1817653319977/4000000000000 : ℝ)^3495 := by
    have hnat : (2716703529 : ℕ)^4519*4000000000000^3495 ≤ 1817653319977^3495*5000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716703529 5000000000 1817653319977 4000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043509187/2000000000 : ℝ)^4519 ≤ (21560396104533/50000000000000 : ℝ)^3495 := by
    have hnat : (1043509187 : ℕ)^4519*50000000000000^3495 ≤ 21560396104533^3495*2000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043509187 2000000000 21560396104533 50000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1869490053/10000000000 : ℝ), (2716703529/5000000000 : ℝ), (1043509187/2000000000 : ℝ)] ![(11437874774553/100000000000000 : ℝ), (1817653319977/4000000000000 : ℝ), (21560396104533/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1869490053/10000000000 : ℝ)|^4519 ≤ (11437874774553/100000000000000 : ℝ)^3495
        have hw : |(-1869490053/10000000000 : ℝ)|=(1869490053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2716703529/5000000000 : ℝ)|^4519 ≤ (1817653319977/4000000000000 : ℝ)^3495
        have hw : |(2716703529/5000000000 : ℝ)|=(2716703529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043509187/2000000000 : ℝ)|^4519 ≤ (21560396104533/50000000000000 : ℝ)^3495
        have hw : |(1043509187/2000000000 : ℝ)|=(1043509187/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1511_s5_1 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351657341/10000000000 : ℝ)*x 0 + (-198004691/1000000000 : ℝ)*x 1 + (5217545931/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351657341/10000000000 : ℝ)^4519 ≤ (22279636103171/50000000000000 : ℝ)^3495 := by
    have hnat : (5351657341 : ℕ)^4519*50000000000000^3495 ≤ 22279636103171^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351657341 10000000000 22279636103171 50000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (198004691/1000000000 : ℝ)^4519 ≤ (492797424609/4000000000000 : ℝ)^3495 := by
    have hnat : (198004691 : ℕ)^4519*4000000000000^3495 ≤ 492797424609^3495*1000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      198004691 1000000000 492797424609 4000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5217545931/10000000000 : ℝ)^4519 ≤ (21560396083161/50000000000000 : ℝ)^3495 := by
    have hnat : (5217545931 : ℕ)^4519*50000000000000^3495 ≤ 21560396083161^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217545931 10000000000 21560396083161 50000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351657341/10000000000 : ℝ), (-198004691/1000000000 : ℝ), (5217545931/10000000000 : ℝ)] ![(22279636103171/50000000000000 : ℝ), (492797424609/4000000000000 : ℝ), (21560396083161/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351657341/10000000000 : ℝ)|^4519 ≤ (22279636103171/50000000000000 : ℝ)^3495
        have hw : |(5351657341/10000000000 : ℝ)|=(5351657341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-198004691/1000000000 : ℝ)|^4519 ≤ (492797424609/4000000000000 : ℝ)^3495
        have hw : |(-198004691/1000000000 : ℝ)|=(198004691/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5217545931/10000000000 : ℝ)|^4519 ≤ (21560396083161/50000000000000 : ℝ)^3495
        have hw : |(5217545931/10000000000 : ℝ)|=(5217545931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1511_s5_2 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351657333/10000000000 : ℝ)*x 0 + (5217545979/10000000000 : ℝ)*x 1 + (-1980046857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351657333/10000000000 : ℝ)^4519 ≤ (8911854424043/20000000000000 : ℝ)^3495 := by
    have hnat : (5351657333 : ℕ)^4519*20000000000000^3495 ≤ 8911854424043^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351657333 10000000000 8911854424043 20000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5217545979/10000000000 : ℝ)^4519 ≤ (172483170717/400000000000 : ℝ)^3495 := by
    have hnat : (5217545979 : ℕ)^4519*400000000000^3495 ≤ 172483170717^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217545979 10000000000 172483170717 400000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1980046857/10000000000 : ℝ)^4519 ≤ (6159967594419/50000000000000 : ℝ)^3495 := by
    have hnat : (1980046857 : ℕ)^4519*50000000000000^3495 ≤ 6159967594419^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1980046857 10000000000 6159967594419 50000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351657333/10000000000 : ℝ), (5217545979/10000000000 : ℝ), (-1980046857/10000000000 : ℝ)] ![(8911854424043/20000000000000 : ℝ), (172483170717/400000000000 : ℝ), (6159967594419/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351657333/10000000000 : ℝ)|^4519 ≤ (8911854424043/20000000000000 : ℝ)^3495
        have hw : |(5351657333/10000000000 : ℝ)|=(5351657333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5217545979/10000000000 : ℝ)|^4519 ≤ (172483170717/400000000000 : ℝ)^3495
        have hw : |(5217545979/10000000000 : ℝ)|=(5217545979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1980046857/10000000000 : ℝ)|^4519 ≤ (6159967594419/50000000000000 : ℝ)^3495
        have hw : |(-1980046857/10000000000 : ℝ)|=(1980046857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1511_s5_3 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (854046803/2000000000 : ℝ)*x 0 + (403161579/1000000000 : ℝ)*x 1 + (565094299/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (854046803/2000000000 : ℝ)^4519 ≤ (33279570856017/100000000000000 : ℝ)^3495 := by
    have hnat : (854046803 : ℕ)^4519*100000000000000^3495 ≤ 33279570856017^3495*2000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      854046803 2000000000 33279570856017 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (403161579/1000000000 : ℝ)^4519 ≤ (15447509818761/50000000000000 : ℝ)^3495 := by
    have hnat : (403161579 : ℕ)^4519*50000000000000^3495 ≤ 15447509818761^3495*1000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      403161579 1000000000 15447509818761 50000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (565094299/1250000000 : ℝ)^4519 ≤ (8956352373481/25000000000000 : ℝ)^3495 := by
    have hnat : (565094299 : ℕ)^4519*25000000000000^3495 ≤ 8956352373481^3495*1250000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      565094299 1250000000 8956352373481 25000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(854046803/2000000000 : ℝ), (403161579/1000000000 : ℝ), (565094299/1250000000 : ℝ)] ![(33279570856017/100000000000000 : ℝ), (15447509818761/50000000000000 : ℝ), (8956352373481/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(854046803/2000000000 : ℝ)|^4519 ≤ (33279570856017/100000000000000 : ℝ)^3495
        have hw : |(854046803/2000000000 : ℝ)|=(854046803/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(403161579/1000000000 : ℝ)|^4519 ≤ (15447509818761/50000000000000 : ℝ)^3495
        have hw : |(403161579/1000000000 : ℝ)|=(403161579/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(565094299/1250000000 : ℝ)|^4519 ≤ (8956352373481/25000000000000 : ℝ)^3495
        have hw : |(565094299/1250000000 : ℝ)|=(565094299/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1511_s5_4 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1869518853/10000000000 : ℝ)*x 0 + (1043731623/2000000000 : ℝ)*x 1 + (2716143437/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1869518853/10000000000 : ℝ)^4519 ≤ (11438102604499/100000000000000 : ℝ)^3495 := by
    have hnat : (1869518853 : ℕ)^4519*100000000000000^3495 ≤ 11438102604499^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1869518853 10000000000 11438102604499 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043731623/2000000000 : ℝ)^4519 ≤ (43132677347727/100000000000000 : ℝ)^3495 := by
    have hnat : (1043731623 : ℕ)^4519*100000000000000^3495 ≤ 43132677347727^3495*2000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043731623 2000000000 43132677347727 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2716143437/5000000000 : ℝ)^4519 ≤ (11357305010233/25000000000000 : ℝ)^3495 := by
    have hnat : (2716143437 : ℕ)^4519*25000000000000^3495 ≤ 11357305010233^3495*5000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716143437 5000000000 11357305010233 25000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1869518853/10000000000 : ℝ), (1043731623/2000000000 : ℝ), (2716143437/5000000000 : ℝ)] ![(11438102604499/100000000000000 : ℝ), (43132677347727/100000000000000 : ℝ), (11357305010233/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1869518853/10000000000 : ℝ)|^4519 ≤ (11438102604499/100000000000000 : ℝ)^3495
        have hw : |(-1869518853/10000000000 : ℝ)|=(1869518853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043731623/2000000000 : ℝ)|^4519 ≤ (43132677347727/100000000000000 : ℝ)^3495
        have hw : |(1043731623/2000000000 : ℝ)|=(1043731623/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2716143437/5000000000 : ℝ)|^4519 ≤ (11357305010233/25000000000000 : ℝ)^3495
        have hw : |(2716143437/5000000000 : ℝ)|=(2716143437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1511_s5_5 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058999901/2000000000 : ℝ)*x 0 + (-13791447/78125000 : ℝ)*x 1 + (2716143901/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058999901/2000000000 : ℝ)^4519 ≤ (43950255568873/100000000000000 : ℝ)^3495 := by
    have hnat : (1058999901 : ℕ)^4519*100000000000000^3495 ≤ 43950255568873^3495*2000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058999901 2000000000 43950255568873 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (13791447/78125000 : ℝ)^4519 ≤ (10620514341111/100000000000000 : ℝ)^3495 := by
    have hnat : (13791447 : ℕ)^4519*100000000000000^3495 ≤ 10620514341111^3495*78125000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13791447 78125000 10620514341111 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2716143901/5000000000 : ℝ)^4519 ≤ (5678653759429/12500000000000 : ℝ)^3495 := by
    have hnat : (2716143901 : ℕ)^4519*12500000000000^3495 ≤ 5678653759429^3495*5000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716143901 5000000000 5678653759429 12500000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058999901/2000000000 : ℝ), (-13791447/78125000 : ℝ), (2716143901/5000000000 : ℝ)] ![(43950255568873/100000000000000 : ℝ), (10620514341111/100000000000000 : ℝ), (5678653759429/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058999901/2000000000 : ℝ)|^4519 ≤ (43950255568873/100000000000000 : ℝ)^3495
        have hw : |(1058999901/2000000000 : ℝ)|=(1058999901/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-13791447/78125000 : ℝ)|^4519 ≤ (10620514341111/100000000000000 : ℝ)^3495
        have hw : |(-13791447/78125000 : ℝ)|=(13791447/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2716143901/5000000000 : ℝ)|^4519 ≤ (5678653759429/12500000000000 : ℝ)^3495
        have hw : |(2716143901/5000000000 : ℝ)|=(2716143901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1511_s5_6 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294999683/10000000000 : ℝ)*x 0 + (1358071821/2500000000 : ℝ)*x 1 + (-1765305691/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294999683/10000000000 : ℝ)^4519 ≤ (43950257479213/100000000000000 : ℝ)^3495 := by
    have hnat : (5294999683 : ℕ)^4519*100000000000000^3495 ≤ 43950257479213^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294999683 10000000000 43950257479213 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1358071821/2500000000 : ℝ)^4519 ≤ (45429224474277/100000000000000 : ℝ)^3495 := by
    have hnat : (1358071821 : ℕ)^4519*100000000000000^3495 ≤ 45429224474277^3495*2500000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358071821 2500000000 45429224474277 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1765305691/10000000000 : ℝ)^4519 ≤ (663782377257/6250000000000 : ℝ)^3495 := by
    have hnat : (1765305691 : ℕ)^4519*6250000000000^3495 ≤ 663782377257^3495*10000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1765305691 10000000000 663782377257 6250000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294999683/10000000000 : ℝ), (1358071821/2500000000 : ℝ), (-1765305691/10000000000 : ℝ)] ![(43950257479213/100000000000000 : ℝ), (45429224474277/100000000000000 : ℝ), (663782377257/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294999683/10000000000 : ℝ)|^4519 ≤ (43950257479213/100000000000000 : ℝ)^3495
        have hw : |(5294999683/10000000000 : ℝ)|=(5294999683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1358071821/2500000000 : ℝ)|^4519 ≤ (45429224474277/100000000000000 : ℝ)^3495
        have hw : |(1358071821/2500000000 : ℝ)|=(1358071821/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1765305691/10000000000 : ℝ)|^4519 ≤ (663782377257/6250000000000 : ℝ)^3495
        have hw : |(-1765305691/10000000000 : ℝ)|=(1765305691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1511_s5_7 (p : ℝ) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1067575009/2500000000 : ℝ)*x 0 + (903647319/2000000000 : ℝ)*x 1 + (806830381/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1067575009/2500000000 : ℝ)^4519 ≤ (33280236135737/100000000000000 : ℝ)^3495 := by
    have hnat : (1067575009 : ℕ)^4519*100000000000000^3495 ≤ 33280236135737^3495*2500000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1067575009 2500000000 33280236135737 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (903647319/2000000000 : ℝ)^4519 ≤ (35799613000017/100000000000000 : ℝ)^3495 := by
    have hnat : (903647319 : ℕ)^4519*100000000000000^3495 ≤ 35799613000017^3495*2000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903647319 2000000000 35799613000017 100000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (806830381/2000000000 : ℝ)^4519 ≤ (15460075425409/50000000000000 : ℝ)^3495 := by
    have hnat : (806830381 : ℕ)^4519*50000000000000^3495 ≤ 15460075425409^3495*2000000000^4519 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      806830381 2000000000 15460075425409 50000000000000 4519 3495 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4519/1024 : ℝ)) 4519 3495 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1067575009/2500000000 : ℝ), (903647319/2000000000 : ℝ), (806830381/2000000000 : ℝ)] ![(33280236135737/100000000000000 : ℝ), (35799613000017/100000000000000 : ℝ), (15460075425409/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1067575009/2500000000 : ℝ)|^4519 ≤ (33280236135737/100000000000000 : ℝ)^3495
        have hw : |(1067575009/2500000000 : ℝ)|=(1067575009/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(903647319/2000000000 : ℝ)|^4519 ≤ (35799613000017/100000000000000 : ℝ)^3495
        have hw : |(903647319/2000000000 : ℝ)|=(903647319/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(806830381/2000000000 : ℝ)|^4519 ≤ (15460075425409/50000000000000 : ℝ)^3495
        have hw : |(806830381/2000000000 : ℝ)|=(806830381/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1511_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163299369/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1363/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (10911/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15483/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1363/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1363/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1363/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1363/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1363/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1363/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1363/12500 : ℝ) ^ (4517/1024 : ℝ) ≤ (5684121232129139/100000000000000000000 : ℝ) := by
    have hpowers : (1363/12500 : ℝ)^4517 ≤ (5684121232129139/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1363 : ℕ)^4517*100000000000000000000^1024 ≤ 5684121232129139^1024*12500^4517 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1363 12500 5684121232129139 100000000000000000000 4517 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1363/12500 : ℝ)) (X := (5684121232129139/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4517 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1549/10000 : ℝ) ^ (4517/1024 : ℝ) ≤ (26742945079162233/100000000000000000000 : ℝ) := by
    have hpowers : (1549/10000 : ℝ)^4517 ≤ (26742945079162233/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1549 : ℕ)^4517*100000000000000000000^1024 ≤ 26742945079162233^1024*10000^4517 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1549 10000 26742945079162233 100000000000000000000 4517 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1549/10000 : ℝ)) (X := (26742945079162233/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4517 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005684121232129139/50000000000000000000 : ℝ) ≤ (15625402665231/15625000000000 : ℝ) ^ (4517/1024 : ℝ) := by
    have hpowers : (50005684121232129139/50000000000000000000 : ℝ)^1024 ≤ (15625402665231/15625000000000 : ℝ)^4517 := by
      have hnat : (50005684121232129139 : ℕ)^1024*15625000000000^4517 ≤ 15625402665231^4517*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005684121232129139 50000000000000000000 15625402665231 15625000000000 1024 4517 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (15625402665231/15625000000000 : ℝ)) (X := (50005684121232129139/50000000000000000000 : ℝ)) (by norm_num) 4517 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25008106766577822843/25000000000000000000 : ℝ) ≤ (1250091878330303/1250000000000000 : ℝ) ^ (4517/1024 : ℝ) := by
    have hpowers : (25008106766577822843/25000000000000000000 : ℝ)^1024 ≤ (1250091878330303/1250000000000000 : ℝ)^4517 := by
      have hnat : (25008106766577822843 : ℕ)^1024*1250000000000000^4517 ≤ 1250091878330303^4517*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25008106766577822843 25000000000000000000 1250091878330303 1250000000000000 1024 4517 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250091878330303/1250000000000000 : ℝ)) (X := (25008106766577822843/25000000000000000000 : ℝ)) (by norm_num) 4517 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50026742945079162233/50000000000000000000 : ℝ) ≤ (625075771721063/625000000000000 : ℝ) ^ (4517/1024 : ℝ) := by
    have hpowers : (50026742945079162233/50000000000000000000 : ℝ)^1024 ≤ (625075771721063/625000000000000 : ℝ)^4517 := by
      have hnat : (50026742945079162233 : ℕ)^1024*625000000000000^4517 ≤ 625075771721063^4517*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026742945079162233 50000000000000000000 625075771721063 625000000000000 1024 4517 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625075771721063/625000000000000 : ℝ)) (X := (50026742945079162233/50000000000000000000 : ℝ)) (by norm_num) 4517 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5684121232129139/100000000000000000000 : ℝ) ≤ ((358209159566332081/358281250000000000 : ℝ)+2*(59665111823/57325000000000 : ℝ)*(1363/12500 : ℝ))^(4517/1024 : ℝ) := by
    rw [show (358209159566332081/358281250000000000 : ℝ)+2*(59665111823/57325000000000 : ℝ)*(1363/12500 : ℝ)=(15625402665231/15625000000000 : ℝ) by norm_num, show 1+2*(5684121232129139/100000000000000000000 : ℝ)=(50005684121232129139/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(26742945079162233/100000000000000000000 : ℝ)+(5684121232129139/100000000000000000000 : ℝ) ≤ ((358209159566332081/358281250000000000 : ℝ)+(59665111823/57325000000000 : ℝ)*((1549/10000 : ℝ)+(1363/12500 : ℝ)))^(4517/1024 : ℝ) := by
    rw [show (358209159566332081/358281250000000000 : ℝ)+(59665111823/57325000000000 : ℝ)*((1549/10000 : ℝ)+(1363/12500 : ℝ))=(1250091878330303/1250000000000000 : ℝ) by norm_num, show 1+(26742945079162233/100000000000000000000 : ℝ)+(5684121232129139/100000000000000000000 : ℝ)=(25008106766577822843/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(26742945079162233/100000000000000000000 : ℝ) ≤ ((358209159566332081/358281250000000000 : ℝ)+2*(59665111823/57325000000000 : ℝ)*(1549/10000 : ℝ))^(4517/1024 : ℝ) := by
    rw [show (358209159566332081/358281250000000000 : ℝ)+2*(59665111823/57325000000000 : ℝ)*(1549/10000 : ℝ)=(625075771721063/625000000000000 : ℝ) by norm_num, show 1+2*(26742945079162233/100000000000000000000 : ℝ)=(50026742945079162233/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (358209159566332081/358281250000000000 : ℝ)*(X 1 0+X 2 0)+(59665111823/57325000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4517/1024 : ℝ)) (lo := (1363/12500 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (358209159566332081/358281250000000000 : ℝ)) (alpha := (59665111823/57325000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (358209159566332081/358281250000000000 : ℝ)*(X 0 1+X 2 1)+(59665111823/57325000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4517/1024 : ℝ)) (lo := (1363/12500 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (358209159566332081/358281250000000000 : ℝ)) (alpha := (59665111823/57325000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (358209159566332081/358281250000000000 : ℝ)*(X 0 2+X 1 2)+(59665111823/57325000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4517/1024 : ℝ)) (lo := (1363/12500 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (358209159566332081/358281250000000000 : ℝ)) (alpha := (59665111823/57325000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1869490053/10000000000 : ℝ)*X 0 0+(2716703529/5000000000 : ℝ)*X 0 1+(1043509187/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351657341/10000000000 : ℝ)*X 1 0+(-198004691/1000000000 : ℝ)*X 1 1+(5217545931/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351657333/10000000000 : ℝ)*X 2 0+(5217545979/10000000000 : ℝ)*X 2 1+(-1980046857/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((854046803/2000000000 : ℝ)*X 0 0+(403161579/1000000000 : ℝ)*X 0 1+(565094299/1250000000 : ℝ)*X 0 2+(854046803/2000000000 : ℝ)*X 1 0+(403161579/1000000000 : ℝ)*X 1 1+(565094299/1250000000 : ℝ)*X 1 2+(854046803/2000000000 : ℝ)*X 2 0+(403161579/1000000000 : ℝ)*X 2 1+(565094299/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1869518853/10000000000 : ℝ)*X 0 0+(1043731623/2000000000 : ℝ)*X 0 1+(2716143437/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1058999901/2000000000 : ℝ)*X 1 0+(-13791447/78125000 : ℝ)*X 1 1+(2716143901/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5294999683/10000000000 : ℝ)*X 2 0+(1358071821/2500000000 : ℝ)*X 2 1+(-1765305691/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1067575009/2500000000 : ℝ)*X 0 0+(903647319/2000000000 : ℝ)*X 0 1+(806830381/2000000000 : ℝ)*X 0 2+(1067575009/2500000000 : ℝ)*X 1 0+(903647319/2000000000 : ℝ)*X 1 1+(806830381/2000000000 : ℝ)*X 1 2+(1067575009/2500000000 : ℝ)*X 2 0+(903647319/2000000000 : ℝ)*X 2 1+(806830381/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1511_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (316010437098571345715027397/35828125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1626944109/100000000000000 : ℝ)*(base19) + (375696333/25000000000000 : ℝ)*(base23) + (12547879/20000000000000 : ℝ)*(lower2) + (212118447/100000000000000 : ℝ)*(upper3) + (44056879/25000000000000 : ℝ)*(upper5) + (1669273557795599/50000000000000 : ℝ)*(major0) + (1669273557795599/50000000000000 : ℝ)*(major1) + (1669273557795599/50000000000000 : ℝ)*(major2) + (2316317050170249/50000000000000 : ℝ)*(sp0) + (4632658742585677/100000000000000 : ℝ)*(sp1) + (2316329433372227/50000000000000 : ℝ)*(sp2) + (2044421508995077/100000000000000 : ℝ)*(sp3) + (3283648661/12500000000000 : ℝ)*(sp4) + (1507331449/12500000000000 : ℝ)*(sp7) + (511108391911667/25000000000000 : ℝ)*(f.failure) + (2316330184764893/50000000000000 : ℝ)*(f.sum) + (69661348473369/11465000000000000000000000000 : ℝ)*base66 + (379115347366423/139953613281250000000000000000 : ℝ)*base67 + (6362590487752053/8957031250000000000000000000000 : ℝ)*base70 + (114595183953136519/17914062500000000000000000000000 : ℝ)*base71 + (5646855969949/716562500000000000000000000 : ℝ)*base74 + (398373106316413663/35828125000000000000000000000000 : ℝ)*base75 + (109302160425367587/35828125000000000000000000000000 : ℝ)*base78 + (255263224163167769/17914062500000000000000000000000 : ℝ)*base79 + (1564730611063/5732500000000000000000000000 : ℝ)*base81 + (25161877/2500000000000000000000 : ℝ)*base90 + (25161877/2500000000000000000000 : ℝ)*base92 + (25161877/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (426101676926760444750357039/35828125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (656640181/50000000000000 : ℝ)*(base19) + (1001813409/50000000000000 : ℝ)*(base23) + (145887401/25000000000000 : ℝ)*(lower1) + (450713413/100000000000000 : ℝ)*(upper3) + (5976287/2500000000000 : ℝ)*(lower4) + (1686682137478619/50000000000000 : ℝ)*(major0) + (1686682137478619/50000000000000 : ℝ)*(major1) + (1686682137478619/50000000000000 : ℝ)*(major2) + (380933903/5000000000000 : ℝ)*(sp2) + (4273018953/100000000000000 : ℝ)*(sp3) + (468097352404721/10000000000000 : ℝ)*(sp4) + (4571261924577/97656250000 : ℝ)*(sp5) + (4680963901742333/100000000000000 : ℝ)*(sp6) + (2065750356417023/100000000000000 : ℝ)*(sp7) + (258219328679497/12500000000000 : ℝ)*(f.failure) + (468097352404721/10000000000000 : ℝ)*(f.sum) + (41268129694751/11465000000000000000000000000 : ℝ)*base65 + (220403265226061653/35828125000000000000000000000000 : ℝ)*base67 + (379517465035155403/35828125000000000000000000000000 : ℝ)*base69 + (279018949854280403/35828125000000000000000000000000 : ℝ)*base71 + (16983008037541/11465000000000000000000000000 : ℝ)*base73 + (765849752333467903/35828125000000000000000000000000 : ℝ)*base75 + (176186803000886507/8957031250000000000000000000000 : ℝ)*base77 + (1146056527531219597/35828125000000000000000000000000 : ℝ)*base80 + (8326860693219/2866250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (11662607/1250000000000000000000 : ℝ)*base90 + (11662607/1250000000000000000000 : ℝ)*base92 + (11662607/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1511_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163299369/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1363/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10911/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1511_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1511_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163299369/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4/25 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2087/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10911/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1511_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1511_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1511_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4517/1024 : ℝ) ≤ p) (hpb : p ≤ (4519/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163299369/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4/25 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2087/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10911/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1511_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
