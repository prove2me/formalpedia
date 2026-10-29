-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1364_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:18:48.594061+00:00
-- url     : https://prove2.me/submissions/9679516f-849c-4dbc-8e8a-0f0ba47581d2

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
theorem support_rectangle_w1364_box_0 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-464898521/2500000000 : ℝ)*x 0 + (5389016461/10000000000 : ℝ)*x 1 + (1077803399/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (464898521/2500000000 : ℝ)^1081 ≤ (11033578666417/100000000000000 : ℝ)^825 := by
    have hnat : (464898521 : ℕ)^1081*100000000000000^825 ≤ 11033578666417^825*2500000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      464898521 2500000000 11033578666417 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5389016461/10000000000 : ℝ)^1081 ≤ (44483207775343/100000000000000 : ℝ)^825 := by
    have hnat : (5389016461 : ℕ)^1081*100000000000000^825 ≤ 44483207775343^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5389016461 10000000000 44483207775343 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1077803399/2000000000 : ℝ)^1081 ≤ (347525105867/781250000000 : ℝ)^825 := by
    have hnat : (1077803399 : ℕ)^1081*781250000000^825 ≤ 347525105867^825*2000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077803399 2000000000 347525105867 781250000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-464898521/2500000000 : ℝ), (5389016461/10000000000 : ℝ), (1077803399/2000000000 : ℝ)] ![(11033578666417/100000000000000 : ℝ), (44483207775343/100000000000000 : ℝ), (347525105867/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-464898521/2500000000 : ℝ)|^1081 ≤ (11033578666417/100000000000000 : ℝ)^825
        have hw : |(-464898521/2500000000 : ℝ)|=(464898521/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5389016461/10000000000 : ℝ)|^1081 ≤ (44483207775343/100000000000000 : ℝ)^825
        have hw : |(5389016461/10000000000 : ℝ)|=(5389016461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1077803399/2000000000 : ℝ)|^1081 ≤ (347525105867/781250000000 : ℝ)^825
        have hw : |(1077803399/2000000000 : ℝ)|=(1077803399/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_box_1 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5285449163/10000000000 : ℝ)*x 0 + (-500398031/2500000000 : ℝ)*x 1 + (5389016399/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285449163/10000000000 : ℝ)^1081 ≤ (43366400312783/100000000000000 : ℝ)^825 := by
    have hnat : (5285449163 : ℕ)^1081*100000000000000^825 ≤ 43366400312783^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285449163 10000000000 43366400312783 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (500398031/2500000000 : ℝ)^1081 ≤ (12150392572193/100000000000000 : ℝ)^825 := by
    have hnat : (500398031 : ℕ)^1081*100000000000000^825 ≤ 12150392572193^825*2500000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      500398031 2500000000 12150392572193 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5389016399/10000000000 : ℝ)^1081 ≤ (11120801776191/25000000000000 : ℝ)^825 := by
    have hnat : (5389016399 : ℕ)^1081*25000000000000^825 ≤ 11120801776191^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5389016399 10000000000 11120801776191 25000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285449163/10000000000 : ℝ), (-500398031/2500000000 : ℝ), (5389016399/10000000000 : ℝ)] ![(43366400312783/100000000000000 : ℝ), (12150392572193/100000000000000 : ℝ), (11120801776191/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285449163/10000000000 : ℝ)|^1081 ≤ (43366400312783/100000000000000 : ℝ)^825
        have hw : |(5285449163/10000000000 : ℝ)|=(5285449163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-500398031/2500000000 : ℝ)|^1081 ≤ (12150392572193/100000000000000 : ℝ)^825
        have hw : |(-500398031/2500000000 : ℝ)|=(500398031/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5389016399/10000000000 : ℝ)|^1081 ≤ (11120801776191/25000000000000 : ℝ)^825
        have hw : |(5389016399/10000000000 : ℝ)|=(5389016399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_box_2 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5285448989/10000000000 : ℝ)*x 0 + (1077803307/2000000000 : ℝ)*x 1 + (-1000796087/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285448989/10000000000 : ℝ)^1081 ≤ (43366398442133/100000000000000 : ℝ)^825 := by
    have hnat : (5285448989 : ℕ)^1081*100000000000000^825 ≤ 43366398442133^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285448989 10000000000 43366398442133 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1077803307/2000000000 : ℝ)^1081 ≤ (1390100267991/3125000000000 : ℝ)^825 := by
    have hnat : (1077803307 : ℕ)^1081*3125000000000^825 ≤ 1390100267991^825*2000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077803307 2000000000 1390100267991 3125000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1000796087/5000000000 : ℝ)^1081 ≤ (12150392969893/100000000000000 : ℝ)^825 := by
    have hnat : (1000796087 : ℕ)^1081*100000000000000^825 ≤ 12150392969893^825*5000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1000796087 5000000000 12150392969893 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285448989/10000000000 : ℝ), (1077803307/2000000000 : ℝ), (-1000796087/5000000000 : ℝ)] ![(43366398442133/100000000000000 : ℝ), (1390100267991/3125000000000 : ℝ), (12150392969893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285448989/10000000000 : ℝ)|^1081 ≤ (43366398442133/100000000000000 : ℝ)^825
        have hw : |(5285448989/10000000000 : ℝ)|=(5285448989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1077803307/2000000000 : ℝ)|^1081 ≤ (1390100267991/3125000000000 : ℝ)^825
        have hw : |(1077803307/2000000000 : ℝ)|=(1077803307/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1000796087/5000000000 : ℝ)|^1081 ≤ (12150392969893/100000000000000 : ℝ)^825
        have hw : |(-1000796087/5000000000 : ℝ)|=(1000796087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_box_3 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2234290521/5000000000 : ℝ)*x 0 + (425090349/1000000000 : ℝ)*x 1 + (425090371/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2234290521/5000000000 : ℝ)^1081 ≤ (17401481407037/50000000000000 : ℝ)^825 := by
    have hnat : (2234290521 : ℕ)^1081*50000000000000^825 ≤ 17401481407037^825*5000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2234290521 5000000000 17401481407037 50000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (425090349/1000000000 : ℝ)^1081 ≤ (8149629370887/25000000000000 : ℝ)^825 := by
    have hnat : (425090349 : ℕ)^1081*25000000000000^825 ≤ 8149629370887^825*1000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425090349 1000000000 8149629370887 25000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (425090371/1000000000 : ℝ)^1081 ≤ (4074814961769/12500000000000 : ℝ)^825 := by
    have hnat : (425090371 : ℕ)^1081*12500000000000^825 ≤ 4074814961769^825*1000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425090371 1000000000 4074814961769 12500000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2234290521/5000000000 : ℝ), (425090349/1000000000 : ℝ), (425090371/1000000000 : ℝ)] ![(17401481407037/50000000000000 : ℝ), (8149629370887/25000000000000 : ℝ), (4074814961769/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2234290521/5000000000 : ℝ)|^1081 ≤ (17401481407037/50000000000000 : ℝ)^825
        have hw : |(2234290521/5000000000 : ℝ)|=(2234290521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(425090349/1000000000 : ℝ)|^1081 ≤ (8149629370887/25000000000000 : ℝ)^825
        have hw : |(425090349/1000000000 : ℝ)|=(425090349/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(425090371/1000000000 : ℝ)|^1081 ≤ (4074814961769/12500000000000 : ℝ)^825
        have hw : |(425090371/1000000000 : ℝ)|=(425090371/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_box_4 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-438677773/2000000000 : ℝ)*x 0 + (1316348729/2500000000 : ℝ)*x 1 + (1316348711/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (438677773/2000000000 : ℝ)^1081 ≤ (13698146894239/100000000000000 : ℝ)^825 := by
    have hnat : (438677773 : ℕ)^1081*100000000000000^825 ≤ 13698146894239^825*2000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      438677773 2000000000 13698146894239 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316348729/2500000000 : ℝ)^1081 ≤ (43150926935111/100000000000000 : ℝ)^825 := by
    have hnat : (1316348729 : ℕ)^1081*100000000000000^825 ≤ 43150926935111^825*2500000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316348729 2500000000 43150926935111 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316348711/2500000000 : ℝ)^1081 ≤ (21575463080981/50000000000000 : ℝ)^825 := by
    have hnat : (1316348711 : ℕ)^1081*50000000000000^825 ≤ 21575463080981^825*2500000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316348711 2500000000 21575463080981 50000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-438677773/2000000000 : ℝ), (1316348729/2500000000 : ℝ), (1316348711/2500000000 : ℝ)] ![(13698146894239/100000000000000 : ℝ), (43150926935111/100000000000000 : ℝ), (21575463080981/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-438677773/2000000000 : ℝ)|^1081 ≤ (13698146894239/100000000000000 : ℝ)^825
        have hw : |(-438677773/2000000000 : ℝ)|=(438677773/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316348729/2500000000 : ℝ)|^1081 ≤ (43150926935111/100000000000000 : ℝ)^825
        have hw : |(1316348729/2500000000 : ℝ)|=(1316348729/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316348711/2500000000 : ℝ)|^1081 ≤ (21575463080981/50000000000000 : ℝ)^825
        have hw : |(1316348711/2500000000 : ℝ)|=(1316348711/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_box_5 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2686099009/5000000000 : ℝ)*x 0 + (-2051350041/10000000000 : ℝ)*x 1 + (1316348641/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2686099009/5000000000 : ℝ)^1081 ≤ (8860278226927/20000000000000 : ℝ)^825 := by
    have hnat : (2686099009 : ℕ)^1081*20000000000000^825 ≤ 8860278226927^825*5000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2686099009 5000000000 8860278226927 20000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2051350041/10000000000 : ℝ)^1081 ≤ (627384284889/5000000000000 : ℝ)^825 := by
    have hnat : (2051350041 : ℕ)^1081*5000000000000^825 ≤ 627384284889^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2051350041 10000000000 627384284889 5000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316348641/2500000000 : ℝ)^1081 ≤ (4315092315527/10000000000000 : ℝ)^825 := by
    have hnat : (1316348641 : ℕ)^1081*10000000000000^825 ≤ 4315092315527^825*2500000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316348641 2500000000 4315092315527 10000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2686099009/5000000000 : ℝ), (-2051350041/10000000000 : ℝ), (1316348641/2500000000 : ℝ)] ![(8860278226927/20000000000000 : ℝ), (627384284889/5000000000000 : ℝ), (4315092315527/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2686099009/5000000000 : ℝ)|^1081 ≤ (8860278226927/20000000000000 : ℝ)^825
        have hw : |(2686099009/5000000000 : ℝ)|=(2686099009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2051350041/10000000000 : ℝ)|^1081 ≤ (627384284889/5000000000000 : ℝ)^825
        have hw : |(-2051350041/10000000000 : ℝ)|=(2051350041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316348641/2500000000 : ℝ)|^1081 ≤ (4315092315527/10000000000000 : ℝ)^825
        have hw : |(1316348641/2500000000 : ℝ)|=(1316348641/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_box_6 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5372198089/10000000000 : ℝ)*x 0 + (658174343/1250000000 : ℝ)*x 1 + (-256418713/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5372198089/10000000000 : ℝ)^1081 ≤ (11075347975453/25000000000000 : ℝ)^825 := by
    have hnat : (5372198089 : ℕ)^1081*25000000000000^825 ≤ 11075347975453^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5372198089 10000000000 11075347975453 25000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658174343/1250000000 : ℝ)^1081 ≤ (43150925088143/100000000000000 : ℝ)^825 := by
    have hnat : (658174343 : ℕ)^1081*100000000000000^825 ≤ 43150925088143^825*1250000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658174343 1250000000 43150925088143 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (256418713/1250000000 : ℝ)^1081 ≤ (6273841498387/50000000000000 : ℝ)^825 := by
    have hnat : (256418713 : ℕ)^1081*50000000000000^825 ≤ 6273841498387^825*1250000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256418713 1250000000 6273841498387 50000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5372198089/10000000000 : ℝ), (658174343/1250000000 : ℝ), (-256418713/1250000000 : ℝ)] ![(11075347975453/25000000000000 : ℝ), (43150925088143/100000000000000 : ℝ), (6273841498387/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5372198089/10000000000 : ℝ)|^1081 ≤ (11075347975453/25000000000000 : ℝ)^825
        have hw : |(5372198089/10000000000 : ℝ)|=(5372198089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658174343/1250000000 : ℝ)|^1081 ≤ (43150925088143/100000000000000 : ℝ)^825
        have hw : |(658174343/1250000000 : ℝ)|=(658174343/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-256418713/1250000000 : ℝ)|^1081 ≤ (6273841498387/50000000000000 : ℝ)^825
        have hw : |(-256418713/1250000000 : ℝ)|=(256418713/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_box_7 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1043066467/2500000000 : ℝ)*x 0 + (109975211/250000000 : ℝ)*x 1 + (274938013/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1043066467/2500000000 : ℝ)^1081 ≤ (3181062840713/10000000000000 : ℝ)^825 := by
    have hnat : (1043066467 : ℕ)^1081*10000000000000^825 ≤ 3181062840713^825*2500000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043066467 2500000000 3181062840713 10000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (109975211/250000000 : ℝ)^1081 ≤ (17047343484179/50000000000000 : ℝ)^825 := by
    have hnat : (109975211 : ℕ)^1081*50000000000000^825 ≤ 17047343484179^825*250000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109975211 250000000 17047343484179 50000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (274938013/625000000 : ℝ)^1081 ≤ (34094684612269/100000000000000 : ℝ)^825 := by
    have hnat : (274938013 : ℕ)^1081*100000000000000^825 ≤ 34094684612269^825*625000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274938013 625000000 34094684612269 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1043066467/2500000000 : ℝ), (109975211/250000000 : ℝ), (274938013/625000000 : ℝ)] ![(3181062840713/10000000000000 : ℝ), (17047343484179/50000000000000 : ℝ), (34094684612269/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1043066467/2500000000 : ℝ)|^1081 ≤ (3181062840713/10000000000000 : ℝ)^825
        have hw : |(1043066467/2500000000 : ℝ)|=(1043066467/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(109975211/250000000 : ℝ)|^1081 ≤ (17047343484179/50000000000000 : ℝ)^825
        have hw : |(109975211/250000000 : ℝ)|=(109975211/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(274938013/625000000 : ℝ)|^1081 ≤ (34094684612269/100000000000000 : ℝ)^825
        have hw : |(274938013/625000000 : ℝ)|=(274938013/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_box_8 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1061618109/5000000000 : ℝ)*x 0 + (1295046629/2500000000 : ℝ)*x 1 + (5403026651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061618109/5000000000 : ℝ)^1081 ≤ (6563475303237/50000000000000 : ℝ)^825 := by
    have hnat : (1061618109 : ℕ)^1081*50000000000000^825 ≤ 6563475303237^825*5000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061618109 5000000000 6563475303237 50000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1295046629/2500000000 : ℝ)^1081 ≤ (42238249203729/100000000000000 : ℝ)^825 := by
    have hnat : (1295046629 : ℕ)^1081*100000000000000^825 ≤ 42238249203729^825*2500000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295046629 2500000000 42238249203729 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5403026651/10000000000 : ℝ)^1081 ≤ (8926960032649/20000000000000 : ℝ)^825 := by
    have hnat : (5403026651 : ℕ)^1081*20000000000000^825 ≤ 8926960032649^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403026651 10000000000 8926960032649 20000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1061618109/5000000000 : ℝ), (1295046629/2500000000 : ℝ), (5403026651/10000000000 : ℝ)] ![(6563475303237/50000000000000 : ℝ), (42238249203729/100000000000000 : ℝ), (8926960032649/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1061618109/5000000000 : ℝ)|^1081 ≤ (6563475303237/50000000000000 : ℝ)^825
        have hw : |(-1061618109/5000000000 : ℝ)|=(1061618109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1295046629/2500000000 : ℝ)|^1081 ≤ (42238249203729/100000000000000 : ℝ)^825
        have hw : |(1295046629/2500000000 : ℝ)|=(1295046629/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5403026651/10000000000 : ℝ)|^1081 ≤ (8926960032649/20000000000000 : ℝ)^825
        have hw : |(5403026651/10000000000 : ℝ)|=(5403026651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_box_9 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5275613543/10000000000 : ℝ)*x 0 + (-498955743/2500000000 : ℝ)*x 1 + (5403025281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275613543/10000000000 : ℝ)^1081 ≤ (5407586184817/12500000000000 : ℝ)^825 := by
    have hnat : (5275613543 : ℕ)^1081*12500000000000^825 ≤ 5407586184817^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275613543 10000000000 5407586184817 12500000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (498955743/2500000000 : ℝ)^1081 ≤ (121045251779/1000000000000 : ℝ)^825 := by
    have hnat : (498955743 : ℕ)^1081*1000000000000^825 ≤ 121045251779^825*2500000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      498955743 2500000000 121045251779 1000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5403025281/10000000000 : ℝ)^1081 ≤ (11158696333417/25000000000000 : ℝ)^825 := by
    have hnat : (5403025281 : ℕ)^1081*25000000000000^825 ≤ 11158696333417^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403025281 10000000000 11158696333417 25000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275613543/10000000000 : ℝ), (-498955743/2500000000 : ℝ), (5403025281/10000000000 : ℝ)] ![(5407586184817/12500000000000 : ℝ), (121045251779/1000000000000 : ℝ), (11158696333417/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275613543/10000000000 : ℝ)|^1081 ≤ (5407586184817/12500000000000 : ℝ)^825
        have hw : |(5275613543/10000000000 : ℝ)|=(5275613543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-498955743/2500000000 : ℝ)|^1081 ≤ (121045251779/1000000000000 : ℝ)^825
        have hw : |(-498955743/2500000000 : ℝ)|=(498955743/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5403025281/10000000000 : ℝ)|^1081 ≤ (11158696333417/25000000000000 : ℝ)^825
        have hw : |(5403025281/10000000000 : ℝ)|=(5403025281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_box_10 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (527561267/1000000000 : ℝ)*x 0 + (5403026303/10000000000 : ℝ)*x 1 + (-49895569/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527561267/1000000000 : ℝ)^1081 ≤ (21630340049229/50000000000000 : ℝ)^825 := by
    have hnat : (527561267 : ℕ)^1081*50000000000000^825 ≤ 21630340049229^825*1000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527561267 1000000000 21630340049229 50000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5403026303/10000000000 : ℝ)^1081 ≤ (11158699099079/25000000000000 : ℝ)^825 := by
    have hnat : (5403026303 : ℕ)^1081*25000000000000^825 ≤ 11158699099079^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403026303 10000000000 11158699099079 25000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (49895569/250000000 : ℝ)^1081 ≤ (12104523493159/100000000000000 : ℝ)^825 := by
    have hnat : (49895569 : ℕ)^1081*100000000000000^825 ≤ 12104523493159^825*250000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49895569 250000000 12104523493159 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(527561267/1000000000 : ℝ), (5403026303/10000000000 : ℝ), (-49895569/250000000 : ℝ)] ![(21630340049229/50000000000000 : ℝ), (11158699099079/25000000000000 : ℝ), (12104523493159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(527561267/1000000000 : ℝ)|^1081 ≤ (21630340049229/50000000000000 : ℝ)^825
        have hw : |(527561267/1000000000 : ℝ)|=(527561267/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5403026303/10000000000 : ℝ)|^1081 ≤ (11158699099079/25000000000000 : ℝ)^825
        have hw : |(5403026303/10000000000 : ℝ)|=(5403026303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-49895569/250000000 : ℝ)|^1081 ≤ (12104523493159/100000000000000 : ℝ)^825
        have hw : |(-49895569/250000000 : ℝ)|=(49895569/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_box_11 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2250800933/5000000000 : ℝ)*x 0 + (1058526479/2500000000 : ℝ)*x 1 + (1058526443/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2250800933/5000000000 : ℝ)^1081 ≤ (439254126781/1250000000000 : ℝ)^825 := by
    have hnat : (2250800933 : ℕ)^1081*1250000000000^825 ≤ 439254126781^825*5000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2250800933 5000000000 439254126781 1250000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1058526479/2500000000 : ℝ)^1081 ≤ (32429835643807/100000000000000 : ℝ)^825 := by
    have hnat : (1058526479 : ℕ)^1081*100000000000000^825 ≤ 32429835643807^825*2500000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058526479 2500000000 32429835643807 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1058526443/2500000000 : ℝ)^1081 ≤ (32429834198643/100000000000000 : ℝ)^825 := by
    have hnat : (1058526443 : ℕ)^1081*100000000000000^825 ≤ 32429834198643^825*2500000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058526443 2500000000 32429834198643 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2250800933/5000000000 : ℝ), (1058526479/2500000000 : ℝ), (1058526443/2500000000 : ℝ)] ![(439254126781/1250000000000 : ℝ), (32429835643807/100000000000000 : ℝ), (32429834198643/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2250800933/5000000000 : ℝ)|^1081 ≤ (439254126781/1250000000000 : ℝ)^825
        have hw : |(2250800933/5000000000 : ℝ)|=(2250800933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1058526479/2500000000 : ℝ)|^1081 ≤ (32429835643807/100000000000000 : ℝ)^825
        have hw : |(1058526479/2500000000 : ℝ)|=(1058526479/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1058526443/2500000000 : ℝ)|^1081 ≤ (32429834198643/100000000000000 : ℝ)^825
        have hw : |(1058526443/2500000000 : ℝ)|=(1058526443/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_box_12 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-965021167/5000000000 : ℝ)*x 0 + (684008481/1250000000 : ℝ)*x 1 + (5254308547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (965021167/5000000000 : ℝ)^1081 ≤ (11584467059837/100000000000000 : ℝ)^825 := by
    have hnat : (965021167 : ℕ)^1081*100000000000000^825 ≤ 11584467059837^825*5000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      965021167 5000000000 11584467059837 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (684008481/1250000000 : ℝ)^1081 ≤ (45383614578069/100000000000000 : ℝ)^825 := by
    have hnat : (684008481 : ℕ)^1081*100000000000000^825 ≤ 45383614578069^825*1250000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      684008481 1250000000 45383614578069 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5254308547/10000000000 : ℝ)^1081 ≤ (43031918350531/100000000000000 : ℝ)^825 := by
    have hnat : (5254308547 : ℕ)^1081*100000000000000^825 ≤ 43031918350531^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254308547 10000000000 43031918350531 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-965021167/5000000000 : ℝ), (684008481/1250000000 : ℝ), (5254308547/10000000000 : ℝ)] ![(11584467059837/100000000000000 : ℝ), (45383614578069/100000000000000 : ℝ), (43031918350531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-965021167/5000000000 : ℝ)|^1081 ≤ (11584467059837/100000000000000 : ℝ)^825
        have hw : |(-965021167/5000000000 : ℝ)|=(965021167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(684008481/1250000000 : ℝ)|^1081 ≤ (45383614578069/100000000000000 : ℝ)^825
        have hw : |(684008481/1250000000 : ℝ)|=(684008481/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5254308547/10000000000 : ℝ)|^1081 ≤ (43031918350531/100000000000000 : ℝ)^825
        have hw : |(5254308547/10000000000 : ℝ)|=(5254308547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_box_13 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5379975307/10000000000 : ℝ)*x 0 + (-128481827/625000000 : ℝ)*x 1 + (65678857/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5379975307/10000000000 : ℝ)^1081 ≤ (44385445996487/100000000000000 : ℝ)^825 := by
    have hnat : (5379975307 : ℕ)^1081*100000000000000^825 ≤ 44385445996487^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5379975307 10000000000 44385445996487 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (128481827/625000000 : ℝ)^1081 ≤ (6291317744889/50000000000000 : ℝ)^825 := by
    have hnat : (128481827 : ℕ)^1081*50000000000000^825 ≤ 6291317744889^825*625000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128481827 625000000 6291317744889 50000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (65678857/125000000 : ℝ)^1081 ≤ (10757979622509/25000000000000 : ℝ)^825 := by
    have hnat : (65678857 : ℕ)^1081*25000000000000^825 ≤ 10757979622509^825*125000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65678857 125000000 10757979622509 25000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5379975307/10000000000 : ℝ), (-128481827/625000000 : ℝ), (65678857/125000000 : ℝ)] ![(44385445996487/100000000000000 : ℝ), (6291317744889/50000000000000 : ℝ), (10757979622509/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5379975307/10000000000 : ℝ)|^1081 ≤ (44385445996487/100000000000000 : ℝ)^825
        have hw : |(5379975307/10000000000 : ℝ)|=(5379975307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-128481827/625000000 : ℝ)|^1081 ≤ (6291317744889/50000000000000 : ℝ)^825
        have hw : |(-128481827/625000000 : ℝ)|=(128481827/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(65678857/125000000 : ℝ)|^1081 ≤ (10757979622509/25000000000000 : ℝ)^825
        have hw : |(65678857/125000000 : ℝ)|=(65678857/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_box_14 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5379975337/10000000000 : ℝ)*x 0 + (5254308597/10000000000 : ℝ)*x 1 + (-2055709143/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5379975337/10000000000 : ℝ)^1081 ≤ (5548180790099/12500000000000 : ℝ)^825 := by
    have hnat : (5379975337 : ℕ)^1081*12500000000000^825 ≤ 5548180790099^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5379975337 10000000000 5548180790099 12500000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5254308597/10000000000 : ℝ)^1081 ≤ (43031918887089/100000000000000 : ℝ)^825 := by
    have hnat : (5254308597 : ℕ)^1081*100000000000000^825 ≤ 43031918887089^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254308597 10000000000 43031918887089 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2055709143/10000000000 : ℝ)^1081 ≤ (6291317387993/50000000000000 : ℝ)^825 := by
    have hnat : (2055709143 : ℕ)^1081*50000000000000^825 ≤ 6291317387993^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2055709143 10000000000 6291317387993 50000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5379975337/10000000000 : ℝ), (5254308597/10000000000 : ℝ), (-2055709143/10000000000 : ℝ)] ![(5548180790099/12500000000000 : ℝ), (43031918887089/100000000000000 : ℝ), (6291317387993/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5379975337/10000000000 : ℝ)|^1081 ≤ (5548180790099/12500000000000 : ℝ)^825
        have hw : |(5379975337/10000000000 : ℝ)|=(5379975337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5254308597/10000000000 : ℝ)|^1081 ≤ (43031918887089/100000000000000 : ℝ)^825
        have hw : |(5254308597/10000000000 : ℝ)|=(5254308597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2055709143/10000000000 : ℝ)|^1081 ≤ (6291317387993/50000000000000 : ℝ)^825
        have hw : |(-2055709143/10000000000 : ℝ)|=(2055709143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_box_15 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1036311077/2500000000 : ℝ)*x 0 + (4412279577/10000000000 : ℝ)*x 1 + (1103069841/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1036311077/2500000000 : ℝ)^1081 ≤ (3942618827861/12500000000000 : ℝ)^825 := by
    have hnat : (1036311077 : ℕ)^1081*12500000000000^825 ≤ 3942618827861^825*2500000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036311077 2500000000 3942618827861 12500000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4412279577/10000000000 : ℝ)^1081 ≤ (34229525769129/100000000000000 : ℝ)^825 := by
    have hnat : (4412279577 : ℕ)^1081*100000000000000^825 ≤ 34229525769129^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4412279577 10000000000 34229525769129 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1103069841/2500000000 : ℝ)^1081 ≤ (34229523603973/100000000000000 : ℝ)^825 := by
    have hnat : (1103069841 : ℕ)^1081*100000000000000^825 ≤ 34229523603973^825*2500000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103069841 2500000000 34229523603973 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1036311077/2500000000 : ℝ), (4412279577/10000000000 : ℝ), (1103069841/2500000000 : ℝ)] ![(3942618827861/12500000000000 : ℝ), (34229525769129/100000000000000 : ℝ), (34229523603973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1036311077/2500000000 : ℝ)|^1081 ≤ (3942618827861/12500000000000 : ℝ)^825
        have hw : |(1036311077/2500000000 : ℝ)|=(1036311077/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4412279577/10000000000 : ℝ)|^1081 ≤ (34229525769129/100000000000000 : ℝ)^825
        have hw : |(4412279577/10000000000 : ℝ)|=(4412279577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1103069841/2500000000 : ℝ)|^1081 ≤ (34229523603973/100000000000000 : ℝ)^825
        have hw : |(1103069841/2500000000 : ℝ)|=(1103069841/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1364_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155596149/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (92/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11201/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(12573/20000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(7373/12500 : ℝ) ∧ (40041/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84437/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (92/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11201/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (92/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11201/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (92/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11201/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (92/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11201/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (92/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11201/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (92/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11201/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11201/100000 : ℝ) ^ (4323/1024 : ℝ) ≤ (484436365523761/5000000000000000000 : ℝ) := by
    have hpowers : (11201/100000 : ℝ)^4323 ≤ (484436365523761/5000000000000000000 : ℝ)^1024 := by
      have hnat : (11201 : ℕ)^4323*5000000000000000000^1024 ≤ 484436365523761^1024*100000^4323 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11201 100000 484436365523761 5000000000000000000 4323 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11201/100000 : ℝ)) (X := (484436365523761/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4323 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (92/625 : ℝ) ^ (4323/1024 : ℝ) ≤ (30702469128759461/100000000000000000000 : ℝ) := by
    have hpowers : (92/625 : ℝ)^4323 ≤ (30702469128759461/100000000000000000000 : ℝ)^1024 := by
      have hnat : (92 : ℕ)^4323*100000000000000000000^1024 ≤ 30702469128759461^1024*625^4323 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        92 625 30702469128759461 100000000000000000000 4323 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (92/625 : ℝ)) (X := (30702469128759461/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4323 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500484436365523761/2500000000000000000 : ℝ) ≤ (10000458964760497/10000000000000000 : ℝ) ^ (4323/1024 : ℝ) := by
    have hpowers : (2500484436365523761/2500000000000000000 : ℝ)^1024 ≤ (10000458964760497/10000000000000000 : ℝ)^4323 := by
      have hnat : (2500484436365523761 : ℕ)^1024*10000000000000000^4323 ≤ 10000458964760497^4323*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500484436365523761 2500000000000000000 10000458964760497 10000000000000000 1024 4323 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000458964760497/10000000000000000 : ℝ)) (X := (2500484436365523761/2500000000000000000 : ℝ)) (by norm_num) 4323 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100040391196439234681/100000000000000000000 : ℝ) ≤ (2500239152279953/2500000000000000 : ℝ) ^ (4323/1024 : ℝ) := by
    have hpowers : (100040391196439234681/100000000000000000000 : ℝ)^1024 ≤ (2500239152279953/2500000000000000 : ℝ)^4323 := by
      have hnat : (100040391196439234681 : ℕ)^1024*2500000000000000^4323 ≤ 2500239152279953^4323*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100040391196439234681 100000000000000000000 2500239152279953 2500000000000000 1024 4323 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500239152279953/2500000000000000 : ℝ)) (X := (100040391196439234681/100000000000000000000 : ℝ)) (by norm_num) 4323 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50030702469128759461/50000000000000000000 : ℝ) ≤ (10001454253479127/10000000000000000 : ℝ) ^ (4323/1024 : ℝ) := by
    have hpowers : (50030702469128759461/50000000000000000000 : ℝ)^1024 ≤ (10001454253479127/10000000000000000 : ℝ)^4323 := by
      have hnat : (50030702469128759461 : ℕ)^1024*10000000000000000^4323 ≤ 10001454253479127^4323*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030702469128759461 50000000000000000000 10001454253479127 10000000000000000 1024 4323 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001454253479127/10000000000000000 : ℝ)) (X := (50030702469128759461/50000000000000000000 : ℝ)) (by norm_num) 4323 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(484436365523761/5000000000000000000 : ℝ) ≤ ((509861838667461077/510000000000000000 : ℝ)+2*(33176290621/23460000000000 : ℝ)*(11201/100000 : ℝ))^(4323/1024 : ℝ) := by
    rw [show (509861838667461077/510000000000000000 : ℝ)+2*(33176290621/23460000000000 : ℝ)*(11201/100000 : ℝ)=(10000458964760497/10000000000000000 : ℝ) by norm_num, show 1+2*(484436365523761/5000000000000000000 : ℝ)=(2500484436365523761/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30702469128759461/100000000000000000000 : ℝ)+(484436365523761/5000000000000000000 : ℝ) ≤ ((509861838667461077/510000000000000000 : ℝ)+(33176290621/23460000000000 : ℝ)*((92/625 : ℝ)+(11201/100000 : ℝ)))^(4323/1024 : ℝ) := by
    rw [show (509861838667461077/510000000000000000 : ℝ)+(33176290621/23460000000000 : ℝ)*((92/625 : ℝ)+(11201/100000 : ℝ))=(2500239152279953/2500000000000000 : ℝ) by norm_num, show 1+(30702469128759461/100000000000000000000 : ℝ)+(484436365523761/5000000000000000000 : ℝ)=(100040391196439234681/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30702469128759461/100000000000000000000 : ℝ) ≤ ((509861838667461077/510000000000000000 : ℝ)+2*(33176290621/23460000000000 : ℝ)*(92/625 : ℝ))^(4323/1024 : ℝ) := by
    rw [show (509861838667461077/510000000000000000 : ℝ)+2*(33176290621/23460000000000 : ℝ)*(92/625 : ℝ)=(10001454253479127/10000000000000000 : ℝ) by norm_num, show 1+2*(30702469128759461/100000000000000000000 : ℝ)=(50030702469128759461/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (509861838667461077/510000000000000000 : ℝ)*(X 1 0+X 2 0)+(33176290621/23460000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4323/1024 : ℝ)) (lo := (11201/100000 : ℝ)) (hi := (92/625 : ℝ)) (c := (509861838667461077/510000000000000000 : ℝ)) (alpha := (33176290621/23460000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (509861838667461077/510000000000000000 : ℝ)*(X 0 1+X 2 1)+(33176290621/23460000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4323/1024 : ℝ)) (lo := (11201/100000 : ℝ)) (hi := (92/625 : ℝ)) (c := (509861838667461077/510000000000000000 : ℝ)) (alpha := (33176290621/23460000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (509861838667461077/510000000000000000 : ℝ)*(X 0 2+X 1 2)+(33176290621/23460000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4323/1024 : ℝ)) (lo := (11201/100000 : ℝ)) (hi := (92/625 : ℝ)) (c := (509861838667461077/510000000000000000 : ℝ)) (alpha := (33176290621/23460000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-464898521/2500000000 : ℝ)*X 0 0+(5389016461/10000000000 : ℝ)*X 0 1+(1077803399/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5285449163/10000000000 : ℝ)*X 1 0+(-500398031/2500000000 : ℝ)*X 1 1+(5389016399/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5285448989/10000000000 : ℝ)*X 2 0+(1077803307/2000000000 : ℝ)*X 2 1+(-1000796087/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2234290521/5000000000 : ℝ)*X 0 0+(425090349/1000000000 : ℝ)*X 0 1+(425090371/1000000000 : ℝ)*X 0 2+(2234290521/5000000000 : ℝ)*X 1 0+(425090349/1000000000 : ℝ)*X 1 1+(425090371/1000000000 : ℝ)*X 1 2+(2234290521/5000000000 : ℝ)*X 2 0+(425090349/1000000000 : ℝ)*X 2 1+(425090371/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-438677773/2000000000 : ℝ)*X 0 0+(1316348729/2500000000 : ℝ)*X 0 1+(1316348711/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2686099009/5000000000 : ℝ)*X 1 0+(-2051350041/10000000000 : ℝ)*X 1 1+(1316348641/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5372198089/10000000000 : ℝ)*X 2 0+(658174343/1250000000 : ℝ)*X 2 1+(-256418713/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1043066467/2500000000 : ℝ)*X 0 0+(109975211/250000000 : ℝ)*X 0 1+(274938013/625000000 : ℝ)*X 0 2+(1043066467/2500000000 : ℝ)*X 1 0+(109975211/250000000 : ℝ)*X 1 1+(274938013/625000000 : ℝ)*X 1 2+(1043066467/2500000000 : ℝ)*X 2 0+(109975211/250000000 : ℝ)*X 2 1+(274938013/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1061618109/5000000000 : ℝ)*X 0 0+(1295046629/2500000000 : ℝ)*X 0 1+(5403026651/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5275613543/10000000000 : ℝ)*X 1 0+(-498955743/2500000000 : ℝ)*X 1 1+(5403025281/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((527561267/1000000000 : ℝ)*X 2 0+(5403026303/10000000000 : ℝ)*X 2 1+(-49895569/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2250800933/5000000000 : ℝ)*X 0 0+(1058526479/2500000000 : ℝ)*X 0 1+(1058526443/2500000000 : ℝ)*X 0 2+(2250800933/5000000000 : ℝ)*X 1 0+(1058526479/2500000000 : ℝ)*X 1 1+(1058526443/2500000000 : ℝ)*X 1 2+(2250800933/5000000000 : ℝ)*X 2 0+(1058526479/2500000000 : ℝ)*X 2 1+(1058526443/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-965021167/5000000000 : ℝ)*X 0 0+(684008481/1250000000 : ℝ)*X 0 1+(5254308547/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5379975307/10000000000 : ℝ)*X 1 0+(-128481827/625000000 : ℝ)*X 1 1+(65678857/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5379975337/10000000000 : ℝ)*X 2 0+(5254308597/10000000000 : ℝ)*X 2 1+(-2055709143/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1036311077/2500000000 : ℝ)*X 0 0+(4412279577/10000000000 : ℝ)*X 0 1+(1103069841/2500000000 : ℝ)*X 0 2+(1036311077/2500000000 : ℝ)*X 1 0+(4412279577/10000000000 : ℝ)*X 1 1+(1103069841/2500000000 : ℝ)*X 1 2+(1036311077/2500000000 : ℝ)*X 2 0+(4412279577/10000000000 : ℝ)*X 2 1+(1103069841/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-12573/20000 : ℝ) ≤ (-2457906169312376420110705410267/3910000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3915963/10000000000000 : ℝ)*(upper0) + (20763191/100000000000000 : ℝ)*(upper1) + (8647153/6250000000000 : ℝ)*(upper4) + (10123117/100000000000000 : ℝ)*(upper5) + (58905630883341/2000000000000 : ℝ)*(major0) + (58905630883341/2000000000000 : ℝ)*(major1) + (58905630883341/2000000000000 : ℝ)*(major2) + (12659795333/100000000000000 : ℝ)*(sp1) + (4106323/1000000000000 : ℝ)*(sp3) + (4018611090006261/100000000000000 : ℝ)*(sp4) + (803720626880843/20000000000000 : ℝ)*(sp5) + (1004653948549887/25000000000000 : ℝ)*(sp6) + (1892900900290923/100000000000000 : ℝ)*(sp7) + (4704193287/100000000000000 : ℝ)*(sp8) + (946450655461611/50000000000000 : ℝ)*(f.failure) + (1004653948549887/25000000000000 : ℝ)*(f.sum) + (217197309953/391000000000000000000000000 : ℝ)*base66 + (106925769858653363/7820000000000000000000000000000 : ℝ)*base68 + (141743028127593363/7820000000000000000000000000000 : ℝ)*base70 + (191633344146153363/7820000000000000000000000000000 : ℝ)*base72 + (117928892733/391000000000000000000000000 : ℝ)*base74 + (101446122434513363/7820000000000000000000000000000 : ℝ)*base76 + (121724590038013363/7820000000000000000000000000000 : ℝ)*base78 + (80914014272733363/7820000000000000000000000000000 : ℝ)*base80 + (195095979639/195500000000000000000000000 : ℝ)*base81 + (11063961/5000000000000000000000 : ℝ)*base90 + (11063961/5000000000000000000000 : ℝ)*base92 + (11063961/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (7373/12500 : ℝ) ≤ (115318858829660994167359472250521/195500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (210383/5000000000000 : ℝ)*(lower0) + (13240873/12500000000000 : ℝ)*(lower1) + (178667/5000000000000 : ℝ)*(lower3) + (24918069/20000000000000 : ℝ)*(lower5) + (3014708973614417/100000000000000 : ℝ)*(major0) + (3014708973614417/100000000000000 : ℝ)*(major1) + (3014708973614417/100000000000000 : ℝ)*(major2) + (4072216028483413/100000000000000 : ℝ)*(sp0) + (2036081055390881/50000000000000 : ℝ)*(sp1) + (25451463449171/625000000000 : ℝ)*(sp2) + (484378247962611/25000000000000 : ℝ)*(sp3) + (85939919/1000000000000 : ℝ)*(sp7) + (36020542799/50000000000000 : ℝ)*(sp9) + (18123383947/100000000000000 : ℝ)*(sp12) + (242190198230293/12500000000000 : ℝ)*(f.failure) + (25451463449171/625000000000 : ℝ)*(f.sum) + (2494301146523/1173000000000000000000000000 : ℝ)*base65 + (1726674624315638831/391000000000000000000000000000000 : ℝ)*base68 + (2062261468940638831/391000000000000000000000000000000 : ℝ)*base70 + (1596232238084638831/391000000000000000000000000000000 : ℝ)*base72 + (3719402379211/1173000000000000000000000000 : ℝ)*base74 + (807080749552638831/391000000000000000000000000000000 : ℝ)*base76 + (1558883965004638831/391000000000000000000000000000000 : ℝ)*base78 + (3019437983356638831/391000000000000000000000000000000 : ℝ)*base80 + (3614503311557/1173000000000000000000000000 : ℝ)*base81 + (6558343/1250000000000000000000 : ℝ)*base90 + (6558343/1250000000000000000000 : ℝ)*base92 + (6558343/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (40041/50000 : ℝ) ≤ (39141395635893120016497489677941/48875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4380637/6250000000000 : ℝ)*(upper1) + (111224307/100000000000000 : ℝ)*(upper2) + (30098033/100000000000000 : ℝ)*(lower5) + (1662950621335271/50000000000000 : ℝ)*(major0) + (1662950621335271/50000000000000 : ℝ)*(major1) + (1662950621335271/50000000000000 : ℝ)*(major2) + (285210303341/100000000000000 : ℝ)*(sp2) + (67225375681/50000000000000 : ℝ)*(sp3) + (9046505987/100000000000000 : ℝ)*(sp4) + (560943589723187/12500000000000 : ℝ)*(sp8) + (2243793009558123/50000000000000 : ℝ)*(sp9) + (2243650404406453/50000000000000 : ℝ)*(sp10) + (106869355824453/5000000000000 : ℝ)*(sp11) + (28254824763/100000000000000 : ℝ)*(sp12) + (1068760783620211/50000000000000 : ℝ)*(f.failure) + (2243793009558123/50000000000000 : ℝ)*(f.sum) + (122528156927/234600000000000000000000000 : ℝ)*base65 + (1146317630803892647/195500000000000000000000000000000 : ℝ)*base67 + (79673667247607353/195500000000000000000000000000000 : ℝ)*base70 + (929813846621107353/195500000000000000000000000000000 : ℝ)*base72 + (581911001069/586500000000000000000000000 : ℝ)*base73 + (1534874171663107353/195500000000000000000000000000000 : ℝ)*base76 + (2168496312211607353/195500000000000000000000000000000 : ℝ)*base78 + (530907347841607353/195500000000000000000000000000000 : ℝ)*base80 + (60953273197/146625000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (10167439/5000000000000000000000 : ℝ)*base89 + (10167439/5000000000000000000000 : ℝ)*base91 + (10167439/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-84437/100000 : ℝ) ≤ (-41267548546608455031974747269989/48875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7755073/20000000000000 : ℝ)*(lower0) + (4474599/12500000000000 : ℝ)*(lower2) + (17407199/50000000000000 : ℝ)*(upper3) + (56086753/100000000000000 : ℝ)*(upper5) + (1681294706468559/50000000000000 : ℝ)*(major0) + (1681294706468559/50000000000000 : ℝ)*(major1) + (1681294706468559/50000000000000 : ℝ)*(major2) + (23603757/12500000000000 : ℝ)*(sp0) + (7078341253/25000000000000 : ℝ)*(sp5) + (7558755437/100000000000000 : ℝ)*(sp7) + (2296111465643157/50000000000000 : ℝ)*(sp12) + (2296097403375679/50000000000000 : ℝ)*(sp13) + (459222312011637/10000000000000 : ℝ)*(sp14) + (2161093107648021/100000000000000 : ℝ)*(sp15) + (1080550333201729/50000000000000 : ℝ)*(f.failure) + (459222312011637/10000000000000 : ℝ)*(f.sum) + (689820670331/195500000000000000000000000 : ℝ)*base65 + (1103412991492368337/195500000000000000000000000000000 : ℝ)*base68 + (220463442806131663/195500000000000000000000000000000 : ℝ)*base69 + (774919255202131663/195500000000000000000000000000000 : ℝ)*base71 + (2364992759467/391000000000000000000000000 : ℝ)*base73 + (1284278301771131663/195500000000000000000000000000000 : ℝ)*base75 + (1583447907658131663/195500000000000000000000000000000 : ℝ)*base77 + (12100467716631663/195500000000000000000000000000000 : ℝ)*base79 + (6914197113/48875000000000000000000000 : ℝ)*base82 + (27458379/5000000000000000000000 : ℝ)*base90 + (27458379/5000000000000000000000 : ℝ)*base92 + (27458379/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1364_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155596149/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (92/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11201/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12573/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(7373/12500 : ℝ) else (40041/50000 : ℝ) ≤ X j i ∧ X j i ≤ (84437/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1364_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1364_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155596149/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (92/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11201/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12573/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(7373/12500 : ℝ) else (40041/50000 : ℝ) ≤ X j i ∧ X j i ≤ (84437/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1364_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155596149/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (92/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11201/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12573/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(7373/12500 : ℝ) else (40041/50000 : ℝ) ≤ X j i ∧ X j i ≤ (84437/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1364_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
