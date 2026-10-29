-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1642_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:11:18.313979+00:00
-- url     : https://prove2.me/submissions/77c3a73a-83fc-4943-becd-bfc875451b77

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
theorem support_rectangle_w1642_s3_0 (p : ℝ) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-162688981/1000000000 : ℝ)*x 0 + (2725004961/5000000000 : ℝ)*x 1 + (1036655067/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (162688981/1000000000 : ℝ)^4887 ≤ (1256654214901/12500000000000 : ℝ)^3863 := by
    have hnat : (162688981 : ℕ)^4887*12500000000000^3863 ≤ 1256654214901^3863*1000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      162688981 1000000000 1256654214901 12500000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2725004961/5000000000 : ℝ)^4887 ≤ (46400404120339/100000000000000 : ℝ)^3863 := by
    have hnat : (2725004961 : ℕ)^4887*100000000000000^3863 ≤ 46400404120339^3863*5000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2725004961 5000000000 46400404120339 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1036655067/2000000000 : ℝ)^4887 ≤ (1741854485521/4000000000000 : ℝ)^3863 := by
    have hnat : (1036655067 : ℕ)^4887*4000000000000^3863 ≤ 1741854485521^3863*2000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036655067 2000000000 1741854485521 4000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4887/1024 : ℝ)) 4887 3863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-162688981/1000000000 : ℝ), (2725004961/5000000000 : ℝ), (1036655067/2000000000 : ℝ)] ![(1256654214901/12500000000000 : ℝ), (46400404120339/100000000000000 : ℝ), (1741854485521/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-162688981/1000000000 : ℝ)|^4887 ≤ (1256654214901/12500000000000 : ℝ)^3863
        have hw : |(-162688981/1000000000 : ℝ)|=(162688981/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2725004961/5000000000 : ℝ)|^4887 ≤ (46400404120339/100000000000000 : ℝ)^3863
        have hw : |(2725004961/5000000000 : ℝ)|=(2725004961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1036655067/2000000000 : ℝ)|^4887 ≤ (1741854485521/4000000000000 : ℝ)^3863
        have hw : |(1036655067/2000000000 : ℝ)|=(1036655067/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1642_s3_1 (p : ℝ) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337242523/2500000000 : ℝ)*x 0 + (-1764249531/10000000000 : ℝ)*x 1 + (5183275257/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337242523/2500000000 : ℝ)^4887 ≤ (11328706333551/25000000000000 : ℝ)^3863 := by
    have hnat : (1337242523 : ℕ)^4887*25000000000000^3863 ≤ 11328706333551^3863*2500000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337242523 2500000000 11328706333551 25000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1764249531/10000000000 : ℝ)^4887 ≤ (1113881333941/10000000000000 : ℝ)^3863 := by
    have hnat : (1764249531 : ℕ)^4887*10000000000000^3863 ≤ 1113881333941^3863*10000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1764249531 10000000000 1113881333941 10000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5183275257/10000000000 : ℝ)^4887 ≤ (8709272261803/20000000000000 : ℝ)^3863 := by
    have hnat : (5183275257 : ℕ)^4887*20000000000000^3863 ≤ 8709272261803^3863*10000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183275257 10000000000 8709272261803 20000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4887/1024 : ℝ)) 4887 3863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337242523/2500000000 : ℝ), (-1764249531/10000000000 : ℝ), (5183275257/10000000000 : ℝ)] ![(11328706333551/25000000000000 : ℝ), (1113881333941/10000000000000 : ℝ), (8709272261803/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337242523/2500000000 : ℝ)|^4887 ≤ (11328706333551/25000000000000 : ℝ)^3863
        have hw : |(1337242523/2500000000 : ℝ)|=(1337242523/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1764249531/10000000000 : ℝ)|^4887 ≤ (1113881333941/10000000000000 : ℝ)^3863
        have hw : |(-1764249531/10000000000 : ℝ)|=(1764249531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5183275257/10000000000 : ℝ)|^4887 ≤ (8709272261803/20000000000000 : ℝ)^3863
        have hw : |(5183275257/10000000000 : ℝ)|=(5183275257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1642_s3_2 (p : ℝ) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674485187/5000000000 : ℝ)*x 0 + (518327509/1000000000 : ℝ)*x 1 + (-882124687/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674485187/5000000000 : ℝ)^4887 ≤ (45314828356499/100000000000000 : ℝ)^3863 := by
    have hnat : (2674485187 : ℕ)^4887*100000000000000^3863 ≤ 45314828356499^3863*5000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674485187 5000000000 45314828356499 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (518327509/1000000000 : ℝ)^4887 ≤ (43546359534083/100000000000000 : ℝ)^3863 := by
    have hnat : (518327509 : ℕ)^4887*100000000000000^3863 ≤ 43546359534083^3863*1000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518327509 1000000000 43546359534083 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (882124687/5000000000 : ℝ)^4887 ≤ (5569406042707/50000000000000 : ℝ)^3863 := by
    have hnat : (882124687 : ℕ)^4887*50000000000000^3863 ≤ 5569406042707^3863*5000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      882124687 5000000000 5569406042707 50000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4887/1024 : ℝ)) 4887 3863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674485187/5000000000 : ℝ), (518327509/1000000000 : ℝ), (-882124687/5000000000 : ℝ)] ![(45314828356499/100000000000000 : ℝ), (43546359534083/100000000000000 : ℝ), (5569406042707/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674485187/5000000000 : ℝ)|^4887 ≤ (45314828356499/100000000000000 : ℝ)^3863
        have hw : |(2674485187/5000000000 : ℝ)|=(2674485187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(518327509/1000000000 : ℝ)|^4887 ≤ (43546359534083/100000000000000 : ℝ)^3863
        have hw : |(518327509/1000000000 : ℝ)|=(518327509/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-882124687/5000000000 : ℝ)|^4887 ≤ (5569406042707/50000000000000 : ℝ)^3863
        have hw : |(-882124687/5000000000 : ℝ)|=(882124687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1642_s3_3 (p : ℝ) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2093445013/5000000000 : ℝ)*x 0 + (1927767119/5000000000 : ℝ)*x 1 + (2269347089/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2093445013/5000000000 : ℝ)^4887 ≤ (33240149029673/100000000000000 : ℝ)^3863 := by
    have hnat : (2093445013 : ℕ)^4887*100000000000000^3863 ≤ 33240149029673^3863*5000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2093445013 5000000000 33240149029673 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1927767119/5000000000 : ℝ)^4887 ≤ (29947756496337/100000000000000 : ℝ)^3863 := by
    have hnat : (1927767119 : ℕ)^4887*100000000000000^3863 ≤ 29947756496337^3863*5000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1927767119 5000000000 29947756496337 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2269347089/5000000000 : ℝ)^4887 ≤ (36812094455563/100000000000000 : ℝ)^3863 := by
    have hnat : (2269347089 : ℕ)^4887*100000000000000^3863 ≤ 36812094455563^3863*5000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2269347089 5000000000 36812094455563 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4887/1024 : ℝ)) 4887 3863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2093445013/5000000000 : ℝ), (1927767119/5000000000 : ℝ), (2269347089/5000000000 : ℝ)] ![(33240149029673/100000000000000 : ℝ), (29947756496337/100000000000000 : ℝ), (36812094455563/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2093445013/5000000000 : ℝ)|^4887 ≤ (33240149029673/100000000000000 : ℝ)^3863
        have hw : |(2093445013/5000000000 : ℝ)|=(2093445013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1927767119/5000000000 : ℝ)|^4887 ≤ (29947756496337/100000000000000 : ℝ)^3863
        have hw : |(1927767119/5000000000 : ℝ)|=(1927767119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2269347089/5000000000 : ℝ)|^4887 ≤ (36812094455563/100000000000000 : ℝ)^3863
        have hw : |(2269347089/5000000000 : ℝ)|=(2269347089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1642_s3_4 (p : ℝ) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-813477707/5000000000 : ℝ)*x 0 + (2592644187/5000000000 : ℝ)*x 1 + (340498479/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (813477707/5000000000 : ℝ)^4887 ≤ (5026873289063/50000000000000 : ℝ)^3863 := by
    have hnat : (813477707 : ℕ)^4887*50000000000000^3863 ≤ 5026873289063^3863*5000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      813477707 5000000000 5026873289063 50000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2592644187/5000000000 : ℝ)^4887 ≤ (43567758491943/100000000000000 : ℝ)^3863 := by
    have hnat : (2592644187 : ℕ)^4887*100000000000000^3863 ≤ 43567758491943^3863*5000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592644187 5000000000 43567758491943 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (340498479/625000000 : ℝ)^4887 ≤ (2318924745699/5000000000000 : ℝ)^3863 := by
    have hnat : (340498479 : ℕ)^4887*5000000000000^3863 ≤ 2318924745699^3863*625000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340498479 625000000 2318924745699 5000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4887/1024 : ℝ)) 4887 3863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-813477707/5000000000 : ℝ), (2592644187/5000000000 : ℝ), (340498479/625000000 : ℝ)] ![(5026873289063/50000000000000 : ℝ), (43567758491943/100000000000000 : ℝ), (2318924745699/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-813477707/5000000000 : ℝ)|^4887 ≤ (5026873289063/50000000000000 : ℝ)^3863
        have hw : |(-813477707/5000000000 : ℝ)|=(813477707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2592644187/5000000000 : ℝ)|^4887 ≤ (43567758491943/100000000000000 : ℝ)^3863
        have hw : |(2592644187/5000000000 : ℝ)|=(2592644187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(340498479/625000000 : ℝ)|^4887 ≤ (2318924745699/5000000000000 : ℝ)^3863
        have hw : |(340498479/625000000 : ℝ)|=(340498479/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1642_s3_5 (p : ℝ) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5277781363/10000000000 : ℝ)*x 0 + (-1499548937/10000000000 : ℝ)*x 1 + (5447975649/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5277781363/10000000000 : ℝ)^4887 ≤ (22276610204561/50000000000000 : ℝ)^3863 := by
    have hnat : (5277781363 : ℕ)^4887*50000000000000^3863 ≤ 22276610204561^3863*10000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5277781363 10000000000 22276610204561 50000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1499548937/10000000000 : ℝ)^4887 ≤ (4534142412879/50000000000000 : ℝ)^3863 := by
    have hnat : (1499548937 : ℕ)^4887*50000000000000^3863 ≤ 4534142412879^3863*10000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1499548937 10000000000 4534142412879 50000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5447975649/10000000000 : ℝ)^4887 ≤ (11594623688109/25000000000000 : ℝ)^3863 := by
    have hnat : (5447975649 : ℕ)^4887*25000000000000^3863 ≤ 11594623688109^3863*10000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5447975649 10000000000 11594623688109 25000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4887/1024 : ℝ)) 4887 3863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5277781363/10000000000 : ℝ), (-1499548937/10000000000 : ℝ), (5447975649/10000000000 : ℝ)] ![(22276610204561/50000000000000 : ℝ), (4534142412879/50000000000000 : ℝ), (11594623688109/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5277781363/10000000000 : ℝ)|^4887 ≤ (22276610204561/50000000000000 : ℝ)^3863
        have hw : |(5277781363/10000000000 : ℝ)|=(5277781363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1499548937/10000000000 : ℝ)|^4887 ≤ (4534142412879/50000000000000 : ℝ)^3863
        have hw : |(-1499548937/10000000000 : ℝ)|=(1499548937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5447975649/10000000000 : ℝ)|^4887 ≤ (11594623688109/25000000000000 : ℝ)^3863
        have hw : |(5447975649/10000000000 : ℝ)|=(5447975649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1642_s3_6 (p : ℝ) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2638890687/5000000000 : ℝ)*x 0 + (5447975687/10000000000 : ℝ)*x 1 + (-1499548869/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638890687/5000000000 : ℝ)^4887 ≤ (8910644105319/20000000000000 : ℝ)^3863 := by
    have hnat : (2638890687 : ℕ)^4887*20000000000000^3863 ≤ 8910644105319^3863*5000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638890687 5000000000 8910644105319 20000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5447975687/10000000000 : ℝ)^4887 ≤ (579731189521/1250000000000 : ℝ)^3863 := by
    have hnat : (5447975687 : ℕ)^4887*1250000000000^3863 ≤ 579731189521^3863*10000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5447975687 10000000000 579731189521 1250000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1499548869/10000000000 : ℝ)^4887 ≤ (4534142152767/50000000000000 : ℝ)^3863 := by
    have hnat : (1499548869 : ℕ)^4887*50000000000000^3863 ≤ 4534142152767^3863*10000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1499548869 10000000000 4534142152767 50000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4887/1024 : ℝ)) 4887 3863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638890687/5000000000 : ℝ), (5447975687/10000000000 : ℝ), (-1499548869/10000000000 : ℝ)] ![(8910644105319/20000000000000 : ℝ), (579731189521/1250000000000 : ℝ), (4534142152767/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638890687/5000000000 : ℝ)|^4887 ≤ (8910644105319/20000000000000 : ℝ)^3863
        have hw : |(2638890687/5000000000 : ℝ)|=(2638890687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5447975687/10000000000 : ℝ)|^4887 ≤ (579731189521/1250000000000 : ℝ)^3863
        have hw : |(5447975687/10000000000 : ℝ)|=(5447975687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1499548869/10000000000 : ℝ)|^4887 ≤ (4534142152767/50000000000000 : ℝ)^3863
        have hw : |(-1499548869/10000000000 : ℝ)|=(1499548869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1642_s3_7 (p : ℝ) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2093528811/5000000000 : ℝ)*x 0 + (2266769069/5000000000 : ℝ)*x 1 + (965186271/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2093528811/5000000000 : ℝ)^4887 ≤ (33241832304361/100000000000000 : ℝ)^3863 := by
    have hnat : (2093528811 : ℕ)^4887*100000000000000^3863 ≤ 33241832304361^3863*5000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2093528811 5000000000 33241832304361 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2266769069/5000000000 : ℝ)^4887 ≤ (7351839562727/20000000000000 : ℝ)^3863 := by
    have hnat : (2266769069 : ℕ)^4887*20000000000000^3863 ≤ 7351839562727^3863*5000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2266769069 5000000000 7351839562727 20000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (965186271/2500000000 : ℝ)^4887 ≤ (2999896986707/10000000000000 : ℝ)^3863 := by
    have hnat : (965186271 : ℕ)^4887*10000000000000^3863 ≤ 2999896986707^3863*2500000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      965186271 2500000000 2999896986707 10000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4887/1024 : ℝ)) 4887 3863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2093528811/5000000000 : ℝ), (2266769069/5000000000 : ℝ), (965186271/2500000000 : ℝ)] ![(33241832304361/100000000000000 : ℝ), (7351839562727/20000000000000 : ℝ), (2999896986707/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2093528811/5000000000 : ℝ)|^4887 ≤ (33241832304361/100000000000000 : ℝ)^3863
        have hw : |(2093528811/5000000000 : ℝ)|=(2093528811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2266769069/5000000000 : ℝ)|^4887 ≤ (7351839562727/20000000000000 : ℝ)^3863
        have hw : |(2266769069/5000000000 : ℝ)|=(2266769069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(965186271/2500000000 : ℝ)|^4887 ≤ (2999896986707/10000000000000 : ℝ)^3863
        have hw : |(965186271/2500000000 : ℝ)|=(965186271/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1642_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (178059701/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4093/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2637/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5311/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16289/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4093/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2637/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4093/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2637/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4093/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2637/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4093/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2637/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4093/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2637/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4093/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2637/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2637/25000 : ℝ) ^ (4883/1024 : ℝ) ≤ (1098761178550909/50000000000000000000 : ℝ) := by
    have hpowers : (2637/25000 : ℝ)^4883 ≤ (1098761178550909/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2637 : ℕ)^4883*50000000000000000000^1024 ≤ 1098761178550909^1024*25000^4883 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2637 25000 1098761178550909 50000000000000000000 4883 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2637/25000 : ℝ)) (X := (1098761178550909/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4883 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4093/25000 : ℝ) ^ (4883/1024 : ℝ) ≤ (3576276960475441/20000000000000000000 : ℝ) := by
    have hpowers : (4093/25000 : ℝ)^4883 ≤ (3576276960475441/20000000000000000000 : ℝ)^1024 := by
      have hnat : (4093 : ℕ)^4883*20000000000000000000^1024 ≤ 3576276960475441^1024*25000^4883 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4093 25000 3576276960475441 20000000000000000000 4883 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4093/25000 : ℝ)) (X := (3576276960475441/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4883 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25001098761178550909/25000000000000000000 : ℝ) ≤ (1000009216562829/1000000000000000 : ℝ) ^ (4883/1024 : ℝ) := by
    have hpowers : (25001098761178550909/25000000000000000000 : ℝ)^1024 ≤ (1000009216562829/1000000000000000 : ℝ)^4883 := by
      have hnat : (25001098761178550909 : ℕ)^1024*1000000000000000^4883 ≤ 1000009216562829^4883*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001098761178550909 25000000000000000000 1000009216562829 1000000000000000 1024 4883 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000009216562829/1000000000000000 : ℝ)) (X := (25001098761178550909/25000000000000000000 : ℝ)) (by norm_num) 4883 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100020078907159479023/100000000000000000000 : ℝ) ≤ (78128289340859/78125000000000 : ℝ) ^ (4883/1024 : ℝ) := by
    have hpowers : (100020078907159479023/100000000000000000000 : ℝ)^1024 ≤ (78128289340859/78125000000000 : ℝ)^4883 := by
      have hnat : (100020078907159479023 : ℕ)^1024*78125000000000^4883 ≤ 78128289340859^4883*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100020078907159479023 100000000000000000000 78128289340859 78125000000000 1024 4883 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (78128289340859/78125000000000 : ℝ)) (X := (100020078907159479023/100000000000000000000 : ℝ)) (by norm_num) 4883 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10003576276960475441/10000000000000000000 : ℝ) ≤ (5000374952815807/5000000000000000 : ℝ) ^ (4883/1024 : ℝ) := by
    have hpowers : (10003576276960475441/10000000000000000000 : ℝ)^1024 ≤ (5000374952815807/5000000000000000 : ℝ)^4883 := by
      have hnat : (10003576276960475441 : ℕ)^1024*5000000000000000^4883 ≤ 5000374952815807^4883*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10003576276960475441 10000000000000000000 5000374952815807 5000000000000000 1024 4883 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000374952815807/5000000000000000 : ℝ)) (X := (10003576276960475441/10000000000000000000 : ℝ)) (by norm_num) 4883 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1098761178550909/50000000000000000000 : ℝ) ≤ ((3639599933191506213/3640000000000000000 : ℝ)+2*(164435000831/291200000000000 : ℝ)*(2637/25000 : ℝ))^(4883/1024 : ℝ) := by
    rw [show (3639599933191506213/3640000000000000000 : ℝ)+2*(164435000831/291200000000000 : ℝ)*(2637/25000 : ℝ)=(1000009216562829/1000000000000000 : ℝ) by norm_num, show 1+2*(1098761178550909/50000000000000000000 : ℝ)=(25001098761178550909/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3576276960475441/20000000000000000000 : ℝ)+(1098761178550909/50000000000000000000 : ℝ) ≤ ((3639599933191506213/3640000000000000000 : ℝ)+(164435000831/291200000000000 : ℝ)*((4093/25000 : ℝ)+(2637/25000 : ℝ)))^(4883/1024 : ℝ) := by
    rw [show (3639599933191506213/3640000000000000000 : ℝ)+(164435000831/291200000000000 : ℝ)*((4093/25000 : ℝ)+(2637/25000 : ℝ))=(78128289340859/78125000000000 : ℝ) by norm_num, show 1+(3576276960475441/20000000000000000000 : ℝ)+(1098761178550909/50000000000000000000 : ℝ)=(100020078907159479023/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3576276960475441/20000000000000000000 : ℝ) ≤ ((3639599933191506213/3640000000000000000 : ℝ)+2*(164435000831/291200000000000 : ℝ)*(4093/25000 : ℝ))^(4883/1024 : ℝ) := by
    rw [show (3639599933191506213/3640000000000000000 : ℝ)+2*(164435000831/291200000000000 : ℝ)*(4093/25000 : ℝ)=(5000374952815807/5000000000000000 : ℝ) by norm_num, show 1+2*(3576276960475441/20000000000000000000 : ℝ)=(10003576276960475441/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3639599933191506213/3640000000000000000 : ℝ)*(X 1 0+X 2 0)+(164435000831/291200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4883/1024 : ℝ)) (lo := (2637/25000 : ℝ)) (hi := (4093/25000 : ℝ)) (c := (3639599933191506213/3640000000000000000 : ℝ)) (alpha := (164435000831/291200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3639599933191506213/3640000000000000000 : ℝ)*(X 0 1+X 2 1)+(164435000831/291200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4883/1024 : ℝ)) (lo := (2637/25000 : ℝ)) (hi := (4093/25000 : ℝ)) (c := (3639599933191506213/3640000000000000000 : ℝ)) (alpha := (164435000831/291200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3639599933191506213/3640000000000000000 : ℝ)*(X 0 2+X 1 2)+(164435000831/291200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4883/1024 : ℝ)) (lo := (2637/25000 : ℝ)) (hi := (4093/25000 : ℝ)) (c := (3639599933191506213/3640000000000000000 : ℝ)) (alpha := (164435000831/291200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-162688981/1000000000 : ℝ)*X 0 0+(2725004961/5000000000 : ℝ)*X 0 1+(1036655067/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1642_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337242523/2500000000 : ℝ)*X 1 0+(-1764249531/10000000000 : ℝ)*X 1 1+(5183275257/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1642_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674485187/5000000000 : ℝ)*X 2 0+(518327509/1000000000 : ℝ)*X 2 1+(-882124687/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1642_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2093445013/5000000000 : ℝ)*X 0 0+(1927767119/5000000000 : ℝ)*X 0 1+(2269347089/5000000000 : ℝ)*X 0 2+(2093445013/5000000000 : ℝ)*X 1 0+(1927767119/5000000000 : ℝ)*X 1 1+(2269347089/5000000000 : ℝ)*X 1 2+(2093445013/5000000000 : ℝ)*X 2 0+(1927767119/5000000000 : ℝ)*X 2 1+(2269347089/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1642_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-813477707/5000000000 : ℝ)*X 0 0+(2592644187/5000000000 : ℝ)*X 0 1+(340498479/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1642_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5277781363/10000000000 : ℝ)*X 1 0+(-1499548937/10000000000 : ℝ)*X 1 1+(5447975649/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1642_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2638890687/5000000000 : ℝ)*X 2 0+(5447975687/10000000000 : ℝ)*X 2 1+(-1499548869/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1642_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2093528811/5000000000 : ℝ)*X 0 0+(2266769069/5000000000 : ℝ)*X 0 1+(965186271/2500000000 : ℝ)*X 0 2+(2093528811/5000000000 : ℝ)*X 1 0+(2266769069/5000000000 : ℝ)*X 1 1+(965186271/2500000000 : ℝ)*X 1 2+(2093528811/5000000000 : ℝ)*X 2 0+(2266769069/5000000000 : ℝ)*X 2 1+(965186271/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1642_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1044965315851100686413726861/91000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (922328517/50000000000000 : ℝ)*(base19) + (233877123/12500000000000 : ℝ)*(base23) + (91624333/100000000000000 : ℝ)*(lower2) + (133278021/50000000000000 : ℝ)*(upper3) + (147186559/50000000000000 : ℝ)*(upper5) + (1303222851905167/50000000000000 : ℝ)*(major0) + (1303222851905167/50000000000000 : ℝ)*(major1) + (1303222851905167/50000000000000 : ℝ)*(major2) + (23431651573751/625000000000 : ℝ)*(sp0) + (1874542399658887/50000000000000 : ℝ)*(sp1) + (149963390918313/4000000000000 : ℝ)*(sp2) + (731897444715613/50000000000000 : ℝ)*(sp3) + (22392174649/100000000000000 : ℝ)*(sp4) + (9491443441/100000000000000 : ℝ)*(sp7) + (1463804380874667/100000000000000 : ℝ)*(f.failure) + (3749086643974809/100000000000000 : ℝ)*(f.sum) + (20433176219983/7280000000000000000000000000 : ℝ)*base66 + (344365563206502153/26000000000000000000000000000000 : ℝ)*base67 + (442063035390502153/26000000000000000000000000000000 : ℝ)*base69 + (292725988362502153/26000000000000000000000000000000 : ℝ)*base71 + (28747120327217/7280000000000000000000000000 : ℝ)*base73 + (494382253458502153/26000000000000000000000000000000 : ℝ)*base75 + (366917993470502153/26000000000000000000000000000000 : ℝ)*base77 + (200204377102502153/26000000000000000000000000000000 : ℝ)*base79 + (25365996617617/7280000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (75505433/10000000000000000000000 : ℝ)*base90 + (75505433/10000000000000000000000 : ℝ)*base92 + (75505433/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (123936601986238660136409351/22750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6658257/781250000000 : ℝ)*(base19) + (882230493/100000000000000 : ℝ)*(base23) + (4365049/100000000000000 : ℝ)*(upper2) + (29079591/25000000000000 : ℝ)*(upper3) + (7549233/6250000000000 : ℝ)*(upper5) + (330821821749803/12500000000000 : ℝ)*(major0) + (330821821749803/12500000000000 : ℝ)*(major1) + (330821821749803/12500000000000 : ℝ)*(major2) + (10046106733/100000000000000 : ℝ)*(sp1) + (11066854367/100000000000000 : ℝ)*(sp2) + (1903403917618189/50000000000000 : ℝ)*(sp4) + (3806796936872749/100000000000000 : ℝ)*(sp5) + (1903397943075759/50000000000000 : ℝ)*(sp6) + (743170565584187/50000000000000 : ℝ)*(sp7) + (743170565584187/50000000000000 : ℝ)*(f.failure) + (1903403917618189/50000000000000 : ℝ)*(f.sum) + (8486477881227/1820000000000000000000000000 : ℝ)*base66 + (25768402769615923/6500000000000000000000000000000 : ℝ)*base68 + (33546052025615923/6500000000000000000000000000000 : ℝ)*base70 + (35541386555115923/6500000000000000000000000000000 : ℝ)*base72 + (5073689302027/1820000000000000000000000000 : ℝ)*base74 + (8015283710615923/6500000000000000000000000000000 : ℝ)*base76 + (39871313890615923/6500000000000000000000000000000 : ℝ)*base78 + (70005397675615923/6500000000000000000000000000000 : ℝ)*base80 + (11076570622827/1820000000000000000000000000 : ℝ)*base82 + (27548087/5000000000000000000000 : ℝ)*base89 + (27548087/5000000000000000000000 : ℝ)*base91 + (27548087/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1642_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (178059701/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4093/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2637/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5311/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16289/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1642_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1642_s4_0 (p : ℝ) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-813472453/5000000000 : ℝ)*x 0 + (2724867161/5000000000 : ℝ)*x 1 + (2591757049/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (813472453/5000000000 : ℝ)^4887 ≤ (2513416107881/25000000000000 : ℝ)^3863 := by
    have hnat : (813472453 : ℕ)^4887*25000000000000^3863 ≤ 2513416107881^3863*5000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      813472453 5000000000 2513416107881 25000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2724867161/5000000000 : ℝ)^4887 ≤ (11599358936953/25000000000000 : ℝ)^3863 := by
    have hnat : (2724867161 : ℕ)^4887*25000000000000^3863 ≤ 11599358936953^3863*5000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2724867161 5000000000 11599358936953 25000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2591757049/5000000000 : ℝ)^4887 ≤ (43548899806649/100000000000000 : ℝ)^3863 := by
    have hnat : (2591757049 : ℕ)^4887*100000000000000^3863 ≤ 43548899806649^3863*5000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591757049 5000000000 43548899806649 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4887/1024 : ℝ)) 4887 3863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-813472453/5000000000 : ℝ), (2724867161/5000000000 : ℝ), (2591757049/5000000000 : ℝ)] ![(2513416107881/25000000000000 : ℝ), (11599358936953/25000000000000 : ℝ), (43548899806649/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-813472453/5000000000 : ℝ)|^4887 ≤ (2513416107881/25000000000000 : ℝ)^3863
        have hw : |(-813472453/5000000000 : ℝ)|=(813472453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2724867161/5000000000 : ℝ)|^4887 ≤ (11599358936953/25000000000000 : ℝ)^3863
        have hw : |(2724867161/5000000000 : ℝ)|=(2724867161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2591757049/5000000000 : ℝ)|^4887 ≤ (43548899806649/100000000000000 : ℝ)^3863
        have hw : |(2591757049/5000000000 : ℝ)|=(2591757049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1642_s4_1 (p : ℝ) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668611917/1250000000 : ℝ)*x 0 + (-441007911/2500000000 : ℝ)*x 1 + (5183514379/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668611917/1250000000 : ℝ)^4887 ≤ (45314024148811/100000000000000 : ℝ)^3863 := by
    have hnat : (668611917 : ℕ)^4887*100000000000000^3863 ≤ 45314024148811^3863*1250000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668611917 1250000000 45314024148811 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (441007911/2500000000 : ℝ)^4887 ≤ (11137073052889/100000000000000 : ℝ)^3863 := by
    have hnat : (441007911 : ℕ)^4887*100000000000000^3863 ≤ 11137073052889^3863*2500000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441007911 2500000000 11137073052889 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5183514379/10000000000 : ℝ)^4887 ≤ (1360903212289/3125000000000 : ℝ)^3863 := by
    have hnat : (5183514379 : ℕ)^4887*3125000000000^3863 ≤ 1360903212289^3863*10000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183514379 10000000000 1360903212289 3125000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4887/1024 : ℝ)) 4887 3863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668611917/1250000000 : ℝ), (-441007911/2500000000 : ℝ), (5183514379/10000000000 : ℝ)] ![(45314024148811/100000000000000 : ℝ), (11137073052889/100000000000000 : ℝ), (1360903212289/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668611917/1250000000 : ℝ)|^4887 ≤ (45314024148811/100000000000000 : ℝ)^3863
        have hw : |(668611917/1250000000 : ℝ)|=(668611917/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-441007911/2500000000 : ℝ)|^4887 ≤ (11137073052889/100000000000000 : ℝ)^3863
        have hw : |(-441007911/2500000000 : ℝ)|=(441007911/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5183514379/10000000000 : ℝ)|^4887 ≤ (1360903212289/3125000000000 : ℝ)^3863
        have hw : |(5183514379/10000000000 : ℝ)|=(5183514379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1642_s4_2 (p : ℝ) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674447731/5000000000 : ℝ)*x 0 + (5183514039/10000000000 : ℝ)*x 1 + (-882015963/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674447731/5000000000 : ℝ)^4887 ≤ (45314025499193/100000000000000 : ℝ)^3863 := by
    have hnat : (2674447731 : ℕ)^4887*100000000000000^3863 ≤ 45314025499193^3863*5000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674447731 5000000000 45314025499193 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5183514039/10000000000 : ℝ)^4887 ≤ (4354889917957/10000000000000 : ℝ)^3863 := by
    have hnat : (5183514039 : ℕ)^4887*10000000000000^3863 ≤ 4354889917957^3863*10000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183514039 10000000000 4354889917957 10000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (882015963/5000000000 : ℝ)^4887 ≤ (43504200411/390625000000 : ℝ)^3863 := by
    have hnat : (882015963 : ℕ)^4887*390625000000^3863 ≤ 43504200411^3863*5000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      882015963 5000000000 43504200411 390625000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4887/1024 : ℝ)) 4887 3863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674447731/5000000000 : ℝ), (5183514039/10000000000 : ℝ), (-882015963/5000000000 : ℝ)] ![(45314025499193/100000000000000 : ℝ), (4354889917957/10000000000000 : ℝ), (43504200411/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674447731/5000000000 : ℝ)|^4887 ≤ (45314025499193/100000000000000 : ℝ)^3863
        have hw : |(2674447731/5000000000 : ℝ)|=(2674447731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5183514039/10000000000 : ℝ)|^4887 ≤ (4354889917957/10000000000000 : ℝ)^3863
        have hw : |(5183514039/10000000000 : ℝ)|=(5183514039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-882015963/5000000000 : ℝ)|^4887 ≤ (43504200411/390625000000 : ℝ)^3863
        have hw : |(-882015963/5000000000 : ℝ)|=(882015963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1642_s4_3 (p : ℝ) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2093462637/5000000000 : ℝ)*x 0 + (3856189103/10000000000 : ℝ)*x 1 + (4538032499/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2093462637/5000000000 : ℝ)^4887 ≤ (33240503046581/100000000000000 : ℝ)^3863 := by
    have hnat : (2093462637 : ℕ)^4887*100000000000000^3863 ≤ 33240503046581^3863*5000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2093462637 5000000000 33240503046581 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3856189103/10000000000 : ℝ)^4887 ≤ (5990838329983/20000000000000 : ℝ)^3863 := by
    have hnat : (3856189103 : ℕ)^4887*20000000000000^3863 ≤ 5990838329983^3863*10000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3856189103 10000000000 5990838329983 20000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4538032499/10000000000 : ℝ)^4887 ≤ (36805305293159/100000000000000 : ℝ)^3863 := by
    have hnat : (4538032499 : ℕ)^4887*100000000000000^3863 ≤ 36805305293159^3863*10000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4538032499 10000000000 36805305293159 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4887/1024 : ℝ)) 4887 3863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2093462637/5000000000 : ℝ), (3856189103/10000000000 : ℝ), (4538032499/10000000000 : ℝ)] ![(33240503046581/100000000000000 : ℝ), (5990838329983/20000000000000 : ℝ), (36805305293159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2093462637/5000000000 : ℝ)|^4887 ≤ (33240503046581/100000000000000 : ℝ)^3863
        have hw : |(2093462637/5000000000 : ℝ)|=(2093462637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3856189103/10000000000 : ℝ)|^4887 ≤ (5990838329983/20000000000000 : ℝ)^3863
        have hw : |(3856189103/10000000000 : ℝ)|=(3856189103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4538032499/10000000000 : ℝ)|^4887 ≤ (36805305293159/100000000000000 : ℝ)^3863
        have hw : |(4538032499/10000000000 : ℝ)|=(4538032499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1642_s4_4 (p : ℝ) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-162701001/1000000000 : ℝ)*x 0 + (648189933/1250000000 : ℝ)*x 1 + (5447707947/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (162701001/1000000000 : ℝ)^4887 ≤ (10054173386243/100000000000000 : ℝ)^3863 := by
    have hnat : (162701001 : ℕ)^4887*100000000000000^3863 ≤ 10054173386243^3863*1000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      162701001 1000000000 10054173386243 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (648189933/1250000000 : ℝ)^4887 ≤ (43570214861187/100000000000000 : ℝ)^3863 := by
    have hnat : (648189933 : ℕ)^4887*100000000000000^3863 ≤ 43570214861187^3863*1250000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      648189933 1250000000 43570214861187 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5447707947/10000000000 : ℝ)^4887 ≤ (23187805865373/50000000000000 : ℝ)^3863 := by
    have hnat : (5447707947 : ℕ)^4887*50000000000000^3863 ≤ 23187805865373^3863*10000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5447707947 10000000000 23187805865373 50000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4887/1024 : ℝ)) 4887 3863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-162701001/1000000000 : ℝ), (648189933/1250000000 : ℝ), (5447707947/10000000000 : ℝ)] ![(10054173386243/100000000000000 : ℝ), (43570214861187/100000000000000 : ℝ), (23187805865373/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-162701001/1000000000 : ℝ)|^4887 ≤ (10054173386243/100000000000000 : ℝ)^3863
        have hw : |(-162701001/1000000000 : ℝ)|=(162701001/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(648189933/1250000000 : ℝ)|^4887 ≤ (43570214861187/100000000000000 : ℝ)^3863
        have hw : |(648189933/1250000000 : ℝ)|=(648189933/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5447707947/10000000000 : ℝ)|^4887 ≤ (23187805865373/50000000000000 : ℝ)^3863
        have hw : |(5447707947/10000000000 : ℝ)|=(5447707947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1642_s4_5 (p : ℝ) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2638922161/5000000000 : ℝ)*x 0 + (-374959473/2500000000 : ℝ)*x 1 + (2723853973/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638922161/5000000000 : ℝ)^4887 ≤ (22276946386091/50000000000000 : ℝ)^3863 := by
    have hnat : (2638922161 : ℕ)^4887*50000000000000^3863 ≤ 22276946386091^3863*5000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638922161 5000000000 22276946386091 50000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (374959473/2500000000 : ℝ)^4887 ≤ (1133811936669/12500000000000 : ℝ)^3863 := by
    have hnat : (374959473 : ℕ)^4887*12500000000000^3863 ≤ 1133811936669^3863*2500000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      374959473 2500000000 1133811936669 12500000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2723853973/5000000000 : ℝ)^4887 ≤ (46375611719977/100000000000000 : ℝ)^3863 := by
    have hnat : (2723853973 : ℕ)^4887*100000000000000^3863 ≤ 46375611719977^3863*5000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2723853973 5000000000 46375611719977 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4887/1024 : ℝ)) 4887 3863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638922161/5000000000 : ℝ), (-374959473/2500000000 : ℝ), (2723853973/5000000000 : ℝ)] ![(22276946386091/50000000000000 : ℝ), (1133811936669/12500000000000 : ℝ), (46375611719977/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638922161/5000000000 : ℝ)|^4887 ≤ (22276946386091/50000000000000 : ℝ)^3863
        have hw : |(2638922161/5000000000 : ℝ)|=(2638922161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-374959473/2500000000 : ℝ)|^4887 ≤ (1133811936669/12500000000000 : ℝ)^3863
        have hw : |(-374959473/2500000000 : ℝ)|=(374959473/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2723853973/5000000000 : ℝ)|^4887 ≤ (46375611719977/100000000000000 : ℝ)^3863
        have hw : |(2723853973/5000000000 : ℝ)|=(2723853973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1642_s4_6 (p : ℝ) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2638922161/5000000000 : ℝ)*x 0 + (5447707947/10000000000 : ℝ)*x 1 + (-1499837891/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638922161/5000000000 : ℝ)^4887 ≤ (22276946386091/50000000000000 : ℝ)^3863 := by
    have hnat : (2638922161 : ℕ)^4887*50000000000000^3863 ≤ 22276946386091^3863*5000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638922161 5000000000 22276946386091 50000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5447707947/10000000000 : ℝ)^4887 ≤ (23187805865373/50000000000000 : ℝ)^3863 := by
    have hnat : (5447707947 : ℕ)^4887*50000000000000^3863 ≤ 23187805865373^3863*10000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5447707947 10000000000 23187805865373 50000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1499837891/10000000000 : ℝ)^4887 ≤ (9070495485701/100000000000000 : ℝ)^3863 := by
    have hnat : (1499837891 : ℕ)^4887*100000000000000^3863 ≤ 9070495485701^3863*10000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1499837891 10000000000 9070495485701 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4887/1024 : ℝ)) 4887 3863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638922161/5000000000 : ℝ), (5447707947/10000000000 : ℝ), (-1499837891/10000000000 : ℝ)] ![(22276946386091/50000000000000 : ℝ), (23187805865373/50000000000000 : ℝ), (9070495485701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638922161/5000000000 : ℝ)|^4887 ≤ (22276946386091/50000000000000 : ℝ)^3863
        have hw : |(2638922161/5000000000 : ℝ)|=(2638922161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5447707947/10000000000 : ℝ)|^4887 ≤ (23187805865373/50000000000000 : ℝ)^3863
        have hw : |(5447707947/10000000000 : ℝ)|=(5447707947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1499837891/10000000000 : ℝ)|^4887 ≤ (9070495485701/100000000000000 : ℝ)^3863
        have hw : |(-1499837891/10000000000 : ℝ)|=(1499837891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1642_s4_7 (p : ℝ) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4187092461/10000000000 : ℝ)*x 0 + (2266447781/5000000000 : ℝ)*x 1 + (3861379991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4187092461/10000000000 : ℝ)^4887 ≤ (33242182217143/100000000000000 : ℝ)^3863 := by
    have hnat : (4187092461 : ℕ)^4887*100000000000000^3863 ≤ 33242182217143^3863*10000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4187092461 10000000000 33242182217143 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2266447781/5000000000 : ℝ)^4887 ≤ (9188151660107/25000000000000 : ℝ)^3863 := by
    have hnat : (2266447781 : ℕ)^4887*25000000000000^3863 ≤ 9188151660107^3863*5000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2266447781 5000000000 9188151660107 25000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3861379991/10000000000 : ℝ)^4887 ≤ (30005211129247/100000000000000 : ℝ)^3863 := by
    have hnat : (3861379991 : ℕ)^4887*100000000000000^3863 ≤ 30005211129247^3863*10000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3861379991 10000000000 30005211129247 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4887/1024 : ℝ)) 4887 3863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4187092461/10000000000 : ℝ), (2266447781/5000000000 : ℝ), (3861379991/10000000000 : ℝ)] ![(33242182217143/100000000000000 : ℝ), (9188151660107/25000000000000 : ℝ), (30005211129247/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4187092461/10000000000 : ℝ)|^4887 ≤ (33242182217143/100000000000000 : ℝ)^3863
        have hw : |(4187092461/10000000000 : ℝ)|=(4187092461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2266447781/5000000000 : ℝ)|^4887 ≤ (9188151660107/25000000000000 : ℝ)^3863
        have hw : |(2266447781/5000000000 : ℝ)|=(2266447781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3861379991/10000000000 : ℝ)|^4887 ≤ (30005211129247/100000000000000 : ℝ)^3863
        have hw : |(3861379991/10000000000 : ℝ)|=(3861379991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1642_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (178059701/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16289/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5311/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2657/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16283/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16289/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5311/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16289/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5311/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16289/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5311/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16289/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5311/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16289/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5311/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16289/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5311/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5311/50000 : ℝ) ^ (4883/1024 : ℝ) ≤ (568004114907079/25000000000000000000 : ℝ) := by
    have hpowers : (5311/50000 : ℝ)^4883 ≤ (568004114907079/25000000000000000000 : ℝ)^1024 := by
      have hnat : (5311 : ℕ)^4883*25000000000000000000^1024 ≤ 568004114907079^1024*50000^4883 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5311 50000 568004114907079 25000000000000000000 4883 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5311/50000 : ℝ)) (X := (568004114907079/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4883 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16289/100000 : ℝ) ^ (4883/1024 : ℝ) ≤ (17453215777544301/100000000000000000000 : ℝ) := by
    have hpowers : (16289/100000 : ℝ)^4883 ≤ (17453215777544301/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16289 : ℕ)^4883*100000000000000000000^1024 ≤ 17453215777544301^1024*100000^4883 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16289 100000 17453215777544301 100000000000000000000 4883 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16289/100000 : ℝ)) (X := (17453215777544301/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4883 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500568004114907079/12500000000000000000 : ℝ) ≤ (10000095289907079/10000000000000000 : ℝ) ^ (4883/1024 : ℝ) := by
    have hpowers : (12500568004114907079/12500000000000000000 : ℝ)^1024 ≤ (10000095289907079/10000000000000000 : ℝ)^4883 := by
      have hnat : (12500568004114907079 : ℕ)^1024*10000000000000000^4883 ≤ 10000095289907079^4883*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500568004114907079 12500000000000000000 10000095289907079 10000000000000000 1024 4883 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000095289907079/10000000000000000 : ℝ)) (X := (12500568004114907079/12500000000000000000 : ℝ)) (by norm_num) 4883 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100019725232237172617/100000000000000000000 : ℝ) ≤ (5000206809990197/5000000000000000 : ℝ) ^ (4883/1024 : ℝ) := by
    have hpowers : (100019725232237172617/100000000000000000000 : ℝ)^1024 ≤ (5000206809990197/5000000000000000 : ℝ)^4883 := by
      have hnat : (100019725232237172617 : ℕ)^1024*5000000000000000^4883 ≤ 5000206809990197^4883*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100019725232237172617 100000000000000000000 5000206809990197 5000000000000000 1024 4883 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000206809990197/5000000000000000 : ℝ)) (X := (100019725232237172617/100000000000000000000 : ℝ)) (by norm_num) 4883 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50017453215777544301/50000000000000000000 : ℝ) ≤ (10000731950053709/10000000000000000 : ℝ) ^ (4883/1024 : ℝ) := by
    have hpowers : (50017453215777544301/50000000000000000000 : ℝ)^1024 ≤ (10000731950053709/10000000000000000 : ℝ)^4883 := by
      have hnat : (50017453215777544301 : ℕ)^1024*10000000000000000^4883 ≤ 10000731950053709^4883*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50017453215777544301 50000000000000000000 10000731950053709 10000000000000000 1024 4883 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000731950053709/10000000000000000 : ℝ)) (X := (50017453215777544301/50000000000000000000 : ℝ)) (by norm_num) 4883 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(568004114907079/25000000000000000000 : ℝ) ≤ ((56663777403825912833/56670000000000000000 : ℝ)+2*(63666014663/113340000000000 : ℝ)*(5311/50000 : ℝ))^(4883/1024 : ℝ) := by
    rw [show (56663777403825912833/56670000000000000000 : ℝ)+2*(63666014663/113340000000000 : ℝ)*(5311/50000 : ℝ)=(10000095289907079/10000000000000000 : ℝ) by norm_num, show 1+2*(568004114907079/25000000000000000000 : ℝ)=(12500568004114907079/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17453215777544301/100000000000000000000 : ℝ)+(568004114907079/25000000000000000000 : ℝ) ≤ ((56663777403825912833/56670000000000000000 : ℝ)+(63666014663/113340000000000 : ℝ)*((16289/100000 : ℝ)+(5311/50000 : ℝ)))^(4883/1024 : ℝ) := by
    rw [show (56663777403825912833/56670000000000000000 : ℝ)+(63666014663/113340000000000 : ℝ)*((16289/100000 : ℝ)+(5311/50000 : ℝ))=(5000206809990197/5000000000000000 : ℝ) by norm_num, show 1+(17453215777544301/100000000000000000000 : ℝ)+(568004114907079/25000000000000000000 : ℝ)=(100019725232237172617/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17453215777544301/100000000000000000000 : ℝ) ≤ ((56663777403825912833/56670000000000000000 : ℝ)+2*(63666014663/113340000000000 : ℝ)*(16289/100000 : ℝ))^(4883/1024 : ℝ) := by
    rw [show (56663777403825912833/56670000000000000000 : ℝ)+2*(63666014663/113340000000000 : ℝ)*(16289/100000 : ℝ)=(10000731950053709/10000000000000000 : ℝ) by norm_num, show 1+2*(17453215777544301/100000000000000000000 : ℝ)=(50017453215777544301/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (56663777403825912833/56670000000000000000 : ℝ)*(X 1 0+X 2 0)+(63666014663/113340000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4883/1024 : ℝ)) (lo := (5311/50000 : ℝ)) (hi := (16289/100000 : ℝ)) (c := (56663777403825912833/56670000000000000000 : ℝ)) (alpha := (63666014663/113340000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (56663777403825912833/56670000000000000000 : ℝ)*(X 0 1+X 2 1)+(63666014663/113340000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4883/1024 : ℝ)) (lo := (5311/50000 : ℝ)) (hi := (16289/100000 : ℝ)) (c := (56663777403825912833/56670000000000000000 : ℝ)) (alpha := (63666014663/113340000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (56663777403825912833/56670000000000000000 : ℝ)*(X 0 2+X 1 2)+(63666014663/113340000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4883/1024 : ℝ)) (lo := (5311/50000 : ℝ)) (hi := (16289/100000 : ℝ)) (c := (56663777403825912833/56670000000000000000 : ℝ)) (alpha := (63666014663/113340000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-813472453/5000000000 : ℝ)*X 0 0+(2724867161/5000000000 : ℝ)*X 0 1+(2591757049/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1642_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668611917/1250000000 : ℝ)*X 1 0+(-441007911/2500000000 : ℝ)*X 1 1+(5183514379/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1642_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674447731/5000000000 : ℝ)*X 2 0+(5183514039/10000000000 : ℝ)*X 2 1+(-882015963/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1642_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2093462637/5000000000 : ℝ)*X 0 0+(3856189103/10000000000 : ℝ)*X 0 1+(4538032499/10000000000 : ℝ)*X 0 2+(2093462637/5000000000 : ℝ)*X 1 0+(3856189103/10000000000 : ℝ)*X 1 1+(4538032499/10000000000 : ℝ)*X 1 2+(2093462637/5000000000 : ℝ)*X 2 0+(3856189103/10000000000 : ℝ)*X 2 1+(4538032499/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1642_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-162701001/1000000000 : ℝ)*X 0 0+(648189933/1250000000 : ℝ)*X 0 1+(5447707947/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1642_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2638922161/5000000000 : ℝ)*X 1 0+(-374959473/2500000000 : ℝ)*X 1 1+(2723853973/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1642_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2638922161/5000000000 : ℝ)*X 2 0+(5447707947/10000000000 : ℝ)*X 2 1+(-1499837891/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1642_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4187092461/10000000000 : ℝ)*X 0 0+(2266447781/5000000000 : ℝ)*X 0 1+(3861379991/10000000000 : ℝ)*X 0 2+(4187092461/10000000000 : ℝ)*X 1 0+(2266447781/5000000000 : ℝ)*X 1 1+(3861379991/10000000000 : ℝ)*X 1 2+(4187092461/10000000000 : ℝ)*X 2 0+(2266447781/5000000000 : ℝ)*X 2 1+(3861379991/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1642_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15183718892035195169625099/5903125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6300969/3125000000000 : ℝ)*(base19) + (48028329/12500000000000 : ℝ)*(base23) + (12618879/25000000000000 : ℝ)*(upper2) + (2883543/2000000000000 : ℝ)*(upper3) + (16321614162711/625000000000 : ℝ)*(major0) + (16321614162711/625000000000 : ℝ)*(major1) + (16321614162711/625000000000 : ℝ)*(major2) + (3756294749535941/100000000000000 : ℝ)*(sp0) + (1878148380906321/50000000000000 : ℝ)*(sp1) + (939074140006147/25000000000000 : ℝ)*(sp2) + (146661540523769/10000000000000 : ℝ)*(sp3) + (2213907709/100000000000000 : ℝ)*(sp4) + (19192431/100000000000000 : ℝ)*(sp6) + (4077647861/100000000000000 : ℝ)*(sp7) + (91663717680347/6250000000000 : ℝ)*(f.failure) + (75125939268873/2000000000000 : ℝ)*(f.sum) + (2728922199651/377800000000000000000000000 : ℝ)*base65 + (99958360830260921/11806250000000000000000000000000 : ℝ)*base67 + (96611332968960921/11806250000000000000000000000000 : ℝ)*base69 + (154228259259592171/11806250000000000000000000000000 : ℝ)*base71 + (88137819997/59031250000000000000000000 : ℝ)*base73 + (113896631282379671/11806250000000000000000000000000 : ℝ)*base75 + (52213891863254671/11806250000000000000000000000000 : ℝ)*base77 + (8714925011482829/11806250000000000000000000000000 : ℝ)*base80 + (1415132537433/472250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (396247/625000000000000000000 : ℝ)*base89 + (396247/625000000000000000000 : ℝ)*base91 + (396247/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (521989970549017858886131707/188900000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (411360629/100000000000000 : ℝ)*(base19) + (2229203/500000000000 : ℝ)*(base23) + (129052929/100000000000000 : ℝ)*(lower1) + (57829043/100000000000000 : ℝ)*(upper3) + (1549051/10000000000000 : ℝ)*(lower4) + (7206289/12500000000000 : ℝ)*(upper5) + (530321175496379/20000000000000 : ℝ)*(major0) + (530321175496379/20000000000000 : ℝ)*(major1) + (530321175496379/20000000000000 : ℝ)*(major2) + (76211979/20000000000000 : ℝ)*(sp2) + (3814044904406441/100000000000000 : ℝ)*(sp4) + (953511123261453/25000000000000 : ℝ)*(sp5) + (1907022038752973/50000000000000 : ℝ)*(sp6) + (744583379223437/50000000000000 : ℝ)*(sp7) + (744583379223437/50000000000000 : ℝ)*(f.failure) + (3814044904406441/100000000000000 : ℝ)*(f.sum) + (9919280143783/5667000000000000000000000000 : ℝ)*base66 + (2308134284040389431/377800000000000000000000000000000 : ℝ)*base68 + (1462558927972589431/377800000000000000000000000000000 : ℝ)*base70 + (28954804856875189431/377800000000000000000000000000000 : ℝ)*base72 + (11386593271243/5667000000000000000000000000 : ℝ)*base74 + (14472767190682410569/377800000000000000000000000000000 : ℝ)*base75 + (973394503088410569/377800000000000000000000000000000 : ℝ)*base77 + (3148305245865789431/377800000000000000000000000000000 : ℝ)*base80 + (59983530112441/5667000000000000000000000000 : ℝ)*base82 + (54412337/5000000000000000000000 : ℝ)*base89 + (54412337/5000000000000000000000 : ℝ)*base91 + (54412337/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1642_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (178059701/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16289/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5311/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2657/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16283/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1642_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1642_box_0 (p : ℝ) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-170757453/1250000000 : ℝ)*x 0 + (338127483/625000000 : ℝ)*x 1 + (2705019773/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (170757453/1250000000 : ℝ)^4887 ≤ (4029682784833/50000000000000 : ℝ)^3863 := by
    have hnat : (170757453 : ℕ)^4887*50000000000000^3863 ≤ 4029682784833^3863*1250000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170757453 1250000000 4029682784833 50000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (338127483/625000000 : ℝ)^4887 ≤ (9194063637389/20000000000000 : ℝ)^3863 := by
    have hnat : (338127483 : ℕ)^4887*20000000000000^3863 ≤ 9194063637389^3863*625000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338127483 625000000 9194063637389 20000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2705019773/5000000000 : ℝ)^4887 ≤ (11492579057627/25000000000000 : ℝ)^3863 := by
    have hnat : (2705019773 : ℕ)^4887*25000000000000^3863 ≤ 11492579057627^3863*5000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705019773 5000000000 11492579057627 25000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4887/1024 : ℝ)) 4887 3863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-170757453/1250000000 : ℝ), (338127483/625000000 : ℝ), (2705019773/5000000000 : ℝ)] ![(4029682784833/50000000000000 : ℝ), (9194063637389/20000000000000 : ℝ), (11492579057627/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-170757453/1250000000 : ℝ)|^4887 ≤ (4029682784833/50000000000000 : ℝ)^3863
        have hw : |(-170757453/1250000000 : ℝ)|=(170757453/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(338127483/625000000 : ℝ)|^4887 ≤ (9194063637389/20000000000000 : ℝ)^3863
        have hw : |(338127483/625000000 : ℝ)|=(338127483/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2705019773/5000000000 : ℝ)|^4887 ≤ (11492579057627/25000000000000 : ℝ)^3863
        have hw : |(2705019773/5000000000 : ℝ)|=(2705019773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1642_box_1 (p : ℝ) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5251178261/10000000000 : ℝ)*x 0 + (-49666013/312500000 : ℝ)*x 1 + (5410039437/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5251178261/10000000000 : ℝ)^4887 ≤ (44269306271831/100000000000000 : ℝ)^3863 := by
    have hnat : (5251178261 : ℕ)^4887*100000000000000^3863 ≤ 44269306271831^3863*10000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5251178261 10000000000 44269306271831 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (49666013/312500000 : ℝ)^4887 ≤ (9760378655447/100000000000000 : ℝ)^3863 := by
    have hnat : (49666013 : ℕ)^4887*100000000000000^3863 ≤ 9760378655447^3863*312500000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49666013 312500000 9760378655447 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5410039437/10000000000 : ℝ)^4887 ≤ (9194063011759/20000000000000 : ℝ)^3863 := by
    have hnat : (5410039437 : ℕ)^4887*20000000000000^3863 ≤ 9194063011759^3863*10000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410039437 10000000000 9194063011759 20000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4887/1024 : ℝ)) 4887 3863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5251178261/10000000000 : ℝ), (-49666013/312500000 : ℝ), (5410039437/10000000000 : ℝ)] ![(44269306271831/100000000000000 : ℝ), (9760378655447/100000000000000 : ℝ), (9194063011759/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5251178261/10000000000 : ℝ)|^4887 ≤ (44269306271831/100000000000000 : ℝ)^3863
        have hw : |(5251178261/10000000000 : ℝ)|=(5251178261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-49666013/312500000 : ℝ)|^4887 ≤ (9760378655447/100000000000000 : ℝ)^3863
        have hw : |(-49666013/312500000 : ℝ)|=(49666013/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5410039437/10000000000 : ℝ)|^4887 ≤ (9194063011759/20000000000000 : ℝ)^3863
        have hw : |(5410039437/10000000000 : ℝ)|=(5410039437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1642_box_2 (p : ℝ) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (210047123/400000000 : ℝ)*x 0 + (135250991/250000000 : ℝ)*x 1 + (-1589312391/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210047123/400000000 : ℝ)^4887 ≤ (345853939751/781250000000 : ℝ)^3863 := by
    have hnat : (210047123 : ℕ)^4887*781250000000^3863 ≤ 345853939751^3863*400000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210047123 400000000 345853939751 781250000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (135250991/250000000 : ℝ)^4887 ≤ (1838812689639/4000000000000 : ℝ)^3863 := by
    have hnat : (135250991 : ℕ)^4887*4000000000000^3863 ≤ 1838812689639^3863*250000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135250991 250000000 1838812689639 4000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1589312391/10000000000 : ℝ)^4887 ≤ (4880189230609/50000000000000 : ℝ)^3863 := by
    have hnat : (1589312391 : ℕ)^4887*50000000000000^3863 ≤ 4880189230609^3863*10000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1589312391 10000000000 4880189230609 50000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4887/1024 : ℝ)) 4887 3863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(210047123/400000000 : ℝ), (135250991/250000000 : ℝ), (-1589312391/10000000000 : ℝ)] ![(345853939751/781250000000 : ℝ), (1838812689639/4000000000000 : ℝ), (4880189230609/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(210047123/400000000 : ℝ)|^4887 ≤ (345853939751/781250000000 : ℝ)^3863
        have hw : |(210047123/400000000 : ℝ)|=(210047123/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(135250991/250000000 : ℝ)|^4887 ≤ (1838812689639/4000000000000 : ℝ)^3863
        have hw : |(135250991/250000000 : ℝ)|=(135250991/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1589312391/10000000000 : ℝ)|^4887 ≤ (4880189230609/50000000000000 : ℝ)^3863
        have hw : |(-1589312391/10000000000 : ℝ)|=(1589312391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1642_box_3 (p : ℝ) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4464271033/10000000000 : ℝ)*x 0 + (4060407777/10000000000 : ℝ)*x 1 + (406040761/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4464271033/10000000000 : ℝ)^4887 ≤ (1802506339293/5000000000000 : ℝ)^3863 := by
    have hnat : (4464271033 : ℕ)^4887*5000000000000^3863 ≤ 1802506339293^3863*10000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4464271033 10000000000 1802506339293 5000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4060407777/10000000000 : ℝ)^4887 ≤ (399686717917/1250000000000 : ℝ)^3863 := by
    have hnat : (4060407777 : ℕ)^4887*1250000000000^3863 ≤ 399686717917^3863*10000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4060407777 10000000000 399686717917 1250000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (406040761/1000000000 : ℝ)^4887 ≤ (31974935769663/100000000000000 : ℝ)^3863 := by
    have hnat : (406040761 : ℕ)^4887*100000000000000^3863 ≤ 31974935769663^3863*1000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      406040761 1000000000 31974935769663 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4887/1024 : ℝ)) 4887 3863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4464271033/10000000000 : ℝ), (4060407777/10000000000 : ℝ), (406040761/1000000000 : ℝ)] ![(1802506339293/5000000000000 : ℝ), (399686717917/1250000000000 : ℝ), (31974935769663/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4464271033/10000000000 : ℝ)|^4887 ≤ (1802506339293/5000000000000 : ℝ)^3863
        have hw : |(4464271033/10000000000 : ℝ)|=(4464271033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4060407777/10000000000 : ℝ)|^4887 ≤ (399686717917/1250000000000 : ℝ)^3863
        have hw : |(4060407777/10000000000 : ℝ)|=(4060407777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(406040761/1000000000 : ℝ)|^4887 ≤ (31974935769663/100000000000000 : ℝ)^3863
        have hw : |(406040761/1000000000 : ℝ)|=(406040761/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1642_box_4 (p : ℝ) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-29663481/156250000 : ℝ)*x 0 + (5215514183/10000000000 : ℝ)*x 1 + (325969643/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (29663481/156250000 : ℝ)^4887 ≤ (763838747989/6250000000000 : ℝ)^3863 := by
    have hnat : (29663481 : ℕ)^4887*6250000000000^3863 ≤ 763838747989^3863*156250000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      29663481 156250000 763838747989 6250000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5215514183/10000000000 : ℝ)^4887 ≤ (21944644724169/50000000000000 : ℝ)^3863 := by
    have hnat : (5215514183 : ℕ)^4887*50000000000000^3863 ≤ 21944644724169^3863*10000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215514183 10000000000 21944644724169 50000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (325969643/625000000 : ℝ)^4887 ≤ (43889290566149/100000000000000 : ℝ)^3863 := by
    have hnat : (325969643 : ℕ)^4887*100000000000000^3863 ≤ 43889290566149^3863*625000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      325969643 625000000 43889290566149 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4887/1024 : ℝ)) 4887 3863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-29663481/156250000 : ℝ), (5215514183/10000000000 : ℝ), (325969643/625000000 : ℝ)] ![(763838747989/6250000000000 : ℝ), (21944644724169/50000000000000 : ℝ), (43889290566149/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-29663481/156250000 : ℝ)|^4887 ≤ (763838747989/6250000000000 : ℝ)^3863
        have hw : |(-29663481/156250000 : ℝ)|=(29663481/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5215514183/10000000000 : ℝ)|^4887 ≤ (21944644724169/50000000000000 : ℝ)^3863
        have hw : |(5215514183/10000000000 : ℝ)|=(5215514183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(325969643/625000000 : ℝ)|^4887 ≤ (43889290566149/100000000000000 : ℝ)^3863
        have hw : |(325969643/625000000 : ℝ)|=(325969643/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1642_box_5 (p : ℝ) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5384840311/10000000000 : ℝ)*x 0 + (-418124973/2500000000 : ℝ)*x 1 + (5215514727/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5384840311/10000000000 : ℝ)^4887 ≤ (45699600471743/100000000000000 : ℝ)^3863 := by
    have hnat : (5384840311 : ℕ)^4887*100000000000000^3863 ≤ 45699600471743^3863*10000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384840311 10000000000 45699600471743 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (418124973/2500000000 : ℝ)^4887 ≤ (10411104267663/100000000000000 : ℝ)^3863 := by
    have hnat : (418124973 : ℕ)^4887*100000000000000^3863 ≤ 10411104267663^3863*2500000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      418124973 2500000000 10411104267663 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215514727/10000000000 : ℝ)^4887 ≤ (2743080952479/6250000000000 : ℝ)^3863 := by
    have hnat : (5215514727 : ℕ)^4887*6250000000000^3863 ≤ 2743080952479^3863*10000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215514727 10000000000 2743080952479 6250000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4887/1024 : ℝ)) 4887 3863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5384840311/10000000000 : ℝ), (-418124973/2500000000 : ℝ), (5215514727/10000000000 : ℝ)] ![(45699600471743/100000000000000 : ℝ), (10411104267663/100000000000000 : ℝ), (2743080952479/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5384840311/10000000000 : ℝ)|^4887 ≤ (45699600471743/100000000000000 : ℝ)^3863
        have hw : |(5384840311/10000000000 : ℝ)|=(5384840311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-418124973/2500000000 : ℝ)|^4887 ≤ (10411104267663/100000000000000 : ℝ)^3863
        have hw : |(-418124973/2500000000 : ℝ)|=(418124973/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215514727/10000000000 : ℝ)|^4887 ≤ (2743080952479/6250000000000 : ℝ)^3863
        have hw : |(5215514727/10000000000 : ℝ)|=(5215514727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1642_box_6 (p : ℝ) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1723149/3200000 : ℝ)*x 0 + (5215513839/10000000000 : ℝ)*x 1 + (-334500133/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1723149/3200000 : ℝ)^4887 ≤ (45699603842961/100000000000000 : ℝ)^3863 := by
    have hnat : (1723149 : ℕ)^4887*100000000000000^3863 ≤ 45699603842961^3863*3200000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1723149 3200000 45699603842961 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5215513839/10000000000 : ℝ)^4887 ≤ (43889285786177/100000000000000 : ℝ)^3863 := by
    have hnat : (5215513839 : ℕ)^4887*100000000000000^3863 ≤ 43889285786177^3863*10000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215513839 10000000000 43889285786177 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (334500133/2000000000 : ℝ)^4887 ≤ (10411110355007/100000000000000 : ℝ)^3863 := by
    have hnat : (334500133 : ℕ)^4887*100000000000000^3863 ≤ 10411110355007^3863*2000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334500133 2000000000 10411110355007 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4887/1024 : ℝ)) 4887 3863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1723149/3200000 : ℝ), (5215513839/10000000000 : ℝ), (-334500133/2000000000 : ℝ)] ![(45699603842961/100000000000000 : ℝ), (43889285786177/100000000000000 : ℝ), (10411110355007/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1723149/3200000 : ℝ)|^4887 ≤ (45699603842961/100000000000000 : ℝ)^3863
        have hw : |(1723149/3200000 : ℝ)|=(1723149/3200000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5215513839/10000000000 : ℝ)|^4887 ≤ (43889285786177/100000000000000 : ℝ)^3863
        have hw : |(5215513839/10000000000 : ℝ)|=(5215513839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-334500133/2000000000 : ℝ)|^4887 ≤ (10411110355007/100000000000000 : ℝ)^3863
        have hw : |(-334500133/2000000000 : ℝ)|=(334500133/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1642_box_7 (p : ℝ) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (487899189/1250000000 : ℝ)*x 0 + (4340618513/10000000000 : ℝ)*x 1 + (135644303/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (487899189/1250000000 : ℝ)^4887 ≤ (30416843703593/100000000000000 : ℝ)^3863 := by
    have hnat : (487899189 : ℕ)^4887*100000000000000^3863 ≤ 30416843703593^3863*1250000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      487899189 1250000000 30416843703593 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4340618513/10000000000 : ℝ)^4887 ≤ (2174473892639/6250000000000 : ℝ)^3863 := by
    have hnat : (4340618513 : ℕ)^4887*6250000000000^3863 ≤ 2174473892639^3863*10000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4340618513 10000000000 2174473892639 6250000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (135644303/312500000 : ℝ)^4887 ≤ (34791573997801/100000000000000 : ℝ)^3863 := by
    have hnat : (135644303 : ℕ)^4887*100000000000000^3863 ≤ 34791573997801^3863*312500000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135644303 312500000 34791573997801 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4887/1024 : ℝ)) 4887 3863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(487899189/1250000000 : ℝ), (4340618513/10000000000 : ℝ), (135644303/312500000 : ℝ)] ![(30416843703593/100000000000000 : ℝ), (2174473892639/6250000000000 : ℝ), (34791573997801/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(487899189/1250000000 : ℝ)|^4887 ≤ (30416843703593/100000000000000 : ℝ)^3863
        have hw : |(487899189/1250000000 : ℝ)|=(487899189/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4340618513/10000000000 : ℝ)|^4887 ≤ (2174473892639/6250000000000 : ℝ)^3863
        have hw : |(4340618513/10000000000 : ℝ)|=(4340618513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(135644303/312500000 : ℝ)|^4887 ≤ (34791573997801/100000000000000 : ℝ)^3863
        have hw : |(135644303/312500000 : ℝ)|=(135644303/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1642_box_8 (p : ℝ) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-356992367/2000000000 : ℝ)*x 0 + (2537900527/5000000000 : ℝ)*x 1 + (1087918891/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (356992367/2000000000 : ℝ)^4887 ≤ (11304504092107/100000000000000 : ℝ)^3863 := by
    have hnat : (356992367 : ℕ)^4887*100000000000000^3863 ≤ 11304504092107^3863*2000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      356992367 2000000000 11304504092107 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2537900527/5000000000 : ℝ)^4887 ≤ (21203622373739/50000000000000 : ℝ)^3863 := by
    have hnat : (2537900527 : ℕ)^4887*50000000000000^3863 ≤ 21203622373739^3863*5000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2537900527 5000000000 21203622373739 50000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1087918891/2000000000 : ℝ)^4887 ≤ (46288251150553/100000000000000 : ℝ)^3863 := by
    have hnat : (1087918891 : ℕ)^4887*100000000000000^3863 ≤ 46288251150553^3863*2000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087918891 2000000000 46288251150553 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4887/1024 : ℝ)) 4887 3863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-356992367/2000000000 : ℝ), (2537900527/5000000000 : ℝ), (1087918891/2000000000 : ℝ)] ![(11304504092107/100000000000000 : ℝ), (21203622373739/50000000000000 : ℝ), (46288251150553/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-356992367/2000000000 : ℝ)|^4887 ≤ (11304504092107/100000000000000 : ℝ)^3863
        have hw : |(-356992367/2000000000 : ℝ)|=(356992367/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2537900527/5000000000 : ℝ)|^4887 ≤ (21203622373739/50000000000000 : ℝ)^3863
        have hw : |(2537900527/5000000000 : ℝ)|=(2537900527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1087918891/2000000000 : ℝ)|^4887 ≤ (46288251150553/100000000000000 : ℝ)^3863
        have hw : |(1087918891/2000000000 : ℝ)|=(1087918891/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1642_box_9 (p : ℝ) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5230870787/10000000000 : ℝ)*x 0 + (-788119187/5000000000 : ℝ)*x 1 + (5439594171/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5230870787/10000000000 : ℝ)^4887 ≤ (44052836817989/100000000000000 : ℝ)^3863 := by
    have hnat : (5230870787 : ℕ)^4887*100000000000000^3863 ≤ 44052836817989^3863*10000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230870787 10000000000 44052836817989 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (788119187/5000000000 : ℝ)^4887 ≤ (4829457539223/50000000000000 : ℝ)^3863 := by
    have hnat : (788119187 : ℕ)^4887*50000000000000^3863 ≤ 4829457539223^3863*5000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      788119187 5000000000 4829457539223 50000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5439594171/10000000000 : ℝ)^4887 ≤ (23144124046619/50000000000000 : ℝ)^3863 := by
    have hnat : (5439594171 : ℕ)^4887*50000000000000^3863 ≤ 23144124046619^3863*10000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439594171 10000000000 23144124046619 50000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4887/1024 : ℝ)) 4887 3863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5230870787/10000000000 : ℝ), (-788119187/5000000000 : ℝ), (5439594171/10000000000 : ℝ)] ![(44052836817989/100000000000000 : ℝ), (4829457539223/50000000000000 : ℝ), (23144124046619/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5230870787/10000000000 : ℝ)|^4887 ≤ (44052836817989/100000000000000 : ℝ)^3863
        have hw : |(5230870787/10000000000 : ℝ)|=(5230870787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-788119187/5000000000 : ℝ)|^4887 ≤ (4829457539223/50000000000000 : ℝ)^3863
        have hw : |(-788119187/5000000000 : ℝ)|=(788119187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5439594171/10000000000 : ℝ)|^4887 ≤ (23144124046619/50000000000000 : ℝ)^3863
        have hw : |(5439594171/10000000000 : ℝ)|=(5439594171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1642_box_10 (p : ℝ) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5230870811/10000000000 : ℝ)*x 0 + (5439594293/10000000000 : ℝ)*x 1 + (-1576238171/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5230870811/10000000000 : ℝ)^4887 ≤ (44052837073687/100000000000000 : ℝ)^3863 := by
    have hnat : (5230870811 : ℕ)^4887*100000000000000^3863 ≤ 44052837073687^3863*10000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230870811 10000000000 44052837073687 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5439594293/10000000000 : ℝ)^4887 ≤ (46288249406591/100000000000000 : ℝ)^3863 := by
    have hnat : (5439594293 : ℕ)^4887*100000000000000^3863 ≤ 46288249406591^3863*10000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439594293 10000000000 46288249406591 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1576238171/10000000000 : ℝ)^4887 ≤ (9658913504753/100000000000000 : ℝ)^3863 := by
    have hnat : (1576238171 : ℕ)^4887*100000000000000^3863 ≤ 9658913504753^3863*10000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1576238171 10000000000 9658913504753 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4887/1024 : ℝ)) 4887 3863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5230870811/10000000000 : ℝ), (5439594293/10000000000 : ℝ), (-1576238171/10000000000 : ℝ)] ![(44052837073687/100000000000000 : ℝ), (46288249406591/100000000000000 : ℝ), (9658913504753/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5230870811/10000000000 : ℝ)|^4887 ≤ (44052837073687/100000000000000 : ℝ)^3863
        have hw : |(5230870811/10000000000 : ℝ)|=(5230870811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5439594293/10000000000 : ℝ)|^4887 ≤ (46288249406591/100000000000000 : ℝ)^3863
        have hw : |(5439594293/10000000000 : ℝ)|=(5439594293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1576238171/10000000000 : ℝ)|^4887 ≤ (9658913504753/100000000000000 : ℝ)^3863
        have hw : |(-1576238171/10000000000 : ℝ)|=(1576238171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1642_box_11 (p : ℝ) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (227356779/500000000 : ℝ)*x 0 + (4017757211/10000000000 : ℝ)*x 1 + (502219653/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (227356779/500000000 : ℝ)^4887 ≤ (18449365269973/50000000000000 : ℝ)^3863 := by
    have hnat : (227356779 : ℕ)^4887*50000000000000^3863 ≤ 18449365269973^3863*500000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      227356779 500000000 18449365269973 50000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4017757211/10000000000 : ℝ)^4887 ≤ (6310126931549/20000000000000 : ℝ)^3863 := by
    have hnat : (4017757211 : ℕ)^4887*20000000000000^3863 ≤ 6310126931549^3863*10000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4017757211 10000000000 6310126931549 20000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (502219653/1250000000 : ℝ)^4887 ≤ (7887658696723/25000000000000 : ℝ)^3863 := by
    have hnat : (502219653 : ℕ)^4887*25000000000000^3863 ≤ 7887658696723^3863*1250000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      502219653 1250000000 7887658696723 25000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4887/1024 : ℝ)) 4887 3863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(227356779/500000000 : ℝ), (4017757211/10000000000 : ℝ), (502219653/1250000000 : ℝ)] ![(18449365269973/50000000000000 : ℝ), (6310126931549/20000000000000 : ℝ), (7887658696723/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(227356779/500000000 : ℝ)|^4887 ≤ (18449365269973/50000000000000 : ℝ)^3863
        have hw : |(227356779/500000000 : ℝ)|=(227356779/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4017757211/10000000000 : ℝ)|^4887 ≤ (6310126931549/20000000000000 : ℝ)^3863
        have hw : |(4017757211/10000000000 : ℝ)|=(4017757211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(502219653/1250000000 : ℝ)|^4887 ≤ (7887658696723/25000000000000 : ℝ)^3863
        have hw : |(502219653/1250000000 : ℝ)|=(502219653/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1642_box_12 (p : ℝ) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1477895161/10000000000 : ℝ)*x 0 + (2772174809/5000000000 : ℝ)*x 1 + (5195678647/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1477895161/10000000000 : ℝ)^4887 ≤ (4451471862511/50000000000000 : ℝ)^3863 := by
    have hnat : (1477895161 : ℕ)^4887*50000000000000^3863 ≤ 4451471862511^3863*10000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1477895161 10000000000 4451471862511 50000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2772174809/5000000000 : ℝ)^4887 ≤ (23709412895577/50000000000000 : ℝ)^3863 := by
    have hnat : (2772174809 : ℕ)^4887*50000000000000^3863 ≤ 23709412895577^3863*5000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2772174809 5000000000 23709412895577 50000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5195678647/10000000000 : ℝ)^4887 ≤ (8735646095559/20000000000000 : ℝ)^3863 := by
    have hnat : (5195678647 : ℕ)^4887*20000000000000^3863 ≤ 8735646095559^3863*10000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195678647 10000000000 8735646095559 20000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4887/1024 : ℝ)) 4887 3863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1477895161/10000000000 : ℝ), (2772174809/5000000000 : ℝ), (5195678647/10000000000 : ℝ)] ![(4451471862511/50000000000000 : ℝ), (23709412895577/50000000000000 : ℝ), (8735646095559/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1477895161/10000000000 : ℝ)|^4887 ≤ (4451471862511/50000000000000 : ℝ)^3863
        have hw : |(-1477895161/10000000000 : ℝ)|=(1477895161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2772174809/5000000000 : ℝ)|^4887 ≤ (23709412895577/50000000000000 : ℝ)^3863
        have hw : |(2772174809/5000000000 : ℝ)|=(2772174809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5195678647/10000000000 : ℝ)|^4887 ≤ (8735646095559/20000000000000 : ℝ)^3863
        have hw : |(5195678647/10000000000 : ℝ)|=(5195678647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1642_box_13 (p : ℝ) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (674809889/1250000000 : ℝ)*x 0 + (-840347871/5000000000 : ℝ)*x 1 + (1298919677/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (674809889/1250000000 : ℝ)^4887 ≤ (45846080722637/100000000000000 : ℝ)^3863 := by
    have hnat : (674809889 : ℕ)^4887*100000000000000^3863 ≤ 45846080722637^3863*1250000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674809889 1250000000 45846080722637 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (840347871/5000000000 : ℝ)^4887 ≤ (2618922030909/25000000000000 : ℝ)^3863 := by
    have hnat : (840347871 : ℕ)^4887*25000000000000^3863 ≤ 2618922030909^3863*5000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      840347871 5000000000 2618922030909 25000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1298919677/2500000000 : ℝ)^4887 ≤ (8735646225307/20000000000000 : ℝ)^3863 := by
    have hnat : (1298919677 : ℕ)^4887*20000000000000^3863 ≤ 8735646225307^3863*2500000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1298919677 2500000000 8735646225307 20000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4887/1024 : ℝ)) 4887 3863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(674809889/1250000000 : ℝ), (-840347871/5000000000 : ℝ), (1298919677/2500000000 : ℝ)] ![(45846080722637/100000000000000 : ℝ), (2618922030909/25000000000000 : ℝ), (8735646225307/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(674809889/1250000000 : ℝ)|^4887 ≤ (45846080722637/100000000000000 : ℝ)^3863
        have hw : |(674809889/1250000000 : ℝ)|=(674809889/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-840347871/5000000000 : ℝ)|^4887 ≤ (2618922030909/25000000000000 : ℝ)^3863
        have hw : |(-840347871/5000000000 : ℝ)|=(840347871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1298919677/2500000000 : ℝ)|^4887 ≤ (8735646225307/20000000000000 : ℝ)^3863
        have hw : |(1298919677/2500000000 : ℝ)|=(1298919677/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1642_box_14 (p : ℝ) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1079695819/2000000000 : ℝ)*x 0 + (1039135767/2000000000 : ℝ)*x 1 + (-336139119/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079695819/2000000000 : ℝ)^4887 ≤ (45846080539997/100000000000000 : ℝ)^3863 := by
    have hnat : (1079695819 : ℕ)^4887*100000000000000^3863 ≤ 45846080539997^3863*2000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079695819 2000000000 45846080539997 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1039135767/2000000000 : ℝ)^4887 ≤ (43678232477189/100000000000000 : ℝ)^3863 := by
    have hnat : (1039135767 : ℕ)^4887*100000000000000^3863 ≤ 43678232477189^3863*2000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039135767 2000000000 43678232477189 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (336139119/2000000000 : ℝ)^4887 ≤ (2618921741129/25000000000000 : ℝ)^3863 := by
    have hnat : (336139119 : ℕ)^4887*25000000000000^3863 ≤ 2618921741129^3863*2000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336139119 2000000000 2618921741129 25000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4887/1024 : ℝ)) 4887 3863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1079695819/2000000000 : ℝ), (1039135767/2000000000 : ℝ), (-336139119/2000000000 : ℝ)] ![(45846080539997/100000000000000 : ℝ), (43678232477189/100000000000000 : ℝ), (2618921741129/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1079695819/2000000000 : ℝ)|^4887 ≤ (45846080539997/100000000000000 : ℝ)^3863
        have hw : |(1079695819/2000000000 : ℝ)|=(1079695819/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1039135767/2000000000 : ℝ)|^4887 ≤ (43678232477189/100000000000000 : ℝ)^3863
        have hw : |(1039135767/2000000000 : ℝ)|=(1039135767/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-336139119/2000000000 : ℝ)|^4887 ≤ (2618921741129/25000000000000 : ℝ)^3863
        have hw : |(-336139119/2000000000 : ℝ)|=(336139119/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1642_box_15 (p : ℝ) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (192217611/500000000 : ℝ)*x 0 + (1092284933/2500000000 : ℝ)*x 1 + (2184569873/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (192217611/500000000 : ℝ)^4887 ≤ (29837919043153/100000000000000 : ℝ)^3863 := by
    have hnat : (192217611 : ℕ)^4887*100000000000000^3863 ≤ 29837919043153^3863*500000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      192217611 500000000 29837919043153 100000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1092284933/2500000000 : ℝ)^4887 ≤ (17540520197583/50000000000000 : ℝ)^3863 := by
    have hnat : (1092284933 : ℕ)^4887*50000000000000^3863 ≤ 17540520197583^3863*2500000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092284933 2500000000 17540520197583 50000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2184569873/5000000000 : ℝ)^4887 ≤ (17540520268687/50000000000000 : ℝ)^3863 := by
    have hnat : (2184569873 : ℕ)^4887*50000000000000^3863 ≤ 17540520268687^3863*5000000000^4887 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184569873 5000000000 17540520268687 50000000000000 4887 3863 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4887/1024 : ℝ)) 4887 3863 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(192217611/500000000 : ℝ), (1092284933/2500000000 : ℝ), (2184569873/5000000000 : ℝ)] ![(29837919043153/100000000000000 : ℝ), (17540520197583/50000000000000 : ℝ), (17540520268687/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(192217611/500000000 : ℝ)|^4887 ≤ (29837919043153/100000000000000 : ℝ)^3863
        have hw : |(192217611/500000000 : ℝ)|=(192217611/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1092284933/2500000000 : ℝ)|^4887 ≤ (17540520197583/50000000000000 : ℝ)^3863
        have hw : |(1092284933/2500000000 : ℝ)|=(1092284933/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2184569873/5000000000 : ℝ)|^4887 ≤ (17540520268687/50000000000000 : ℝ)^3863
        have hw : |(2184569873/5000000000 : ℝ)|=(2184569873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1642_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (178059701/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16283/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2657/25000 : ℝ)*pair X i i ≤ pair X i h) :
    -(13007/20000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(2927/5000 : ℝ) ∧ (1621/2000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (17629/20000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16283/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2657/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16283/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2657/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16283/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2657/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16283/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2657/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16283/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2657/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16283/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2657/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2657/25000 : ℝ) ^ (4883/1024 : ℝ) ≤ (2278142860857987/100000000000000000000 : ℝ) := by
    have hpowers : (2657/25000 : ℝ)^4883 ≤ (2278142860857987/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2657 : ℕ)^4883*100000000000000000000^1024 ≤ 2278142860857987^1024*25000^4883 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2657 25000 2278142860857987 100000000000000000000 4883 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2657/25000 : ℝ)) (X := (2278142860857987/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4883 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16283/100000 : ℝ) ^ (4883/1024 : ℝ) ≤ (8711290398074083/50000000000000000000 : ℝ) := by
    have hpowers : (16283/100000 : ℝ)^4883 ≤ (8711290398074083/50000000000000000000 : ℝ)^1024 := by
      have hnat : (16283 : ℕ)^4883*50000000000000000000^1024 ≤ 8711290398074083^1024*100000^4883 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16283 100000 8711290398074083 50000000000000000000 4883 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16283/100000 : ℝ)) (X := (8711290398074083/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4883 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002278142860857987/50000000000000000000 : ℝ) ≤ (2000019109369573/2000000000000000 : ℝ) ^ (4883/1024 : ℝ) := by
    have hpowers : (50002278142860857987/50000000000000000000 : ℝ)^1024 ≤ (2000019109369573/2000000000000000 : ℝ)^4883 := by
      have hnat : (50002278142860857987 : ℕ)^1024*2000000000000000^4883 ≤ 2000019109369573^4883*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002278142860857987 50000000000000000000 2000019109369573 2000000000000000 1024 4883 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000019109369573/2000000000000000 : ℝ)) (X := (50002278142860857987/50000000000000000000 : ℝ)) (by norm_num) 4883 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100019700723657006153/100000000000000000000 : ℝ) ≤ (10000413106098007/10000000000000000 : ℝ) ^ (4883/1024 : ℝ) := by
    have hpowers : (100019700723657006153/100000000000000000000 : ℝ)^1024 ≤ (10000413106098007/10000000000000000 : ℝ)^4883 := by
      have hnat : (100019700723657006153 : ℕ)^1024*10000000000000000^4883 ≤ 10000413106098007^4883*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100019700723657006153 100000000000000000000 10000413106098007 10000000000000000 1024 4883 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000413106098007/10000000000000000 : ℝ)) (X := (100019700723657006153/100000000000000000000 : ℝ)) (by norm_num) 4883 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25008711290398074083/25000000000000000000 : ℝ) ≤ (10000730665348149/10000000000000000 : ℝ) ^ (4883/1024 : ℝ) := by
    have hpowers : (25008711290398074083/25000000000000000000 : ℝ)^1024 ≤ (10000730665348149/10000000000000000 : ℝ)^4883 := by
      have hnat : (25008711290398074083 : ℕ)^1024*10000000000000000^4883 ≤ 10000730665348149^4883*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25008711290398074083 25000000000000000000 10000730665348149 10000000000000000 1024 4883 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000730665348149/10000000000000000 : ℝ)) (X := (25008711290398074083/25000000000000000000 : ℝ)) (by norm_num) 4883 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2278142860857987/100000000000000000000 : ℝ) ≤ ((56543790278003658223/56550000000000000000 : ℝ)+2*(158779625071/282750000000000 : ℝ)*(2657/25000 : ℝ))^(4883/1024 : ℝ) := by
    rw [show (56543790278003658223/56550000000000000000 : ℝ)+2*(158779625071/282750000000000 : ℝ)*(2657/25000 : ℝ)=(2000019109369573/2000000000000000 : ℝ) by norm_num, show 1+2*(2278142860857987/100000000000000000000 : ℝ)=(50002278142860857987/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8711290398074083/50000000000000000000 : ℝ)+(2278142860857987/100000000000000000000 : ℝ) ≤ ((56543790278003658223/56550000000000000000 : ℝ)+(158779625071/282750000000000 : ℝ)*((16283/100000 : ℝ)+(2657/25000 : ℝ)))^(4883/1024 : ℝ) := by
    rw [show (56543790278003658223/56550000000000000000 : ℝ)+(158779625071/282750000000000 : ℝ)*((16283/100000 : ℝ)+(2657/25000 : ℝ))=(10000413106098007/10000000000000000 : ℝ) by norm_num, show 1+(8711290398074083/50000000000000000000 : ℝ)+(2278142860857987/100000000000000000000 : ℝ)=(100019700723657006153/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8711290398074083/50000000000000000000 : ℝ) ≤ ((56543790278003658223/56550000000000000000 : ℝ)+2*(158779625071/282750000000000 : ℝ)*(16283/100000 : ℝ))^(4883/1024 : ℝ) := by
    rw [show (56543790278003658223/56550000000000000000 : ℝ)+2*(158779625071/282750000000000 : ℝ)*(16283/100000 : ℝ)=(10000730665348149/10000000000000000 : ℝ) by norm_num, show 1+2*(8711290398074083/50000000000000000000 : ℝ)=(25008711290398074083/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (56543790278003658223/56550000000000000000 : ℝ)*(X 1 0+X 2 0)+(158779625071/282750000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4883/1024 : ℝ)) (lo := (2657/25000 : ℝ)) (hi := (16283/100000 : ℝ)) (c := (56543790278003658223/56550000000000000000 : ℝ)) (alpha := (158779625071/282750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (56543790278003658223/56550000000000000000 : ℝ)*(X 0 1+X 2 1)+(158779625071/282750000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4883/1024 : ℝ)) (lo := (2657/25000 : ℝ)) (hi := (16283/100000 : ℝ)) (c := (56543790278003658223/56550000000000000000 : ℝ)) (alpha := (158779625071/282750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (56543790278003658223/56550000000000000000 : ℝ)*(X 0 2+X 1 2)+(158779625071/282750000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4883/1024 : ℝ)) (lo := (2657/25000 : ℝ)) (hi := (16283/100000 : ℝ)) (c := (56543790278003658223/56550000000000000000 : ℝ)) (alpha := (158779625071/282750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-170757453/1250000000 : ℝ)*X 0 0+(338127483/625000000 : ℝ)*X 0 1+(2705019773/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1642_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5251178261/10000000000 : ℝ)*X 1 0+(-49666013/312500000 : ℝ)*X 1 1+(5410039437/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1642_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((210047123/400000000 : ℝ)*X 2 0+(135250991/250000000 : ℝ)*X 2 1+(-1589312391/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1642_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4464271033/10000000000 : ℝ)*X 0 0+(4060407777/10000000000 : ℝ)*X 0 1+(406040761/1000000000 : ℝ)*X 0 2+(4464271033/10000000000 : ℝ)*X 1 0+(4060407777/10000000000 : ℝ)*X 1 1+(406040761/1000000000 : ℝ)*X 1 2+(4464271033/10000000000 : ℝ)*X 2 0+(4060407777/10000000000 : ℝ)*X 2 1+(406040761/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1642_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-29663481/156250000 : ℝ)*X 0 0+(5215514183/10000000000 : ℝ)*X 0 1+(325969643/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1642_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5384840311/10000000000 : ℝ)*X 1 0+(-418124973/2500000000 : ℝ)*X 1 1+(5215514727/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1642_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1723149/3200000 : ℝ)*X 2 0+(5215513839/10000000000 : ℝ)*X 2 1+(-334500133/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1642_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((487899189/1250000000 : ℝ)*X 0 0+(4340618513/10000000000 : ℝ)*X 0 1+(135644303/312500000 : ℝ)*X 0 2+(487899189/1250000000 : ℝ)*X 1 0+(4340618513/10000000000 : ℝ)*X 1 1+(135644303/312500000 : ℝ)*X 1 2+(487899189/1250000000 : ℝ)*X 2 0+(4340618513/10000000000 : ℝ)*X 2 1+(135644303/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1642_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-356992367/2000000000 : ℝ)*X 0 0+(2537900527/5000000000 : ℝ)*X 0 1+(1087918891/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1642_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5230870787/10000000000 : ℝ)*X 1 0+(-788119187/5000000000 : ℝ)*X 1 1+(5439594171/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1642_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5230870811/10000000000 : ℝ)*X 2 0+(5439594293/10000000000 : ℝ)*X 2 1+(-1576238171/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1642_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((227356779/500000000 : ℝ)*X 0 0+(4017757211/10000000000 : ℝ)*X 0 1+(502219653/1250000000 : ℝ)*X 0 2+(227356779/500000000 : ℝ)*X 1 0+(4017757211/10000000000 : ℝ)*X 1 1+(502219653/1250000000 : ℝ)*X 1 2+(227356779/500000000 : ℝ)*X 2 0+(4017757211/10000000000 : ℝ)*X 2 1+(502219653/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1642_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1477895161/10000000000 : ℝ)*X 0 0+(2772174809/5000000000 : ℝ)*X 0 1+(5195678647/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1642_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((674809889/1250000000 : ℝ)*X 1 0+(-840347871/5000000000 : ℝ)*X 1 1+(1298919677/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1642_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1079695819/2000000000 : ℝ)*X 2 0+(1039135767/2000000000 : ℝ)*X 2 1+(-336139119/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1642_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((192217611/500000000 : ℝ)*X 0 0+(1092284933/2500000000 : ℝ)*X 0 1+(2184569873/5000000000 : ℝ)*X 0 2+(192217611/500000000 : ℝ)*X 1 0+(1092284933/2500000000 : ℝ)*X 1 1+(2184569873/5000000000 : ℝ)*X 1 2+(192217611/500000000 : ℝ)*X 2 0+(1092284933/2500000000 : ℝ)*X 2 1+(2184569873/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1642_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-13007/20000 : ℝ) ≤ (-306464912434205313884895763500533/471250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4205951/12500000000000 : ℝ)*(lower0) + (87500331/100000000000000 : ℝ)*(upper1) + (17693939/50000000000000 : ℝ)*(upper3) + (4626931/4000000000000 : ℝ)*(lower4) + (871848337257029/50000000000000 : ℝ)*(major0) + (871848337257029/50000000000000 : ℝ)*(major1) + (871848337257029/50000000000000 : ℝ)*(major2) + (3101710257/50000000000000 : ℝ)*(sp2) + (252979437130531/10000000000000 : ℝ)*(sp4) + (252971211164157/10000000000000 : ℝ)*(sp5) + (632447041971199/25000000000000 : ℝ)*(sp6) + (489637008418397/50000000000000 : ℝ)*(sp7) + (82259663741/100000000000000 : ℝ)*(sp13) + (30103413/1250000000000 : ℝ)*(sp15) + (979276425109833/100000000000000 : ℝ)*(f.failure) + (252979437130531/10000000000000 : ℝ)*(f.sum) + (25130730324241/7068750000000000000000000000 : ℝ)*base66 + (2223458482165933511/942500000000000000000000000000000 : ℝ)*base68 + (7800387722024066489/942500000000000000000000000000000 : ℝ)*base69 + (8797708192830933511/942500000000000000000000000000000 : ℝ)*base72 + (7012667830283/3534375000000000000000000000 : ℝ)*base74 + (2867259638540933511/942500000000000000000000000000000 : ℝ)*base76 + (2049466071979066489/942500000000000000000000000000000 : ℝ)*base77 + (2880055889410933511/942500000000000000000000000000000 : ℝ)*base80 + (40640828427493/14137500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (43860067/10000000000000000000000 : ℝ)*base90 + (43860067/10000000000000000000000 : ℝ)*base92 + (43860067/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (2927/5000 : ℝ) ≤ (110351742239542140720654751062691/188500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5218033/100000000000000 : ℝ)*(upper2) + (18689781/50000000000000 : ℝ)*(upper3) + (1247793/100000000000000 : ℝ)*(lower5) + (366594848522317/20000000000000 : ℝ)*(major0) + (366594848522317/20000000000000 : ℝ)*(major1) + (366594848522317/20000000000000 : ℝ)*(major2) + (261701840110633/10000000000000 : ℝ)*(sp0) + (261699610177611/10000000000000 : ℝ)*(sp1) + (2617017502019449/100000000000000 : ℝ)*(sp2) + (1029411101473767/100000000000000 : ℝ)*(sp3) + (262851897/50000000000000 : ℝ)*(sp8) + (4565006803/20000000000000 : ℝ)*(sp9) + (56991627/4000000000000 : ℝ)*(sp10) + (4444164819/100000000000000 : ℝ)*(sp11) + (514707772819293/50000000000000 : ℝ)*(f.failure) + (654254731702531/25000000000000 : ℝ)*(f.sum) + (32851150543259/5655000000000000000000000000 : ℝ)*base65 + (1937996922682179103/377000000000000000000000000000000 : ℝ)*base68 + (209608123033820897/377000000000000000000000000000000 : ℝ)*base69 + (755646869356179103/377000000000000000000000000000000 : ℝ)*base72 + (2294203877081/1413750000000000000000000000 : ℝ)*base73 + (1090811222711179103/377000000000000000000000000000000 : ℝ)*base76 + (3470936479098820897/377000000000000000000000000000000 : ℝ)*base77 + (980906652845179103/377000000000000000000000000000000 : ℝ)*base80 + (480915192499/1413750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (11388607/5000000000000000000000 : ℝ)*base90 + (11388607/5000000000000000000000 : ℝ)*base92 + (11388607/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (1621/2000 : ℝ) ≤ (763916099378398756765408332095297/942500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (27413/50000000000000 : ℝ)*(upper0) + (38549433/100000000000000 : ℝ)*(lower3) + (8873963/25000000000000 : ℝ)*(upper4) + (1929819510360239/100000000000000 : ℝ)*(major0) + (1929819510360239/100000000000000 : ℝ)*(major1) + (1929819510360239/100000000000000 : ℝ)*(major2) + (14230716161/100000000000000 : ℝ)*(sp2) + (6605438267/100000000000000 : ℝ)*(sp3) + (152714523/25000000000000 : ℝ)*(sp4) + (42950237889217/1562500000000 : ℝ)*(sp8) + (34360211183659/1250000000000 : ℝ)*(sp9) + (34360033299707/1250000000000 : ℝ)*(sp10) + (1083798151911201/100000000000000 : ℝ)*(sp11) + (1058924741/100000000000000 : ℝ)*(sp12) + (1083804757349469/100000000000000 : ℝ)*(f.failure) + (34360211183659/1250000000000 : ℝ)*(f.sum) + (121114264181153/7068750000000000000000000000 : ℝ)*base66 + (2693941766859465099/1885000000000000000000000000000000 : ℝ)*base67 + (5253991575125534901/1885000000000000000000000000000000 : ℝ)*base70 + (2982470768115534901/1885000000000000000000000000000000 : ℝ)*base72 + (83505700573/110449218750000000000000000 : ℝ)*base73 + (6907010228929465099/1885000000000000000000000000000000 : ℝ)*base75 + (4290641154690534901/1885000000000000000000000000000000 : ℝ)*base78 + (9774493265830534901/1885000000000000000000000000000000 : ℝ)*base80 + (104320204104613/28275000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (102648769/10000000000000000000000 : ℝ)*base89 + (102648769/10000000000000000000000 : ℝ)*base91 + (102648769/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-17629/20000 : ℝ) ≤ (-103843248514225666883168554578051/117812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13305831/100000000000000 : ℝ)*(lower1) + (15755023/50000000000000 : ℝ)*(lower2) + (1708007/20000000000000 : ℝ)*(upper5) + (246686882626879/12500000000000 : ℝ)*(major0) + (246686882626879/12500000000000 : ℝ)*(major1) + (246686882626879/12500000000000 : ℝ)*(major2) + (108720513/50000000000000 : ℝ)*(sp0) + (26678085429/100000000000000 : ℝ)*(sp5) + (11990169049/100000000000000 : ℝ)*(sp7) + (2150201543/100000000000000 : ℝ)*(sp8) + (1434017667247719/50000000000000 : ℝ)*(sp12) + (1434005512026289/50000000000000 : ℝ)*(sp13) + (2868037702138007/100000000000000 : ℝ)*(sp14) + (277080341631579/25000000000000 : ℝ)*(sp15) + (554166678347683/50000000000000 : ℝ)*(f.failure) + (2868037702138007/100000000000000 : ℝ)*(f.sum) + (144215129349769/28275000000000000000000000000 : ℝ)*base65 + (1250430165840950339/235625000000000000000000000000000 : ℝ)*base67 + (2261125671335950339/235625000000000000000000000000000 : ℝ)*base69 + (2294350380678450339/235625000000000000000000000000000 : ℝ)*base71 + (151657549195669/28275000000000000000000000000 : ℝ)*base73 + (2556328108573450339/235625000000000000000000000000000 : ℝ)*base75 + (2932709280509700339/235625000000000000000000000000000 : ℝ)*base77 + (2218370146811575339/235625000000000000000000000000000 : ℝ)*base79 + (182356486623919/28275000000000000000000000000 : ℝ)*base81 + (9022783/5000000000000000000000 : ℝ)*base89 + (9022783/5000000000000000000000 : ℝ)*base91 + (9022783/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1642_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (178059701/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16283/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2657/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(13007/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(2927/5000 : ℝ) else (1621/2000 : ℝ) ≤ X j i ∧ X j i ≤ (17629/20000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1642_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1642_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (178059701/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4093/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2637/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(13007/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(2927/5000 : ℝ) else (1621/2000 : ℝ) ≤ X j i ∧ X j i ≤ (17629/20000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1642_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1642_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1642_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4883/1024 : ℝ) ≤ p) (hpb : p ≤ (4887/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (178059701/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4093/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2637/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(13007/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(2927/5000 : ℝ) else (1621/2000 : ℝ) ≤ X j i ∧ X j i ≤ (17629/20000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1642_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
