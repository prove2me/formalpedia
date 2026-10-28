-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1066_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:06:49.873197+00:00
-- url     : https://prove2.me/submissions/1551b02e-65ee-4fb4-8918-af3cc5171cbb

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
theorem support_rectangle_w1066_s0_0 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-958049671/5000000000 : ℝ)*x 0 + (379503967/625000000 : ℝ)*x 1 + (74543523/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (958049671/5000000000 : ℝ)^8259 ≤ (11112308490481/100000000000000 : ℝ)^6211 := by
    have hnat : (958049671 : ℕ)^8259*100000000000000^6211 ≤ 11112308490481^6211*5000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      958049671 5000000000 11112308490481 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (379503967/625000000 : ℝ)^8259 ≤ (25755153793361/50000000000000 : ℝ)^6211 := by
    have hnat : (379503967 : ℕ)^8259*50000000000000^6211 ≤ 25755153793361^6211*625000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      379503967 625000000 25755153793361 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (74543523/156250000 : ℝ)^8259 ≤ (37377383905177/100000000000000 : ℝ)^6211 := by
    have hnat : (74543523 : ℕ)^8259*100000000000000^6211 ≤ 37377383905177^6211*156250000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      74543523 156250000 37377383905177 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-958049671/5000000000 : ℝ), (379503967/625000000 : ℝ), (74543523/156250000 : ℝ)] ![(11112308490481/100000000000000 : ℝ), (25755153793361/50000000000000 : ℝ), (37377383905177/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-958049671/5000000000 : ℝ)|^8259 ≤ (11112308490481/100000000000000 : ℝ)^6211
        have hw : |(-958049671/5000000000 : ℝ)|=(958049671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(379503967/625000000 : ℝ)|^8259 ≤ (25755153793361/50000000000000 : ℝ)^6211
        have hw : |(379503967/625000000 : ℝ)|=(379503967/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(74543523/156250000 : ℝ)|^8259 ≤ (37377383905177/100000000000000 : ℝ)^6211
        have hw : |(74543523/156250000 : ℝ)|=(74543523/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s0_1 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5521074971/10000000000 : ℝ)*x 0 + (-533024281/2000000000 : ℝ)*x 1 + (4770783999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5521074971/10000000000 : ℝ)^8259 ≤ (22694946025081/50000000000000 : ℝ)^6211 := by
    have hnat : (5521074971 : ℕ)^8259*50000000000000^6211 ≤ 22694946025081^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5521074971 10000000000 22694946025081 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (533024281/2000000000 : ℝ)^8259 ≤ (17232739377559/100000000000000 : ℝ)^6211 := by
    have hnat : (533024281 : ℕ)^8259*100000000000000^6211 ≤ 17232739377559^6211*2000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533024281 2000000000 17232739377559 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4770783999/10000000000 : ℝ)^8259 ≤ (18688684279721/50000000000000 : ℝ)^6211 := by
    have hnat : (4770783999 : ℕ)^8259*50000000000000^6211 ≤ 18688684279721^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4770783999 10000000000 18688684279721 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5521074971/10000000000 : ℝ), (-533024281/2000000000 : ℝ), (4770783999/10000000000 : ℝ)] ![(22694946025081/50000000000000 : ℝ), (17232739377559/100000000000000 : ℝ), (18688684279721/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5521074971/10000000000 : ℝ)|^8259 ≤ (22694946025081/50000000000000 : ℝ)^6211
        have hw : |(5521074971/10000000000 : ℝ)|=(5521074971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-533024281/2000000000 : ℝ)|^8259 ≤ (17232739377559/100000000000000 : ℝ)^6211
        have hw : |(-533024281/2000000000 : ℝ)|=(533024281/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4770783999/10000000000 : ℝ)|^8259 ≤ (18688684279721/50000000000000 : ℝ)^6211
        have hw : |(4770783999/10000000000 : ℝ)|=(4770783999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s0_2 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (552107217/1000000000 : ℝ)*x 0 + (2385392851/5000000000 : ℝ)*x 1 + (-1332561451/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (552107217/1000000000 : ℝ)^8259 ≤ (9077972285901/20000000000000 : ℝ)^6211 := by
    have hnat : (552107217 : ℕ)^8259*20000000000000^6211 ≤ 9077972285901^6211*1000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      552107217 1000000000 9077972285901 20000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2385392851/5000000000 : ℝ)^8259 ≤ (934434657533/2500000000000 : ℝ)^6211 := by
    have hnat : (2385392851 : ℕ)^8259*2500000000000^6211 ≤ 934434657533^6211*5000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2385392851 5000000000 934434657533 2500000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1332561451/5000000000 : ℝ)^8259 ≤ (17232752248939/100000000000000 : ℝ)^6211 := by
    have hnat : (1332561451 : ℕ)^8259*100000000000000^6211 ≤ 17232752248939^6211*5000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1332561451 5000000000 17232752248939 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(552107217/1000000000 : ℝ), (2385392851/5000000000 : ℝ), (-1332561451/5000000000 : ℝ)] ![(9077972285901/20000000000000 : ℝ), (934434657533/2500000000000 : ℝ), (17232752248939/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(552107217/1000000000 : ℝ)|^8259 ≤ (9077972285901/20000000000000 : ℝ)^6211
        have hw : |(552107217/1000000000 : ℝ)|=(552107217/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2385392851/5000000000 : ℝ)|^8259 ≤ (934434657533/2500000000000 : ℝ)^6211
        have hw : |(2385392851/5000000000 : ℝ)|=(2385392851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1332561451/5000000000 : ℝ)|^8259 ≤ (17232752248939/100000000000000 : ℝ)^6211
        have hw : |(-1332561451/5000000000 : ℝ)|=(1332561451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s0_3 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1051802319/2500000000 : ℝ)*x 0 + (781217019/2500000000 : ℝ)*x 1 + (5675187347/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051802319/2500000000 : ℝ)^8259 ≤ (31623566752617/100000000000000 : ℝ)^6211 := by
    have hnat : (1051802319 : ℕ)^8259*100000000000000^6211 ≤ 31623566752617^6211*2500000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051802319 2500000000 31623566752617 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (781217019/2500000000 : ℝ)^8259 ≤ (21294072050781/100000000000000 : ℝ)^6211 := by
    have hnat : (781217019 : ℕ)^8259*100000000000000^6211 ≤ 21294072050781^6211*2500000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      781217019 2500000000 21294072050781 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5675187347/10000000000 : ℝ)^8259 ≤ (47082361187021/100000000000000 : ℝ)^6211 := by
    have hnat : (5675187347 : ℕ)^8259*100000000000000^6211 ≤ 47082361187021^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5675187347 10000000000 47082361187021 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1051802319/2500000000 : ℝ), (781217019/2500000000 : ℝ), (5675187347/10000000000 : ℝ)] ![(31623566752617/100000000000000 : ℝ), (21294072050781/100000000000000 : ℝ), (47082361187021/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1051802319/2500000000 : ℝ)|^8259 ≤ (31623566752617/100000000000000 : ℝ)^6211
        have hw : |(1051802319/2500000000 : ℝ)|=(1051802319/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(781217019/2500000000 : ℝ)|^8259 ≤ (21294072050781/100000000000000 : ℝ)^6211
        have hw : |(781217019/2500000000 : ℝ)|=(781217019/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5675187347/10000000000 : ℝ)|^8259 ≤ (47082361187021/100000000000000 : ℝ)^6211
        have hw : |(5675187347/10000000000 : ℝ)|=(5675187347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s0_4 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1921472809/10000000000 : ℝ)*x 0 + (1201096361/2500000000 : ℝ)*x 1 + (754661011/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1921472809/10000000000 : ℝ)^8259 ≤ (11153766401643/100000000000000 : ℝ)^6211 := by
    have hnat : (1921472809 : ℕ)^8259*100000000000000^6211 ≤ 11153766401643^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1921472809 10000000000 11153766401643 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1201096361/2500000000 : ℝ)^8259 ≤ (37727834710841/100000000000000 : ℝ)^6211 := by
    have hnat : (1201096361 : ℕ)^8259*100000000000000^6211 ≤ 37727834710841^6211*2500000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1201096361 2500000000 37727834710841 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (754661011/1250000000 : ℝ)^8259 ≤ (6389799858957/12500000000000 : ℝ)^6211 := by
    have hnat : (754661011 : ℕ)^8259*12500000000000^6211 ≤ 6389799858957^6211*1250000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      754661011 1250000000 6389799858957 12500000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1921472809/10000000000 : ℝ), (1201096361/2500000000 : ℝ), (754661011/1250000000 : ℝ)] ![(11153766401643/100000000000000 : ℝ), (37727834710841/100000000000000 : ℝ), (6389799858957/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1921472809/10000000000 : ℝ)|^8259 ≤ (11153766401643/100000000000000 : ℝ)^6211
        have hw : |(-1921472809/10000000000 : ℝ)|=(1921472809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1201096361/2500000000 : ℝ)|^8259 ≤ (37727834710841/100000000000000 : ℝ)^6211
        have hw : |(1201096361/2500000000 : ℝ)|=(1201096361/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(754661011/1250000000 : ℝ)|^8259 ≤ (6389799858957/12500000000000 : ℝ)^6211
        have hw : |(754661011/1250000000 : ℝ)|=(754661011/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s0_5 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (516788571/1000000000 : ℝ)*x 0 + (-349655769/2500000000 : ℝ)*x 1 + (1207457193/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (516788571/1000000000 : ℝ)^8259 ≤ (41570131193519/100000000000000 : ℝ)^6211 := by
    have hnat : (516788571 : ℕ)^8259*100000000000000^6211 ≤ 41570131193519^6211*1000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516788571 1000000000 41570131193519 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (349655769/2500000000 : ℝ)^8259 ≤ (1827873454827/25000000000000 : ℝ)^6211 := by
    have hnat : (349655769 : ℕ)^8259*25000000000000^6211 ≤ 1827873454827^6211*2500000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      349655769 2500000000 1827873454827 25000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1207457193/2000000000 : ℝ)^8259 ≤ (638979687109/1250000000000 : ℝ)^6211 := by
    have hnat : (1207457193 : ℕ)^8259*1250000000000^6211 ≤ 638979687109^6211*2000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1207457193 2000000000 638979687109 1250000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(516788571/1000000000 : ℝ), (-349655769/2500000000 : ℝ), (1207457193/2000000000 : ℝ)] ![(41570131193519/100000000000000 : ℝ), (1827873454827/25000000000000 : ℝ), (638979687109/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(516788571/1000000000 : ℝ)|^8259 ≤ (41570131193519/100000000000000 : ℝ)^6211
        have hw : |(516788571/1000000000 : ℝ)|=(516788571/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-349655769/2500000000 : ℝ)|^8259 ≤ (1827873454827/25000000000000 : ℝ)^6211
        have hw : |(-349655769/2500000000 : ℝ)|=(349655769/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1207457193/2000000000 : ℝ)|^8259 ≤ (638979687109/1250000000000 : ℝ)^6211
        have hw : |(1207457193/2000000000 : ℝ)|=(1207457193/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s0_6 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2583942953/5000000000 : ℝ)*x 0 + (754660889/1250000000 : ℝ)*x 1 + (-1398620917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2583942953/5000000000 : ℝ)^8259 ≤ (20785066644999/50000000000000 : ℝ)^6211 := by
    have hnat : (2583942953 : ℕ)^8259*50000000000000^6211 ≤ 20785066644999^6211*5000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2583942953 5000000000 20785066644999 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (754660889/1250000000 : ℝ)^8259 ≤ (10223677576567/20000000000000 : ℝ)^6211 := by
    have hnat : (754660889 : ℕ)^8259*20000000000000^6211 ≤ 10223677576567^6211*1250000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      754660889 1250000000 10223677576567 20000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1398620917/10000000000 : ℝ)^8259 ≤ (7311478811271/100000000000000 : ℝ)^6211 := by
    have hnat : (1398620917 : ℕ)^8259*100000000000000^6211 ≤ 7311478811271^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1398620917 10000000000 7311478811271 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2583942953/5000000000 : ℝ), (754660889/1250000000 : ℝ), (-1398620917/10000000000 : ℝ)] ![(20785066644999/50000000000000 : ℝ), (10223677576567/20000000000000 : ℝ), (7311478811271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2583942953/5000000000 : ℝ)|^8259 ≤ (20785066644999/50000000000000 : ℝ)^6211
        have hw : |(2583942953/5000000000 : ℝ)|=(2583942953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(754660889/1250000000 : ℝ)|^8259 ≤ (10223677576567/20000000000000 : ℝ)^6211
        have hw : |(754660889/1250000000 : ℝ)|=(754660889/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1398620917/10000000000 : ℝ)|^8259 ≤ (7311478811271/100000000000000 : ℝ)^6211
        have hw : |(-1398620917/10000000000 : ℝ)|=(1398620917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s0_7 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2108869699/5000000000 : ℝ)*x 0 + (1402333767/2500000000 : ℝ)*x 1 + (199563897/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2108869699/5000000000 : ℝ)^8259 ≤ (15864429348871/50000000000000 : ℝ)^6211 := by
    have hnat : (2108869699 : ℕ)^8259*50000000000000^6211 ≤ 15864429348871^6211*5000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108869699 5000000000 15864429348871 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1402333767/2500000000 : ℝ)^8259 ≤ (23178644721009/50000000000000 : ℝ)^6211 := by
    have hnat : (1402333767 : ℕ)^8259*50000000000000^6211 ≤ 23178644721009^6211*2500000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1402333767 2500000000 23178644721009 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (199563897/625000000 : ℝ)^8259 ≤ (5478462961389/25000000000000 : ℝ)^6211 := by
    have hnat : (199563897 : ℕ)^8259*25000000000000^6211 ≤ 5478462961389^6211*625000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      199563897 625000000 5478462961389 25000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2108869699/5000000000 : ℝ), (1402333767/2500000000 : ℝ), (199563897/625000000 : ℝ)] ![(15864429348871/50000000000000 : ℝ), (23178644721009/50000000000000 : ℝ), (5478462961389/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2108869699/5000000000 : ℝ)|^8259 ≤ (15864429348871/50000000000000 : ℝ)^6211
        have hw : |(2108869699/5000000000 : ℝ)|=(2108869699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1402333767/2500000000 : ℝ)|^8259 ≤ (23178644721009/50000000000000 : ℝ)^6211
        have hw : |(1402333767/2500000000 : ℝ)|=(1402333767/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(199563897/625000000 : ℝ)|^8259 ≤ (5478462961389/25000000000000 : ℝ)^6211
        have hw : |(199563897/625000000 : ℝ)|=(199563897/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1066_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73996519/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (97/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (28109/100000 : ℝ)*pair X 0 0 := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
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
  have hpowlo : (0 : ℝ) ^ (4129/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4129 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4129*1^1024 ≤ 0^1024*1^4129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4129 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4129 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4129/1024 : ℝ) ≤ (99420448524396521/4000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4129 ≤ (99420448524396521/4000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4129*4000000000000000000^1024 ≤ 99420448524396521^1024*5^4129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 99420448524396521 4000000000000000000 4129 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (99420448524396521/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4129 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4129/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4129 := by
      have hnat : (1 : ℕ)^1024*1^4129 ≤ 1^4129*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4129 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (4099420448524396521/4000000000000000000 : ℝ) ≤ (10061073313773191/10000000000000000 : ℝ) ^ (4129/1024 : ℝ) := by
    have hpowers : (4099420448524396521/4000000000000000000 : ℝ)^1024 ≤ (10061073313773191/10000000000000000 : ℝ)^4129 := by
      have hnat : (4099420448524396521 : ℕ)^1024*10000000000000000^4129 ≤ 10061073313773191^4129*4000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4099420448524396521 4000000000000000000 10061073313773191 10000000000000000 1024 4129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10061073313773191/10000000000000000 : ℝ)) (X := (4099420448524396521/4000000000000000000 : ℝ)) (by norm_num) 4129 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2099420448524396521/2000000000000000000 : ℝ) ≤ (5061073313773191/5000000000000000 : ℝ) ^ (4129/1024 : ℝ) := by
    have hpowers : (2099420448524396521/2000000000000000000 : ℝ)^1024 ≤ (5061073313773191/5000000000000000 : ℝ)^4129 := by
      have hnat : (2099420448524396521 : ℕ)^1024*5000000000000000^4129 ≤ 5061073313773191^4129*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2099420448524396521 2000000000000000000 5061073313773191 5000000000000000 1024 4129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5061073313773191/5000000000000000 : ℝ)) (X := (2099420448524396521/2000000000000000000 : ℝ)) (by norm_num) 4129 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(61073313773191/4000000000000000 : ℝ)*(0 : ℝ))^(4129/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(61073313773191/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(99420448524396521/4000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(61073313773191/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4129/1024 : ℝ) := by
    rw [show (1 : ℝ)+(61073313773191/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10061073313773191/10000000000000000 : ℝ) by norm_num, show 1+(99420448524396521/4000000000000000000 : ℝ)+(0 : ℝ)=(4099420448524396521/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(99420448524396521/4000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(61073313773191/4000000000000000 : ℝ)*(2/5 : ℝ))^(4129/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(61073313773191/4000000000000000 : ℝ)*(2/5 : ℝ)=(5061073313773191/5000000000000000 : ℝ) by norm_num, show 1+2*(99420448524396521/4000000000000000000 : ℝ)=(2099420448524396521/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(61073313773191/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4129/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (61073313773191/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(61073313773191/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4129/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (61073313773191/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(61073313773191/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4129/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (61073313773191/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-958049671/5000000000 : ℝ)*X 0 0+(379503967/625000000 : ℝ)*X 0 1+(74543523/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5521074971/10000000000 : ℝ)*X 1 0+(-533024281/2000000000 : ℝ)*X 1 1+(4770783999/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((552107217/1000000000 : ℝ)*X 2 0+(2385392851/5000000000 : ℝ)*X 2 1+(-1332561451/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1051802319/2500000000 : ℝ)*X 0 0+(781217019/2500000000 : ℝ)*X 0 1+(5675187347/10000000000 : ℝ)*X 0 2+(1051802319/2500000000 : ℝ)*X 1 0+(781217019/2500000000 : ℝ)*X 1 1+(5675187347/10000000000 : ℝ)*X 1 2+(1051802319/2500000000 : ℝ)*X 2 0+(781217019/2500000000 : ℝ)*X 2 1+(5675187347/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1921472809/10000000000 : ℝ)*X 0 0+(1201096361/2500000000 : ℝ)*X 0 1+(754661011/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((516788571/1000000000 : ℝ)*X 1 0+(-349655769/2500000000 : ℝ)*X 1 1+(1207457193/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2583942953/5000000000 : ℝ)*X 2 0+(754660889/1250000000 : ℝ)*X 2 1+(-1398620917/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2108869699/5000000000 : ℝ)*X 0 0+(1402333767/2500000000 : ℝ)*X 0 1+(199563897/625000000 : ℝ)*X 0 2+(2108869699/5000000000 : ℝ)*X 1 0+(1402333767/2500000000 : ℝ)*X 1 1+(199563897/625000000 : ℝ)*X 1 2+(2108869699/5000000000 : ℝ)*X 2 0+(1402333767/2500000000 : ℝ)*X 2 1+(199563897/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (77028530087189980341267/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11057667/50000000000000 : ℝ)*(base1) + (42206791/50000000000000 : ℝ)*(base16) + (251272707/50000000000000 : ℝ)*(base19) + (165347119/100000000000000 : ℝ)*(base23) + (4685811/12500000000000 : ℝ)*(upper3) + (580292480115079/100000000000000 : ℝ)*(major0) + (580292480115079/100000000000000 : ℝ)*(major1) + (580292480115079/100000000000000 : ℝ)*(major2) + (768476488531543/100000000000000 : ℝ)*(sp0) + (768476363357213/100000000000000 : ℝ)*(sp1) + (153695257755923/20000000000000 : ℝ)*(sp2) + (392107936446257/100000000000000 : ℝ)*(sp3) + (4839/1000000000 : ℝ)*(sp4) + (248094737/50000000000000 : ℝ)*(sp6) + (392107958561591/100000000000000 : ℝ)*(f.failure) + (768476950316209/100000000000000 : ℝ)*(f.sum) + (293667660152911/200000000000000000000000000000 : ℝ)*base66 + (145496146152911/400000000000000000000000000000 : ℝ)*base68 + (2026522004952911/400000000000000000000000000000 : ℝ)*base70 + (1042218916952911/400000000000000000000000000000 : ℝ)*base72 + (453530068352911/200000000000000000000000000000 : ℝ)*base74 + (410638601352911/400000000000000000000000000000 : ℝ)*base76 + (1036440214647089/400000000000000000000000000000 : ℝ)*base77 + (3358653245047089/400000000000000000000000000000 : ℝ)*base79 + (1215828573152911/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (31101729/5000000000000000000000 : ℝ)*base89 + (31101729/5000000000000000000000 : ℝ)*base91 + (31101729/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (225043735979613732474453/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (908917141/100000000000000 : ℝ)*(base19) + (1060291831/100000000000000 : ℝ)*(base23) + (16336311/25000000000000 : ℝ)*(base39) + (4062103/4000000000000 : ℝ)*(base45) + (4321503/5000000000000 : ℝ)*(upper3) + (255225829/100000000000000 : ℝ)*(upper5) + (306236762200473/50000000000000 : ℝ)*(major0) + (306236762200473/50000000000000 : ℝ)*(major1) + (612473459055703/100000000000000 : ℝ)*(major2) + (836933057/100000000000000 : ℝ)*(sp2) + (811093903128867/100000000000000 : ℝ)*(sp4) + (405546497105863/50000000000000 : ℝ)*(sp5) + (405546035624611/50000000000000 : ℝ)*(sp6) + (206926465149309/50000000000000 : ℝ)*(sp7) + (206926465149309/50000000000000 : ℝ)*(f.failure) + (811093968474111/100000000000000 : ℝ)*(f.sum) + (702635857503041/400000000000000000000000000000 : ℝ)*base66 + (4332104411741727/400000000000000000000000000000 : ℝ)*base68 + (769330428519343/200000000000000000000000000000 : ℝ)*base69 + (3621320192541727/400000000000000000000000000000 : ℝ)*base72 + (1568984772303041/400000000000000000000000000000 : ℝ)*base74 + (220707430280657/200000000000000000000000000000 : ℝ)*base76 + (512628562280657/200000000000000000000000000000 : ℝ)*base78 + (1084663185480657/200000000000000000000000000000 : ℝ)*base80 + (580116559880657/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (31255371/2500000000000000000000 : ℝ)*base89 + (31255371/2500000000000000000000 : ℝ)*base91 + (6255371/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1066_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73996519/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (97/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (28109/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1066_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1066_s1_0 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-425246539/2000000000 : ℝ)*x 0 + (572231237/1000000000 : ℝ)*x 1 + (2492983001/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (425246539/2000000000 : ℝ)^8259 ≤ (2552282891027/20000000000000 : ℝ)^6211 := by
    have hnat : (425246539 : ℕ)^8259*20000000000000^6211 ≤ 2552282891027^6211*2000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425246539 2000000000 2552282891027 20000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (572231237/1000000000 : ℝ)^8259 ≤ (2975183907967/6250000000000 : ℝ)^6211 := by
    have hnat : (572231237 : ℕ)^8259*6250000000000^6211 ≤ 2975183907967^6211*1000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      572231237 1000000000 2975183907967 6250000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2492983001/5000000000 : ℝ)^8259 ≤ (39635642997693/100000000000000 : ℝ)^6211 := by
    have hnat : (2492983001 : ℕ)^8259*100000000000000^6211 ≤ 39635642997693^6211*5000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2492983001 5000000000 39635642997693 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-425246539/2000000000 : ℝ), (572231237/1000000000 : ℝ), (2492983001/5000000000 : ℝ)] ![(2552282891027/20000000000000 : ℝ), (2975183907967/6250000000000 : ℝ), (39635642997693/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-425246539/2000000000 : ℝ)|^8259 ≤ (2552282891027/20000000000000 : ℝ)^6211
        have hw : |(-425246539/2000000000 : ℝ)|=(425246539/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(572231237/1000000000 : ℝ)|^8259 ≤ (2975183907967/6250000000000 : ℝ)^6211
        have hw : |(572231237/1000000000 : ℝ)|=(572231237/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2492983001/5000000000 : ℝ)|^8259 ≤ (39635642997693/100000000000000 : ℝ)^6211
        have hw : |(2492983001/5000000000 : ℝ)|=(2492983001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s1_1 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5423311161/10000000000 : ℝ)*x 0 + (-2525184623/10000000000 : ℝ)*x 1 + (62324579/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5423311161/10000000000 : ℝ)^8259 ≤ (2216213308333/5000000000000 : ℝ)^6211 := by
    have hnat : (5423311161 : ℕ)^8259*5000000000000^6211 ≤ 2216213308333^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423311161 10000000000 2216213308333 5000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2525184623/10000000000 : ℝ)^8259 ≤ (8020043724813/50000000000000 : ℝ)^6211 := by
    have hnat : (2525184623 : ℕ)^8259*50000000000000^6211 ≤ 8020043724813^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2525184623 10000000000 8020043724813 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (62324579/125000000 : ℝ)^8259 ≤ (19817823179583/50000000000000 : ℝ)^6211 := by
    have hnat : (62324579 : ℕ)^8259*50000000000000^6211 ≤ 19817823179583^6211*125000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62324579 125000000 19817823179583 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5423311161/10000000000 : ℝ), (-2525184623/10000000000 : ℝ), (62324579/125000000 : ℝ)] ![(2216213308333/5000000000000 : ℝ), (8020043724813/50000000000000 : ℝ), (19817823179583/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5423311161/10000000000 : ℝ)|^8259 ≤ (2216213308333/5000000000000 : ℝ)^6211
        have hw : |(5423311161/10000000000 : ℝ)|=(5423311161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2525184623/10000000000 : ℝ)|^8259 ≤ (8020043724813/50000000000000 : ℝ)^6211
        have hw : |(-2525184623/10000000000 : ℝ)|=(2525184623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(62324579/125000000 : ℝ)|^8259 ≤ (19817823179583/50000000000000 : ℝ)^6211
        have hw : |(62324579/125000000 : ℝ)|=(62324579/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s1_2 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (677913967/1250000000 : ℝ)*x 0 + (4985965667/10000000000 : ℝ)*x 1 + (-2525184701/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (677913967/1250000000 : ℝ)^8259 ≤ (2770267025979/6250000000000 : ℝ)^6211 := by
    have hnat : (677913967 : ℕ)^8259*6250000000000^6211 ≤ 2770267025979^6211*1250000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677913967 1250000000 2770267025979 6250000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4985965667/10000000000 : ℝ)^8259 ≤ (19817819728259/50000000000000 : ℝ)^6211 := by
    have hnat : (4985965667 : ℕ)^8259*50000000000000^6211 ≤ 19817819728259^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4985965667 10000000000 19817819728259 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2525184701/10000000000 : ℝ)^8259 ≤ (16040088108457/100000000000000 : ℝ)^6211 := by
    have hnat : (2525184701 : ℕ)^8259*100000000000000^6211 ≤ 16040088108457^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2525184701 10000000000 16040088108457 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(677913967/1250000000 : ℝ), (4985965667/10000000000 : ℝ), (-2525184701/10000000000 : ℝ)] ![(2770267025979/6250000000000 : ℝ), (19817819728259/50000000000000 : ℝ), (16040088108457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(677913967/1250000000 : ℝ)|^8259 ≤ (2770267025979/6250000000000 : ℝ)^6211
        have hw : |(677913967/1250000000 : ℝ)|=(677913967/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4985965667/10000000000 : ℝ)|^8259 ≤ (19817819728259/50000000000000 : ℝ)^6211
        have hw : |(4985965667/10000000000 : ℝ)|=(4985965667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2525184701/10000000000 : ℝ)|^8259 ≤ (16040088108457/100000000000000 : ℝ)^6211
        have hw : |(-2525184701/10000000000 : ℝ)|=(2525184701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s1_3 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4323804893/10000000000 : ℝ)*x 0 + (183127959/500000000 : ℝ)*x 1 + (2552847071/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4323804893/10000000000 : ℝ)^8259 ≤ (2049639479351/6250000000000 : ℝ)^6211 := by
    have hnat : (4323804893 : ℕ)^8259*6250000000000^6211 ≤ 2049639479351^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4323804893 10000000000 2049639479351 6250000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (183127959/500000000 : ℝ)^8259 ≤ (2629953469947/10000000000000 : ℝ)^6211 := by
    have hnat : (183127959 : ℕ)^8259*10000000000000^6211 ≤ 2629953469947^6211*500000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      183127959 500000000 2629953469947 10000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2552847071/5000000000 : ℝ)^8259 ≤ (8181246724941/20000000000000 : ℝ)^6211 := by
    have hnat : (2552847071 : ℕ)^8259*20000000000000^6211 ≤ 8181246724941^6211*5000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2552847071 5000000000 8181246724941 20000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4323804893/10000000000 : ℝ), (183127959/500000000 : ℝ), (2552847071/5000000000 : ℝ)] ![(2049639479351/6250000000000 : ℝ), (2629953469947/10000000000000 : ℝ), (8181246724941/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4323804893/10000000000 : ℝ)|^8259 ≤ (2049639479351/6250000000000 : ℝ)^6211
        have hw : |(4323804893/10000000000 : ℝ)|=(4323804893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(183127959/500000000 : ℝ)|^8259 ≤ (2629953469947/10000000000000 : ℝ)^6211
        have hw : |(183127959/500000000 : ℝ)|=(183127959/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2552847071/5000000000 : ℝ)|^8259 ≤ (8181246724941/20000000000000 : ℝ)^6211
        have hw : |(2552847071/5000000000 : ℝ)|=(2552847071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s1_4 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1063577381/5000000000 : ℝ)*x 0 + (624539249/1250000000 : ℝ)*x 1 + (5711751973/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1063577381/5000000000 : ℝ)^8259 ≤ (399024185661/3125000000000 : ℝ)^6211 := by
    have hnat : (1063577381 : ℕ)^8259*3125000000000^6211 ≤ 399024185661^6211*5000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1063577381 5000000000 399024185661 3125000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (624539249/1250000000 : ℝ)^8259 ≤ (39745065600697/100000000000000 : ℝ)^6211 := by
    have hnat : (624539249 : ℕ)^8259*100000000000000^6211 ≤ 39745065600697^6211*1250000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      624539249 1250000000 39745065600697 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5711751973/10000000000 : ℝ)^8259 ≤ (9497232089517/20000000000000 : ℝ)^6211 := by
    have hnat : (5711751973 : ℕ)^8259*20000000000000^6211 ≤ 9497232089517^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5711751973 10000000000 9497232089517 20000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1063577381/5000000000 : ℝ), (624539249/1250000000 : ℝ), (5711751973/10000000000 : ℝ)] ![(399024185661/3125000000000 : ℝ), (39745065600697/100000000000000 : ℝ), (9497232089517/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1063577381/5000000000 : ℝ)|^8259 ≤ (399024185661/3125000000000 : ℝ)^6211
        have hw : |(-1063577381/5000000000 : ℝ)|=(1063577381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(624539249/1250000000 : ℝ)|^8259 ≤ (39745065600697/100000000000000 : ℝ)^6211
        have hw : |(624539249/1250000000 : ℝ)|=(624539249/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5711751973/10000000000 : ℝ)|^8259 ≤ (9497232089517/20000000000000 : ℝ)^6211
        have hw : |(5711751973/10000000000 : ℝ)|=(5711751973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s1_5 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5235259579/10000000000 : ℝ)*x 0 + (-449849191/2500000000 : ℝ)*x 1 + (5711753693/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5235259579/10000000000 : ℝ)^8259 ≤ (21146164105971/50000000000000 : ℝ)^6211 := by
    have hnat : (5235259579 : ℕ)^8259*50000000000000^6211 ≤ 21146164105971^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5235259579 10000000000 21146164105971 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (449849191/2500000000 : ℝ)^8259 ≤ (2044298462827/20000000000000 : ℝ)^6211 := by
    have hnat : (449849191 : ℕ)^8259*20000000000000^6211 ≤ 2044298462827^6211*2500000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449849191 2500000000 2044298462827 20000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5711753693/10000000000 : ℝ)^8259 ≤ (7419715541/15625000000 : ℝ)^6211 := by
    have hnat : (5711753693 : ℕ)^8259*15625000000^6211 ≤ 7419715541^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5711753693 10000000000 7419715541 15625000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5235259579/10000000000 : ℝ), (-449849191/2500000000 : ℝ), (5711753693/10000000000 : ℝ)] ![(21146164105971/50000000000000 : ℝ), (2044298462827/20000000000000 : ℝ), (7419715541/15625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5235259579/10000000000 : ℝ)|^8259 ≤ (21146164105971/50000000000000 : ℝ)^6211
        have hw : |(5235259579/10000000000 : ℝ)|=(5235259579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-449849191/2500000000 : ℝ)|^8259 ≤ (2044298462827/20000000000000 : ℝ)^6211
        have hw : |(-449849191/2500000000 : ℝ)|=(449849191/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5711753693/10000000000 : ℝ)|^8259 ≤ (7419715541/15625000000 : ℝ)^6211
        have hw : |(5711753693/10000000000 : ℝ)|=(5711753693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s1_6 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2617628773/5000000000 : ℝ)*x 0 + (5711755939/10000000000 : ℝ)*x 1 + (-112462273/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2617628773/5000000000 : ℝ)^8259 ≤ (330408643541/781250000000 : ℝ)^6211 := by
    have hnat : (2617628773 : ℕ)^8259*781250000000^6211 ≤ 330408643541^6211*5000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2617628773 5000000000 330408643541 781250000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5711755939/10000000000 : ℝ)^8259 ≤ (9497240858443/20000000000000 : ℝ)^6211 := by
    have hnat : (5711755939 : ℕ)^8259*20000000000000^6211 ≤ 9497240858443^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5711755939 10000000000 9497240858443 20000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (112462273/625000000 : ℝ)^8259 ≤ (5110744661457/50000000000000 : ℝ)^6211 := by
    have hnat : (112462273 : ℕ)^8259*50000000000000^6211 ≤ 5110744661457^6211*625000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112462273 625000000 5110744661457 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2617628773/5000000000 : ℝ), (5711755939/10000000000 : ℝ), (-112462273/625000000 : ℝ)] ![(330408643541/781250000000 : ℝ), (9497240858443/20000000000000 : ℝ), (5110744661457/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2617628773/5000000000 : ℝ)|^8259 ≤ (330408643541/781250000000 : ℝ)^6211
        have hw : |(2617628773/5000000000 : ℝ)|=(2617628773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5711755939/10000000000 : ℝ)|^8259 ≤ (9497240858443/20000000000000 : ℝ)^6211
        have hw : |(5711755939/10000000000 : ℝ)|=(5711755939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-112462273/625000000 : ℝ)|^8259 ≤ (5110744661457/50000000000000 : ℝ)^6211
        have hw : |(-112462273/625000000 : ℝ)|=(112462273/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s1_7 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1081402003/2500000000 : ℝ)*x 0 + (5085410081/10000000000 : ℝ)*x 1 + (184162629/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081402003/2500000000 : ℝ)^8259 ≤ (6562483654249/20000000000000 : ℝ)^6211 := by
    have hnat : (1081402003 : ℕ)^8259*20000000000000^6211 ≤ 6562483654249^6211*2500000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081402003 2500000000 6562483654249 20000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5085410081/10000000000 : ℝ)^8259 ≤ (8138054981699/20000000000000 : ℝ)^6211 := by
    have hnat : (5085410081 : ℕ)^8259*20000000000000^6211 ≤ 8138054981699^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5085410081 10000000000 8138054981699 20000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (184162629/500000000 : ℝ)^8259 ≤ (26497306812761/100000000000000 : ℝ)^6211 := by
    have hnat : (184162629 : ℕ)^8259*100000000000000^6211 ≤ 26497306812761^6211*500000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      184162629 500000000 26497306812761 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1081402003/2500000000 : ℝ), (5085410081/10000000000 : ℝ), (184162629/500000000 : ℝ)] ![(6562483654249/20000000000000 : ℝ), (8138054981699/20000000000000 : ℝ), (26497306812761/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1081402003/2500000000 : ℝ)|^8259 ≤ (6562483654249/20000000000000 : ℝ)^6211
        have hw : |(1081402003/2500000000 : ℝ)|=(1081402003/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5085410081/10000000000 : ℝ)|^8259 ≤ (8138054981699/20000000000000 : ℝ)^6211
        have hw : |(5085410081/10000000000 : ℝ)|=(5085410081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(184162629/500000000 : ℝ)|^8259 ≤ (26497306812761/100000000000000 : ℝ)^6211
        have hw : |(184162629/500000000 : ℝ)|=(184162629/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1066_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73996519/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (28109/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (97/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5213/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20791/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (28109/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (97/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (28109/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (97/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (28109/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (97/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (28109/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (97/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (28109/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (97/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (28109/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (97/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (97/100000 : ℝ) ^ (4129/1024 : ℝ) ≤ (70791473/100000000000000000000 : ℝ) := by
    have hpowers : (97/100000 : ℝ)^4129 ≤ (70791473/100000000000000000000 : ℝ)^1024 := by
      have hnat : (97 : ℕ)^4129*100000000000000000000^1024 ≤ 70791473^1024*100000^4129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        97 100000 70791473 100000000000000000000 4129 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (97/100000 : ℝ)) (X := (70791473/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4129 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (28109/100000 : ℝ) ^ (4129/1024 : ℝ) ≤ (29963308658915949/5000000000000000000 : ℝ) := by
    have hpowers : (28109/100000 : ℝ)^4129 ≤ (29963308658915949/5000000000000000000 : ℝ)^1024 := by
      have hnat : (28109 : ℕ)^4129*5000000000000000000^1024 ≤ 29963308658915949^1024*100000^4129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28109 100000 29963308658915949 5000000000000000000 4129 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (28109/100000 : ℝ)) (X := (29963308658915949/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4129 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000000070791473/50000000000000000000 : ℝ) ≤ (1250000000000439/1250000000000000 : ℝ) ^ (4129/1024 : ℝ) := by
    have hpowers : (50000000000070791473/50000000000000000000 : ℝ)^1024 ≤ (1250000000000439/1250000000000000 : ℝ)^4129 := by
      have hnat : (50000000000070791473 : ℕ)^1024*1250000000000000^4129 ≤ 1250000000000439^4129*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000000070791473 50000000000000000000 1250000000000439 1250000000000000 1024 4129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250000000000439/1250000000000000 : ℝ)) (X := (50000000000070791473/50000000000000000000 : ℝ)) (by norm_num) 4129 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100599266173249110453/100000000000000000000 : ℝ) ≤ (10014828546528353/10000000000000000 : ℝ) ^ (4129/1024 : ℝ) := by
    have hpowers : (100599266173249110453/100000000000000000000 : ℝ)^1024 ≤ (10014828546528353/10000000000000000 : ℝ)^4129 := by
      have hnat : (100599266173249110453 : ℕ)^1024*10000000000000000^4129 ≤ 10014828546528353^4129*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100599266173249110453 100000000000000000000 10014828546528353 10000000000000000 1024 4129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10014828546528353/10000000000000000 : ℝ)) (X := (100599266173249110453/100000000000000000000 : ℝ)) (by norm_num) 4129 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2529963308658915949/2500000000000000000 : ℝ) ≤ (5014828546526597/5000000000000000 : ℝ) ^ (4129/1024 : ℝ) := by
    have hpowers : (2529963308658915949/2500000000000000000 : ℝ)^1024 ≤ (5014828546526597/5000000000000000 : ℝ)^4129 := by
      have hnat : (2529963308658915949 : ℕ)^1024*5000000000000000^4129 ≤ 5014828546526597^4129*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2529963308658915949 2500000000000000000 5014828546526597 5000000000000000 1024 4129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5014828546526597/5000000000000000 : ℝ)) (X := (2529963308658915949/2500000000000000000 : ℝ)) (by norm_num) 4129 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(70791473/100000000000000000000 : ℝ) ≤ ((28011712326207255899/28012000000000000000 : ℝ)+2*(14828546524841/2801200000000000 : ℝ)*(97/100000 : ℝ))^(4129/1024 : ℝ) := by
    rw [show (28011712326207255899/28012000000000000000 : ℝ)+2*(14828546524841/2801200000000000 : ℝ)*(97/100000 : ℝ)=(1250000000000439/1250000000000000 : ℝ) by norm_num, show 1+2*(70791473/100000000000000000000 : ℝ)=(50000000000070791473/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(29963308658915949/5000000000000000000 : ℝ)+(70791473/100000000000000000000 : ℝ) ≤ ((28011712326207255899/28012000000000000000 : ℝ)+(14828546524841/2801200000000000 : ℝ)*((28109/100000 : ℝ)+(97/100000 : ℝ)))^(4129/1024 : ℝ) := by
    rw [show (28011712326207255899/28012000000000000000 : ℝ)+(14828546524841/2801200000000000 : ℝ)*((28109/100000 : ℝ)+(97/100000 : ℝ))=(10014828546528353/10000000000000000 : ℝ) by norm_num, show 1+(29963308658915949/5000000000000000000 : ℝ)+(70791473/100000000000000000000 : ℝ)=(100599266173249110453/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(29963308658915949/5000000000000000000 : ℝ) ≤ ((28011712326207255899/28012000000000000000 : ℝ)+2*(14828546524841/2801200000000000 : ℝ)*(28109/100000 : ℝ))^(4129/1024 : ℝ) := by
    rw [show (28011712326207255899/28012000000000000000 : ℝ)+2*(14828546524841/2801200000000000 : ℝ)*(28109/100000 : ℝ)=(5014828546526597/5000000000000000 : ℝ) by norm_num, show 1+2*(29963308658915949/5000000000000000000 : ℝ)=(2529963308658915949/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (28011712326207255899/28012000000000000000 : ℝ)*(X 1 0+X 2 0)+(14828546524841/2801200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4129/1024 : ℝ)) (lo := (97/100000 : ℝ)) (hi := (28109/100000 : ℝ)) (c := (28011712326207255899/28012000000000000000 : ℝ)) (alpha := (14828546524841/2801200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (28011712326207255899/28012000000000000000 : ℝ)*(X 0 1+X 2 1)+(14828546524841/2801200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4129/1024 : ℝ)) (lo := (97/100000 : ℝ)) (hi := (28109/100000 : ℝ)) (c := (28011712326207255899/28012000000000000000 : ℝ)) (alpha := (14828546524841/2801200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (28011712326207255899/28012000000000000000 : ℝ)*(X 0 2+X 1 2)+(14828546524841/2801200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4129/1024 : ℝ)) (lo := (97/100000 : ℝ)) (hi := (28109/100000 : ℝ)) (c := (28011712326207255899/28012000000000000000 : ℝ)) (alpha := (14828546524841/2801200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-425246539/2000000000 : ℝ)*X 0 0+(572231237/1000000000 : ℝ)*X 0 1+(2492983001/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5423311161/10000000000 : ℝ)*X 1 0+(-2525184623/10000000000 : ℝ)*X 1 1+(62324579/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((677913967/1250000000 : ℝ)*X 2 0+(4985965667/10000000000 : ℝ)*X 2 1+(-2525184701/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4323804893/10000000000 : ℝ)*X 0 0+(183127959/500000000 : ℝ)*X 0 1+(2552847071/5000000000 : ℝ)*X 0 2+(4323804893/10000000000 : ℝ)*X 1 0+(183127959/500000000 : ℝ)*X 1 1+(2552847071/5000000000 : ℝ)*X 1 2+(4323804893/10000000000 : ℝ)*X 2 0+(183127959/500000000 : ℝ)*X 2 1+(2552847071/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1063577381/5000000000 : ℝ)*X 0 0+(624539249/1250000000 : ℝ)*X 0 1+(5711751973/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5235259579/10000000000 : ℝ)*X 1 0+(-449849191/2500000000 : ℝ)*X 1 1+(5711753693/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2617628773/5000000000 : ℝ)*X 2 0+(5711755939/10000000000 : ℝ)*X 2 1+(-112462273/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1081402003/2500000000 : ℝ)*X 0 0+(5085410081/10000000000 : ℝ)*X 0 1+(184162629/500000000 : ℝ)*X 0 2+(1081402003/2500000000 : ℝ)*X 1 0+(5085410081/10000000000 : ℝ)*X 1 1+(184162629/500000000 : ℝ)*X 1 2+(1081402003/2500000000 : ℝ)*X 2 0+(5085410081/10000000000 : ℝ)*X 2 1+(184162629/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (214612113822924343714609107/28012000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (67358739/50000000000000 : ℝ)*(base1) + (1665247707/100000000000000 : ℝ)*(base19) + (1809235601/100000000000000 : ℝ)*(base23) + (85627803/50000000000000 : ℝ)*(upper3) + (184164851/100000000000000 : ℝ)*(upper5) + (20510175793823/2000000000000 : ℝ)*(major0) + (20510175793823/2000000000000 : ℝ)*(major1) + (20510175793823/2000000000000 : ℝ)*(major2) + (135806470367531/10000000000000 : ℝ)*(sp0) + (1358071717909969/100000000000000 : ℝ)*(sp1) + (679035786961037/50000000000000 : ℝ)*(sp2) + (692939742608469/100000000000000 : ℝ)*(sp3) + (2203549961/25000000000000 : ℝ)*(sp4) + (2031758753/50000000000000 : ℝ)*(sp7) + (346471970421727/50000000000000 : ℝ)*(f.failure) + (339518345789419/25000000000000 : ℝ)*(f.sum) + (46169724255849/14006000000000000000000000000 : ℝ)*base65 + (143208193363445877/56024000000000000000000000000000 : ℝ)*base67 + (468703064270101877/56024000000000000000000000000000 : ℝ)*base69 + (326659591246389877/56024000000000000000000000000000 : ℝ)*base71 + (50846504019401/14006000000000000000000000000 : ℝ)*base73 + (91317486992149877/56024000000000000000000000000000 : ℝ)*base75 + (494574922651469877/56024000000000000000000000000000 : ℝ)*base77 + (492829808049605877/56024000000000000000000000000000 : ℝ)*base79 + (95739971044491/14006000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (9968313/2500000000000000000000 : ℝ)*base89 + (9968313/2500000000000000000000 : ℝ)*base91 + (9968313/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (248807876894125155261807/70030000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1324748837/50000000000000 : ℝ)*(base19) + (1292452741/50000000000000 : ℝ)*(base23) + (113367551/50000000000000 : ℝ)*(upper2) + (4246313/1000000000000 : ℝ)*(upper3) + (135370911/25000000000000 : ℝ)*(upper5) + (527732422497009/50000000000000 : ℝ)*(major0) + (527732422497009/50000000000000 : ℝ)*(major1) + (527732422497009/50000000000000 : ℝ)*(major2) + (1311610787/10000000000000 : ℝ)*(sp1) + (14371418287/100000000000000 : ℝ)*(sp2) + (349436025158883/25000000000000 : ℝ)*(sp4) + (349432083757497/25000000000000 : ℝ)*(sp5) + (1397727144311763/100000000000000 : ℝ)*(sp6) + (713185470923313/100000000000000 : ℝ)*(sp7) + (713185470923313/100000000000000 : ℝ)*(f.failure) + (349436025158883/25000000000000 : ℝ)*(f.sum) + (57436864750591/70030000000000000000000000000 : ℝ)*base66 + (10322310561372596091/1400600000000000000000000000000000 : ℝ)*base67 + (3087622201274803909/1400600000000000000000000000000000 : ℝ)*base70 + (1415128908296003909/1400600000000000000000000000000000 : ℝ)*base72 + (188053570635239/70030000000000000000000000000 : ℝ)*base73 + (5208440503856396091/1400600000000000000000000000000000 : ℝ)*base75 + (2667598242120803909/1400600000000000000000000000000000 : ℝ)*base78 + (6349089683087396091/1400600000000000000000000000000000 : ℝ)*base79 + (250251387936501/70030000000000000000000000000 : ℝ)*base82 + (22052553/5000000000000000000000 : ℝ)*base90 + (22052553/5000000000000000000000 : ℝ)*base92 + (22052553/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1066_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73996519/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (28109/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (97/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5213/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20791/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1066_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1066_s2_0 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2183652749/10000000000 : ℝ)*x 0 + (2762954103/5000000000 : ℝ)*x 1 + (160810617/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2183652749/10000000000 : ℝ)^8259 ≤ (13221708564107/100000000000000 : ℝ)^6211 := by
    have hnat : (2183652749 : ℕ)^8259*100000000000000^6211 ≤ 13221708564107^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183652749 10000000000 13221708564107 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2762954103/5000000000 : ℝ)^8259 ≤ (22721368410469/50000000000000 : ℝ)^6211 := by
    have hnat : (2762954103 : ℕ)^8259*50000000000000^6211 ≤ 22721368410469^6211*5000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2762954103 5000000000 22721368410469 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (160810617/312500000 : ℝ)^8259 ≤ (8267110920117/20000000000000 : ℝ)^6211 := by
    have hnat : (160810617 : ℕ)^8259*20000000000000^6211 ≤ 8267110920117^6211*312500000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      160810617 312500000 8267110920117 20000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2183652749/10000000000 : ℝ), (2762954103/5000000000 : ℝ), (160810617/312500000 : ℝ)] ![(13221708564107/100000000000000 : ℝ), (22721368410469/50000000000000 : ℝ), (8267110920117/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2183652749/10000000000 : ℝ)|^8259 ≤ (13221708564107/100000000000000 : ℝ)^6211
        have hw : |(-2183652749/10000000000 : ℝ)|=(2183652749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2762954103/5000000000 : ℝ)|^8259 ≤ (22721368410469/50000000000000 : ℝ)^6211
        have hw : |(2762954103/5000000000 : ℝ)|=(2762954103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(160810617/312500000 : ℝ)|^8259 ≤ (8267110920117/20000000000000 : ℝ)^6211
        have hw : |(160810617/312500000 : ℝ)|=(160810617/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s2_1 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1075440883/2000000000 : ℝ)*x 0 + (-2381809143/10000000000 : ℝ)*x 1 + (1286485251/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075440883/2000000000 : ℝ)^8259 ≤ (2738993088327/6250000000000 : ℝ)^6211 := by
    have hnat : (1075440883 : ℕ)^8259*6250000000000^6211 ≤ 2738993088327^6211*2000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075440883 2000000000 2738993088327 6250000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2381809143/10000000000 : ℝ)^8259 ≤ (14840542509007/100000000000000 : ℝ)^6211 := by
    have hnat : (2381809143 : ℕ)^8259*100000000000000^6211 ≤ 14840542509007^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2381809143 10000000000 14840542509007 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1286485251/2500000000 : ℝ)^8259 ≤ (41335568059051/100000000000000 : ℝ)^6211 := by
    have hnat : (1286485251 : ℕ)^8259*100000000000000^6211 ≤ 41335568059051^6211*2500000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1286485251 2500000000 41335568059051 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075440883/2000000000 : ℝ), (-2381809143/10000000000 : ℝ), (1286485251/2500000000 : ℝ)] ![(2738993088327/6250000000000 : ℝ), (14840542509007/100000000000000 : ℝ), (41335568059051/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075440883/2000000000 : ℝ)|^8259 ≤ (2738993088327/6250000000000 : ℝ)^6211
        have hw : |(1075440883/2000000000 : ℝ)|=(1075440883/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2381809143/10000000000 : ℝ)|^8259 ≤ (14840542509007/100000000000000 : ℝ)^6211
        have hw : |(-2381809143/10000000000 : ℝ)|=(2381809143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1286485251/2500000000 : ℝ)|^8259 ≤ (41335568059051/100000000000000 : ℝ)^6211
        have hw : |(1286485251/2500000000 : ℝ)|=(1286485251/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s2_2 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2688602211/5000000000 : ℝ)*x 0 + (1286485251/2500000000 : ℝ)*x 1 + (-476361827/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2688602211/5000000000 : ℝ)^8259 ≤ (43823889489093/100000000000000 : ℝ)^6211 := by
    have hnat : (2688602211 : ℕ)^8259*100000000000000^6211 ≤ 43823889489093^6211*5000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688602211 5000000000 43823889489093 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1286485251/2500000000 : ℝ)^8259 ≤ (41335568059051/100000000000000 : ℝ)^6211 := by
    have hnat : (1286485251 : ℕ)^8259*100000000000000^6211 ≤ 41335568059051^6211*2500000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1286485251 2500000000 41335568059051 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (476361827/2000000000 : ℝ)^8259 ≤ (3710135610681/25000000000000 : ℝ)^6211 := by
    have hnat : (476361827 : ℕ)^8259*25000000000000^6211 ≤ 3710135610681^6211*2000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      476361827 2000000000 3710135610681 25000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2688602211/5000000000 : ℝ), (1286485251/2500000000 : ℝ), (-476361827/2000000000 : ℝ)] ![(43823889489093/100000000000000 : ℝ), (41335568059051/100000000000000 : ℝ), (3710135610681/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2688602211/5000000000 : ℝ)|^8259 ≤ (43823889489093/100000000000000 : ℝ)^6211
        have hw : |(2688602211/5000000000 : ℝ)|=(2688602211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1286485251/2500000000 : ℝ)|^8259 ≤ (41335568059051/100000000000000 : ℝ)^6211
        have hw : |(1286485251/2500000000 : ℝ)|=(1286485251/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-476361827/2000000000 : ℝ)|^8259 ≤ (3710135610681/25000000000000 : ℝ)^6211
        have hw : |(-476361827/2000000000 : ℝ)|=(476361827/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s2_3 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (872597159/2000000000 : ℝ)*x 0 + (4006666163/10000000000 : ℝ)*x 1 + (950268403/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (872597159/2000000000 : ℝ)^8259 ≤ (33189979714279/100000000000000 : ℝ)^6211 := by
    have hnat : (872597159 : ℕ)^8259*100000000000000^6211 ≤ 33189979714279^6211*2000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      872597159 2000000000 33189979714279 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4006666163/10000000000 : ℝ)^8259 ≤ (29635062346503/100000000000000 : ℝ)^6211 := by
    have hnat : (4006666163 : ℕ)^8259*100000000000000^6211 ≤ 29635062346503^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4006666163 10000000000 29635062346503 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (950268403/2000000000 : ℝ)^8259 ≤ (37174957922873/100000000000000 : ℝ)^6211 := by
    have hnat : (950268403 : ℕ)^8259*100000000000000^6211 ≤ 37174957922873^6211*2000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      950268403 2000000000 37174957922873 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(872597159/2000000000 : ℝ), (4006666163/10000000000 : ℝ), (950268403/2000000000 : ℝ)] ![(33189979714279/100000000000000 : ℝ), (29635062346503/100000000000000 : ℝ), (37174957922873/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(872597159/2000000000 : ℝ)|^8259 ≤ (33189979714279/100000000000000 : ℝ)^6211
        have hw : |(872597159/2000000000 : ℝ)|=(872597159/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4006666163/10000000000 : ℝ)|^8259 ≤ (29635062346503/100000000000000 : ℝ)^6211
        have hw : |(4006666163/10000000000 : ℝ)|=(4006666163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(950268403/2000000000 : ℝ)|^8259 ≤ (37174957922873/100000000000000 : ℝ)^6211
        have hw : |(950268403/2000000000 : ℝ)|=(950268403/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s2_4 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1091889181/5000000000 : ℝ)*x 0 + (1287176357/2500000000 : ℝ)*x 1 + (1380778443/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1091889181/5000000000 : ℝ)^8259 ≤ (13222719930799/100000000000000 : ℝ)^6211 := by
    have hnat : (1091889181 : ℕ)^8259*100000000000000^6211 ≤ 13222719930799^6211*5000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091889181 5000000000 13222719930799 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1287176357/2500000000 : ℝ)^8259 ≤ (2585318648709/6250000000000 : ℝ)^6211 := by
    have hnat : (1287176357 : ℕ)^8259*6250000000000^6211 ≤ 2585318648709^6211*2500000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1287176357 2500000000 2585318648709 6250000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1380778443/2500000000 : ℝ)^8259 ≤ (22706090836451/50000000000000 : ℝ)^6211 := by
    have hnat : (1380778443 : ℕ)^8259*50000000000000^6211 ≤ 22706090836451^6211*2500000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1380778443 2500000000 22706090836451 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1091889181/5000000000 : ℝ), (1287176357/2500000000 : ℝ), (1380778443/2500000000 : ℝ)] ![(13222719930799/100000000000000 : ℝ), (2585318648709/6250000000000 : ℝ), (22706090836451/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1091889181/5000000000 : ℝ)|^8259 ≤ (13222719930799/100000000000000 : ℝ)^6211
        have hw : |(-1091889181/5000000000 : ℝ)|=(1091889181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1287176357/2500000000 : ℝ)|^8259 ≤ (2585318648709/6250000000000 : ℝ)^6211
        have hw : |(1287176357/2500000000 : ℝ)|=(1287176357/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1380778443/2500000000 : ℝ)|^8259 ≤ (22706090836451/50000000000000 : ℝ)^6211
        have hw : |(1380778443/2500000000 : ℝ)|=(1380778443/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s2_5 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5281296287/10000000000 : ℝ)*x 0 + (-2004637783/10000000000 : ℝ)*x 1 + (5523113857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5281296287/10000000000 : ℝ)^8259 ≤ (21393787415471/50000000000000 : ℝ)^6211 := by
    have hnat : (5281296287 : ℕ)^8259*50000000000000^6211 ≤ 21393787415471^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281296287 10000000000 21393787415471 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2004637783/10000000000 : ℝ)^8259 ≤ (11800242557353/100000000000000 : ℝ)^6211 := by
    have hnat : (2004637783 : ℕ)^8259*100000000000000^6211 ≤ 11800242557353^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2004637783 10000000000 11800242557353 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5523113857/10000000000 : ℝ)^8259 ≤ (45412182602239/100000000000000 : ℝ)^6211 := by
    have hnat : (5523113857 : ℕ)^8259*100000000000000^6211 ≤ 45412182602239^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5523113857 10000000000 45412182602239 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5281296287/10000000000 : ℝ), (-2004637783/10000000000 : ℝ), (5523113857/10000000000 : ℝ)] ![(21393787415471/50000000000000 : ℝ), (11800242557353/100000000000000 : ℝ), (45412182602239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5281296287/10000000000 : ℝ)|^8259 ≤ (21393787415471/50000000000000 : ℝ)^6211
        have hw : |(5281296287/10000000000 : ℝ)|=(5281296287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2004637783/10000000000 : ℝ)|^8259 ≤ (11800242557353/100000000000000 : ℝ)^6211
        have hw : |(-2004637783/10000000000 : ℝ)|=(2004637783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5523113857/10000000000 : ℝ)|^8259 ≤ (45412182602239/100000000000000 : ℝ)^6211
        have hw : |(5523113857/10000000000 : ℝ)|=(5523113857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s2_6 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5281296531/10000000000 : ℝ)*x 0 + (5523113693/10000000000 : ℝ)*x 1 + (-501159419/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5281296531/10000000000 : ℝ)^8259 ≤ (42787577459593/100000000000000 : ℝ)^6211 := by
    have hnat : (5281296531 : ℕ)^8259*100000000000000^6211 ≤ 42787577459593^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281296531 10000000000 42787577459593 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5523113693/10000000000 : ℝ)^8259 ≤ (22706090404583/50000000000000 : ℝ)^6211 := by
    have hnat : (5523113693 : ℕ)^8259*50000000000000^6211 ≤ 22706090404583^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5523113693 10000000000 22706090404583 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (501159419/2500000000 : ℝ)^8259 ≤ (2360048343963/20000000000000 : ℝ)^6211 := by
    have hnat : (501159419 : ℕ)^8259*20000000000000^6211 ≤ 2360048343963^6211*2500000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      501159419 2500000000 2360048343963 20000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5281296531/10000000000 : ℝ), (5523113693/10000000000 : ℝ), (-501159419/2500000000 : ℝ)] ![(42787577459593/100000000000000 : ℝ), (22706090404583/50000000000000 : ℝ), (2360048343963/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5281296531/10000000000 : ℝ)|^8259 ≤ (42787577459593/100000000000000 : ℝ)^6211
        have hw : |(5281296531/10000000000 : ℝ)|=(5281296531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5523113693/10000000000 : ℝ)|^8259 ≤ (22706090404583/50000000000000 : ℝ)^6211
        have hw : |(5523113693/10000000000 : ℝ)|=(5523113693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-501159419/2500000000 : ℝ)|^8259 ≤ (2360048343963/20000000000000 : ℝ)^6211
        have hw : |(-501159419/2500000000 : ℝ)|=(501159419/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s2_7 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (545403791/1250000000 : ℝ)*x 0 + (148310249/312500000 : ℝ)*x 1 + (802427887/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (545403791/1250000000 : ℝ)^8259 ≤ (1659622666039/5000000000000 : ℝ)^6211 := by
    have hnat : (545403791 : ℕ)^8259*5000000000000^6211 ≤ 1659622666039^6211*1250000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545403791 1250000000 1659622666039 5000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (148310249/312500000 : ℝ)^8259 ≤ (37118640790341/100000000000000 : ℝ)^6211 := by
    have hnat : (148310249 : ℕ)^8259*100000000000000^6211 ≤ 37118640790341^6211*312500000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      148310249 312500000 37118640790341 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (802427887/2000000000 : ℝ)^8259 ≤ (29688905864159/100000000000000 : ℝ)^6211 := by
    have hnat : (802427887 : ℕ)^8259*100000000000000^6211 ≤ 29688905864159^6211*2000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      802427887 2000000000 29688905864159 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(545403791/1250000000 : ℝ), (148310249/312500000 : ℝ), (802427887/2000000000 : ℝ)] ![(1659622666039/5000000000000 : ℝ), (37118640790341/100000000000000 : ℝ), (29688905864159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(545403791/1250000000 : ℝ)|^8259 ≤ (1659622666039/5000000000000 : ℝ)^6211
        have hw : |(545403791/1250000000 : ℝ)|=(545403791/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(148310249/312500000 : ℝ)|^8259 ≤ (37118640790341/100000000000000 : ℝ)^6211
        have hw : |(148310249/312500000 : ℝ)|=(148310249/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(802427887/2000000000 : ℝ)|^8259 ≤ (29688905864159/100000000000000 : ℝ)^6211
        have hw : |(802427887/2000000000 : ℝ)|=(802427887/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s2_8 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-158123/16000000 : ℝ)*x 0 + (5928142499/10000000000 : ℝ)*x 1 + (5927960671/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (158123/16000000 : ℝ)^8259 ≤ (43126086471/20000000000000 : ℝ)^6211 := by
    have hnat : (158123 : ℕ)^8259*20000000000000^6211 ≤ 43126086471^6211*16000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      158123 16000000 43126086471 20000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5928142499/10000000000 : ℝ)^8259 ≤ (12473300558849/25000000000000 : ℝ)^6211 := by
    have hnat : (5928142499 : ℕ)^8259*25000000000000^6211 ≤ 12473300558849^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5928142499 10000000000 12473300558849 25000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5927960671/10000000000 : ℝ)^8259 ≤ (9978233463167/20000000000000 : ℝ)^6211 := by
    have hnat : (5927960671 : ℕ)^8259*20000000000000^6211 ≤ 9978233463167^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5927960671 10000000000 9978233463167 20000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-158123/16000000 : ℝ), (5928142499/10000000000 : ℝ), (5927960671/10000000000 : ℝ)] ![(43126086471/20000000000000 : ℝ), (12473300558849/25000000000000 : ℝ), (9978233463167/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-158123/16000000 : ℝ)|^8259 ≤ (43126086471/20000000000000 : ℝ)^6211
        have hw : |(-158123/16000000 : ℝ)|=(158123/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5928142499/10000000000 : ℝ)|^8259 ≤ (12473300558849/25000000000000 : ℝ)^6211
        have hw : |(5928142499/10000000000 : ℝ)|=(5928142499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5927960671/10000000000 : ℝ)|^8259 ≤ (9978233463167/20000000000000 : ℝ)^6211
        have hw : |(5927960671/10000000000 : ℝ)|=(5927960671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s2_9 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (793605429/10000000000 : ℝ)*x 0 + (-4972632277/10000000000 : ℝ)*x 1 + (6558059757/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (793605429/10000000000 : ℝ)^8259 ≤ (172081010453/5000000000000 : ℝ)^6211 := by
    have hnat : (793605429 : ℕ)^8259*5000000000000^6211 ≤ 172081010453^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      793605429 10000000000 172081010453 5000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4972632277/10000000000 : ℝ)^8259 ≤ (19747379382921/50000000000000 : ℝ)^6211 := by
    have hnat : (4972632277 : ℕ)^8259*50000000000000^6211 ≤ 19747379382921^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4972632277 10000000000 19747379382921 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6558059757/10000000000 : ℝ)^8259 ≤ (11412724202393/20000000000000 : ℝ)^6211 := by
    have hnat : (6558059757 : ℕ)^8259*20000000000000^6211 ≤ 11412724202393^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6558059757 10000000000 11412724202393 20000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(793605429/10000000000 : ℝ), (-4972632277/10000000000 : ℝ), (6558059757/10000000000 : ℝ)] ![(172081010453/5000000000000 : ℝ), (19747379382921/50000000000000 : ℝ), (11412724202393/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(793605429/10000000000 : ℝ)|^8259 ≤ (172081010453/5000000000000 : ℝ)^6211
        have hw : |(793605429/10000000000 : ℝ)|=(793605429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4972632277/10000000000 : ℝ)|^8259 ≤ (19747379382921/50000000000000 : ℝ)^6211
        have hw : |(-4972632277/10000000000 : ℝ)|=(4972632277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6558059757/10000000000 : ℝ)|^8259 ≤ (11412724202393/20000000000000 : ℝ)^6211
        have hw : |(6558059757/10000000000 : ℝ)|=(6558059757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s2_10 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (792228099/10000000000 : ℝ)*x 0 + (3277255763/5000000000 : ℝ)*x 1 + (-2488635149/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (792228099/10000000000 : ℝ)^8259 ≤ (214604993159/6250000000000 : ℝ)^6211 := by
    have hnat : (792228099 : ℕ)^8259*6250000000000^6211 ≤ 214604993159^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      792228099 10000000000 214604993159 6250000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3277255763/5000000000 : ℝ)^8259 ≤ (57022570078847/100000000000000 : ℝ)^6211 := by
    have hnat : (3277255763 : ℕ)^8259*100000000000000^6211 ≤ 57022570078847^6211*5000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3277255763 5000000000 57022570078847 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2488635149/5000000000 : ℝ)^8259 ≤ (19771875008619/50000000000000 : ℝ)^6211 := by
    have hnat : (2488635149 : ℕ)^8259*50000000000000^6211 ≤ 19771875008619^6211*5000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2488635149 5000000000 19771875008619 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(792228099/10000000000 : ℝ), (3277255763/5000000000 : ℝ), (-2488635149/5000000000 : ℝ)] ![(214604993159/6250000000000 : ℝ), (57022570078847/100000000000000 : ℝ), (19771875008619/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(792228099/10000000000 : ℝ)|^8259 ≤ (214604993159/6250000000000 : ℝ)^6211
        have hw : |(792228099/10000000000 : ℝ)|=(792228099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3277255763/5000000000 : ℝ)|^8259 ≤ (57022570078847/100000000000000 : ℝ)^6211
        have hw : |(3277255763/5000000000 : ℝ)|=(3277255763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2488635149/5000000000 : ℝ)|^8259 ≤ (19771875008619/50000000000000 : ℝ)^6211
        have hw : |(-2488635149/5000000000 : ℝ)|=(2488635149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s2_11 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (420460723/10000000000 : ℝ)*x 0 + (733697361/1250000000 : ℝ)*x 1 + (1174694969/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (420460723/10000000000 : ℝ)^8259 ≤ (184852796377/12500000000000 : ℝ)^6211 := by
    have hnat : (420460723 : ℕ)^8259*12500000000000^6211 ≤ 184852796377^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420460723 10000000000 184852796377 12500000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (733697361/1250000000 : ℝ)^8259 ≤ (49238856863283/100000000000000 : ℝ)^6211 := by
    have hnat : (733697361 : ℕ)^8259*100000000000000^6211 ≤ 49238856863283^6211*1250000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      733697361 1250000000 49238856863283 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1174694969/2000000000 : ℝ)^8259 ≤ (6160290094571/12500000000000 : ℝ)^6211 := by
    have hnat : (1174694969 : ℕ)^8259*12500000000000^6211 ≤ 6160290094571^6211*2000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1174694969 2000000000 6160290094571 12500000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(420460723/10000000000 : ℝ), (733697361/1250000000 : ℝ), (1174694969/2000000000 : ℝ)] ![(184852796377/12500000000000 : ℝ), (49238856863283/100000000000000 : ℝ), (6160290094571/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(420460723/10000000000 : ℝ)|^8259 ≤ (184852796377/12500000000000 : ℝ)^6211
        have hw : |(420460723/10000000000 : ℝ)|=(420460723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(733697361/1250000000 : ℝ)|^8259 ≤ (49238856863283/100000000000000 : ℝ)^6211
        have hw : |(733697361/1250000000 : ℝ)|=(733697361/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1174694969/2000000000 : ℝ)|^8259 ≤ (6160290094571/12500000000000 : ℝ)^6211
        have hw : |(1174694969/2000000000 : ℝ)|=(1174694969/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1066_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73996519/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20791/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5213/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1089/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16741/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20791/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5213/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20791/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5213/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20791/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5213/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20791/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5213/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20791/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5213/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20791/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5213/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5213/100000 : ℝ) ^ (4129/1024 : ℝ) ≤ (671439747976287/100000000000000000000 : ℝ) := by
    have hpowers : (5213/100000 : ℝ)^4129 ≤ (671439747976287/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5213 : ℕ)^4129*100000000000000000000^1024 ≤ 671439747976287^1024*100000^4129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5213 100000 671439747976287 100000000000000000000 4129 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5213/100000 : ℝ)) (X := (671439747976287/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4129 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (20791/100000 : ℝ) ^ (4129/1024 : ℝ) ≤ (177631090462644241/100000000000000000000 : ℝ) := by
    have hpowers : (20791/100000 : ℝ)^4129 ≤ (177631090462644241/100000000000000000000 : ℝ)^1024 := by
      have hnat : (20791 : ℕ)^4129*100000000000000000000^1024 ≤ 177631090462644241^1024*100000^4129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20791 100000 177631090462644241 100000000000000000000 4129 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20791/100000 : ℝ)) (X := (177631090462644241/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4129 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000671439747976287/50000000000000000000 : ℝ) ≤ (10000033303503529/10000000000000000 : ℝ) ^ (4129/1024 : ℝ) := by
    have hpowers : (50000671439747976287/50000000000000000000 : ℝ)^1024 ≤ (10000033303503529/10000000000000000 : ℝ)^4129 := by
      have hnat : (50000671439747976287 : ℕ)^1024*10000000000000000^4129 ≤ 10000033303503529^4129*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000671439747976287 50000000000000000000 10000033303503529 10000000000000000 1024 4129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000033303503529/10000000000000000 : ℝ)) (X := (50000671439747976287/50000000000000000000 : ℝ)) (by norm_num) 4129 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6261143908138163783/6250000000000000000 : ℝ) ≤ (2501104743960547/2500000000000000 : ℝ) ^ (4129/1024 : ℝ) := by
    have hpowers : (6261143908138163783/6250000000000000000 : ℝ)^1024 ≤ (2501104743960547/2500000000000000 : ℝ)^4129 := by
      have hnat : (6261143908138163783 : ℕ)^1024*2500000000000000^4129 ≤ 2501104743960547^4129*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6261143908138163783 6250000000000000000 2501104743960547 2500000000000000 1024 4129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2501104743960547/2500000000000000 : ℝ)) (X := (6261143908138163783/6250000000000000000 : ℝ)) (by norm_num) 4129 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50177631090462644241/50000000000000000000 : ℝ) ≤ (10008804648180847/10000000000000000 : ℝ) ^ (4129/1024 : ℝ) := by
    have hpowers : (50177631090462644241/50000000000000000000 : ℝ)^1024 ≤ (10008804648180847/10000000000000000 : ℝ)^4129 := by
      have hnat : (50177631090462644241 : ℕ)^1024*10000000000000000^4129 ≤ 10008804648180847^4129*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50177631090462644241 50000000000000000000 10008804648180847 10000000000000000 1024 4129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10008804648180847/10000000000000000 : ℝ)) (X := (50177631090462644241/50000000000000000000 : ℝ)) (by norm_num) 4129 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(671439747976287/100000000000000000000 : ℝ) ≤ ((38933698445543779007/38945000000000000000 : ℝ)+2*(4385672338659/1557800000000000 : ℝ)*(5213/100000 : ℝ))^(4129/1024 : ℝ) := by
    rw [show (38933698445543779007/38945000000000000000 : ℝ)+2*(4385672338659/1557800000000000 : ℝ)*(5213/100000 : ℝ)=(10000033303503529/10000000000000000 : ℝ) by norm_num, show 1+2*(671439747976287/100000000000000000000 : ℝ)=(50000671439747976287/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(177631090462644241/100000000000000000000 : ℝ)+(671439747976287/100000000000000000000 : ℝ) ≤ ((38933698445543779007/38945000000000000000 : ℝ)+(4385672338659/1557800000000000 : ℝ)*((20791/100000 : ℝ)+(5213/100000 : ℝ)))^(4129/1024 : ℝ) := by
    rw [show (38933698445543779007/38945000000000000000 : ℝ)+(4385672338659/1557800000000000 : ℝ)*((20791/100000 : ℝ)+(5213/100000 : ℝ))=(2501104743960547/2500000000000000 : ℝ) by norm_num, show 1+(177631090462644241/100000000000000000000 : ℝ)+(671439747976287/100000000000000000000 : ℝ)=(6261143908138163783/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(177631090462644241/100000000000000000000 : ℝ) ≤ ((38933698445543779007/38945000000000000000 : ℝ)+2*(4385672338659/1557800000000000 : ℝ)*(20791/100000 : ℝ))^(4129/1024 : ℝ) := by
    rw [show (38933698445543779007/38945000000000000000 : ℝ)+2*(4385672338659/1557800000000000 : ℝ)*(20791/100000 : ℝ)=(10008804648180847/10000000000000000 : ℝ) by norm_num, show 1+2*(177631090462644241/100000000000000000000 : ℝ)=(50177631090462644241/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (38933698445543779007/38945000000000000000 : ℝ)*(X 1 0+X 2 0)+(4385672338659/1557800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4129/1024 : ℝ)) (lo := (5213/100000 : ℝ)) (hi := (20791/100000 : ℝ)) (c := (38933698445543779007/38945000000000000000 : ℝ)) (alpha := (4385672338659/1557800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (38933698445543779007/38945000000000000000 : ℝ)*(X 0 1+X 2 1)+(4385672338659/1557800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4129/1024 : ℝ)) (lo := (5213/100000 : ℝ)) (hi := (20791/100000 : ℝ)) (c := (38933698445543779007/38945000000000000000 : ℝ)) (alpha := (4385672338659/1557800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (38933698445543779007/38945000000000000000 : ℝ)*(X 0 2+X 1 2)+(4385672338659/1557800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4129/1024 : ℝ)) (lo := (5213/100000 : ℝ)) (hi := (20791/100000 : ℝ)) (c := (38933698445543779007/38945000000000000000 : ℝ)) (alpha := (4385672338659/1557800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2183652749/10000000000 : ℝ)*X 0 0+(2762954103/5000000000 : ℝ)*X 0 1+(160810617/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1075440883/2000000000 : ℝ)*X 1 0+(-2381809143/10000000000 : ℝ)*X 1 1+(1286485251/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2688602211/5000000000 : ℝ)*X 2 0+(1286485251/2500000000 : ℝ)*X 2 1+(-476361827/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((872597159/2000000000 : ℝ)*X 0 0+(4006666163/10000000000 : ℝ)*X 0 1+(950268403/2000000000 : ℝ)*X 0 2+(872597159/2000000000 : ℝ)*X 1 0+(4006666163/10000000000 : ℝ)*X 1 1+(950268403/2000000000 : ℝ)*X 1 2+(872597159/2000000000 : ℝ)*X 2 0+(4006666163/10000000000 : ℝ)*X 2 1+(950268403/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1091889181/5000000000 : ℝ)*X 0 0+(1287176357/2500000000 : ℝ)*X 0 1+(1380778443/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5281296287/10000000000 : ℝ)*X 1 0+(-2004637783/10000000000 : ℝ)*X 1 1+(5523113857/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5281296531/10000000000 : ℝ)*X 2 0+(5523113693/10000000000 : ℝ)*X 2 1+(-501159419/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((545403791/1250000000 : ℝ)*X 0 0+(148310249/312500000 : ℝ)*X 0 1+(802427887/2000000000 : ℝ)*X 0 2+(545403791/1250000000 : ℝ)*X 1 0+(148310249/312500000 : ℝ)*X 1 1+(802427887/2000000000 : ℝ)*X 1 2+(545403791/1250000000 : ℝ)*X 2 0+(148310249/312500000 : ℝ)*X 2 1+(802427887/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-158123/16000000 : ℝ)*X 0 0+(5928142499/10000000000 : ℝ)*X 0 1+(5927960671/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s2_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((793605429/10000000000 : ℝ)*X 1 0+(-4972632277/10000000000 : ℝ)*X 1 1+(6558059757/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s2_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((792228099/10000000000 : ℝ)*X 2 0+(3277255763/5000000000 : ℝ)*X 2 1+(-2488635149/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s2_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((420460723/10000000000 : ℝ)*X 0 0+(733697361/1250000000 : ℝ)*X 0 1+(1174694969/2000000000 : ℝ)*X 0 2+(420460723/10000000000 : ℝ)*X 1 0+(733697361/1250000000 : ℝ)*X 1 1+(1174694969/2000000000 : ℝ)*X 1 2+(420460723/10000000000 : ℝ)*X 2 0+(733697361/1250000000 : ℝ)*X 2 1+(1174694969/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s2_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (55788262302415839139149/19472500000000000000000000000 : ℝ) := by norm_num
    linear_combination (993675104231177/50000000000000 : ℝ)*(major0) + (993675104231177/50000000000000 : ℝ)*(major1) + (993675104231177/50000000000000 : ℝ)*(major2) + (2631814430159589/100000000000000 : ℝ)*(sp0) + (2631824778501561/100000000000000 : ℝ)*(sp1) + (13159123925103/500000000000 : ℝ)*(sp2) + (3357165370923/250000000000 : ℝ)*(sp3) + (8658490137/50000000000000 : ℝ)*(sp4) + (178455363/2500000000000 : ℝ)*(sp5) + (222742849/3125000000000 : ℝ)*(sp6) + (1210171931/100000000000000 : ℝ)*(sp8) + (520297857/50000000000000 : ℝ)*(sp9) + (1044520027/100000000000000 : ℝ)*(sp10) + (607872239/50000000000000 : ℝ)*(sp11) + (671433682056839/50000000000000 : ℝ)*(f.failure) + (1315916478655897/50000000000000 : ℝ)*(f.sum) + (72412003795743/38945000000000000000000000000 : ℝ)*base65 + (12335551472325826239/1947250000000000000000000000000000 : ℝ)*base67 + (13289532388444826239/1947250000000000000000000000000000 : ℝ)*base69 + (17971626121655173761/1947250000000000000000000000000000 : ℝ)*base72 + (32482436609827/9736250000000000000000000000 : ℝ)*base73 + (8466951536878423761/1947250000000000000000000000000000 : ℝ)*base76 + (3145638608574826239/1947250000000000000000000000000000 : ℝ)*base77 + (6883819368283923761/1947250000000000000000000000000000 : ℝ)*base80 + (68431253238923/38945000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (3856559/2500000000000000000000 : ℝ)*base90 + (3856559/2500000000000000000000 : ℝ)*base92 + (3856559/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (203497469332325021006735139/19472500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (40336744574541/2000000000000 : ℝ)*(major0) + (40336744574541/2000000000000 : ℝ)*(major1) + (40336744574541/2000000000000 : ℝ)*(major2) + (395629693/50000000000000 : ℝ)*(sp1) + (240535711/100000000000000 : ℝ)*(sp2) + (17850941/6250000000000 : ℝ)*(sp3) + (2670880900786447/100000000000000 : ℝ)*(sp4) + (267088079826249/10000000000000 : ℝ)*(sp5) + (1335440607874521/50000000000000 : ℝ)*(sp6) + (681395433247393/50000000000000 : ℝ)*(sp7) + (622299417/50000000000000 : ℝ)*(sp8) + (111172681/20000000000000 : ℝ)*(sp9) + (43068783/6250000000000 : ℝ)*(sp10) + (811608781/100000000000000 : ℝ)*(sp11) + (42587248866207/3125000000000 : ℝ)*(f.failure) + (8346506704329/312500000000 : ℝ)*(f.sum) + (6301708750173/1947250000000000000000000000 : ℝ)*base65 + (328420354955895787/77890000000000000000000000000000 : ℝ)*base67 + (389683768074665787/77890000000000000000000000000000 : ℝ)*base69 + (43212366918595787/77890000000000000000000000000000 : ℝ)*base71 + (12122609497689/1947250000000000000000000000 : ℝ)*base73 + (716979545096375787/77890000000000000000000000000000 : ℝ)*base75 + (264331161313794213/77890000000000000000000000000000 : ℝ)*base78 + (215267122099455787/77890000000000000000000000000000 : ℝ)*base79 + (52195334079109/7789000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (891567/156250000000000000000 : ℝ)*base90 + (891567/156250000000000000000 : ℝ)*base92 + (891567/156250000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1066_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73996519/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20791/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5213/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1089/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16741/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1066_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1066_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73996519/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1089/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16741/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1066_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1066_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1066_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73996519/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1089/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16741/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1066_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
