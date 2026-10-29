-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1323_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:44:15.55442+00:00
-- url     : https://prove2.me/submissions/8aaf0f5a-3dd4-48d2-868b-f8aa4125feee

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
theorem support_rectangle_w1323_s6_0 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2060492889/10000000000 : ℝ)*x 0 + (541371151/1000000000 : ℝ)*x 1 + (5243985617/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2060492889/10000000000 : ℝ)^4283 ≤ (6271713011363/50000000000000 : ℝ)^3259 := by
    have hnat : (2060492889 : ℕ)^4283*50000000000000^3259 ≤ 6271713011363^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2060492889 10000000000 6271713011363 50000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (541371151/1000000000 : ℝ)^4283 ≤ (44643419966173/100000000000000 : ℝ)^3259 := by
    have hnat : (541371151 : ℕ)^4283*100000000000000^3259 ≤ 44643419966173^3259*1000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541371151 1000000000 44643419966173 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243985617/10000000000 : ℝ)^4283 ≤ (42813153992543/100000000000000 : ℝ)^3259 := by
    have hnat : (5243985617 : ℕ)^4283*100000000000000^3259 ≤ 42813153992543^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243985617 10000000000 42813153992543 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2060492889/10000000000 : ℝ), (541371151/1000000000 : ℝ), (5243985617/10000000000 : ℝ)] ![(6271713011363/50000000000000 : ℝ), (44643419966173/100000000000000 : ℝ), (42813153992543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2060492889/10000000000 : ℝ)|^4283 ≤ (6271713011363/50000000000000 : ℝ)^3259
        have hw : |(-2060492889/10000000000 : ℝ)|=(2060492889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(541371151/1000000000 : ℝ)|^4283 ≤ (44643419966173/100000000000000 : ℝ)^3259
        have hw : |(541371151/1000000000 : ℝ)|=(541371151/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243985617/10000000000 : ℝ)|^4283 ≤ (42813153992543/100000000000000 : ℝ)^3259
        have hw : |(5243985617/10000000000 : ℝ)|=(5243985617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_s6_1 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267466257/500000000 : ℝ)*x 0 + (-2146985981/10000000000 : ℝ)*x 1 + (5243983757/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267466257/500000000 : ℝ)^4283 ≤ (2197347246129/5000000000000 : ℝ)^3259 := by
    have hnat : (267466257 : ℕ)^4283*5000000000000^3259 ≤ 2197347246129^3259*500000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267466257 500000000 2197347246129 5000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2146985981/10000000000 : ℝ)^4283 ≤ (13239921022973/100000000000000 : ℝ)^3259 := by
    have hnat : (2146985981 : ℕ)^4283*100000000000000^3259 ≤ 13239921022973^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2146985981 10000000000 13239921022973 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243983757/10000000000 : ℝ)^4283 ≤ (10703283508919/25000000000000 : ℝ)^3259 := by
    have hnat : (5243983757 : ℕ)^4283*25000000000000^3259 ≤ 10703283508919^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243983757 10000000000 10703283508919 25000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267466257/500000000 : ℝ), (-2146985981/10000000000 : ℝ), (5243983757/10000000000 : ℝ)] ![(2197347246129/5000000000000 : ℝ), (13239921022973/100000000000000 : ℝ), (10703283508919/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267466257/500000000 : ℝ)|^4283 ≤ (2197347246129/5000000000000 : ℝ)^3259
        have hw : |(267466257/500000000 : ℝ)|=(267466257/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2146985981/10000000000 : ℝ)|^4283 ≤ (13239921022973/100000000000000 : ℝ)^3259
        have hw : |(-2146985981/10000000000 : ℝ)|=(2146985981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243983757/10000000000 : ℝ)|^4283 ≤ (10703283508919/25000000000000 : ℝ)^3259
        have hw : |(5243983757/10000000000 : ℝ)|=(5243983757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_s6_2 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349323051/10000000000 : ℝ)*x 0 + (5243986173/10000000000 : ℝ)*x 1 + (-1073492783/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349323051/10000000000 : ℝ)^4283 ≤ (5493365296019/12500000000000 : ℝ)^3259 := by
    have hnat : (5349323051 : ℕ)^4283*12500000000000^3259 ≤ 5493365296019^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349323051 10000000000 5493365296019 12500000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243986173/10000000000 : ℝ)^4283 ≤ (334477812173/781250000000 : ℝ)^3259 := by
    have hnat : (5243986173 : ℕ)^4283*781250000000^3259 ≤ 334477812173^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243986173 10000000000 334477812173 781250000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1073492783/5000000000 : ℝ)^4283 ≤ (6619958829827/50000000000000 : ℝ)^3259 := by
    have hnat : (1073492783 : ℕ)^4283*50000000000000^3259 ≤ 6619958829827^3259*5000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073492783 5000000000 6619958829827 50000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349323051/10000000000 : ℝ), (5243986173/10000000000 : ℝ), (-1073492783/5000000000 : ℝ)] ![(5493365296019/12500000000000 : ℝ), (334477812173/781250000000 : ℝ), (6619958829827/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349323051/10000000000 : ℝ)|^4283 ≤ (5493365296019/12500000000000 : ℝ)^3259
        have hw : |(5349323051/10000000000 : ℝ)|=(5349323051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243986173/10000000000 : ℝ)|^4283 ≤ (334477812173/781250000000 : ℝ)^3259
        have hw : |(5243986173/10000000000 : ℝ)|=(5243986173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1073492783/5000000000 : ℝ)|^4283 ≤ (6619958829827/50000000000000 : ℝ)^3259
        have hw : |(-1073492783/5000000000 : ℝ)|=(1073492783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_s6_3 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4331609597/10000000000 : ℝ)*x 0 + (519814251/1250000000 : ℝ)*x 1 + (70491907/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4331609597/10000000000 : ℝ)^4283 ≤ (8325724830949/25000000000000 : ℝ)^3259 := by
    have hnat : (4331609597 : ℕ)^4283*25000000000000^3259 ≤ 8325724830949^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4331609597 10000000000 8325724830949 25000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (519814251/1250000000 : ℝ)^4283 ≤ (7891252760929/25000000000000 : ℝ)^3259 := by
    have hnat : (519814251 : ℕ)^4283*25000000000000^3259 ≤ 7891252760929^3259*1250000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519814251 1250000000 7891252760929 25000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (70491907/156250000 : ℝ)^4283 ≤ (17566044812911/50000000000000 : ℝ)^3259 := by
    have hnat : (70491907 : ℕ)^4283*50000000000000^3259 ≤ 17566044812911^3259*156250000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70491907 156250000 17566044812911 50000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4331609597/10000000000 : ℝ), (519814251/1250000000 : ℝ), (70491907/156250000 : ℝ)] ![(8325724830949/25000000000000 : ℝ), (7891252760929/25000000000000 : ℝ), (17566044812911/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4331609597/10000000000 : ℝ)|^4283 ≤ (8325724830949/25000000000000 : ℝ)^3259
        have hw : |(4331609597/10000000000 : ℝ)|=(4331609597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(519814251/1250000000 : ℝ)|^4283 ≤ (7891252760929/25000000000000 : ℝ)^3259
        have hw : |(519814251/1250000000 : ℝ)|=(519814251/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(70491907/156250000 : ℝ)|^4283 ≤ (17566044812911/50000000000000 : ℝ)^3259
        have hw : |(70491907/156250000 : ℝ)|=(70491907/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_s6_4 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-206050553/1000000000 : ℝ)*x 0 + (2622295897/5000000000 : ℝ)*x 1 + (5413102017/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (206050553/1000000000 : ℝ)^4283 ≤ (3135881788799/25000000000000 : ℝ)^3259 := by
    have hnat : (206050553 : ℕ)^4283*25000000000000^3259 ≤ 3135881788799^3259*1000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206050553 1000000000 3135881788799 25000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622295897/5000000000 : ℝ)^4283 ≤ (4281965808619/10000000000000 : ℝ)^3259 := by
    have hnat : (2622295897 : ℕ)^4283*10000000000000^3259 ≤ 4281965808619^3259*5000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622295897 5000000000 4281965808619 10000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413102017/10000000000 : ℝ)^4283 ≤ (44636814748987/100000000000000 : ℝ)^3259 := by
    have hnat : (5413102017 : ℕ)^4283*100000000000000^3259 ≤ 44636814748987^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413102017 10000000000 44636814748987 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-206050553/1000000000 : ℝ), (2622295897/5000000000 : ℝ), (5413102017/10000000000 : ℝ)] ![(3135881788799/25000000000000 : ℝ), (4281965808619/10000000000000 : ℝ), (44636814748987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-206050553/1000000000 : ℝ)|^4283 ≤ (3135881788799/25000000000000 : ℝ)^3259
        have hw : |(-206050553/1000000000 : ℝ)|=(206050553/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622295897/5000000000 : ℝ)|^4283 ≤ (4281965808619/10000000000000 : ℝ)^3259
        have hw : |(2622295897/5000000000 : ℝ)|=(2622295897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413102017/10000000000 : ℝ)|^4283 ≤ (44636814748987/100000000000000 : ℝ)^3259
        have hw : |(5413102017/10000000000 : ℝ)|=(5413102017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_s6_5 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326425819/2500000000 : ℝ)*x 0 + (-12361683/62500000 : ℝ)*x 1 + (5413101921/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326425819/2500000000 : ℝ)^4283 ≤ (43476574674833/100000000000000 : ℝ)^3259 := by
    have hnat : (1326425819 : ℕ)^4283*100000000000000^3259 ≤ 43476574674833^3259*2500000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326425819 2500000000 43476574674833 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (12361683/62500000 : ℝ)^4283 ≤ (1188661159821/10000000000000 : ℝ)^3259 := by
    have hnat : (12361683 : ℕ)^4283*10000000000000^3259 ≤ 1188661159821^3259*62500000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12361683 62500000 1188661159821 10000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413101921/10000000000 : ℝ)^4283 ≤ (44636813708631/100000000000000 : ℝ)^3259 := by
    have hnat : (5413101921 : ℕ)^4283*100000000000000^3259 ≤ 44636813708631^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413101921 10000000000 44636813708631 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326425819/2500000000 : ℝ), (-12361683/62500000 : ℝ), (5413101921/10000000000 : ℝ)] ![(43476574674833/100000000000000 : ℝ), (1188661159821/10000000000000 : ℝ), (44636813708631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326425819/2500000000 : ℝ)|^4283 ≤ (43476574674833/100000000000000 : ℝ)^3259
        have hw : |(1326425819/2500000000 : ℝ)|=(1326425819/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-12361683/62500000 : ℝ)|^4283 ≤ (1188661159821/10000000000000 : ℝ)^3259
        have hw : |(-12361683/62500000 : ℝ)|=(12361683/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413101921/10000000000 : ℝ)|^4283 ≤ (44636813708631/100000000000000 : ℝ)^3259
        have hw : |(5413101921/10000000000 : ℝ)|=(5413101921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_s6_6 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326425817/2500000000 : ℝ)*x 0 + (2706551/5000000 : ℝ)*x 1 + (-1977869183/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326425817/2500000000 : ℝ)^4283 ≤ (43476574588681/100000000000000 : ℝ)^3259 := by
    have hnat : (1326425817 : ℕ)^4283*100000000000000^3259 ≤ 43476574588681^3259*2500000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326425817 2500000000 43476574588681 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2706551/5000000 : ℝ)^4283 ≤ (44636814564757/100000000000000 : ℝ)^3259 := by
    have hnat : (2706551 : ℕ)^4283*100000000000000^3259 ≤ 44636814564757^3259*5000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706551 5000000 44636814564757 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1977869183/10000000000 : ℝ)^4283 ≤ (11886610832091/100000000000000 : ℝ)^3259 := by
    have hnat : (1977869183 : ℕ)^4283*100000000000000^3259 ≤ 11886610832091^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1977869183 10000000000 11886610832091 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326425817/2500000000 : ℝ), (2706551/5000000 : ℝ), (-1977869183/10000000000 : ℝ)] ![(43476574588681/100000000000000 : ℝ), (44636814564757/100000000000000 : ℝ), (11886610832091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326425817/2500000000 : ℝ)|^4283 ≤ (43476574588681/100000000000000 : ℝ)^3259
        have hw : |(1326425817/2500000000 : ℝ)|=(1326425817/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2706551/5000000 : ℝ)|^4283 ≤ (44636814564757/100000000000000 : ℝ)^3259
        have hw : |(2706551/5000000 : ℝ)|=(2706551/5000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1977869183/10000000000 : ℝ)|^4283 ≤ (11886610832091/100000000000000 : ℝ)^3259
        have hw : |(-1977869183/10000000000 : ℝ)|=(1977869183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_s6_7 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4331635019/10000000000 : ℝ)*x 0 + (4510219163/10000000000 : ℝ)*x 1 + (4159783769/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4331635019/10000000000 : ℝ)^4283 ≤ (33303156189763/100000000000000 : ℝ)^3259 := by
    have hnat : (4331635019 : ℕ)^4283*100000000000000^3259 ≤ 33303156189763^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4331635019 10000000000 33303156189763 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4510219163/10000000000 : ℝ)^4283 ≤ (17559582869197/50000000000000 : ℝ)^3259 := by
    have hnat : (4510219163 : ℕ)^4283*50000000000000^3259 ≤ 17559582869197^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4510219163 10000000000 17559582869197 50000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4159783769/10000000000 : ℝ)^4283 ≤ (15788839029663/50000000000000 : ℝ)^3259 := by
    have hnat : (4159783769 : ℕ)^4283*50000000000000^3259 ≤ 15788839029663^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4159783769 10000000000 15788839029663 50000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4331635019/10000000000 : ℝ), (4510219163/10000000000 : ℝ), (4159783769/10000000000 : ℝ)] ![(33303156189763/100000000000000 : ℝ), (17559582869197/50000000000000 : ℝ), (15788839029663/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4331635019/10000000000 : ℝ)|^4283 ≤ (33303156189763/100000000000000 : ℝ)^3259
        have hw : |(4331635019/10000000000 : ℝ)|=(4331635019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4510219163/10000000000 : ℝ)|^4283 ≤ (17559582869197/50000000000000 : ℝ)^3259
        have hw : |(4510219163/10000000000 : ℝ)|=(4510219163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4159783769/10000000000 : ℝ)|^4283 ≤ (15788839029663/50000000000000 : ℝ)^3259
        have hw : |(4159783769/10000000000 : ℝ)|=(4159783769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1323_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76990221/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2941/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5547/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11103/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1837/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2941/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5547/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2941/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5547/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2941/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5547/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2941/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5547/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2941/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5547/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2941/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5547/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5547/50000 : ℝ) ^ (2141/512 : ℝ) ≤ (2032038156713013/20000000000000000000 : ℝ) := by
    have hpowers : (5547/50000 : ℝ)^2141 ≤ (2032038156713013/20000000000000000000 : ℝ)^512 := by
      have hnat : (5547 : ℕ)^2141*20000000000000000000^512 ≤ 2032038156713013^512*50000^2141 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5547 50000 2032038156713013 20000000000000000000 2141 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5547/50000 : ℝ)) (X := (2032038156713013/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2141 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2941/20000 : ℝ) ^ (2141/512 : ℝ) ≤ (33009423751399/100000000000000000 : ℝ) := by
    have hpowers : (2941/20000 : ℝ)^2141 ≤ (33009423751399/100000000000000000 : ℝ)^512 := by
      have hnat : (2941 : ℕ)^2141*100000000000000000^512 ≤ 33009423751399^512*20000^2141 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2941 20000 33009423751399 100000000000000000 2141 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2941/20000 : ℝ)) (X := (33009423751399/100000000000000000 : ℝ)) (by norm_num) (by norm_num) 2141 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002032038156713013/10000000000000000000 : ℝ) ≤ (312515184538733/312500000000000 : ℝ) ^ (2141/512 : ℝ) := by
    have hpowers : (10002032038156713013/10000000000000000000 : ℝ)^512 ≤ (312515184538733/312500000000000 : ℝ)^2141 := by
      have hnat : (10002032038156713013 : ℕ)^512*312500000000000^2141 ≤ 312515184538733^2141*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002032038156713013 10000000000000000000 312515184538733 312500000000000 512 2141 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312515184538733/312500000000000 : ℝ)) (X := (10002032038156713013/10000000000000000000 : ℝ)) (by norm_num) 2141 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (20008633922906992813/20000000000000000000 : ℝ) ≤ (80008257529607/80000000000000 : ℝ) ^ (2141/512 : ℝ) := by
    have hpowers : (20008633922906992813/20000000000000000000 : ℝ)^512 ≤ (80008257529607/80000000000000 : ℝ)^2141 := by
      have hnat : (20008633922906992813 : ℕ)^512*80000000000000^2141 ≤ 80008257529607^2141*20000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20008633922906992813 20000000000000000000 80008257529607 80000000000000 512 2141 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (80008257529607/80000000000000 : ℝ)) (X := (20008633922906992813/20000000000000000000 : ℝ)) (by norm_num) 2141 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033009423751399/50000000000000000 : ℝ) ≤ (5000789238581147/5000000000000000 : ℝ) ^ (2141/512 : ℝ) := by
    have hpowers : (50033009423751399/50000000000000000 : ℝ)^512 ≤ (5000789238581147/5000000000000000 : ℝ)^2141 := by
      have hnat : (50033009423751399 : ℕ)^512*5000000000000000^2141 ≤ 5000789238581147^2141*50000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033009423751399 50000000000000000 5000789238581147 5000000000000000 512 2141 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000789238581147/5000000000000000 : ℝ)) (X := (50033009423751399/50000000000000000 : ℝ)) (by norm_num) 2141 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2032038156713013/20000000000000000000 : ℝ) ≤ ((9024908402726927711/9027500000000000000 : ℝ)+2*(546285961419/361100000000000 : ℝ)*(5547/50000 : ℝ))^(2141/512 : ℝ) := by
    rw [show (9024908402726927711/9027500000000000000 : ℝ)+2*(546285961419/361100000000000 : ℝ)*(5547/50000 : ℝ)=(312515184538733/312500000000000 : ℝ) by norm_num, show 1+2*(2032038156713013/20000000000000000000 : ℝ)=(10002032038156713013/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33009423751399/100000000000000000 : ℝ)+(2032038156713013/20000000000000000000 : ℝ) ≤ ((9024908402726927711/9027500000000000000 : ℝ)+(546285961419/361100000000000 : ℝ)*((2941/20000 : ℝ)+(5547/50000 : ℝ)))^(2141/512 : ℝ) := by
    rw [show (9024908402726927711/9027500000000000000 : ℝ)+(546285961419/361100000000000 : ℝ)*((2941/20000 : ℝ)+(5547/50000 : ℝ))=(80008257529607/80000000000000 : ℝ) by norm_num, show 1+(33009423751399/100000000000000000 : ℝ)+(2032038156713013/20000000000000000000 : ℝ)=(20008633922906992813/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33009423751399/100000000000000000 : ℝ) ≤ ((9024908402726927711/9027500000000000000 : ℝ)+2*(546285961419/361100000000000 : ℝ)*(2941/20000 : ℝ))^(2141/512 : ℝ) := by
    rw [show (9024908402726927711/9027500000000000000 : ℝ)+2*(546285961419/361100000000000 : ℝ)*(2941/20000 : ℝ)=(5000789238581147/5000000000000000 : ℝ) by norm_num, show 1+2*(33009423751399/100000000000000000 : ℝ)=(50033009423751399/50000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9024908402726927711/9027500000000000000 : ℝ)*(X 1 0+X 2 0)+(546285961419/361100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2141/512 : ℝ)) (lo := (5547/50000 : ℝ)) (hi := (2941/20000 : ℝ)) (c := (9024908402726927711/9027500000000000000 : ℝ)) (alpha := (546285961419/361100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9024908402726927711/9027500000000000000 : ℝ)*(X 0 1+X 2 1)+(546285961419/361100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2141/512 : ℝ)) (lo := (5547/50000 : ℝ)) (hi := (2941/20000 : ℝ)) (c := (9024908402726927711/9027500000000000000 : ℝ)) (alpha := (546285961419/361100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9024908402726927711/9027500000000000000 : ℝ)*(X 0 2+X 1 2)+(546285961419/361100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2141/512 : ℝ)) (lo := (5547/50000 : ℝ)) (hi := (2941/20000 : ℝ)) (c := (9024908402726927711/9027500000000000000 : ℝ)) (alpha := (546285961419/361100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2060492889/10000000000 : ℝ)*X 0 0+(541371151/1000000000 : ℝ)*X 0 1+(5243985617/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267466257/500000000 : ℝ)*X 1 0+(-2146985981/10000000000 : ℝ)*X 1 1+(5243983757/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349323051/10000000000 : ℝ)*X 2 0+(5243986173/10000000000 : ℝ)*X 2 1+(-1073492783/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4331609597/10000000000 : ℝ)*X 0 0+(519814251/1250000000 : ℝ)*X 0 1+(70491907/156250000 : ℝ)*X 0 2+(4331609597/10000000000 : ℝ)*X 1 0+(519814251/1250000000 : ℝ)*X 1 1+(70491907/156250000 : ℝ)*X 1 2+(4331609597/10000000000 : ℝ)*X 2 0+(519814251/1250000000 : ℝ)*X 2 1+(70491907/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-206050553/1000000000 : ℝ)*X 0 0+(2622295897/5000000000 : ℝ)*X 0 1+(5413102017/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326425819/2500000000 : ℝ)*X 1 0+(-12361683/62500000 : ℝ)*X 1 1+(5413101921/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326425817/2500000000 : ℝ)*X 2 0+(2706551/5000000 : ℝ)*X 2 1+(-1977869183/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4331635019/10000000000 : ℝ)*X 0 0+(4510219163/10000000000 : ℝ)*X 0 1+(4159783769/10000000000 : ℝ)*X 0 2+(4331635019/10000000000 : ℝ)*X 1 0+(4510219163/10000000000 : ℝ)*X 1 1+(4159783769/10000000000 : ℝ)*X 1 2+(4331635019/10000000000 : ℝ)*X 2 0+(4510219163/10000000000 : ℝ)*X 2 1+(4159783769/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (86652978713736734697406239/22568750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (337002727/12500000000000 : ℝ)*(base19) + (92960673/50000000000000 : ℝ)*(base23) + (191545957/100000000000000 : ℝ)*(lower2) + (7666629/12500000000000 : ℝ)*(upper3) + (79626299/100000000000000 : ℝ)*(lower4) + (218126368041483/5000000000000 : ℝ)*(major0) + (218126368041483/5000000000000 : ℝ)*(major1) + (218126368041483/5000000000000 : ℝ)*(major2) + (368242338416977/6250000000000 : ℝ)*(sp0) + (1472970527631523/25000000000000 : ℝ)*(sp1) + (2945942310313281/50000000000000 : ℝ)*(sp2) + (283314696087917/10000000000000 : ℝ)*(sp3) + (7391876277/100000000000000 : ℝ)*(sp4) + (22826248509/100000000000000 : ℝ)*(sp7) + (4426827792387/156250000000 : ℝ)*(f.failure) + (1472971201636977/25000000000000 : ℝ)*(f.sum) + (1244310721087/144440000000000000000000000 : ℝ)*base65 + (538285853080777087/45137500000000000000000000000000 : ℝ)*base68 + (911659265137514587/45137500000000000000000000000000 : ℝ)*base70 + (491042122500977087/45137500000000000000000000000000 : ℝ)*base72 + (7261877481683/3611000000000000000000000000 : ℝ)*base73 + (92938087518722913/45137500000000000000000000000000 : ℝ)*base75 + (292794962761002087/45137500000000000000000000000000 : ℝ)*base78 + (360935659713622913/45137500000000000000000000000000 : ℝ)*base79 + (11106959634271/3611000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (60027/7812500000000000000 : ℝ)*base89 + (60027/7812500000000000000 : ℝ)*base91 + (60027/7812500000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (326453379909997727478087723/28210937500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1866458257/100000000000000 : ℝ)*(base19) + (51560161/2500000000000 : ℝ)*(base23) + (105951031/50000000000000 : ℝ)*(upper3) + (39389893/50000000000000 : ℝ)*(lower4) + (202754687/100000000000000 : ℝ)*(upper5) + (549246838010731/12500000000000 : ℝ)*(major0) + (549246838010731/12500000000000 : ℝ)*(major1) + (549246838010731/12500000000000 : ℝ)*(major2) + (34724448457/100000000000000 : ℝ)*(sp1) + (8317625309/20000000000000 : ℝ)*(sp2) + (2967178144418477/50000000000000 : ℝ)*(sp4) + (5934319697930241/100000000000000 : ℝ)*(sp5) + (5934312638303969/100000000000000 : ℝ)*(sp6) + (71339818340141/2500000000000 : ℝ)*(sp7) + (71339818340141/2500000000000 : ℝ)*(f.failure) + (2967178144418477/50000000000000 : ℝ)*(f.sum) + (2788665960903/4513750000000000000000000000 : ℝ)*base65 + (414995342599633259/112843750000000000000000000000000 : ℝ)*base68 + (139776046962195759/112843750000000000000000000000000 : ℝ)*base70 + (406323397457758259/112843750000000000000000000000000 : ℝ)*base72 + (86166869900547/18055000000000000000000000000 : ℝ)*base73 + (849706511268820759/112843750000000000000000000000000 : ℝ)*base76 + (539681756964085491/112843750000000000000000000000000 : ℝ)*base77 + (573399170890227009/112843750000000000000000000000000 : ℝ)*base80 + (11584935744347/18055000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1238839/125000000000000000000 : ℝ)*base90 + (1238839/125000000000000000000 : ℝ)*base92 + (1238839/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1323_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76990221/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2941/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5547/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11103/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1837/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1323_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1323_s7_0 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1030250301/5000000000 : ℝ)*x 0 + (270681761/500000000 : ℝ)*x 1 + (5244056923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1030250301/5000000000 : ℝ)^4283 ≤ (1254348772943/10000000000000 : ℝ)^3259 := by
    have hnat : (1030250301 : ℕ)^4283*10000000000000^3259 ≤ 1254348772943^3259*5000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030250301 5000000000 1254348772943 10000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (270681761/500000000 : ℝ)^4283 ≤ (11160648295233/25000000000000 : ℝ)^3259 := by
    have hnat : (270681761 : ℕ)^4283*25000000000000^3259 ≤ 11160648295233^3259*500000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270681761 500000000 11160648295233 25000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244056923/10000000000 : ℝ)^4283 ≤ (8562783814367/20000000000000 : ℝ)^3259 := by
    have hnat : (5244056923 : ℕ)^4283*20000000000000^3259 ≤ 8562783814367^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244056923 10000000000 8562783814367 20000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1030250301/5000000000 : ℝ), (270681761/500000000 : ℝ), (5244056923/10000000000 : ℝ)] ![(1254348772943/10000000000000 : ℝ), (11160648295233/25000000000000 : ℝ), (8562783814367/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1030250301/5000000000 : ℝ)|^4283 ≤ (1254348772943/10000000000000 : ℝ)^3259
        have hw : |(-1030250301/5000000000 : ℝ)|=(1030250301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(270681761/500000000 : ℝ)|^4283 ≤ (11160648295233/25000000000000 : ℝ)^3259
        have hw : |(270681761/500000000 : ℝ)|=(270681761/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244056923/10000000000 : ℝ)|^4283 ≤ (8562783814367/20000000000000 : ℝ)^3259
        have hw : |(5244056923/10000000000 : ℝ)|=(5244056923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_s7_1 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674652421/5000000000 : ℝ)*x 0 + (-1073458383/5000000000 : ℝ)*x 1 + (5244056463/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674652421/5000000000 : ℝ)^4283 ≤ (2746670360631/6250000000000 : ℝ)^3259 := by
    have hnat : (2674652421 : ℕ)^4283*6250000000000^3259 ≤ 2746670360631^3259*5000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674652421 5000000000 2746670360631 6250000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1073458383/5000000000 : ℝ)^4283 ≤ (6619680040509/50000000000000 : ℝ)^3259 := by
    have hnat : (1073458383 : ℕ)^4283*50000000000000^3259 ≤ 6619680040509^3259*5000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073458383 5000000000 6619680040509 50000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244056463/10000000000 : ℝ)^4283 ≤ (8562782827249/20000000000000 : ℝ)^3259 := by
    have hnat : (5244056463 : ℕ)^4283*20000000000000^3259 ≤ 8562782827249^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244056463 10000000000 8562782827249 20000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674652421/5000000000 : ℝ), (-1073458383/5000000000 : ℝ), (5244056463/10000000000 : ℝ)] ![(2746670360631/6250000000000 : ℝ), (6619680040509/50000000000000 : ℝ), (8562782827249/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674652421/5000000000 : ℝ)|^4283 ≤ (2746670360631/6250000000000 : ℝ)^3259
        have hw : |(2674652421/5000000000 : ℝ)|=(2674652421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1073458383/5000000000 : ℝ)|^4283 ≤ (6619680040509/50000000000000 : ℝ)^3259
        have hw : |(-1073458383/5000000000 : ℝ)|=(1073458383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244056463/10000000000 : ℝ)|^4283 ≤ (8562782827249/20000000000000 : ℝ)^3259
        have hw : |(5244056463/10000000000 : ℝ)|=(5244056463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_s7_2 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668663093/1250000000 : ℝ)*x 0 + (5244056753/10000000000 : ℝ)*x 1 + (-67091141/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668663093/1250000000 : ℝ)^4283 ≤ (8789344942403/20000000000000 : ℝ)^3259 := by
    have hnat : (668663093 : ℕ)^4283*20000000000000^3259 ≤ 8789344942403^3259*1250000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668663093 1250000000 8789344942403 20000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244056753/10000000000 : ℝ)^4283 ≤ (42813917247813/100000000000000 : ℝ)^3259 := by
    have hnat : (5244056753 : ℕ)^4283*100000000000000^3259 ≤ 42813917247813^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244056753 10000000000 42813917247813 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (67091141/312500000 : ℝ)^4283 ≤ (6619679011263/50000000000000 : ℝ)^3259 := by
    have hnat : (67091141 : ℕ)^4283*50000000000000^3259 ≤ 6619679011263^3259*312500000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67091141 312500000 6619679011263 50000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668663093/1250000000 : ℝ), (5244056753/10000000000 : ℝ), (-67091141/312500000 : ℝ)] ![(8789344942403/20000000000000 : ℝ), (42813917247813/100000000000000 : ℝ), (6619679011263/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668663093/1250000000 : ℝ)|^4283 ≤ (8789344942403/20000000000000 : ℝ)^3259
        have hw : |(668663093/1250000000 : ℝ)|=(668663093/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244056753/10000000000 : ℝ)|^4283 ≤ (42813917247813/100000000000000 : ℝ)^3259
        have hw : |(5244056753/10000000000 : ℝ)|=(5244056753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-67091141/312500000 : ℝ)|^4283 ≤ (6619679011263/50000000000000 : ℝ)^3259
        have hw : |(-67091141/312500000 : ℝ)|=(67091141/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_s7_3 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4331614533/10000000000 : ℝ)*x 0 + (2079334453/5000000000 : ℝ)*x 1 + (4511326189/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4331614533/10000000000 : ℝ)^4283 ≤ (33302949197507/100000000000000 : ℝ)^3259 := by
    have hnat : (4331614533 : ℕ)^4283*100000000000000^3259 ≤ 33302949197507^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4331614533 10000000000 33302949197507 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2079334453/5000000000 : ℝ)^4283 ≤ (6313311245287/20000000000000 : ℝ)^3259 := by
    have hnat : (2079334453 : ℕ)^4283*20000000000000^3259 ≤ 6313311245287^3259*5000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2079334453 5000000000 6313311245287 20000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4511326189/10000000000 : ℝ)^4283 ≤ (1097827955071/3125000000000 : ℝ)^3259 := by
    have hnat : (4511326189 : ℕ)^4283*3125000000000^3259 ≤ 1097827955071^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4511326189 10000000000 1097827955071 3125000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4331614533/10000000000 : ℝ), (2079334453/5000000000 : ℝ), (4511326189/10000000000 : ℝ)] ![(33302949197507/100000000000000 : ℝ), (6313311245287/20000000000000 : ℝ), (1097827955071/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4331614533/10000000000 : ℝ)|^4283 ≤ (33302949197507/100000000000000 : ℝ)^3259
        have hw : |(4331614533/10000000000 : ℝ)|=(4331614533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2079334453/5000000000 : ℝ)|^4283 ≤ (6313311245287/20000000000000 : ℝ)^3259
        have hw : |(2079334453/5000000000 : ℝ)|=(2079334453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4511326189/10000000000 : ℝ)|^4283 ≤ (1097827955071/3125000000000 : ℝ)^3259
        have hw : |(4511326189/10000000000 : ℝ)|=(4511326189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_s7_4 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-515128363/2500000000 : ℝ)*x 0 + (5244662309/10000000000 : ℝ)*x 1 + (108260527/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (515128363/2500000000 : ℝ)^4283 ≤ (12543590534097/100000000000000 : ℝ)^3259 := by
    have hnat : (515128363 : ℕ)^4283*100000000000000^3259 ≤ 12543590534097^3259*2500000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515128363 2500000000 12543590534097 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244662309/10000000000 : ℝ)^4283 ≤ (10705103676473/25000000000000 : ℝ)^3259 := by
    have hnat : (5244662309 : ℕ)^4283*25000000000000^3259 ≤ 10705103676473^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244662309 10000000000 10705103676473 25000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (108260527/200000000 : ℝ)^4283 ≤ (44635994744441/100000000000000 : ℝ)^3259 := by
    have hnat : (108260527 : ℕ)^4283*100000000000000^3259 ≤ 44635994744441^3259*200000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108260527 200000000 44635994744441 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-515128363/2500000000 : ℝ), (5244662309/10000000000 : ℝ), (108260527/200000000 : ℝ)] ![(12543590534097/100000000000000 : ℝ), (10705103676473/25000000000000 : ℝ), (44635994744441/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-515128363/2500000000 : ℝ)|^4283 ≤ (12543590534097/100000000000000 : ℝ)^3259
        have hw : |(-515128363/2500000000 : ℝ)|=(515128363/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244662309/10000000000 : ℝ)|^4283 ≤ (10705103676473/25000000000000 : ℝ)^3259
        have hw : |(5244662309/10000000000 : ℝ)|=(5244662309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(108260527/200000000 : ℝ)|^4283 ≤ (44635994744441/100000000000000 : ℝ)^3259
        have hw : |(108260527/200000000 : ℝ)|=(108260527/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_s7_5 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1061144541/2000000000 : ℝ)*x 0 + (-1545271/7812500 : ℝ)*x 1 + (5413026059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061144541/2000000000 : ℝ)^4283 ≤ (43476783906191/100000000000000 : ℝ)^3259 := by
    have hnat : (1061144541 : ℕ)^4283*100000000000000^3259 ≤ 43476783906191^3259*2000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061144541 2000000000 43476783906191 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1545271/7812500 : ℝ)^4283 ≤ (11887224496767/100000000000000 : ℝ)^3259 := by
    have hnat : (1545271 : ℕ)^4283*100000000000000^3259 ≤ 11887224496767^3259*7812500^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1545271 7812500 11887224496767 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413026059/10000000000 : ℝ)^4283 ≤ (11158997897719/25000000000000 : ℝ)^3259 := by
    have hnat : (5413026059 : ℕ)^4283*25000000000000^3259 ≤ 11158997897719^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413026059 10000000000 11158997897719 25000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061144541/2000000000 : ℝ), (-1545271/7812500 : ℝ), (5413026059/10000000000 : ℝ)] ![(43476783906191/100000000000000 : ℝ), (11887224496767/100000000000000 : ℝ), (11158997897719/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061144541/2000000000 : ℝ)|^4283 ≤ (43476783906191/100000000000000 : ℝ)^3259
        have hw : |(1061144541/2000000000 : ℝ)|=(1061144541/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1545271/7812500 : ℝ)|^4283 ≤ (11887224496767/100000000000000 : ℝ)^3259
        have hw : |(-1545271/7812500 : ℝ)|=(1545271/7812500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413026059/10000000000 : ℝ)|^4283 ≤ (11158997897719/25000000000000 : ℝ)^3259
        have hw : |(5413026059/10000000000 : ℝ)|=(5413026059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_s7_6 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305722599/10000000000 : ℝ)*x 0 + (5413026167/10000000000 : ℝ)*x 1 + (-632943/3200000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305722599/10000000000 : ℝ)^4283 ≤ (21738391382337/50000000000000 : ℝ)^3259 := by
    have hnat : (5305722599 : ℕ)^4283*50000000000000^3259 ≤ 21738391382337^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305722599 10000000000 21738391382337 50000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5413026167/10000000000 : ℝ)^4283 ≤ (5579499095159/12500000000000 : ℝ)^3259 := by
    have hnat : (5413026167 : ℕ)^4283*12500000000000^3259 ≤ 5579499095159^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413026167 10000000000 5579499095159 12500000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (632943/3200000 : ℝ)^4283 ≤ (2971806114319/25000000000000 : ℝ)^3259 := by
    have hnat : (632943 : ℕ)^4283*25000000000000^3259 ≤ 2971806114319^3259*3200000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      632943 3200000 2971806114319 25000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305722599/10000000000 : ℝ), (5413026167/10000000000 : ℝ), (-632943/3200000 : ℝ)] ![(21738391382337/50000000000000 : ℝ), (5579499095159/12500000000000 : ℝ), (2971806114319/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305722599/10000000000 : ℝ)|^4283 ≤ (21738391382337/50000000000000 : ℝ)^3259
        have hw : |(5305722599/10000000000 : ℝ)|=(5305722599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5413026167/10000000000 : ℝ)|^4283 ≤ (5579499095159/12500000000000 : ℝ)^3259
        have hw : |(5413026167/10000000000 : ℝ)|=(5413026167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-632943/3200000 : ℝ)|^4283 ≤ (2971806114319/25000000000000 : ℝ)^3259
        have hw : |(-632943/3200000 : ℝ)|=(632943/3200000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_s7_7 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2165820143/5000000000 : ℝ)*x 0 + (4510066243/10000000000 : ℝ)*x 1 + (4159935289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2165820143/5000000000 : ℝ)^4283 ≤ (33303209408021/100000000000000 : ℝ)^3259 := by
    have hnat : (2165820143 : ℕ)^4283*100000000000000^3259 ≤ 33303209408021^3259*5000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2165820143 5000000000 33303209408021 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4510066243/10000000000 : ℝ)^4283 ≤ (17558800445061/50000000000000 : ℝ)^3259 := by
    have hnat : (4510066243 : ℕ)^4283*50000000000000^3259 ≤ 17558800445061^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4510066243 10000000000 17558800445061 50000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4159935289/10000000000 : ℝ)^4283 ≤ (31579189689657/100000000000000 : ℝ)^3259 := by
    have hnat : (4159935289 : ℕ)^4283*100000000000000^3259 ≤ 31579189689657^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4159935289 10000000000 31579189689657 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2165820143/5000000000 : ℝ), (4510066243/10000000000 : ℝ), (4159935289/10000000000 : ℝ)] ![(33303209408021/100000000000000 : ℝ), (17558800445061/50000000000000 : ℝ), (31579189689657/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2165820143/5000000000 : ℝ)|^4283 ≤ (33303209408021/100000000000000 : ℝ)^3259
        have hw : |(2165820143/5000000000 : ℝ)|=(2165820143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4510066243/10000000000 : ℝ)|^4283 ≤ (17558800445061/50000000000000 : ℝ)^3259
        have hw : |(4510066243/10000000000 : ℝ)|=(4510066243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4159935289/10000000000 : ℝ)|^4283 ≤ (31579189689657/100000000000000 : ℝ)^3259
        have hw : |(4159935289/10000000000 : ℝ)|=(4159935289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1323_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76990221/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1837/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11103/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (347/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7347/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1837/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11103/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1837/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11103/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1837/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11103/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1837/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11103/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1837/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11103/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1837/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11103/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11103/100000 : ℝ) ^ (2141/512 : ℝ) ≤ (5097351123107167/50000000000000000000 : ℝ) := by
    have hpowers : (11103/100000 : ℝ)^2141 ≤ (5097351123107167/50000000000000000000 : ℝ)^512 := by
      have hnat : (11103 : ℕ)^2141*50000000000000000000^512 ≤ 5097351123107167^512*100000^2141 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11103 100000 5097351123107167 50000000000000000000 2141 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11103/100000 : ℝ)) (X := (5097351123107167/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2141 512 (by norm_num) hpowers
    exact h
  have hpowhi : (1837/12500 : ℝ) ^ (2141/512 : ℝ) ≤ (1317000974784563/4000000000000000000 : ℝ) := by
    have hpowers : (1837/12500 : ℝ)^2141 ≤ (1317000974784563/4000000000000000000 : ℝ)^512 := by
      have hnat : (1837 : ℕ)^2141*4000000000000000000^512 ≤ 1317000974784563^512*12500^2141 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1837 12500 1317000974784563 4000000000000000000 2141 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1837/12500 : ℝ)) (X := (1317000974784563/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2141 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005097351123107167/25000000000000000000 : ℝ) ≤ (2000097511120433/2000000000000000 : ℝ) ^ (2141/512 : ℝ) := by
    have hpowers : (25005097351123107167/25000000000000000000 : ℝ)^512 ≤ (2000097511120433/2000000000000000 : ℝ)^2141 := by
      have hnat : (25005097351123107167 : ℕ)^512*2000000000000000^2141 ≤ 2000097511120433^2141*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005097351123107167 25000000000000000000 2000097511120433 2000000000000000 512 2141 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000097511120433/2000000000000000 : ℝ)) (X := (25005097351123107167/25000000000000000000 : ℝ)) (by norm_num) 2141 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100043119726615828409/100000000000000000000 : ℝ) ≤ (5000515499284863/5000000000000000 : ℝ) ^ (2141/512 : ℝ) := by
    have hpowers : (100043119726615828409/100000000000000000000 : ℝ)^512 ≤ (5000515499284863/5000000000000000 : ℝ)^2141 := by
      have hnat : (100043119726615828409 : ℕ)^512*5000000000000000^2141 ≤ 5000515499284863^2141*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100043119726615828409 100000000000000000000 5000515499284863 5000000000000000 512 2141 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000515499284863/5000000000000000 : ℝ)) (X := (100043119726615828409/100000000000000000000 : ℝ)) (by norm_num) 2141 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (2001317000974784563/2000000000000000000 : ℝ) ≤ (10001574441537287/10000000000000000 : ℝ) ^ (2141/512 : ℝ) := by
    have hpowers : (2001317000974784563/2000000000000000000 : ℝ)^512 ≤ (10001574441537287/10000000000000000 : ℝ)^2141 := by
      have hnat : (2001317000974784563 : ℕ)^512*10000000000000000^2141 ≤ 10001574441537287^2141*2000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2001317000974784563 2000000000000000000 10001574441537287 10000000000000000 512 2141 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001574441537287/10000000000000000 : ℝ)) (X := (2001317000974784563/2000000000000000000 : ℝ)) (by norm_num) 2141 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5097351123107167/50000000000000000000 : ℝ) ≤ ((35919684092740919279/35930000000000000000 : ℝ)+2*(543442967561/359300000000000 : ℝ)*(11103/100000 : ℝ))^(2141/512 : ℝ) := by
    rw [show (35919684092740919279/35930000000000000000 : ℝ)+2*(543442967561/359300000000000 : ℝ)*(11103/100000 : ℝ)=(2000097511120433/2000000000000000 : ℝ) by norm_num, show 1+2*(5097351123107167/50000000000000000000 : ℝ)=(25005097351123107167/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1317000974784563/4000000000000000000 : ℝ)+(5097351123107167/50000000000000000000 : ℝ) ≤ ((35919684092740919279/35930000000000000000 : ℝ)+(543442967561/359300000000000 : ℝ)*((1837/12500 : ℝ)+(11103/100000 : ℝ)))^(2141/512 : ℝ) := by
    rw [show (35919684092740919279/35930000000000000000 : ℝ)+(543442967561/359300000000000 : ℝ)*((1837/12500 : ℝ)+(11103/100000 : ℝ))=(5000515499284863/5000000000000000 : ℝ) by norm_num, show 1+(1317000974784563/4000000000000000000 : ℝ)+(5097351123107167/50000000000000000000 : ℝ)=(100043119726615828409/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1317000974784563/4000000000000000000 : ℝ) ≤ ((35919684092740919279/35930000000000000000 : ℝ)+2*(543442967561/359300000000000 : ℝ)*(1837/12500 : ℝ))^(2141/512 : ℝ) := by
    rw [show (35919684092740919279/35930000000000000000 : ℝ)+2*(543442967561/359300000000000 : ℝ)*(1837/12500 : ℝ)=(10001574441537287/10000000000000000 : ℝ) by norm_num, show 1+2*(1317000974784563/4000000000000000000 : ℝ)=(2001317000974784563/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (35919684092740919279/35930000000000000000 : ℝ)*(X 1 0+X 2 0)+(543442967561/359300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2141/512 : ℝ)) (lo := (11103/100000 : ℝ)) (hi := (1837/12500 : ℝ)) (c := (35919684092740919279/35930000000000000000 : ℝ)) (alpha := (543442967561/359300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (35919684092740919279/35930000000000000000 : ℝ)*(X 0 1+X 2 1)+(543442967561/359300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2141/512 : ℝ)) (lo := (11103/100000 : ℝ)) (hi := (1837/12500 : ℝ)) (c := (35919684092740919279/35930000000000000000 : ℝ)) (alpha := (543442967561/359300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (35919684092740919279/35930000000000000000 : ℝ)*(X 0 2+X 1 2)+(543442967561/359300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2141/512 : ℝ)) (lo := (11103/100000 : ℝ)) (hi := (1837/12500 : ℝ)) (c := (35919684092740919279/35930000000000000000 : ℝ)) (alpha := (543442967561/359300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1030250301/5000000000 : ℝ)*X 0 0+(270681761/500000000 : ℝ)*X 0 1+(5244056923/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674652421/5000000000 : ℝ)*X 1 0+(-1073458383/5000000000 : ℝ)*X 1 1+(5244056463/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668663093/1250000000 : ℝ)*X 2 0+(5244056753/10000000000 : ℝ)*X 2 1+(-67091141/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4331614533/10000000000 : ℝ)*X 0 0+(2079334453/5000000000 : ℝ)*X 0 1+(4511326189/10000000000 : ℝ)*X 0 2+(4331614533/10000000000 : ℝ)*X 1 0+(2079334453/5000000000 : ℝ)*X 1 1+(4511326189/10000000000 : ℝ)*X 1 2+(4331614533/10000000000 : ℝ)*X 2 0+(2079334453/5000000000 : ℝ)*X 2 1+(4511326189/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-515128363/2500000000 : ℝ)*X 0 0+(5244662309/10000000000 : ℝ)*X 0 1+(108260527/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1061144541/2000000000 : ℝ)*X 1 0+(-1545271/7812500 : ℝ)*X 1 1+(5413026059/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305722599/10000000000 : ℝ)*X 2 0+(5413026167/10000000000 : ℝ)*X 2 1+(-632943/3200000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2165820143/5000000000 : ℝ)*X 0 0+(4510066243/10000000000 : ℝ)*X 0 1+(4159935289/10000000000 : ℝ)*X 0 2+(2165820143/5000000000 : ℝ)*X 1 0+(4510066243/10000000000 : ℝ)*X 1 1+(4159935289/10000000000 : ℝ)*X 1 2+(2165820143/5000000000 : ℝ)*X 2 0+(4510066243/10000000000 : ℝ)*X 2 1+(4159935289/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (569387860238360593341987567/56140625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2217390593/100000000000000 : ℝ)*(base19) + (980202547/50000000000000 : ℝ)*(base23) + (15935651/20000000000000 : ℝ)*(lower2) + (44907783/50000000000000 : ℝ)*(upper3) + (53659651/20000000000000 : ℝ)*(upper5) + (68224309507611/1562500000000 : ℝ)*(major0) + (68224309507611/1562500000000 : ℝ)*(major1) + (68224309507611/1562500000000 : ℝ)*(major2) + (5897014128209359/100000000000000 : ℝ)*(sp0) + (1474263238412109/25000000000000 : ℝ)*(sp1) + (1179410642126787/20000000000000 : ℝ)*(sp2) + (1417818136420921/50000000000000 : ℝ)*(sp3) + (41042829669/100000000000000 : ℝ)*(sp4) + (19835020937/100000000000000 : ℝ)*(sp7) + (2835656107862779/100000000000000 : ℝ)*(f.failure) + (5897055171039029/100000000000000 : ℝ)*(f.sum) + (31845223656743/8982500000000000000000000000 : ℝ)*base66 + (174724082034080031/56140625000000000000000000000000 : ℝ)*base68 + (484317295831611281/56140625000000000000000000000000 : ℝ)*base70 + (232976753052017531/56140625000000000000000000000000 : ℝ)*base72 + (59475863792811/17965000000000000000000000000 : ℝ)*base74 + (655340212369500953/28070312500000000000000000000000 : ℝ)*base76 + (765322399569267531/56140625000000000000000000000000 : ℝ)*base78 + (574470222204736281/56140625000000000000000000000000 : ℝ)*base80 + (3658631927729/17965000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (7115841/5000000000000000000000 : ℝ)*base90 + (7115841/5000000000000000000000 : ℝ)*base92 + (7115841/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (692954361788636448023343849/179650000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (263904349/12500000000000 : ℝ)*(base19) + (49742367/2000000000000 : ℝ)*(base23) + (81235511/12500000000000 : ℝ)*(lower1) + (24044431/10000000000000 : ℝ)*(upper2) + (145695219/100000000000000 : ℝ)*(upper3) + (272726581/100000000000000 : ℝ)*(upper5) + (879552247370723/20000000000000 : ℝ)*(major0) + (879552247370723/20000000000000 : ℝ)*(major1) + (879552247370723/20000000000000 : ℝ)*(major2) + (1007175929/20000000000000 : ℝ)*(sp2) + (148486762792737/2500000000000 : ℝ)*(sp4) + (92804193757417/1562500000000 : ℝ)*(sp5) + (1187892597742297/20000000000000 : ℝ)*(sp6) + (1428025916711427/50000000000000 : ℝ)*(sp7) + (1428025916711427/50000000000000 : ℝ)*(f.failure) + (148486762792737/2500000000000 : ℝ)*(f.sum) + (2414198493191/3593000000000000000000000000 : ℝ)*base65 + (583669336729968717/718600000000000000000000000000000 : ℝ)*base67 + (347051297000431283/718600000000000000000000000000000 : ℝ)*base70 + (1015130831108768717/718600000000000000000000000000000 : ℝ)*base71 + (21392522229977/3593000000000000000000000000 : ℝ)*base73 + (10195459891988368717/718600000000000000000000000000000 : ℝ)*base75 + (2331969387605768717/718600000000000000000000000000000 : ℝ)*base77 + (7294005461433968717/718600000000000000000000000000000 : ℝ)*base79 + (644826959467/179650000000000000000000000 : ℝ)*base81 + (17044633/2500000000000000000000 : ℝ)*base90 + (17044633/2500000000000000000000 : ℝ)*base92 + (17044633/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1323_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76990221/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1837/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11103/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (347/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7347/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1323_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1323_s8_0 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2060504823/10000000000 : ℝ)*x 0 + (5413621263/10000000000 : ℝ)*x 1 + (5244067873/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2060504823/10000000000 : ℝ)^4283 ≤ (12543521498941/100000000000000 : ℝ)^3259 := by
    have hnat : (2060504823 : ℕ)^4283*100000000000000^3259 ≤ 12543521498941^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2060504823 10000000000 12543521498941 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5413621263/10000000000 : ℝ)^4283 ≤ (44642441923737/100000000000000 : ℝ)^3259 := by
    have hnat : (5413621263 : ℕ)^4283*100000000000000^3259 ≤ 44642441923737^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413621263 10000000000 44642441923737 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244067873/10000000000 : ℝ)^4283 ≤ (4281403656039/10000000000000 : ℝ)^3259 := by
    have hnat : (5244067873 : ℕ)^4283*10000000000000^3259 ≤ 4281403656039^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244067873 10000000000 4281403656039 10000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2060504823/10000000000 : ℝ), (5413621263/10000000000 : ℝ), (5244067873/10000000000 : ℝ)] ![(12543521498941/100000000000000 : ℝ), (44642441923737/100000000000000 : ℝ), (4281403656039/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2060504823/10000000000 : ℝ)|^4283 ≤ (12543521498941/100000000000000 : ℝ)^3259
        have hw : |(-2060504823/10000000000 : ℝ)|=(2060504823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5413621263/10000000000 : ℝ)|^4283 ≤ (44642441923737/100000000000000 : ℝ)^3259
        have hw : |(5413621263/10000000000 : ℝ)|=(5413621263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244067873/10000000000 : ℝ)|^4283 ≤ (4281403656039/10000000000000 : ℝ)^3259
        have hw : |(5244067873/10000000000 : ℝ)|=(5244067873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_s8_1 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349300607/10000000000 : ℝ)*x 0 + (-536726881/2500000000 : ℝ)*x 1 + (1048813541/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349300607/10000000000 : ℝ)^4283 ≤ (21973340022941/50000000000000 : ℝ)^3259 := by
    have hnat : (5349300607 : ℕ)^4283*50000000000000^3259 ≤ 21973340022941^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349300607 10000000000 21973340022941 50000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (536726881/2500000000 : ℝ)^4283 ≤ (1323928518113/10000000000000 : ℝ)^3259 := by
    have hnat : (536726881 : ℕ)^4283*10000000000000^3259 ≤ 1323928518113^3259*2500000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536726881 2500000000 1323928518113 10000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048813541/2000000000 : ℝ)^4283 ≤ (1712561390313/4000000000000 : ℝ)^3259 := by
    have hnat : (1048813541 : ℕ)^4283*4000000000000^3259 ≤ 1712561390313^3259*2000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048813541 2000000000 1712561390313 4000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349300607/10000000000 : ℝ), (-536726881/2500000000 : ℝ), (1048813541/2000000000 : ℝ)] ![(21973340022941/50000000000000 : ℝ), (1323928518113/10000000000000 : ℝ), (1712561390313/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349300607/10000000000 : ℝ)|^4283 ≤ (21973340022941/50000000000000 : ℝ)^3259
        have hw : |(5349300607/10000000000 : ℝ)|=(5349300607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-536726881/2500000000 : ℝ)|^4283 ≤ (1323928518113/10000000000000 : ℝ)^3259
        have hw : |(-536726881/2500000000 : ℝ)|=(536726881/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048813541/2000000000 : ℝ)|^4283 ≤ (1712561390313/4000000000000 : ℝ)^3259
        have hw : |(1048813541/2000000000 : ℝ)|=(1048813541/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_s8_2 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349300227/10000000000 : ℝ)*x 0 + (2622034141/5000000000 : ℝ)*x 1 + (-2146907267/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349300227/10000000000 : ℝ)^4283 ≤ (549333449289/1250000000000 : ℝ)^3259 := by
    have hnat : (5349300227 : ℕ)^4283*1250000000000^3259 ≤ 549333449289^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349300227 10000000000 549333449289 1250000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622034141/5000000000 : ℝ)^4283 ≤ (42814040948777/100000000000000 : ℝ)^3259 := by
    have hnat : (2622034141 : ℕ)^4283*100000000000000^3259 ≤ 42814040948777^3259*5000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622034141 5000000000 42814040948777 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2146907267/10000000000 : ℝ)^4283 ≤ (13239283098327/100000000000000 : ℝ)^3259 := by
    have hnat : (2146907267 : ℕ)^4283*100000000000000^3259 ≤ 13239283098327^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2146907267 10000000000 13239283098327 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349300227/10000000000 : ℝ), (2622034141/5000000000 : ℝ), (-2146907267/10000000000 : ℝ)] ![(549333449289/1250000000000 : ℝ), (42814040948777/100000000000000 : ℝ), (13239283098327/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349300227/10000000000 : ℝ)|^4283 ≤ (549333449289/1250000000000 : ℝ)^3259
        have hw : |(5349300227/10000000000 : ℝ)|=(5349300227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622034141/5000000000 : ℝ)|^4283 ≤ (42814040948777/100000000000000 : ℝ)^3259
        have hw : |(2622034141/5000000000 : ℝ)|=(2622034141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2146907267/10000000000 : ℝ)|^4283 ≤ (13239283098327/100000000000000 : ℝ)^3259
        have hw : |(-2146907267/10000000000 : ℝ)|=(2146907267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_s8_3 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2165807503/5000000000 : ℝ)*x 0 + (4158695629/10000000000 : ℝ)*x 1 + (2255649837/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2165807503/5000000000 : ℝ)^4283 ≤ (6660590795347/20000000000000 : ℝ)^3259 := by
    have hnat : (2165807503 : ℕ)^4283*20000000000000^3259 ≤ 6660590795347^3259*5000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2165807503 5000000000 6660590795347 20000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4158695629/10000000000 : ℝ)^4283 ≤ (31566822803157/100000000000000 : ℝ)^3259 := by
    have hnat : (4158695629 : ℕ)^4283*100000000000000^3259 ≤ 31566822803157^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4158695629 10000000000 31566822803157 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2255649837/5000000000 : ℝ)^4283 ≤ (35130223209053/100000000000000 : ℝ)^3259 := by
    have hnat : (2255649837 : ℕ)^4283*100000000000000^3259 ≤ 35130223209053^3259*5000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2255649837 5000000000 35130223209053 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2165807503/5000000000 : ℝ), (4158695629/10000000000 : ℝ), (2255649837/5000000000 : ℝ)] ![(6660590795347/20000000000000 : ℝ), (31566822803157/100000000000000 : ℝ), (35130223209053/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2165807503/5000000000 : ℝ)|^4283 ≤ (6660590795347/20000000000000 : ℝ)^3259
        have hw : |(2165807503/5000000000 : ℝ)|=(2165807503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4158695629/10000000000 : ℝ)|^4283 ≤ (31566822803157/100000000000000 : ℝ)^3259
        have hw : |(4158695629/10000000000 : ℝ)|=(4158695629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2255649837/5000000000 : ℝ)|^4283 ≤ (35130223209053/100000000000000 : ℝ)^3259
        have hw : |(2255649837/5000000000 : ℝ)|=(2255649837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_s8_4 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2060517357/10000000000 : ℝ)*x 0 + (5244673799/10000000000 : ℝ)*x 1 + (541301209/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2060517357/10000000000 : ℝ)^4283 ≤ (2508724355111/20000000000000 : ℝ)^3259 := by
    have hnat : (2060517357 : ℕ)^4283*20000000000000^3259 ≤ 2508724355111^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2060517357 10000000000 2508724355111 20000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244673799/10000000000 : ℝ)^4283 ≤ (10705134498219/25000000000000 : ℝ)^3259 := by
    have hnat : (5244673799 : ℕ)^4283*25000000000000^3259 ≤ 10705134498219^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244673799 10000000000 10705134498219 25000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (541301209/1000000000 : ℝ)^4283 ≤ (22317920104493/50000000000000 : ℝ)^3259 := by
    have hnat : (541301209 : ℕ)^4283*50000000000000^3259 ≤ 22317920104493^3259*1000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541301209 1000000000 22317920104493 50000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2060517357/10000000000 : ℝ), (5244673799/10000000000 : ℝ), (541301209/1000000000 : ℝ)] ![(2508724355111/20000000000000 : ℝ), (10705134498219/25000000000000 : ℝ), (22317920104493/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2060517357/10000000000 : ℝ)|^4283 ≤ (2508724355111/20000000000000 : ℝ)^3259
        have hw : |(-2060517357/10000000000 : ℝ)|=(2060517357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244673799/10000000000 : ℝ)|^4283 ≤ (10705134498219/25000000000000 : ℝ)^3259
        have hw : |(5244673799/10000000000 : ℝ)|=(5244673799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(541301209/1000000000 : ℝ)|^4283 ≤ (22317920104493/50000000000000 : ℝ)^3259
        have hw : |(541301209/1000000000 : ℝ)|=(541301209/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_s8_5 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1082910301/2500000000 : ℝ)*x 0 + (56375503/125000000 : ℝ)*x 1 + (4159961031/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1082910301/2500000000 : ℝ)^4283 ≤ (1665160934179/5000000000000 : ℝ)^3259 := by
    have hnat : (1082910301 : ℕ)^4283*5000000000000^3259 ≤ 1665160934179^3259*2500000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082910301 2500000000 1665160934179 5000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (56375503/125000000 : ℝ)^4283 ≤ (7023466960007/20000000000000 : ℝ)^3259 := by
    have hnat : (56375503 : ℕ)^4283*20000000000000^3259 ≤ 7023466960007^3259*125000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56375503 125000000 7023466960007 20000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4159961031/10000000000 : ℝ)^4283 ≤ (31579446504919/100000000000000 : ℝ)^3259 := by
    have hnat : (4159961031 : ℕ)^4283*100000000000000^3259 ≤ 31579446504919^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4159961031 10000000000 31579446504919 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1082910301/2500000000 : ℝ), (56375503/125000000 : ℝ), (4159961031/10000000000 : ℝ)] ![(1665160934179/5000000000000 : ℝ), (7023466960007/20000000000000 : ℝ), (31579446504919/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1082910301/2500000000 : ℝ)|^4283 ≤ (1665160934179/5000000000000 : ℝ)^3259
        have hw : |(1082910301/2500000000 : ℝ)|=(1082910301/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(56375503/125000000 : ℝ)|^4283 ≤ (7023466960007/20000000000000 : ℝ)^3259
        have hw : |(56375503/125000000 : ℝ)|=(56375503/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4159961031/10000000000 : ℝ)|^4283 ≤ (31579446504919/100000000000000 : ℝ)^3259
        have hw : |(4159961031/10000000000 : ℝ)|=(4159961031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1323_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76990221/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7347/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (347/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (2221/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7347/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7347/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (347/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7347/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (347/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7347/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (347/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7347/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (347/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7347/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (347/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7347/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (347/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (347/3125 : ℝ) ^ (2141/512 : ℝ) ≤ (407941694061903/4000000000000000000 : ℝ) := by
    have hpowers : (347/3125 : ℝ)^2141 ≤ (407941694061903/4000000000000000000 : ℝ)^512 := by
      have hnat : (347 : ℕ)^2141*4000000000000000000^512 ≤ 407941694061903^512*3125^2141 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        347 3125 407941694061903 4000000000000000000 2141 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (347/3125 : ℝ)) (X := (407941694061903/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2141 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7347/50000 : ℝ) ^ (2141/512 : ℝ) ≤ (16453145635066619/50000000000000000000 : ℝ) := by
    have hpowers : (7347/50000 : ℝ)^2141 ≤ (16453145635066619/50000000000000000000 : ℝ)^512 := by
      have hnat : (7347 : ℕ)^2141*50000000000000000000^512 ≤ 16453145635066619^512*50000^2141 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7347 50000 16453145635066619 50000000000000000000 2141 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7347/50000 : ℝ)) (X := (16453145635066619/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2141 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000407941694061903/2000000000000000000 : ℝ) ≤ (5000243869619341/5000000000000000 : ℝ) ^ (2141/512 : ℝ) := by
    have hpowers : (2000407941694061903/2000000000000000000 : ℝ)^512 ≤ (5000243869619341/5000000000000000 : ℝ)^2141 := by
      have hnat : (2000407941694061903 : ℕ)^512*5000000000000000^2141 ≤ 5000243869619341^2141*2000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000407941694061903 2000000000000000000 5000243869619341 5000000000000000 512 2141 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000243869619341/5000000000000000 : ℝ)) (X := (2000407941694061903/2000000000000000000 : ℝ)) (by norm_num) 2141 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100043104833621680813/100000000000000000000 : ℝ) ≤ (1000103064253457/1000000000000000 : ℝ) ^ (2141/512 : ℝ) := by
    have hpowers : (100043104833621680813/100000000000000000000 : ℝ)^512 ≤ (1000103064253457/1000000000000000 : ℝ)^2141 := by
      have hnat : (100043104833621680813 : ℕ)^512*1000000000000000^2141 ≤ 1000103064253457^2141*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100043104833621680813 100000000000000000000 1000103064253457 1000000000000000 512 2141 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000103064253457/1000000000000000 : ℝ)) (X := (100043104833621680813/100000000000000000000 : ℝ)) (by norm_num) 2141 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016453145635066619/25000000000000000000 : ℝ) ≤ (5000786772915229/5000000000000000 : ℝ) ^ (2141/512 : ℝ) := by
    have hpowers : (25016453145635066619/25000000000000000000 : ℝ)^512 ≤ (5000786772915229/5000000000000000 : ℝ)^2141 := by
      have hnat : (25016453145635066619 : ℕ)^512*5000000000000000^2141 ≤ 5000786772915229^2141*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016453145635066619 25000000000000000000 5000786772915229 5000000000000000 512 2141 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000786772915229/5000000000000000 : ℝ)) (X := (25016453145635066619/25000000000000000000 : ℝ)) (by norm_num) 2141 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(407941694061903/4000000000000000000 : ℝ) ≤ ((8972423546867946919/8975000000000000000 : ℝ)+2*(33931455993/22437500000000 : ℝ)*(347/3125 : ℝ))^(2141/512 : ℝ) := by
    rw [show (8972423546867946919/8975000000000000000 : ℝ)+2*(33931455993/22437500000000 : ℝ)*(347/3125 : ℝ)=(5000243869619341/5000000000000000 : ℝ) by norm_num, show 1+2*(407941694061903/4000000000000000000 : ℝ)=(2000407941694061903/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16453145635066619/50000000000000000000 : ℝ)+(407941694061903/4000000000000000000 : ℝ) ≤ ((8972423546867946919/8975000000000000000 : ℝ)+(33931455993/22437500000000 : ℝ)*((7347/50000 : ℝ)+(347/3125 : ℝ)))^(2141/512 : ℝ) := by
    rw [show (8972423546867946919/8975000000000000000 : ℝ)+(33931455993/22437500000000 : ℝ)*((7347/50000 : ℝ)+(347/3125 : ℝ))=(1000103064253457/1000000000000000 : ℝ) by norm_num, show 1+(16453145635066619/50000000000000000000 : ℝ)+(407941694061903/4000000000000000000 : ℝ)=(100043104833621680813/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16453145635066619/50000000000000000000 : ℝ) ≤ ((8972423546867946919/8975000000000000000 : ℝ)+2*(33931455993/22437500000000 : ℝ)*(7347/50000 : ℝ))^(2141/512 : ℝ) := by
    rw [show (8972423546867946919/8975000000000000000 : ℝ)+2*(33931455993/22437500000000 : ℝ)*(7347/50000 : ℝ)=(5000786772915229/5000000000000000 : ℝ) by norm_num, show 1+2*(16453145635066619/50000000000000000000 : ℝ)=(25016453145635066619/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8972423546867946919/8975000000000000000 : ℝ)*(X 1 0+X 2 0)+(33931455993/22437500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2141/512 : ℝ)) (lo := (347/3125 : ℝ)) (hi := (7347/50000 : ℝ)) (c := (8972423546867946919/8975000000000000000 : ℝ)) (alpha := (33931455993/22437500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8972423546867946919/8975000000000000000 : ℝ)*(X 0 1+X 2 1)+(33931455993/22437500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2141/512 : ℝ)) (lo := (347/3125 : ℝ)) (hi := (7347/50000 : ℝ)) (c := (8972423546867946919/8975000000000000000 : ℝ)) (alpha := (33931455993/22437500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8972423546867946919/8975000000000000000 : ℝ)*(X 0 2+X 1 2)+(33931455993/22437500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2141/512 : ℝ)) (lo := (347/3125 : ℝ)) (hi := (7347/50000 : ℝ)) (c := (8972423546867946919/8975000000000000000 : ℝ)) (alpha := (33931455993/22437500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2060504823/10000000000 : ℝ)*X 0 0+(5413621263/10000000000 : ℝ)*X 0 1+(5244067873/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349300607/10000000000 : ℝ)*X 1 0+(-536726881/2500000000 : ℝ)*X 1 1+(1048813541/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349300227/10000000000 : ℝ)*X 2 0+(2622034141/5000000000 : ℝ)*X 2 1+(-2146907267/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2165807503/5000000000 : ℝ)*X 0 0+(4158695629/10000000000 : ℝ)*X 0 1+(2255649837/5000000000 : ℝ)*X 0 2+(2165807503/5000000000 : ℝ)*X 1 0+(4158695629/10000000000 : ℝ)*X 1 1+(2255649837/5000000000 : ℝ)*X 1 2+(2165807503/5000000000 : ℝ)*X 2 0+(4158695629/10000000000 : ℝ)*X 2 1+(2255649837/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2060517357/10000000000 : ℝ)*X 0 0+(5244673799/10000000000 : ℝ)*X 0 1+(541301209/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1082910301/2500000000 : ℝ)*X 0 0+(56375503/125000000 : ℝ)*X 0 1+(4159961031/10000000000 : ℝ)*X 0 2+(1082910301/2500000000 : ℝ)*X 1 0+(56375503/125000000 : ℝ)*X 1 1+(4159961031/10000000000 : ℝ)*X 1 2+(1082910301/2500000000 : ℝ)*X 2 0+(56375503/125000000 : ℝ)*X 2 1+(4159961031/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_s8_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1286026417169724957085302429/448750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (587549759/50000000000000 : ℝ)*(base19) + (12647361/4000000000000 : ℝ)*(base23) + (82896969/100000000000000 : ℝ)*(upper3) + (235339821/100000000000000 : ℝ)*(upper4) + (5023687/100000000000000 : ℝ)*(upper5) + (4366975470185699/100000000000000 : ℝ)*(major0) + (4366975470185699/100000000000000 : ℝ)*(major1) + (4366975470185699/100000000000000 : ℝ)*(major2) + (589786999972961/10000000000000 : ℝ)*(sp0) + (5897891133047703/100000000000000 : ℝ)*(sp1) + (1474472997990799/25000000000000 : ℝ)*(sp2) + (1418024883460413/50000000000000 : ℝ)*(sp3) + (22308417611/100000000000000 : ℝ)*(sp4) + (1096222097/12500000000000 : ℝ)*(sp5) + (2836058536697601/100000000000000 : ℝ)*(f.failure) + (5897892308147221/100000000000000 : ℝ)*(f.sum) + (12355373378431/8975000000000000000000000000 : ℝ)*base65 + (300727417719788619/897500000000000000000000000000000 : ℝ)*base68 + (2345462076302288619/897500000000000000000000000000000 : ℝ)*base70 + (1040753474999788619/897500000000000000000000000000000 : ℝ)*base72 + (13938018142297/4487500000000000000000000000 : ℝ)*base74 + (5869940174064788619/897500000000000000000000000000000 : ℝ)*base76 + (2046482794472288619/897500000000000000000000000000000 : ℝ)*base78 + (11561101361287288619/897500000000000000000000000000000 : ℝ)*base80 + (593517881921/140234375000000000000000000 : ℝ)*base82 + (38840179/5000000000000000000000 : ℝ)*base90 + (38840179/5000000000000000000000 : ℝ)*base92 + (38840179/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1323_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76990221/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7347/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (347/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2221/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7347/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1323_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1323_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76990221/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2941/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5547/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2221/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7347/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1323_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1323_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1323_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76990221/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2941/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5547/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2221/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7347/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1323_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
