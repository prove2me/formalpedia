-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1322_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:43:40.491912+00:00
-- url     : https://prove2.me/submissions/dfad7024-8158-4225-b1d7-acedb1a15a10

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
theorem support_rectangle_w1322_s3_0 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2059396831/10000000000 : ℝ)*x 0 + (1085961851/2000000000 : ℝ)*x 1 + (2614600793/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2059396831/10000000000 : ℝ)^2141 ≤ (1566593480869/12500000000000 : ℝ)^1629 := by
    have hnat : (2059396831 : ℕ)^2141*12500000000000^1629 ≤ 1566593480869^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2059396831 10000000000 1566593480869 12500000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1085961851/2000000000 : ℝ)^2141 ≤ (44815320016139/100000000000000 : ℝ)^1629 := by
    have hnat : (1085961851 : ℕ)^2141*100000000000000^1629 ≤ 44815320016139^1629*2000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085961851 2000000000 44815320016139 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2614600793/5000000000 : ℝ)^2141 ≤ (1066298303123/2500000000000 : ℝ)^1629 := by
    have hnat : (2614600793 : ℕ)^2141*2500000000000^1629 ≤ 1066298303123^1629*5000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614600793 5000000000 1066298303123 2500000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2059396831/10000000000 : ℝ), (1085961851/2000000000 : ℝ), (2614600793/5000000000 : ℝ)] ![(1566593480869/12500000000000 : ℝ), (44815320016139/100000000000000 : ℝ), (1066298303123/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2059396831/10000000000 : ℝ)|^2141 ≤ (1566593480869/12500000000000 : ℝ)^1629
        have hw : |(-2059396831/10000000000 : ℝ)|=(2059396831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1085961851/2000000000 : ℝ)|^2141 ≤ (44815320016139/100000000000000 : ℝ)^1629
        have hw : |(1085961851/2000000000 : ℝ)|=(1085961851/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2614600793/5000000000 : ℝ)|^2141 ≤ (1066298303123/2500000000000 : ℝ)^1629
        have hw : |(2614600793/5000000000 : ℝ)|=(2614600793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_s3_1 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5353419029/10000000000 : ℝ)*x 0 + (-2161976399/10000000000 : ℝ)*x 1 + (10458403/20000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353419029/10000000000 : ℝ)^2141 ≤ (43988500075351/100000000000000 : ℝ)^1629 := by
    have hnat : (5353419029 : ℕ)^2141*100000000000000^1629 ≤ 43988500075351^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353419029 10000000000 43988500075351 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2161976399/10000000000 : ℝ)^2141 ≤ (2671913741201/20000000000000 : ℝ)^1629 := by
    have hnat : (2161976399 : ℕ)^2141*20000000000000^1629 ≤ 2671913741201^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2161976399 10000000000 2671913741201 20000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (10458403/20000000 : ℝ)^2141 ≤ (42651931202991/100000000000000 : ℝ)^1629 := by
    have hnat : (10458403 : ℕ)^2141*100000000000000^1629 ≤ 42651931202991^1629*20000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10458403 20000000 42651931202991 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353419029/10000000000 : ℝ), (-2161976399/10000000000 : ℝ), (10458403/20000000 : ℝ)] ![(43988500075351/100000000000000 : ℝ), (2671913741201/20000000000000 : ℝ), (42651931202991/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353419029/10000000000 : ℝ)|^2141 ≤ (43988500075351/100000000000000 : ℝ)^1629
        have hw : |(5353419029/10000000000 : ℝ)|=(5353419029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2161976399/10000000000 : ℝ)|^2141 ≤ (2671913741201/20000000000000 : ℝ)^1629
        have hw : |(-2161976399/10000000000 : ℝ)|=(2161976399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(10458403/20000000 : ℝ)|^2141 ≤ (42651931202991/100000000000000 : ℝ)^1629
        have hw : |(10458403/20000000 : ℝ)|=(10458403/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_s3_2 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (3345887/6250000 : ℝ)*x 0 + (2614600453/5000000000 : ℝ)*x 1 + (-540494239/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3345887/6250000 : ℝ)^2141 ≤ (8797700384413/20000000000000 : ℝ)^1629 := by
    have hnat : (3345887 : ℕ)^2141*20000000000000^1629 ≤ 8797700384413^1629*6250000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3345887 6250000 8797700384413 20000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2614600453/5000000000 : ℝ)^2141 ≤ (42651924835251/100000000000000 : ℝ)^1629 := by
    have hnat : (2614600453 : ℕ)^2141*100000000000000^1629 ≤ 42651924835251^1629*5000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614600453 5000000000 42651924835251 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (540494239/2500000000 : ℝ)^2141 ≤ (13359573229689/100000000000000 : ℝ)^1629 := by
    have hnat : (540494239 : ℕ)^2141*100000000000000^1629 ≤ 13359573229689^1629*2500000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540494239 2500000000 13359573229689 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3345887/6250000 : ℝ), (2614600453/5000000000 : ℝ), (-540494239/2500000000 : ℝ)] ![(8797700384413/20000000000000 : ℝ), (42651924835251/100000000000000 : ℝ), (13359573229689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3345887/6250000 : ℝ)|^2141 ≤ (8797700384413/20000000000000 : ℝ)^1629
        have hw : |(3345887/6250000 : ℝ)|=(3345887/6250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2614600453/5000000000 : ℝ)|^2141 ≤ (42651924835251/100000000000000 : ℝ)^1629
        have hw : |(2614600453/5000000000 : ℝ)|=(2614600453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-540494239/2500000000 : ℝ)|^2141 ≤ (13359573229689/100000000000000 : ℝ)^1629
        have hw : |(-540494239/2500000000 : ℝ)|=(540494239/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_s3_3 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4330682503/10000000000 : ℝ)*x 0 + (1031724681/2500000000 : ℝ)*x 1 + (4543926923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4330682503/10000000000 : ℝ)^2141 ≤ (8322711315873/25000000000000 : ℝ)^1629 := by
    have hnat : (4330682503 : ℕ)^2141*25000000000000^1629 ≤ 8322711315873^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4330682503 10000000000 8322711315873 25000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1031724681/2500000000 : ℝ)^2141 ≤ (3905918143483/12500000000000 : ℝ)^1629 := by
    have hnat : (1031724681 : ℕ)^2141*12500000000000^1629 ≤ 3905918143483^1629*2500000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031724681 2500000000 3905918143483 12500000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4543926923/10000000000 : ℝ)^2141 ≤ (1108181549161/3125000000000 : ℝ)^1629 := by
    have hnat : (4543926923 : ℕ)^2141*3125000000000^1629 ≤ 1108181549161^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4543926923 10000000000 1108181549161 3125000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4330682503/10000000000 : ℝ), (1031724681/2500000000 : ℝ), (4543926923/10000000000 : ℝ)] ![(8322711315873/25000000000000 : ℝ), (3905918143483/12500000000000 : ℝ), (1108181549161/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4330682503/10000000000 : ℝ)|^2141 ≤ (8322711315873/25000000000000 : ℝ)^1629
        have hw : |(4330682503/10000000000 : ℝ)|=(4330682503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1031724681/2500000000 : ℝ)|^2141 ≤ (3905918143483/12500000000000 : ℝ)^1629
        have hw : |(1031724681/2500000000 : ℝ)|=(1031724681/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4543926923/10000000000 : ℝ)|^2141 ≤ (1108181549161/3125000000000 : ℝ)^1629
        have hw : |(4543926923/10000000000 : ℝ)|=(4543926923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_s3_4 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1029708717/5000000000 : ℝ)*x 0 + (5230047721/10000000000 : ℝ)*x 1 + (5428957839/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1029708717/5000000000 : ℝ)^2141 ≤ (12532912637763/100000000000000 : ℝ)^1629 := by
    have hnat : (1029708717 : ℕ)^2141*100000000000000^1629 ≤ 12532912637763^1629*5000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1029708717 5000000000 12532912637763 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5230047721/10000000000 : ℝ)^2141 ≤ (21330501504437/50000000000000 : ℝ)^1629 := by
    have hnat : (5230047721 : ℕ)^2141*50000000000000^1629 ≤ 21330501504437^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230047721 10000000000 21330501504437 50000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5428957839/10000000000 : ℝ)^2141 ≤ (560076054271/1250000000000 : ℝ)^1629 := by
    have hnat : (5428957839 : ℕ)^2141*1250000000000^1629 ≤ 560076054271^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428957839 10000000000 560076054271 1250000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1029708717/5000000000 : ℝ), (5230047721/10000000000 : ℝ), (5428957839/10000000000 : ℝ)] ![(12532912637763/100000000000000 : ℝ), (21330501504437/50000000000000 : ℝ), (560076054271/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1029708717/5000000000 : ℝ)|^2141 ≤ (12532912637763/100000000000000 : ℝ)^1629
        have hw : |(-1029708717/5000000000 : ℝ)|=(1029708717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5230047721/10000000000 : ℝ)|^2141 ≤ (21330501504437/50000000000000 : ℝ)^1629
        have hw : |(5230047721/10000000000 : ℝ)|=(5230047721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5428957839/10000000000 : ℝ)|^2141 ≤ (560076054271/1250000000000 : ℝ)^1629
        have hw : |(5428957839/10000000000 : ℝ)|=(5428957839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_s3_5 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2650932751/5000000000 : ℝ)*x 0 + (-49055509/250000000 : ℝ)*x 1 + (5428958047/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2650932751/5000000000 : ℝ)^2141 ≤ (4343259238933/10000000000000 : ℝ)^1629 := by
    have hnat : (2650932751 : ℕ)^2141*10000000000000^1629 ≤ 4343259238933^1629*5000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2650932751 5000000000 4343259238933 10000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (49055509/250000000 : ℝ)^2141 ≤ (11761320995033/100000000000000 : ℝ)^1629 := by
    have hnat : (49055509 : ℕ)^2141*100000000000000^1629 ≤ 11761320995033^1629*250000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49055509 250000000 11761320995033 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5428958047/10000000000 : ℝ)^2141 ≤ (44806086597889/100000000000000 : ℝ)^1629 := by
    have hnat : (5428958047 : ℕ)^2141*100000000000000^1629 ≤ 44806086597889^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428958047 10000000000 44806086597889 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2650932751/5000000000 : ℝ), (-49055509/250000000 : ℝ), (5428958047/10000000000 : ℝ)] ![(4343259238933/10000000000000 : ℝ), (11761320995033/100000000000000 : ℝ), (44806086597889/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2650932751/5000000000 : ℝ)|^2141 ≤ (4343259238933/10000000000000 : ℝ)^1629
        have hw : |(2650932751/5000000000 : ℝ)|=(2650932751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-49055509/250000000 : ℝ)|^2141 ≤ (11761320995033/100000000000000 : ℝ)^1629
        have hw : |(-49055509/250000000 : ℝ)|=(49055509/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5428958047/10000000000 : ℝ)|^2141 ≤ (44806086597889/100000000000000 : ℝ)^1629
        have hw : |(5428958047/10000000000 : ℝ)|=(5428958047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_s3_6 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5301867237/10000000000 : ℝ)*x 0 + (5428956829/10000000000 : ℝ)*x 1 + (-392443933/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5301867237/10000000000 : ℝ)^2141 ≤ (10858152767389/25000000000000 : ℝ)^1629 := by
    have hnat : (5301867237 : ℕ)^2141*25000000000000^1629 ≤ 10858152767389^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5301867237 10000000000 10858152767389 25000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5428956829/10000000000 : ℝ)^2141 ≤ (44806073386047/100000000000000 : ℝ)^1629 := by
    have hnat : (5428956829 : ℕ)^2141*100000000000000^1629 ≤ 44806073386047^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428956829 10000000000 44806073386047 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (392443933/2000000000 : ℝ)^2141 ≤ (470452620799/4000000000000 : ℝ)^1629 := by
    have hnat : (392443933 : ℕ)^2141*4000000000000^1629 ≤ 470452620799^1629*2000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      392443933 2000000000 470452620799 4000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5301867237/10000000000 : ℝ), (5428956829/10000000000 : ℝ), (-392443933/2000000000 : ℝ)] ![(10858152767389/25000000000000 : ℝ), (44806073386047/100000000000000 : ℝ), (470452620799/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5301867237/10000000000 : ℝ)|^2141 ≤ (10858152767389/25000000000000 : ℝ)^1629
        have hw : |(5301867237/10000000000 : ℝ)|=(5301867237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5428956829/10000000000 : ℝ)|^2141 ≤ (44806073386047/100000000000000 : ℝ)^1629
        have hw : |(5428956829/10000000000 : ℝ)|=(5428956829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-392443933/2000000000 : ℝ)|^2141 ≤ (470452620799/4000000000000 : ℝ)^1629
        have hw : |(-392443933/2000000000 : ℝ)|=(392443933/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_s3_7 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4330725291/10000000000 : ℝ)*x 0 + (4542167763/10000000000 : ℝ)*x 1 + (1032167063/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4330725291/10000000000 : ℝ)^2141 ≤ (33291277564971/100000000000000 : ℝ)^1629 := by
    have hnat : (4330725291 : ℕ)^2141*100000000000000^1629 ≤ 33291277564971^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4330725291 10000000000 33291277564971 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4542167763/10000000000 : ℝ)^2141 ≤ (35443766768227/100000000000000 : ℝ)^1629 := by
    have hnat : (4542167763 : ℕ)^2141*100000000000000^1629 ≤ 35443766768227^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4542167763 10000000000 35443766768227 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1032167063/2500000000 : ℝ)^2141 ≤ (15632477822087/50000000000000 : ℝ)^1629 := by
    have hnat : (1032167063 : ℕ)^2141*50000000000000^1629 ≤ 15632477822087^1629*2500000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1032167063 2500000000 15632477822087 50000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4330725291/10000000000 : ℝ), (4542167763/10000000000 : ℝ), (1032167063/2500000000 : ℝ)] ![(33291277564971/100000000000000 : ℝ), (35443766768227/100000000000000 : ℝ), (15632477822087/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4330725291/10000000000 : ℝ)|^2141 ≤ (33291277564971/100000000000000 : ℝ)^1629
        have hw : |(4330725291/10000000000 : ℝ)|=(4330725291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4542167763/10000000000 : ℝ)|^2141 ≤ (35443766768227/100000000000000 : ℝ)^1629
        have hw : |(4542167763/10000000000 : ℝ)|=(4542167763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1032167063/2500000000 : ℝ)|^2141 ≤ (15632477822087/50000000000000 : ℝ)^1629
        have hw : |(1032167063/2500000000 : ℝ)|=(1032167063/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1322_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38485273/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8093/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4859/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2157/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1503/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8093/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4859/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8093/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4859/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8093/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4859/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8093/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4859/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8093/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4859/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8093/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4859/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4859/50000 : ℝ) ^ (4281/1024 : ℝ) ≤ (2926638706367113/50000000000000000000 : ℝ) := by
    have hpowers : (4859/50000 : ℝ)^4281 ≤ (2926638706367113/50000000000000000000 : ℝ)^1024 := by
      have hnat : (4859 : ℕ)^4281*50000000000000000000^1024 ≤ 2926638706367113^1024*50000^4281 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4859 50000 2926638706367113 50000000000000000000 4281 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4859/50000 : ℝ)) (X := (2926638706367113/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4281 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8093/50000 : ℝ) ^ (4281/1024 : ℝ) ≤ (9878888315601941/20000000000000000000 : ℝ) := by
    have hpowers : (8093/50000 : ℝ)^4281 ≤ (9878888315601941/20000000000000000000 : ℝ)^1024 := by
      have hnat : (8093 : ℕ)^4281*20000000000000000000^1024 ≤ 9878888315601941^1024*50000^4281 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8093 50000 9878888315601941 20000000000000000000 4281 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8093/50000 : ℝ)) (X := (9878888315601941/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4281 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002926638706367113/25000000000000000000 : ℝ) ≤ (10000280004166101/10000000000000000 : ℝ) ^ (4281/1024 : ℝ) := by
    have hpowers : (25002926638706367113/25000000000000000000 : ℝ)^1024 ≤ (10000280004166101/10000000000000000 : ℝ)^4281 := by
      have hnat : (25002926638706367113 : ℕ)^1024*10000000000000000^4281 ≤ 10000280004166101^4281*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002926638706367113 25000000000000000000 10000280004166101 10000000000000000 1024 4281 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000280004166101/10000000000000000 : ℝ)) (X := (25002926638706367113/25000000000000000000 : ℝ)) (by norm_num) 4281 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100055247718990743931/100000000000000000000 : ℝ) ≤ (10001321228180153/10000000000000000 : ℝ) ^ (4281/1024 : ℝ) := by
    have hpowers : (100055247718990743931/100000000000000000000 : ℝ)^1024 ≤ (10001321228180153/10000000000000000 : ℝ)^4281 := by
      have hnat : (100055247718990743931 : ℕ)^1024*10000000000000000^4281 ≤ 10001321228180153^4281*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100055247718990743931 100000000000000000000 10001321228180153 10000000000000000 1024 4281 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001321228180153/10000000000000000 : ℝ)) (X := (100055247718990743931/100000000000000000000 : ℝ)) (by norm_num) 4281 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10009878888315601941/10000000000000000000 : ℝ) ≤ (2000472490438841/2000000000000000 : ℝ) ^ (4281/1024 : ℝ) := by
    have hpowers : (10009878888315601941/10000000000000000000 : ℝ)^1024 ≤ (2000472490438841/2000000000000000 : ℝ)^4281 := by
      have hnat : (10009878888315601941 : ℕ)^1024*2000000000000000^4281 ≤ 2000472490438841^4281*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10009878888315601941 10000000000000000000 2000472490438841 2000000000000000 1024 4281 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000472490438841/2000000000000000 : ℝ)) (X := (10009878888315601941/10000000000000000000 : ℝ)) (by norm_num) 4281 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2926638706367113/50000000000000000000 : ℝ) ≤ ((16165393459252306649/16170000000000000000 : ℝ)+2*(260306003513/161700000000000 : ℝ)*(4859/50000 : ℝ))^(4281/1024 : ℝ) := by
    rw [show (16165393459252306649/16170000000000000000 : ℝ)+2*(260306003513/161700000000000 : ℝ)*(4859/50000 : ℝ)=(10000280004166101/10000000000000000 : ℝ) by norm_num, show 1+2*(2926638706367113/50000000000000000000 : ℝ)=(25002926638706367113/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9878888315601941/20000000000000000000 : ℝ)+(2926638706367113/50000000000000000000 : ℝ) ≤ ((16165393459252306649/16170000000000000000 : ℝ)+(260306003513/161700000000000 : ℝ)*((8093/50000 : ℝ)+(4859/50000 : ℝ)))^(4281/1024 : ℝ) := by
    rw [show (16165393459252306649/16170000000000000000 : ℝ)+(260306003513/161700000000000 : ℝ)*((8093/50000 : ℝ)+(4859/50000 : ℝ))=(10001321228180153/10000000000000000 : ℝ) by norm_num, show 1+(9878888315601941/20000000000000000000 : ℝ)+(2926638706367113/50000000000000000000 : ℝ)=(100055247718990743931/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9878888315601941/20000000000000000000 : ℝ) ≤ ((16165393459252306649/16170000000000000000 : ℝ)+2*(260306003513/161700000000000 : ℝ)*(8093/50000 : ℝ))^(4281/1024 : ℝ) := by
    rw [show (16165393459252306649/16170000000000000000 : ℝ)+2*(260306003513/161700000000000 : ℝ)*(8093/50000 : ℝ)=(2000472490438841/2000000000000000 : ℝ) by norm_num, show 1+2*(9878888315601941/20000000000000000000 : ℝ)=(10009878888315601941/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (16165393459252306649/16170000000000000000 : ℝ)*(X 1 0+X 2 0)+(260306003513/161700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4281/1024 : ℝ)) (lo := (4859/50000 : ℝ)) (hi := (8093/50000 : ℝ)) (c := (16165393459252306649/16170000000000000000 : ℝ)) (alpha := (260306003513/161700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (16165393459252306649/16170000000000000000 : ℝ)*(X 0 1+X 2 1)+(260306003513/161700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4281/1024 : ℝ)) (lo := (4859/50000 : ℝ)) (hi := (8093/50000 : ℝ)) (c := (16165393459252306649/16170000000000000000 : ℝ)) (alpha := (260306003513/161700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (16165393459252306649/16170000000000000000 : ℝ)*(X 0 2+X 1 2)+(260306003513/161700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4281/1024 : ℝ)) (lo := (4859/50000 : ℝ)) (hi := (8093/50000 : ℝ)) (c := (16165393459252306649/16170000000000000000 : ℝ)) (alpha := (260306003513/161700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2059396831/10000000000 : ℝ)*X 0 0+(1085961851/2000000000 : ℝ)*X 0 1+(2614600793/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5353419029/10000000000 : ℝ)*X 1 0+(-2161976399/10000000000 : ℝ)*X 1 1+(10458403/20000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((3345887/6250000 : ℝ)*X 2 0+(2614600453/5000000000 : ℝ)*X 2 1+(-540494239/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4330682503/10000000000 : ℝ)*X 0 0+(1031724681/2500000000 : ℝ)*X 0 1+(4543926923/10000000000 : ℝ)*X 0 2+(4330682503/10000000000 : ℝ)*X 1 0+(1031724681/2500000000 : ℝ)*X 1 1+(4543926923/10000000000 : ℝ)*X 1 2+(4330682503/10000000000 : ℝ)*X 2 0+(1031724681/2500000000 : ℝ)*X 2 1+(4543926923/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1029708717/5000000000 : ℝ)*X 0 0+(5230047721/10000000000 : ℝ)*X 0 1+(5428957839/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2650932751/5000000000 : ℝ)*X 1 0+(-49055509/250000000 : ℝ)*X 1 1+(5428958047/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5301867237/10000000000 : ℝ)*X 2 0+(5428956829/10000000000 : ℝ)*X 2 1+(-392443933/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4330725291/10000000000 : ℝ)*X 0 0+(4542167763/10000000000 : ℝ)*X 0 1+(1032167063/2500000000 : ℝ)*X 0 2+(4330725291/10000000000 : ℝ)*X 1 0+(4542167763/10000000000 : ℝ)*X 1 1+(1032167063/2500000000 : ℝ)*X 1 2+(4330725291/10000000000 : ℝ)*X 2 0+(4542167763/10000000000 : ℝ)*X 2 1+(1032167063/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (48760996906011413811387167/4812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (522373331/25000000000000 : ℝ)*(base19) + (2300407819/100000000000000 : ℝ)*(base23) + (26289269/50000000000000 : ℝ)*(lower2) + (256657589/50000000000000 : ℝ)*(upper3) + (40123957/50000000000000 : ℝ)*(lower4) + (461429133061519/12500000000000 : ℝ)*(major0) + (461429133061519/12500000000000 : ℝ)*(major1) + (461429133061519/12500000000000 : ℝ)*(major2) + (4984892010164927/100000000000000 : ℝ)*(sp0) + (996982396208703/20000000000000 : ℝ)*(sp1) + (249245588506451/5000000000000 : ℝ)*(sp2) + (479586418944811/20000000000000 : ℝ)*(sp3) + (2757546489/12500000000000 : ℝ)*(sp4) + (9812992449/50000000000000 : ℝ)*(sp7) + (2397951720708953/100000000000000 : ℝ)*(f.failure) + (2492457035268419/50000000000000 : ℝ)*(f.sum) + (778248665339/577500000000000000000000000 : ℝ)*base65 + (7096876869039803/2625000000000000000000000000000 : ℝ)*base67 + (14897007245960197/2625000000000000000000000000000 : ℝ)*base70 + (10998280528164803/2625000000000000000000000000000 : ℝ)*base71 + (1436906700673/1155000000000000000000000000 : ℝ)*base73 + (3726107465289803/2625000000000000000000000000000 : ℝ)*base75 + (6622045732539803/2625000000000000000000000000000 : ℝ)*base77 + (12989308611335197/2625000000000000000000000000000 : ℝ)*base80 + (5736531146713/1155000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (9749169/2500000000000000000000 : ℝ)*base89 + (9749169/2500000000000000000000 : ℝ)*base91 + (9749169/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (871946737366827808300269111/269500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (43902623/4000000000000 : ℝ)*(base19) + (3185630099/100000000000000 : ℝ)*(base23) + (284667233/100000000000000 : ℝ)*(upper3) + (15166863/20000000000000 : ℝ)*(lower4) + (14979291/12500000000000 : ℝ)*(upper5) + (3722895963579761/100000000000000 : ℝ)*(major0) + (3722895963579761/100000000000000 : ℝ)*(major1) + (3722895963579761/100000000000000 : ℝ)*(major2) + (4024956343/25000000000000 : ℝ)*(sp1) + (2933642229/6250000000000 : ℝ)*(sp2) + (5027401826612923/100000000000000 : ℝ)*(sp4) + (2513692314610987/50000000000000 : ℝ)*(sp5) + (125683792567679/2500000000000 : ℝ)*(sp6) + (241838999269913/10000000000000 : ℝ)*(sp7) + (241838999269913/10000000000000 : ℝ)*(f.failure) + (5027401826612923/100000000000000 : ℝ)*(f.sum) + (30794395950313/8085000000000000000000000000 : ℝ)*base65 + (747885048332688101/147000000000000000000000000000000 : ℝ)*base68 + (1371982917519311899/147000000000000000000000000000000 : ℝ)*base69 + (1112870808396311899/147000000000000000000000000000000 : ℝ)*base71 + (2901966885977/8085000000000000000000000000 : ℝ)*base74 + (643240798512311899/147000000000000000000000000000000 : ℝ)*base75 + (338633423748311899/147000000000000000000000000000000 : ℝ)*base77 + (343701013259688101/147000000000000000000000000000000 : ℝ)*base80 + (47463051843433/8085000000000000000000000000 : ℝ)*base81 + (1/50000000000000 : ℝ)*base86 + (8751/250000000000000000000 : ℝ)*base90 + (8751/250000000000000000000 : ℝ)*base92 + (8751/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1322_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38485273/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8093/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4859/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2157/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1503/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1322_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1322_s4_0 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-51525751/250000000 : ℝ)*x 0 + (541668949/1000000000 : ℝ)*x 1 + (5241249397/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (51525751/250000000 : ℝ)^2141 ≤ (6272906247611/50000000000000 : ℝ)^1629 := by
    have hnat : (51525751 : ℕ)^2141*50000000000000^1629 ≤ 6272906247611^1629*250000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51525751 250000000 6272906247611 50000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (541668949/1000000000 : ℝ)^2141 ≤ (22336527431457/50000000000000 : ℝ)^1629 := by
    have hnat : (541668949 : ℕ)^2141*50000000000000^1629 ≤ 22336527431457^1629*1000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541668949 1000000000 22336527431457 50000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5241249397/10000000000 : ℝ)^2141 ≤ (42781132622911/100000000000000 : ℝ)^1629 := by
    have hnat : (5241249397 : ℕ)^2141*100000000000000^1629 ≤ 42781132622911^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241249397 10000000000 42781132622911 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-51525751/250000000 : ℝ), (541668949/1000000000 : ℝ), (5241249397/10000000000 : ℝ)] ![(6272906247611/50000000000000 : ℝ), (22336527431457/50000000000000 : ℝ), (42781132622911/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-51525751/250000000 : ℝ)|^2141 ≤ (6272906247611/50000000000000 : ℝ)^1629
        have hw : |(-51525751/250000000 : ℝ)|=(51525751/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(541668949/1000000000 : ℝ)|^2141 ≤ (22336527431457/50000000000000 : ℝ)^1629
        have hw : |(541668949/1000000000 : ℝ)|=(541668949/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5241249397/10000000000 : ℝ)|^2141 ≤ (42781132622911/100000000000000 : ℝ)^1629
        have hw : |(5241249397/10000000000 : ℝ)|=(5241249397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_s4_1 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2675042671/5000000000 : ℝ)*x 0 + (-1075245517/5000000000 : ℝ)*x 1 + (5241249191/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675042671/5000000000 : ℝ)^2141 ≤ (21976250729401/50000000000000 : ℝ)^1629 := by
    have hnat : (2675042671 : ℕ)^2141*50000000000000^1629 ≤ 21976250729401^1629*5000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675042671 5000000000 21976250729401 50000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1075245517/5000000000 : ℝ)^2141 ≤ (13266368106449/100000000000000 : ℝ)^1629 := by
    have hnat : (1075245517 : ℕ)^2141*100000000000000^1629 ≤ 13266368106449^1629*5000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075245517 5000000000 13266368106449 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5241249191/10000000000 : ℝ)^2141 ≤ (10695282603243/25000000000000 : ℝ)^1629 := by
    have hnat : (5241249191 : ℕ)^2141*25000000000000^1629 ≤ 10695282603243^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241249191 10000000000 10695282603243 25000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675042671/5000000000 : ℝ), (-1075245517/5000000000 : ℝ), (5241249191/10000000000 : ℝ)] ![(21976250729401/50000000000000 : ℝ), (13266368106449/100000000000000 : ℝ), (10695282603243/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675042671/5000000000 : ℝ)|^2141 ≤ (21976250729401/50000000000000 : ℝ)^1629
        have hw : |(2675042671/5000000000 : ℝ)|=(2675042671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1075245517/5000000000 : ℝ)|^2141 ≤ (13266368106449/100000000000000 : ℝ)^1629
        have hw : |(-1075245517/5000000000 : ℝ)|=(1075245517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5241249191/10000000000 : ℝ)|^2141 ≤ (10695282603243/25000000000000 : ℝ)^1629
        have hw : |(5241249191/10000000000 : ℝ)|=(5241249191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_s4_2 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5350085353/10000000000 : ℝ)*x 0 + (1310312229/2500000000 : ℝ)*x 1 + (-268811423/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350085353/10000000000 : ℝ)^2141 ≤ (43952501577573/100000000000000 : ℝ)^1629 := by
    have hnat : (5350085353 : ℕ)^2141*100000000000000^1629 ≤ 43952501577573^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350085353 10000000000 43952501577573 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310312229/2500000000 : ℝ)^2141 ≤ (42781127462811/100000000000000 : ℝ)^1629 := by
    have hnat : (1310312229 : ℕ)^2141*100000000000000^1629 ≤ 42781127462811^1629*2500000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310312229 2500000000 42781127462811 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (268811423/1250000000 : ℝ)^2141 ≤ (530654837769/4000000000000 : ℝ)^1629 := by
    have hnat : (268811423 : ℕ)^2141*4000000000000^1629 ≤ 530654837769^1629*1250000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268811423 1250000000 530654837769 4000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350085353/10000000000 : ℝ), (1310312229/2500000000 : ℝ), (-268811423/1250000000 : ℝ)] ![(43952501577573/100000000000000 : ℝ), (42781127462811/100000000000000 : ℝ), (530654837769/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350085353/10000000000 : ℝ)|^2141 ≤ (43952501577573/100000000000000 : ℝ)^1629
        have hw : |(5350085353/10000000000 : ℝ)|=(5350085353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310312229/2500000000 : ℝ)|^2141 ≤ (42781127462811/100000000000000 : ℝ)^1629
        have hw : |(1310312229/2500000000 : ℝ)|=(1310312229/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-268811423/1250000000 : ℝ)|^2141 ≤ (530654837769/4000000000000 : ℝ)^1629
        have hw : |(-268811423/1250000000 : ℝ)|=(268811423/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_s4_3 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4331670453/10000000000 : ℝ)*x 0 + (2076467483/5000000000 : ℝ)*x 1 + (2258822273/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4331670453/10000000000 : ℝ)^2141 ≤ (6660165439039/20000000000000 : ℝ)^1629 := by
    have hnat : (4331670453 : ℕ)^2141*20000000000000^1629 ≤ 6660165439039^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4331670453 10000000000 6660165439039 20000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2076467483/5000000000 : ℝ)^2141 ≤ (15753349573089/50000000000000 : ℝ)^1629 := by
    have hnat : (2076467483 : ℕ)^2141*50000000000000^1629 ≤ 15753349573089^1629*5000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2076467483 5000000000 15753349573089 50000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2258822273/5000000000 : ℝ)^2141 ≤ (17596236815577/50000000000000 : ℝ)^1629 := by
    have hnat : (2258822273 : ℕ)^2141*50000000000000^1629 ≤ 17596236815577^1629*5000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2258822273 5000000000 17596236815577 50000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4331670453/10000000000 : ℝ), (2076467483/5000000000 : ℝ), (2258822273/5000000000 : ℝ)] ![(6660165439039/20000000000000 : ℝ), (15753349573089/50000000000000 : ℝ), (17596236815577/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4331670453/10000000000 : ℝ)|^2141 ≤ (6660165439039/20000000000000 : ℝ)^1629
        have hw : |(4331670453/10000000000 : ℝ)|=(4331670453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2076467483/5000000000 : ℝ)|^2141 ≤ (15753349573089/50000000000000 : ℝ)^1629
        have hw : |(2076467483/5000000000 : ℝ)|=(2076467483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2258822273/5000000000 : ℝ)|^2141 ≤ (17596236815577/50000000000000 : ℝ)^1629
        have hw : |(2258822273/5000000000 : ℝ)|=(2258822273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_s4_4 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2061043751/10000000000 : ℝ)*x 0 + (2620948567/5000000000 : ℝ)*x 1 + (5416038277/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2061043751/10000000000 : ℝ)^2141 ≤ (2509184437681/20000000000000 : ℝ)^1629 := by
    have hnat : (2061043751 : ℕ)^2141*20000000000000^1629 ≤ 2509184437681^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2061043751 10000000000 2509184437681 20000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2620948567/5000000000 : ℝ)^2141 ≤ (42788081588733/100000000000000 : ℝ)^1629 := by
    have hnat : (2620948567 : ℕ)^2141*100000000000000^1629 ≤ 42788081588733^1629*5000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620948567 5000000000 42788081588733 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5416038277/10000000000 : ℝ)^2141 ≤ (2791624762797/6250000000000 : ℝ)^1629 := by
    have hnat : (5416038277 : ℕ)^2141*6250000000000^1629 ≤ 2791624762797^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416038277 10000000000 2791624762797 6250000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2061043751/10000000000 : ℝ), (2620948567/5000000000 : ℝ), (5416038277/10000000000 : ℝ)] ![(2509184437681/20000000000000 : ℝ), (42788081588733/100000000000000 : ℝ), (2791624762797/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2061043751/10000000000 : ℝ)|^2141 ≤ (2509184437681/20000000000000 : ℝ)^1629
        have hw : |(-2061043751/10000000000 : ℝ)|=(2061043751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2620948567/5000000000 : ℝ)|^2141 ≤ (42788081588733/100000000000000 : ℝ)^1629
        have hw : |(2620948567/5000000000 : ℝ)|=(2620948567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5416038277/10000000000 : ℝ)|^2141 ≤ (2791624762797/6250000000000 : ℝ)^1629
        have hw : |(5416038277/10000000000 : ℝ)|=(5416038277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_s4_5 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305001611/10000000000 : ℝ)*x 0 + (-493925559/2500000000 : ℝ)*x 1 + (42312799/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305001611/10000000000 : ℝ)^2141 ≤ (43466361073707/100000000000000 : ℝ)^1629 := by
    have hnat : (5305001611 : ℕ)^2141*100000000000000^1629 ≤ 43466361073707^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305001611 10000000000 43466361073707 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (493925559/2500000000 : ℝ)^2141 ≤ (5933821380061/50000000000000 : ℝ)^1629 := by
    have hnat : (493925559 : ℕ)^2141*50000000000000^1629 ≤ 5933821380061^1629*2500000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      493925559 2500000000 5933821380061 50000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42312799/78125000 : ℝ)^2141 ≤ (44665996150557/100000000000000 : ℝ)^1629 := by
    have hnat : (42312799 : ℕ)^2141*100000000000000^1629 ≤ 44665996150557^1629*78125000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42312799 78125000 44665996150557 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305001611/10000000000 : ℝ), (-493925559/2500000000 : ℝ), (42312799/78125000 : ℝ)] ![(43466361073707/100000000000000 : ℝ), (5933821380061/50000000000000 : ℝ), (44665996150557/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305001611/10000000000 : ℝ)|^2141 ≤ (43466361073707/100000000000000 : ℝ)^1629
        have hw : |(5305001611/10000000000 : ℝ)|=(5305001611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-493925559/2500000000 : ℝ)|^2141 ≤ (5933821380061/50000000000000 : ℝ)^1629
        have hw : |(-493925559/2500000000 : ℝ)|=(493925559/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(42312799/78125000 : ℝ)|^2141 ≤ (44665996150557/100000000000000 : ℝ)^1629
        have hw : |(42312799/78125000 : ℝ)|=(42312799/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_s4_6 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (42440013/80000000 : ℝ)*x 0 + (1083207651/2000000000 : ℝ)*x 1 + (-1975702241/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42440013/80000000 : ℝ)^2141 ≤ (43466361224469/100000000000000 : ℝ)^1629 := by
    have hnat : (42440013 : ℕ)^2141*100000000000000^1629 ≤ 43466361224469^1629*80000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42440013 80000000 43466361224469 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1083207651/2000000000 : ℝ)^2141 ≤ (44665995966293/100000000000000 : ℝ)^1629 := by
    have hnat : (1083207651 : ℕ)^2141*100000000000000^1629 ≤ 44665995966293^1629*2000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083207651 2000000000 44665995966293 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1975702241/10000000000 : ℝ)^2141 ≤ (2966910699899/25000000000000 : ℝ)^1629 := by
    have hnat : (1975702241 : ℕ)^2141*25000000000000^1629 ≤ 2966910699899^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1975702241 10000000000 2966910699899 25000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42440013/80000000 : ℝ), (1083207651/2000000000 : ℝ), (-1975702241/10000000000 : ℝ)] ![(43466361224469/100000000000000 : ℝ), (44665995966293/100000000000000 : ℝ), (2966910699899/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42440013/80000000 : ℝ)|^2141 ≤ (43466361224469/100000000000000 : ℝ)^1629
        have hw : |(42440013/80000000 : ℝ)|=(42440013/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1083207651/2000000000 : ℝ)|^2141 ≤ (44665995966293/100000000000000 : ℝ)^1629
        have hw : |(1083207651/2000000000 : ℝ)|=(1083207651/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1975702241/10000000000 : ℝ)|^2141 ≤ (2966910699899/25000000000000 : ℝ)^1629
        have hw : |(-1975702241/10000000000 : ℝ)|=(1975702241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_s4_7 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4331698939/10000000000 : ℝ)*x 0 + (4516297501/10000000000 : ℝ)*x 1 + (2077144563/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4331698939/10000000000 : ℝ)^2141 ≤ (8325278754817/25000000000000 : ℝ)^1629 := by
    have hnat : (4331698939 : ℕ)^2141*25000000000000^1629 ≤ 8325278754817^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4331698939 10000000000 8325278754817 25000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4516297501/10000000000 : ℝ)^2141 ≤ (35178682652963/100000000000000 : ℝ)^1629 := by
    have hnat : (4516297501 : ℕ)^2141*100000000000000^1629 ≤ 35178682652963^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4516297501 10000000000 35178682652963 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2077144563/5000000000 : ℝ)^2141 ≤ (31520202311729/100000000000000 : ℝ)^1629 := by
    have hnat : (2077144563 : ℕ)^2141*100000000000000^1629 ≤ 31520202311729^1629*5000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2077144563 5000000000 31520202311729 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4331698939/10000000000 : ℝ), (4516297501/10000000000 : ℝ), (2077144563/5000000000 : ℝ)] ![(8325278754817/25000000000000 : ℝ), (35178682652963/100000000000000 : ℝ), (31520202311729/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4331698939/10000000000 : ℝ)|^2141 ≤ (8325278754817/25000000000000 : ℝ)^1629
        have hw : |(4331698939/10000000000 : ℝ)|=(4331698939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4516297501/10000000000 : ℝ)|^2141 ≤ (35178682652963/100000000000000 : ℝ)^1629
        have hw : |(4516297501/10000000000 : ℝ)|=(4516297501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2077144563/5000000000 : ℝ)|^2141 ≤ (31520202311729/100000000000000 : ℝ)^1629
        have hw : |(2077144563/5000000000 : ℝ)|=(2077144563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1322_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38485273/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1503/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2157/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (11043/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3689/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1503/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2157/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1503/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2157/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1503/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2157/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1503/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2157/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1503/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2157/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1503/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2157/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2157/20000 : ℝ) ^ (4281/1024 : ℝ) ≤ (9047861766074041/100000000000000000000 : ℝ) := by
    have hpowers : (2157/20000 : ℝ)^4281 ≤ (9047861766074041/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2157 : ℕ)^4281*100000000000000000000^1024 ≤ 9047861766074041^1024*20000^4281 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2157 20000 9047861766074041 100000000000000000000 4281 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2157/20000 : ℝ)) (X := (9047861766074041/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4281 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1503/10000 : ℝ) ^ (4281/1024 : ℝ) ≤ (36236144945335537/100000000000000000000 : ℝ) := by
    have hpowers : (1503/10000 : ℝ)^4281 ≤ (36236144945335537/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1503 : ℕ)^4281*100000000000000000000^1024 ≤ 36236144945335537^1024*10000^4281 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1503 10000 36236144945335537 100000000000000000000 4281 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1503/10000 : ℝ)) (X := (36236144945335537/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4281 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009047861766074041/50000000000000000000 : ℝ) ≤ (250010820337241/250000000000000 : ℝ) ^ (4281/1024 : ℝ) := by
    have hpowers : (50009047861766074041/50000000000000000000 : ℝ)^1024 ≤ (250010820337241/250000000000000 : ℝ)^4281 := by
      have hnat : (50009047861766074041 : ℕ)^1024*250000000000000^4281 ≤ 250010820337241^4281*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009047861766074041 50000000000000000000 250010820337241 250000000000000 1024 4281 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250010820337241/250000000000000 : ℝ)) (X := (50009047861766074041/50000000000000000000 : ℝ)) (by norm_num) 4281 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022642003355704789/50000000000000000000 : ℝ) ≤ (5000541495411153/5000000000000000 : ℝ) ^ (4281/1024 : ℝ) := by
    have hpowers : (50022642003355704789/50000000000000000000 : ℝ)^1024 ≤ (5000541495411153/5000000000000000 : ℝ)^4281 := by
      have hnat : (50022642003355704789 : ℕ)^1024*5000000000000000^4281 ≤ 5000541495411153^4281*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022642003355704789 50000000000000000000 5000541495411153 5000000000000000 1024 4281 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000541495411153/5000000000000000 : ℝ)) (X := (50022642003355704789/50000000000000000000 : ℝ)) (by norm_num) 4281 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036236144945335537/50000000000000000000 : ℝ) ≤ (2500433292038743/2500000000000000 : ℝ) ^ (4281/1024 : ℝ) := by
    have hpowers : (50036236144945335537/50000000000000000000 : ℝ)^1024 ≤ (2500433292038743/2500000000000000 : ℝ)^4281 := by
      have hnat : (50036236144945335537 : ℕ)^1024*2500000000000000^4281 ≤ 2500433292038743^4281*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036236144945335537 50000000000000000000 2500433292038743 2500000000000000 1024 4281 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500433292038743/2500000000000000 : ℝ)) (X := (50036236144945335537/50000000000000000000 : ℝ)) (by norm_num) 4281 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9047861766074041/100000000000000000000 : ℝ) ≤ ((707296882803298603/707500000000000000 : ℝ)+2*(325088666333/212250000000000 : ℝ)*(2157/20000 : ℝ))^(4281/1024 : ℝ) := by
    rw [show (707296882803298603/707500000000000000 : ℝ)+2*(325088666333/212250000000000 : ℝ)*(2157/20000 : ℝ)=(250010820337241/250000000000000 : ℝ) by norm_num, show 1+2*(9047861766074041/100000000000000000000 : ℝ)=(50009047861766074041/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36236144945335537/100000000000000000000 : ℝ)+(9047861766074041/100000000000000000000 : ℝ) ≤ ((707296882803298603/707500000000000000 : ℝ)+(325088666333/212250000000000 : ℝ)*((1503/10000 : ℝ)+(2157/20000 : ℝ)))^(4281/1024 : ℝ) := by
    rw [show (707296882803298603/707500000000000000 : ℝ)+(325088666333/212250000000000 : ℝ)*((1503/10000 : ℝ)+(2157/20000 : ℝ))=(5000541495411153/5000000000000000 : ℝ) by norm_num, show 1+(36236144945335537/100000000000000000000 : ℝ)+(9047861766074041/100000000000000000000 : ℝ)=(50022642003355704789/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36236144945335537/100000000000000000000 : ℝ) ≤ ((707296882803298603/707500000000000000 : ℝ)+2*(325088666333/212250000000000 : ℝ)*(1503/10000 : ℝ))^(4281/1024 : ℝ) := by
    rw [show (707296882803298603/707500000000000000 : ℝ)+2*(325088666333/212250000000000 : ℝ)*(1503/10000 : ℝ)=(2500433292038743/2500000000000000 : ℝ) by norm_num, show 1+2*(36236144945335537/100000000000000000000 : ℝ)=(50036236144945335537/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (707296882803298603/707500000000000000 : ℝ)*(X 1 0+X 2 0)+(325088666333/212250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4281/1024 : ℝ)) (lo := (2157/20000 : ℝ)) (hi := (1503/10000 : ℝ)) (c := (707296882803298603/707500000000000000 : ℝ)) (alpha := (325088666333/212250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (707296882803298603/707500000000000000 : ℝ)*(X 0 1+X 2 1)+(325088666333/212250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4281/1024 : ℝ)) (lo := (2157/20000 : ℝ)) (hi := (1503/10000 : ℝ)) (c := (707296882803298603/707500000000000000 : ℝ)) (alpha := (325088666333/212250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (707296882803298603/707500000000000000 : ℝ)*(X 0 2+X 1 2)+(325088666333/212250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4281/1024 : ℝ)) (lo := (2157/20000 : ℝ)) (hi := (1503/10000 : ℝ)) (c := (707296882803298603/707500000000000000 : ℝ)) (alpha := (325088666333/212250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-51525751/250000000 : ℝ)*X 0 0+(541668949/1000000000 : ℝ)*X 0 1+(5241249397/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675042671/5000000000 : ℝ)*X 1 0+(-1075245517/5000000000 : ℝ)*X 1 1+(5241249191/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350085353/10000000000 : ℝ)*X 2 0+(1310312229/2500000000 : ℝ)*X 2 1+(-268811423/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4331670453/10000000000 : ℝ)*X 0 0+(2076467483/5000000000 : ℝ)*X 0 1+(2258822273/5000000000 : ℝ)*X 0 2+(4331670453/10000000000 : ℝ)*X 1 0+(2076467483/5000000000 : ℝ)*X 1 1+(2258822273/5000000000 : ℝ)*X 1 2+(4331670453/10000000000 : ℝ)*X 2 0+(2076467483/5000000000 : ℝ)*X 2 1+(2258822273/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2061043751/10000000000 : ℝ)*X 0 0+(2620948567/5000000000 : ℝ)*X 0 1+(5416038277/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305001611/10000000000 : ℝ)*X 1 0+(-493925559/2500000000 : ℝ)*X 1 1+(42312799/78125000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((42440013/80000000 : ℝ)*X 2 0+(1083207651/2000000000 : ℝ)*X 2 1+(-1975702241/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4331698939/10000000000 : ℝ)*X 0 0+(4516297501/10000000000 : ℝ)*X 0 1+(2077144563/5000000000 : ℝ)*X 0 2+(4331698939/10000000000 : ℝ)*X 1 0+(4516297501/10000000000 : ℝ)*X 1 1+(2077144563/5000000000 : ℝ)*X 1 2+(4331698939/10000000000 : ℝ)*X 2 0+(4516297501/10000000000 : ℝ)*X 2 1+(2077144563/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (595125280633346607437/176875000000000000000000000 : ℝ) := by norm_num
    linear_combination (1079960303/100000000000000 : ℝ)*(base19) + (1072254673/100000000000000 : ℝ)*(base23) + (27454031/25000000000000 : ℝ)*(upper3) + (6136393/25000000000000 : ℝ)*(lower4) + (422096071806593/10000000000000 : ℝ)*(major0) + (422096071806593/10000000000000 : ℝ)*(major1) + (422096071806593/10000000000000 : ℝ)*(major2) + (2849986248079507/50000000000000 : ℝ)*(sp0) + (5699987818289217/100000000000000 : ℝ)*(sp1) + (1139996015276767/20000000000000 : ℝ)*(sp2) + (1370959701040199/50000000000000 : ℝ)*(sp3) + (8201045253/50000000000000 : ℝ)*(sp4) + (1937402753/25000000000000 : ℝ)*(sp6) + (6511823203/50000000000000 : ℝ)*(sp7) + (2741932425726803/100000000000000 : ℝ)*(f.failure) + (71249861228119/1250000000000 : ℝ)*(f.sum) + (920286110093/2122500000000000000000000000 : ℝ)*base65 + (82561661555091263/21225000000000000000000000000000 : ℝ)*base68 + (158748855216441263/21225000000000000000000000000000 : ℝ)*base70 + (77614919115008737/21225000000000000000000000000000 : ℝ)*base71 + (193069621661/1061250000000000000000000000 : ℝ)*base74 + (194703413352983737/21225000000000000000000000000000 : ℝ)*base75 + (118270734105216263/21225000000000000000000000000000 : ℝ)*base78 + (60869157111308737/21225000000000000000000000000000 : ℝ)*base79 + (344485478279/265312500000000000000000000 : ℝ)*base82 + (13127781/2500000000000000000000 : ℝ)*base90 + (13127781/2500000000000000000000 : ℝ)*base92 + (13127781/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (44374408772281759926107/7075000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1116878489/100000000000000 : ℝ)*(base19) + (24343907/2000000000000 : ℝ)*(base23) + (64002087/50000000000000 : ℝ)*(upper3) + (19947539/50000000000000 : ℝ)*(lower4) + (137299481/100000000000000 : ℝ)*(upper5) + (2126208713350349/50000000000000 : ℝ)*(major0) + (2126208713350349/50000000000000 : ℝ)*(major1) + (2126208713350349/50000000000000 : ℝ)*(major2) + (21803273741/100000000000000 : ℝ)*(sp1) + (4595044691/20000000000000 : ℝ)*(sp2) + (2871233983965253/50000000000000 : ℝ)*(sp4) + (1435611261944569/25000000000000 : ℝ)*(sp5) + (5742443775511701/100000000000000 : ℝ)*(sp6) + (1381183338202089/50000000000000 : ℝ)*(sp7) + (1381183338202089/50000000000000 : ℝ)*(f.failure) + (2871233983965253/50000000000000 : ℝ)*(f.sum) + (33784933434817/5306250000000000000000000000 : ℝ)*base65 + (301073430191207341/106125000000000000000000000000000 : ℝ)*base67 + (74653388457792659/106125000000000000000000000000000 : ℝ)*base70 + (241039093569042659/106125000000000000000000000000000 : ℝ)*base72 + (34901385881767/5306250000000000000000000000 : ℝ)*base73 + (1137082451491082341/106125000000000000000000000000000 : ℝ)*base75 + (455481814571292659/106125000000000000000000000000000 : ℝ)*base78 + (313800287113832341/106125000000000000000000000000000 : ℝ)*base79 + (13913585028707/21225000000000000000000000000 : ℝ)*base82 + (664703/1250000000000000000000 : ℝ)*base90 + (664703/1250000000000000000000 : ℝ)*base92 + (664703/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1322_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38485273/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1503/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2157/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11043/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3689/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1322_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1322_s5_0 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2061318679/10000000000 : ℝ)*x 0 + (5414200619/10000000000 : ℝ)*x 1 + (5243548559/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2061318679/10000000000 : ℝ)^2141 ≤ (6274060882369/50000000000000 : ℝ)^1629 := by
    have hnat : (2061318679 : ℕ)^2141*50000000000000^1629 ≤ 6274060882369^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2061318679 10000000000 6274060882369 50000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414200619/10000000000 : ℝ)^2141 ≤ (22323039407713/50000000000000 : ℝ)^1629 := by
    have hnat : (5414200619 : ℕ)^2141*50000000000000^1629 ≤ 22323039407713^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414200619 10000000000 22323039407713 50000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243548559/10000000000 : ℝ)^2141 ≤ (10701449851911/25000000000000 : ℝ)^1629 := by
    have hnat : (5243548559 : ℕ)^2141*25000000000000^1629 ≤ 10701449851911^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243548559 10000000000 10701449851911 25000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2061318679/10000000000 : ℝ), (5414200619/10000000000 : ℝ), (5243548559/10000000000 : ℝ)] ![(6274060882369/50000000000000 : ℝ), (22323039407713/50000000000000 : ℝ), (10701449851911/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2061318679/10000000000 : ℝ)|^2141 ≤ (6274060882369/50000000000000 : ℝ)^1629
        have hw : |(-2061318679/10000000000 : ℝ)|=(2061318679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414200619/10000000000 : ℝ)|^2141 ≤ (22323039407713/50000000000000 : ℝ)^1629
        have hw : |(5414200619/10000000000 : ℝ)|=(5414200619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243548559/10000000000 : ℝ)|^2141 ≤ (10701449851911/25000000000000 : ℝ)^1629
        have hw : |(5243548559/10000000000 : ℝ)|=(5243548559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_s5_1 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5349451561/10000000000 : ℝ)*x 0 + (-537073023/2500000000 : ℝ)*x 1 + (1310887141/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349451561/10000000000 : ℝ)^2141 ≤ (43945658410581/100000000000000 : ℝ)^1629 := by
    have hnat : (5349451561 : ℕ)^2141*100000000000000^1629 ≤ 43945658410581^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349451561 10000000000 43945658410581 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (537073023/2500000000 : ℝ)^2141 ≤ (529941684171/4000000000000 : ℝ)^1629 := by
    have hnat : (537073023 : ℕ)^2141*4000000000000^1629 ≤ 529941684171^1629*2500000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537073023 2500000000 529941684171 4000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310887141/2500000000 : ℝ)^2141 ≤ (4280579946129/10000000000000 : ℝ)^1629 := by
    have hnat : (1310887141 : ℕ)^2141*10000000000000^1629 ≤ 4280579946129^1629*2500000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310887141 2500000000 4280579946129 10000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349451561/10000000000 : ℝ), (-537073023/2500000000 : ℝ), (1310887141/2500000000 : ℝ)] ![(43945658410581/100000000000000 : ℝ), (529941684171/4000000000000 : ℝ), (4280579946129/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349451561/10000000000 : ℝ)|^2141 ≤ (43945658410581/100000000000000 : ℝ)^1629
        have hw : |(5349451561/10000000000 : ℝ)|=(5349451561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-537073023/2500000000 : ℝ)|^2141 ≤ (529941684171/4000000000000 : ℝ)^1629
        have hw : |(-537073023/2500000000 : ℝ)|=(537073023/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310887141/2500000000 : ℝ)|^2141 ≤ (4280579946129/10000000000000 : ℝ)^1629
        have hw : |(1310887141/2500000000 : ℝ)|=(1310887141/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_s5_2 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1337362901/2500000000 : ℝ)*x 0 + (5243548543/10000000000 : ℝ)*x 1 + (-2148292063/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337362901/2500000000 : ℝ)^2141 ≤ (43945658874851/100000000000000 : ℝ)^1629 := by
    have hnat : (1337362901 : ℕ)^2141*100000000000000^1629 ≤ 43945658874851^1629*2500000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337362901 2500000000 43945658874851 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243548543/10000000000 : ℝ)^2141 ≤ (21402899617987/50000000000000 : ℝ)^1629 := by
    have hnat : (5243548543 : ℕ)^2141*50000000000000^1629 ≤ 21402899617987^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243548543 10000000000 21402899617987 50000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2148292063/10000000000 : ℝ)^2141 ≤ (13248541869221/100000000000000 : ℝ)^1629 := by
    have hnat : (2148292063 : ℕ)^2141*100000000000000^1629 ≤ 13248541869221^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2148292063 10000000000 13248541869221 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337362901/2500000000 : ℝ), (5243548543/10000000000 : ℝ), (-2148292063/10000000000 : ℝ)] ![(43945658874851/100000000000000 : ℝ), (21402899617987/50000000000000 : ℝ), (13248541869221/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337362901/2500000000 : ℝ)|^2141 ≤ (43945658874851/100000000000000 : ℝ)^1629
        have hw : |(1337362901/2500000000 : ℝ)|=(1337362901/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243548543/10000000000 : ℝ)|^2141 ≤ (21402899617987/50000000000000 : ℝ)^1629
        have hw : |(5243548543/10000000000 : ℝ)|=(5243548543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2148292063/10000000000 : ℝ)|^2141 ≤ (13248541869221/100000000000000 : ℝ)^1629
        have hw : |(-2148292063/10000000000 : ℝ)|=(2148292063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_s5_3 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2165921807/5000000000 : ℝ)*x 0 + (519736313/1250000000 : ℝ)*x 1 + (4512645733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2165921807/5000000000 : ℝ)^2141 ≤ (33302576832417/100000000000000 : ℝ)^1629 := by
    have hnat : (2165921807 : ℕ)^2141*100000000000000^1629 ≤ 33302576832417^1629*5000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2165921807 5000000000 33302576832417 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (519736313/1250000000 : ℝ)^2141 ≤ (7889030151793/25000000000000 : ℝ)^1629 := by
    have hnat : (519736313 : ℕ)^2141*25000000000000^1629 ≤ 7889030151793^1629*1250000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519736313 1250000000 7889030151793 25000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4512645733/10000000000 : ℝ)^2141 ≤ (17570651270733/50000000000000 : ℝ)^1629 := by
    have hnat : (4512645733 : ℕ)^2141*50000000000000^1629 ≤ 17570651270733^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4512645733 10000000000 17570651270733 50000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2165921807/5000000000 : ℝ), (519736313/1250000000 : ℝ), (4512645733/10000000000 : ℝ)] ![(33302576832417/100000000000000 : ℝ), (7889030151793/25000000000000 : ℝ), (17570651270733/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2165921807/5000000000 : ℝ)|^2141 ≤ (33302576832417/100000000000000 : ℝ)^1629
        have hw : |(2165921807/5000000000 : ℝ)|=(2165921807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(519736313/1250000000 : ℝ)|^2141 ≤ (7889030151793/25000000000000 : ℝ)^1629
        have hw : |(519736313/1250000000 : ℝ)|=(519736313/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4512645733/10000000000 : ℝ)|^2141 ≤ (17570651270733/50000000000000 : ℝ)^1629
        have hw : |(4512645733/10000000000 : ℝ)|=(4512645733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_s5_4 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1030665631/5000000000 : ℝ)*x 0 + (5244161717/10000000000 : ℝ)*x 1 + (5413584291/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1030665631/5000000000 : ℝ)^2141 ≤ (12548222437917/100000000000000 : ℝ)^1629 := by
    have hnat : (1030665631 : ℕ)^2141*100000000000000^1629 ≤ 12548222437917^1629*5000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030665631 5000000000 12548222437917 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244161717/10000000000 : ℝ)^2141 ≤ (42812378307571/100000000000000 : ℝ)^1629 := by
    have hnat : (5244161717 : ℕ)^2141*100000000000000^1629 ≤ 42812378307571^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244161717 10000000000 42812378307571 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413584291/10000000000 : ℝ)^2141 ≤ (44639399242601/100000000000000 : ℝ)^1629 := by
    have hnat : (5413584291 : ℕ)^2141*100000000000000^1629 ≤ 44639399242601^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413584291 10000000000 44639399242601 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1030665631/5000000000 : ℝ), (5244161717/10000000000 : ℝ), (5413584291/10000000000 : ℝ)] ![(12548222437917/100000000000000 : ℝ), (42812378307571/100000000000000 : ℝ), (44639399242601/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1030665631/5000000000 : ℝ)|^2141 ≤ (12548222437917/100000000000000 : ℝ)^1629
        have hw : |(-1030665631/5000000000 : ℝ)|=(1030665631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244161717/10000000000 : ℝ)|^2141 ≤ (42812378307571/100000000000000 : ℝ)^1629
        have hw : |(5244161717/10000000000 : ℝ)|=(5244161717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413584291/10000000000 : ℝ)|^2141 ≤ (44639399242601/100000000000000 : ℝ)^1629
        have hw : |(5413584291/10000000000 : ℝ)|=(5413584291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_s5_5 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1326399649/2500000000 : ℝ)*x 0 + (-1978256329/10000000000 : ℝ)*x 1 + (1353396073/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326399649/2500000000 : ℝ)^2141 ≤ (43472789940769/100000000000000 : ℝ)^1629 := by
    have hnat : (1326399649 : ℕ)^2141*100000000000000^1629 ≤ 43472789940769^1629*2500000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326399649 2500000000 43472789940769 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1978256329/10000000000 : ℝ)^2141 ≤ (11887810789187/100000000000000 : ℝ)^1629 := by
    have hnat : (1978256329 : ℕ)^2141*100000000000000^1629 ≤ 11887810789187^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1978256329 10000000000 11887810789187 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1353396073/2500000000 : ℝ)^2141 ≤ (22319699626719/50000000000000 : ℝ)^1629 := by
    have hnat : (1353396073 : ℕ)^2141*50000000000000^1629 ≤ 22319699626719^1629*2500000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353396073 2500000000 22319699626719 50000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326399649/2500000000 : ℝ), (-1978256329/10000000000 : ℝ), (1353396073/2500000000 : ℝ)] ![(43472789940769/100000000000000 : ℝ), (11887810789187/100000000000000 : ℝ), (22319699626719/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326399649/2500000000 : ℝ)|^2141 ≤ (43472789940769/100000000000000 : ℝ)^1629
        have hw : |(1326399649/2500000000 : ℝ)|=(1326399649/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1978256329/10000000000 : ℝ)|^2141 ≤ (11887810789187/100000000000000 : ℝ)^1629
        have hw : |(-1978256329/10000000000 : ℝ)|=(1978256329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1353396073/2500000000 : ℝ)|^2141 ≤ (22319699626719/50000000000000 : ℝ)^1629
        have hw : |(1353396073/2500000000 : ℝ)|=(1353396073/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_s5_6 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305598597/10000000000 : ℝ)*x 0 + (1353396073/2500000000 : ℝ)*x 1 + (-1978256329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305598597/10000000000 : ℝ)^2141 ≤ (21736394975769/50000000000000 : ℝ)^1629 := by
    have hnat : (5305598597 : ℕ)^2141*50000000000000^1629 ≤ 21736394975769^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305598597 10000000000 21736394975769 50000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353396073/2500000000 : ℝ)^2141 ≤ (22319699626719/50000000000000 : ℝ)^1629 := by
    have hnat : (1353396073 : ℕ)^2141*50000000000000^1629 ≤ 22319699626719^1629*2500000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353396073 2500000000 22319699626719 50000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1978256329/10000000000 : ℝ)^2141 ≤ (11887810789187/100000000000000 : ℝ)^1629 := by
    have hnat : (1978256329 : ℕ)^2141*100000000000000^1629 ≤ 11887810789187^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1978256329 10000000000 11887810789187 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305598597/10000000000 : ℝ), (1353396073/2500000000 : ℝ), (-1978256329/10000000000 : ℝ)] ![(21736394975769/50000000000000 : ℝ), (22319699626719/50000000000000 : ℝ), (11887810789187/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305598597/10000000000 : ℝ)|^2141 ≤ (21736394975769/50000000000000 : ℝ)^1629
        have hw : |(5305598597/10000000000 : ℝ)|=(5305598597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353396073/2500000000 : ℝ)|^2141 ≤ (22319699626719/50000000000000 : ℝ)^1629
        have hw : |(1353396073/2500000000 : ℝ)|=(1353396073/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1978256329/10000000000 : ℝ)|^2141 ≤ (11887810789187/100000000000000 : ℝ)^1629
        have hw : |(-1978256329/10000000000 : ℝ)|=(1978256329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1322_s5_7 (p : ℝ) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1082967437/2500000000 : ℝ)*x 0 + (4511371109/10000000000 : ℝ)*x 1 + (4159171761/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1082967437/2500000000 : ℝ)^2141 ≤ (33302840895051/100000000000000 : ℝ)^1629 := by
    have hnat : (1082967437 : ℕ)^2141*100000000000000^1629 ≤ 33302840895051^1629*2500000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082967437 2500000000 33302840895051 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4511371109/10000000000 : ℝ)^2141 ≤ (35128257513641/100000000000000 : ℝ)^1629 := by
    have hnat : (4511371109 : ℕ)^2141*100000000000000^1629 ≤ 35128257513641^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4511371109 10000000000 35128257513641 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4159171761/10000000000 : ℝ)^2141 ≤ (31568901565607/100000000000000 : ℝ)^1629 := by
    have hnat : (4159171761 : ℕ)^2141*100000000000000^1629 ≤ 31568901565607^1629*10000000000^2141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4159171761 10000000000 31568901565607 100000000000000 2141 1629 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2141/512 : ℝ)) 2141 1629 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1082967437/2500000000 : ℝ), (4511371109/10000000000 : ℝ), (4159171761/10000000000 : ℝ)] ![(33302840895051/100000000000000 : ℝ), (35128257513641/100000000000000 : ℝ), (31568901565607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1082967437/2500000000 : ℝ)|^2141 ≤ (33302840895051/100000000000000 : ℝ)^1629
        have hw : |(1082967437/2500000000 : ℝ)|=(1082967437/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4511371109/10000000000 : ℝ)|^2141 ≤ (35128257513641/100000000000000 : ℝ)^1629
        have hw : |(4511371109/10000000000 : ℝ)|=(4511371109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4159171761/10000000000 : ℝ)|^2141 ≤ (31568901565607/100000000000000 : ℝ)^1629
        have hw : |(4159171761/10000000000 : ℝ)|=(4159171761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1322_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38485273/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3689/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11043/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2773/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (919/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3689/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11043/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3689/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11043/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3689/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11043/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3689/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11043/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3689/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11043/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3689/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11043/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11043/100000 : ℝ) ^ (4281/1024 : ℝ) ≤ (4993884757075029/50000000000000000000 : ℝ) := by
    have hpowers : (11043/100000 : ℝ)^4281 ≤ (4993884757075029/50000000000000000000 : ℝ)^1024 := by
      have hnat : (11043 : ℕ)^4281*50000000000000000000^1024 ≤ 4993884757075029^1024*100000^4281 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11043 100000 4993884757075029 50000000000000000000 4281 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11043/100000 : ℝ)) (X := (4993884757075029/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4281 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3689/25000 : ℝ) ^ (4281/1024 : ℝ) ≤ (33553442616887027/100000000000000000000 : ℝ) := by
    have hpowers : (3689/25000 : ℝ)^4281 ≤ (33553442616887027/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3689 : ℕ)^4281*100000000000000000000^1024 ≤ 33553442616887027^1024*25000^4281 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3689 25000 33553442616887027 100000000000000000000 4281 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3689/25000 : ℝ)) (X := (33553442616887027/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4281 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004993884757075029/25000000000000000000 : ℝ) ≤ (10000477771498027/10000000000000000 : ℝ) ^ (4281/1024 : ℝ) := by
    have hpowers : (25004993884757075029/25000000000000000000 : ℝ)^1024 ≤ (10000477771498027/10000000000000000 : ℝ)^4281 := by
      have hnat : (25004993884757075029 : ℕ)^1024*10000000000000000^4281 ≤ 10000477771498027^4281*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004993884757075029 25000000000000000000 10000477771498027 10000000000000000 1024 4281 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000477771498027/10000000000000000 : ℝ)) (X := (25004993884757075029/25000000000000000000 : ℝ)) (by norm_num) 4281 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20008708242426207417/20000000000000000000 : ℝ) ≤ (2500260329468743/2500000000000000 : ℝ) ^ (4281/1024 : ℝ) := by
    have hpowers : (20008708242426207417/20000000000000000000 : ℝ)^1024 ≤ (2500260329468743/2500000000000000 : ℝ)^4281 := by
      have hnat : (20008708242426207417 : ℕ)^1024*2500000000000000^4281 ≤ 2500260329468743^4281*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20008708242426207417 20000000000000000000 2500260329468743 2500000000000000 1024 4281 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500260329468743/2500000000000000 : ℝ)) (X := (20008708242426207417/20000000000000000000 : ℝ)) (by norm_num) 4281 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033553442616887027/50000000000000000000 : ℝ) ≤ (10001604864251917/10000000000000000 : ℝ) ^ (4281/1024 : ℝ) := by
    have hpowers : (50033553442616887027/50000000000000000000 : ℝ)^1024 ≤ (10001604864251917/10000000000000000 : ℝ)^4281 := by
      have hnat : (50033553442616887027 : ℕ)^1024*10000000000000000^4281 ≤ 10001604864251917^4281*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033553442616887027 50000000000000000000 10001604864251917 10000000000000000 1024 4281 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001604864251917/10000000000000000 : ℝ)) (X := (50033553442616887027/50000000000000000000 : ℝ)) (by norm_num) 4281 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4993884757075029/50000000000000000000 : ℝ) ≤ ((37119327480290966981/37130000000000000000 : ℝ)+2*(112709275389/74260000000000 : ℝ)*(11043/100000 : ℝ))^(4281/1024 : ℝ) := by
    rw [show (37119327480290966981/37130000000000000000 : ℝ)+2*(112709275389/74260000000000 : ℝ)*(11043/100000 : ℝ)=(10000477771498027/10000000000000000 : ℝ) by norm_num, show 1+2*(4993884757075029/50000000000000000000 : ℝ)=(25004993884757075029/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33553442616887027/100000000000000000000 : ℝ)+(4993884757075029/50000000000000000000 : ℝ) ≤ ((37119327480290966981/37130000000000000000 : ℝ)+(112709275389/74260000000000 : ℝ)*((3689/25000 : ℝ)+(11043/100000 : ℝ)))^(4281/1024 : ℝ) := by
    rw [show (37119327480290966981/37130000000000000000 : ℝ)+(112709275389/74260000000000 : ℝ)*((3689/25000 : ℝ)+(11043/100000 : ℝ))=(2500260329468743/2500000000000000 : ℝ) by norm_num, show 1+(33553442616887027/100000000000000000000 : ℝ)+(4993884757075029/50000000000000000000 : ℝ)=(20008708242426207417/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33553442616887027/100000000000000000000 : ℝ) ≤ ((37119327480290966981/37130000000000000000 : ℝ)+2*(112709275389/74260000000000 : ℝ)*(3689/25000 : ℝ))^(4281/1024 : ℝ) := by
    rw [show (37119327480290966981/37130000000000000000 : ℝ)+2*(112709275389/74260000000000 : ℝ)*(3689/25000 : ℝ)=(10001604864251917/10000000000000000 : ℝ) by norm_num, show 1+2*(33553442616887027/100000000000000000000 : ℝ)=(50033553442616887027/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (37119327480290966981/37130000000000000000 : ℝ)*(X 1 0+X 2 0)+(112709275389/74260000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4281/1024 : ℝ)) (lo := (11043/100000 : ℝ)) (hi := (3689/25000 : ℝ)) (c := (37119327480290966981/37130000000000000000 : ℝ)) (alpha := (112709275389/74260000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (37119327480290966981/37130000000000000000 : ℝ)*(X 0 1+X 2 1)+(112709275389/74260000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4281/1024 : ℝ)) (lo := (11043/100000 : ℝ)) (hi := (3689/25000 : ℝ)) (c := (37119327480290966981/37130000000000000000 : ℝ)) (alpha := (112709275389/74260000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (37119327480290966981/37130000000000000000 : ℝ)*(X 0 2+X 1 2)+(112709275389/74260000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4281/1024 : ℝ)) (lo := (11043/100000 : ℝ)) (hi := (3689/25000 : ℝ)) (c := (37119327480290966981/37130000000000000000 : ℝ)) (alpha := (112709275389/74260000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2061318679/10000000000 : ℝ)*X 0 0+(5414200619/10000000000 : ℝ)*X 0 1+(5243548559/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349451561/10000000000 : ℝ)*X 1 0+(-537073023/2500000000 : ℝ)*X 1 1+(1310887141/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337362901/2500000000 : ℝ)*X 2 0+(5243548543/10000000000 : ℝ)*X 2 1+(-2148292063/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2165921807/5000000000 : ℝ)*X 0 0+(519736313/1250000000 : ℝ)*X 0 1+(4512645733/10000000000 : ℝ)*X 0 2+(2165921807/5000000000 : ℝ)*X 1 0+(519736313/1250000000 : ℝ)*X 1 1+(4512645733/10000000000 : ℝ)*X 1 2+(2165921807/5000000000 : ℝ)*X 2 0+(519736313/1250000000 : ℝ)*X 2 1+(4512645733/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1030665631/5000000000 : ℝ)*X 0 0+(5244161717/10000000000 : ℝ)*X 0 1+(5413584291/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326399649/2500000000 : ℝ)*X 1 0+(-1978256329/10000000000 : ℝ)*X 1 1+(1353396073/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305598597/10000000000 : ℝ)*X 2 0+(1353396073/2500000000 : ℝ)*X 2 1+(-1978256329/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1082967437/2500000000 : ℝ)*X 0 0+(4511371109/10000000000 : ℝ)*X 0 1+(4159171761/10000000000 : ℝ)*X 0 2+(1082967437/2500000000 : ℝ)*X 1 0+(4511371109/10000000000 : ℝ)*X 1 1+(4159171761/10000000000 : ℝ)*X 1 2+(1082967437/2500000000 : ℝ)*X 2 0+(4511371109/10000000000 : ℝ)*X 2 1+(4159171761/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1322_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (951193677627678283672876701/185650000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (959558371/100000000000000 : ℝ)*(base19) + (463754247/50000000000000 : ℝ)*(base23) + (42342559/100000000000000 : ℝ)*(lower2) + (119168273/100000000000000 : ℝ)*(upper3) + (26048169/25000000000000 : ℝ)*(upper5) + (433938985870707/10000000000000 : ℝ)*(major0) + (433938985870707/10000000000000 : ℝ)*(major1) + (433938985870707/10000000000000 : ℝ)*(major2) + (732486955985893/12500000000000 : ℝ)*(sp0) + (2929957347090277/50000000000000 : ℝ)*(sp1) + (585991472623043/10000000000000 : ℝ)*(sp2) + (28188540525359/1000000000000 : ℝ)*(sp3) + (1000292589/5000000000000 : ℝ)*(sp4) + (4920176561/50000000000000 : ℝ)*(sp7) + (1409431946444511/50000000000000 : ℝ)*(f.failure) + (1464978913434731/25000000000000 : ℝ)*(f.sum) + (1574804259113/371300000000000000000000000 : ℝ)*base66 + (2332233555078574433/371300000000000000000000000000000 : ℝ)*base68 + (1762481771199774433/371300000000000000000000000000000 : ℝ)*base70 + (2807143467061374433/371300000000000000000000000000000 : ℝ)*base72 + (84360470543/185650000000000000000000000 : ℝ)*base74 + (656459391926225567/371300000000000000000000000000000 : ℝ)*base75 + (3707904244085174433/371300000000000000000000000000000 : ℝ)*base78 + (129665490519225567/371300000000000000000000000000000 : ℝ)*base79 + (126679198477/1856500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (10186503/1250000000000000000000 : ℝ)*base89 + (10186503/1250000000000000000000 : ℝ)*base91 + (10186503/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1523980026000813264746774481/232062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1150860963/100000000000000 : ℝ)*(base19) + (313164773/25000000000000 : ℝ)*(base23) + (66984923/50000000000000 : ℝ)*(upper3) + (45550731/100000000000000 : ℝ)*(lower4) + (134878953/100000000000000 : ℝ)*(upper5) + (1092712660506667/25000000000000 : ℝ)*(major0) + (1092712660506667/25000000000000 : ℝ)*(major1) + (1092712660506667/25000000000000 : ℝ)*(major2) + (11599123269/50000000000000 : ℝ)*(sp1) + (3124079339/12500000000000 : ℝ)*(sp2) + (5902400274671523/100000000000000 : ℝ)*(sp4) + (5902375925564021/100000000000000 : ℝ)*(sp5) + (5902374029377719/100000000000000 : ℝ)*(sp6) + (709825197619533/25000000000000 : ℝ)*(sp7) + (709825197619533/25000000000000 : ℝ)*(f.failure) + (5902400274671523/100000000000000 : ℝ)*(f.sum) + (557070018189/1856500000000000000000000000 : ℝ)*base66 + (4977294416997887673/928250000000000000000000000000000 : ℝ)*base68 + (2829882970412387673/928250000000000000000000000000000 : ℝ)*base70 + (8735628003668637673/928250000000000000000000000000000 : ℝ)*base72 + (19730369900973/3713000000000000000000000000 : ℝ)*base73 + (1926484537206862327/928250000000000000000000000000000 : ℝ)*base75 + (4568971767253887673/928250000000000000000000000000000 : ℝ)*base78 + (5242151593135137673/928250000000000000000000000000000 : ℝ)*base80 + (16760586028767/3713000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (2637509/625000000000000000000 : ℝ)*base89 + (2637509/625000000000000000000 : ℝ)*base91 + (2637509/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1322_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38485273/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3689/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11043/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2773/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (919/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1322_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1322_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38485273/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8093/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4859/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2773/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (919/6250 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1322_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1322_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1322_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4281/1024 : ℝ) ≤ p) (hpb : p ≤ (2141/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38485273/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8093/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4859/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2773/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (919/6250 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1322_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
