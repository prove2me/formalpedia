-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1118_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:08:10.894702+00:00
-- url     : https://prove2.me/submissions/fc9cb62b-8961-42db-90d9-585148432212

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
theorem support_rectangle_w1118_s6_0 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2178382963/10000000000 : ℝ)*x 0 + (2696931863/5000000000 : ℝ)*x 1 + (5264966453/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2178382963/10000000000 : ℝ)^8311 ≤ (6617199611161/50000000000000 : ℝ)^6263 := by
    have hnat : (2178382963 : ℕ)^8311*50000000000000^6263 ≤ 6617199611161^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178382963 10000000000 6617199611161 50000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696931863/5000000000 : ℝ)^8311 ≤ (44078956319601/100000000000000 : ℝ)^6263 := by
    have hnat : (2696931863 : ℕ)^8311*100000000000000^6263 ≤ 44078956319601^6263*5000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696931863 5000000000 44078956319601 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264966453/10000000000 : ℝ)^8311 ≤ (42686644448727/100000000000000 : ℝ)^6263 := by
    have hnat : (5264966453 : ℕ)^8311*100000000000000^6263 ≤ 42686644448727^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264966453 10000000000 42686644448727 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2178382963/10000000000 : ℝ), (2696931863/5000000000 : ℝ), (5264966453/10000000000 : ℝ)] ![(6617199611161/50000000000000 : ℝ), (44078956319601/100000000000000 : ℝ), (42686644448727/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2178382963/10000000000 : ℝ)|^8311 ≤ (6617199611161/50000000000000 : ℝ)^6263
        have hw : |(-2178382963/10000000000 : ℝ)|=(2178382963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696931863/5000000000 : ℝ)|^8311 ≤ (44078956319601/100000000000000 : ℝ)^6263
        have hw : |(2696931863/5000000000 : ℝ)|=(2696931863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264966453/10000000000 : ℝ)|^8311 ≤ (42686644448727/100000000000000 : ℝ)^6263
        have hw : |(5264966453/10000000000 : ℝ)|=(5264966453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1118_s6_1 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336235209/2500000000 : ℝ)*x 0 + (-280471747/1250000000 : ℝ)*x 1 + (658120769/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336235209/2500000000 : ℝ)^8311 ≤ (21774604681431/50000000000000 : ℝ)^6263 := by
    have hnat : (1336235209 : ℕ)^8311*50000000000000^6263 ≤ 21774604681431^6263*2500000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336235209 2500000000 21774604681431 50000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (280471747/1250000000 : ℝ)^8311 ≤ (13764149406211/100000000000000 : ℝ)^6263 := by
    have hnat : (280471747 : ℕ)^8311*100000000000000^6263 ≤ 13764149406211^6263*1250000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280471747 1250000000 13764149406211 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658120769/1250000000 : ℝ)^8311 ≤ (42686641210303/100000000000000 : ℝ)^6263 := by
    have hnat : (658120769 : ℕ)^8311*100000000000000^6263 ≤ 42686641210303^6263*1250000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658120769 1250000000 42686641210303 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336235209/2500000000 : ℝ), (-280471747/1250000000 : ℝ), (658120769/1250000000 : ℝ)] ![(21774604681431/50000000000000 : ℝ), (13764149406211/100000000000000 : ℝ), (42686641210303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336235209/2500000000 : ℝ)|^8311 ≤ (21774604681431/50000000000000 : ℝ)^6263
        have hw : |(1336235209/2500000000 : ℝ)|=(1336235209/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-280471747/1250000000 : ℝ)|^8311 ≤ (13764149406211/100000000000000 : ℝ)^6263
        have hw : |(-280471747/1250000000 : ℝ)|=(280471747/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658120769/1250000000 : ℝ)|^8311 ≤ (42686641210303/100000000000000 : ℝ)^6263
        have hw : |(658120769/1250000000 : ℝ)|=(658120769/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1118_s6_2 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068988233/2000000000 : ℝ)*x 0 + (2632482837/5000000000 : ℝ)*x 1 + (-560943543/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068988233/2000000000 : ℝ)^8311 ≤ (10887303230007/25000000000000 : ℝ)^6263 := by
    have hnat : (1068988233 : ℕ)^8311*25000000000000^6263 ≤ 10887303230007^6263*2000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068988233 2000000000 10887303230007 25000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632482837/5000000000 : ℝ)^8311 ≤ (10671659016889/25000000000000 : ℝ)^6263 := by
    have hnat : (2632482837 : ℕ)^8311*25000000000000^6263 ≤ 10671659016889^6263*5000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632482837 5000000000 10671659016889 25000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (560943543/2500000000 : ℝ)^8311 ≤ (13764151001713/100000000000000 : ℝ)^6263 := by
    have hnat : (560943543 : ℕ)^8311*100000000000000^6263 ≤ 13764151001713^6263*2500000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560943543 2500000000 13764151001713 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068988233/2000000000 : ℝ), (2632482837/5000000000 : ℝ), (-560943543/2500000000 : ℝ)] ![(10887303230007/25000000000000 : ℝ), (10671659016889/25000000000000 : ℝ), (13764151001713/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068988233/2000000000 : ℝ)|^8311 ≤ (10887303230007/25000000000000 : ℝ)^6263
        have hw : |(1068988233/2000000000 : ℝ)|=(1068988233/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632482837/5000000000 : ℝ)|^8311 ≤ (10671659016889/25000000000000 : ℝ)^6263
        have hw : |(2632482837/5000000000 : ℝ)|=(2632482837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-560943543/2500000000 : ℝ)|^8311 ≤ (13764151001713/100000000000000 : ℝ)^6263
        have hw : |(-560943543/2500000000 : ℝ)|=(560943543/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1118_s6_3 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2184022389/5000000000 : ℝ)*x 0 + (4242294707/10000000000 : ℝ)*x 1 + (2248763823/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2184022389/5000000000 : ℝ)^8311 ≤ (33316626102689/100000000000000 : ℝ)^6263 := by
    have hnat : (2184022389 : ℕ)^8311*100000000000000^6263 ≤ 33316626102689^6263*5000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184022389 5000000000 33316626102689 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4242294707/10000000000 : ℝ)^8311 ≤ (6409975408037/20000000000000 : ℝ)^6263 := by
    have hnat : (4242294707 : ℕ)^8311*20000000000000^6263 ≤ 6409975408037^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4242294707 10000000000 6409975408037 20000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2248763823/5000000000 : ℝ)^8311 ≤ (34633496843803/100000000000000 : ℝ)^6263 := by
    have hnat : (2248763823 : ℕ)^8311*100000000000000^6263 ≤ 34633496843803^6263*5000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248763823 5000000000 34633496843803 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2184022389/5000000000 : ℝ), (4242294707/10000000000 : ℝ), (2248763823/5000000000 : ℝ)] ![(33316626102689/100000000000000 : ℝ), (6409975408037/20000000000000 : ℝ), (34633496843803/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2184022389/5000000000 : ℝ)|^8311 ≤ (33316626102689/100000000000000 : ℝ)^6263
        have hw : |(2184022389/5000000000 : ℝ)|=(2184022389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4242294707/10000000000 : ℝ)|^8311 ≤ (6409975408037/20000000000000 : ℝ)^6263
        have hw : |(4242294707/10000000000 : ℝ)|=(4242294707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2248763823/5000000000 : ℝ)|^8311 ≤ (34633496843803/100000000000000 : ℝ)^6263
        have hw : |(2248763823/5000000000 : ℝ)|=(2248763823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1118_s6_4 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-272298497/1250000000 : ℝ)*x 0 + (2632645767/5000000000 : ℝ)*x 1 + (84274023/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (272298497/1250000000 : ℝ)^8311 ≤ (3308609909241/25000000000000 : ℝ)^6263 := by
    have hnat : (272298497 : ℕ)^8311*25000000000000^6263 ≤ 3308609909241^6263*1250000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272298497 1250000000 3308609909241 25000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632645767/5000000000 : ℝ)^8311 ≤ (42690141993239/100000000000000 : ℝ)^6263 := by
    have hnat : (2632645767 : ℕ)^8311*100000000000000^6263 ≤ 42690141993239^6263*5000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632645767 5000000000 42690141993239 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84274023/156250000 : ℝ)^8311 ≤ (22037709176399/50000000000000 : ℝ)^6263 := by
    have hnat : (84274023 : ℕ)^8311*50000000000000^6263 ≤ 22037709176399^6263*156250000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84274023 156250000 22037709176399 50000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-272298497/1250000000 : ℝ), (2632645767/5000000000 : ℝ), (84274023/156250000 : ℝ)] ![(3308609909241/25000000000000 : ℝ), (42690141993239/100000000000000 : ℝ), (22037709176399/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-272298497/1250000000 : ℝ)|^8311 ≤ (3308609909241/25000000000000 : ℝ)^6263
        have hw : |(-272298497/1250000000 : ℝ)|=(272298497/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632645767/5000000000 : ℝ)|^8311 ≤ (42690141993239/100000000000000 : ℝ)^6263
        have hw : |(2632645767/5000000000 : ℝ)|=(2632645767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84274023/156250000 : ℝ)|^8311 ≤ (22037709176399/50000000000000 : ℝ)^6263
        have hw : |(84274023/156250000 : ℝ)|=(84274023/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1118_s6_5 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (664042841/1250000000 : ℝ)*x 0 + (-528800661/2500000000 : ℝ)*x 1 + (1078707491/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664042841/1250000000 : ℝ)^8311 ≤ (172788435057/400000000000 : ℝ)^6263 := by
    have hnat : (664042841 : ℕ)^8311*400000000000^6263 ≤ 172788435057^6263*1250000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664042841 1250000000 172788435057 400000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (528800661/2500000000 : ℝ)^8311 ≤ (12727473049029/100000000000000 : ℝ)^6263 := by
    have hnat : (528800661 : ℕ)^8311*100000000000000^6263 ≤ 12727473049029^6263*2500000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528800661 2500000000 12727473049029 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078707491/2000000000 : ℝ)^8311 ≤ (344339204441/781250000000 : ℝ)^6263 := by
    have hnat : (1078707491 : ℕ)^8311*781250000000^6263 ≤ 344339204441^6263*2000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078707491 2000000000 344339204441 781250000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664042841/1250000000 : ℝ), (-528800661/2500000000 : ℝ), (1078707491/2000000000 : ℝ)] ![(172788435057/400000000000 : ℝ), (12727473049029/100000000000000 : ℝ), (344339204441/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664042841/1250000000 : ℝ)|^8311 ≤ (172788435057/400000000000 : ℝ)^6263
        have hw : |(664042841/1250000000 : ℝ)|=(664042841/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-528800661/2500000000 : ℝ)|^8311 ≤ (12727473049029/100000000000000 : ℝ)^6263
        have hw : |(-528800661/2500000000 : ℝ)|=(528800661/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078707491/2000000000 : ℝ)|^8311 ≤ (344339204441/781250000000 : ℝ)^6263
        have hw : |(1078707491/2000000000 : ℝ)|=(1078707491/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1118_s6_6 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656171381/5000000000 : ℝ)*x 0 + (5393537379/10000000000 : ℝ)*x 1 + (-1057601351/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656171381/5000000000 : ℝ)^8311 ≤ (345576873049/800000000000 : ℝ)^6263 := by
    have hnat : (2656171381 : ℕ)^8311*800000000000^6263 ≤ 345576873049^6263*5000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656171381 5000000000 345576873049 800000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393537379/10000000000 : ℝ)^8311 ≤ (5509427168037/12500000000000 : ℝ)^6263 := by
    have hnat : (5393537379 : ℕ)^8311*12500000000000^6263 ≤ 5509427168037^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393537379 10000000000 5509427168037 12500000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1057601351/5000000000 : ℝ)^8311 ≤ (795467094509/6250000000000 : ℝ)^6263 := by
    have hnat : (1057601351 : ℕ)^8311*6250000000000^6263 ≤ 795467094509^6263*5000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057601351 5000000000 795467094509 6250000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656171381/5000000000 : ℝ), (5393537379/10000000000 : ℝ), (-1057601351/5000000000 : ℝ)] ![(345576873049/800000000000 : ℝ), (5509427168037/12500000000000 : ℝ), (795467094509/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656171381/5000000000 : ℝ)|^8311 ≤ (345576873049/800000000000 : ℝ)^6263
        have hw : |(2656171381/5000000000 : ℝ)|=(2656171381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393537379/10000000000 : ℝ)|^8311 ≤ (5509427168037/12500000000000 : ℝ)^6263
        have hw : |(5393537379/10000000000 : ℝ)|=(5393537379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1057601351/5000000000 : ℝ)|^8311 ≤ (795467094509/6250000000000 : ℝ)^6263
        have hw : |(-1057601351/5000000000 : ℝ)|=(1057601351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1118_s6_7 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (174722213/400000000 : ℝ)*x 0 + (2248441347/5000000000 : ℝ)*x 1 + (4242941419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (174722213/400000000 : ℝ)^8311 ≤ (16658366427087/50000000000000 : ℝ)^6263 := by
    have hnat : (174722213 : ℕ)^8311*50000000000000^6263 ≤ 16658366427087^6263*400000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174722213 400000000 16658366427087 50000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2248441347/5000000000 : ℝ)^8311 ≤ (8656726615471/25000000000000 : ℝ)^6263 := by
    have hnat : (2248441347 : ℕ)^8311*25000000000000^6263 ≤ 8656726615471^6263*5000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248441347 5000000000 8656726615471 25000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4242941419/10000000000 : ℝ)^8311 ≤ (16028180334523/50000000000000 : ℝ)^6263 := by
    have hnat : (4242941419 : ℕ)^8311*50000000000000^6263 ≤ 16028180334523^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4242941419 10000000000 16028180334523 50000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(174722213/400000000 : ℝ), (2248441347/5000000000 : ℝ), (4242941419/10000000000 : ℝ)] ![(16658366427087/50000000000000 : ℝ), (8656726615471/25000000000000 : ℝ), (16028180334523/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(174722213/400000000 : ℝ)|^8311 ≤ (16658366427087/50000000000000 : ℝ)^6263
        have hw : |(174722213/400000000 : ℝ)|=(174722213/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2248441347/5000000000 : ℝ)|^8311 ≤ (8656726615471/25000000000000 : ℝ)^6263
        have hw : |(2248441347/5000000000 : ℝ)|=(2248441347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4242941419/10000000000 : ℝ)|^8311 ≤ (16028180334523/50000000000000 : ℝ)^6263
        have hw : |(4242941419/10000000000 : ℝ)|=(4242941419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1118_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29801131/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14079/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11279/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11313/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3511/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14079/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11279/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14079/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11279/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14079/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11279/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14079/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11279/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14079/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11279/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14079/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11279/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11279/100000 : ℝ) ^ (4155/1024 : ℝ) ≤ (14271738642481009/100000000000000000000 : ℝ) := by
    have hpowers : (11279/100000 : ℝ)^4155 ≤ (14271738642481009/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11279 : ℕ)^4155*100000000000000000000^1024 ≤ 14271738642481009^1024*100000^4155 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11279 100000 14271738642481009 100000000000000000000 4155 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11279/100000 : ℝ)) (X := (14271738642481009/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4155 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14079/100000 : ℝ) ^ (4155/1024 : ℝ) ≤ (17546897628196763/50000000000000000000 : ℝ) := by
    have hpowers : (14079/100000 : ℝ)^4155 ≤ (17546897628196763/50000000000000000000 : ℝ)^1024 := by
      have hnat : (14079 : ℕ)^4155*50000000000000000000^1024 ≤ 17546897628196763^1024*100000^4155 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14079 100000 17546897628196763 50000000000000000000 4155 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14079/100000 : ℝ)) (X := (17546897628196763/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4155 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014271738642481009/50000000000000000000 : ℝ) ≤ (5000351689264649/5000000000000000 : ℝ) ^ (4155/1024 : ℝ) := by
    have hpowers : (50014271738642481009/50000000000000000000 : ℝ)^1024 ≤ (5000351689264649/5000000000000000 : ℝ)^4155 := by
      have hnat : (50014271738642481009 : ℕ)^1024*5000000000000000^4155 ≤ 5000351689264649^4155*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014271738642481009 50000000000000000000 5000351689264649 5000000000000000 1024 4155 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000351689264649/5000000000000000 : ℝ)) (X := (50014271738642481009/50000000000000000000 : ℝ)) (by norm_num) 4155 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009873106779774907/20000000000000000000 : ℝ) ≤ (5000608193829367/5000000000000000 : ℝ) ^ (4155/1024 : ℝ) := by
    have hpowers : (20009873106779774907/20000000000000000000 : ℝ)^1024 ≤ (5000608193829367/5000000000000000 : ℝ)^4155 := by
      have hnat : (20009873106779774907 : ℕ)^1024*5000000000000000^4155 ≤ 5000608193829367^4155*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009873106779774907 20000000000000000000 5000608193829367 5000000000000000 1024 4155 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000608193829367/5000000000000000 : ℝ)) (X := (20009873106779774907/20000000000000000000 : ℝ)) (by norm_num) 4155 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017546897628196763/25000000000000000000 : ℝ) ≤ (1000172939678817/1000000000000000 : ℝ) ^ (4155/1024 : ℝ) := by
    have hpowers : (25017546897628196763/25000000000000000000 : ℝ)^1024 ≤ (1000172939678817/1000000000000000 : ℝ)^4155 := by
      have hnat : (25017546897628196763 : ℕ)^1024*1000000000000000^4155 ≤ 1000172939678817^4155*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017546897628196763 25000000000000000000 1000172939678817 1000000000000000 1024 4155 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000172939678817/1000000000000000 : ℝ)) (X := (25017546897628196763/25000000000000000000 : ℝ)) (by norm_num) 4155 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14271738642481009/100000000000000000000 : ℝ) ≤ ((3498799624992527139/3500000000000000000 : ℝ)+2*(128252282359/70000000000000 : ℝ)*(11279/100000 : ℝ))^(4155/1024 : ℝ) := by
    rw [show (3498799624992527139/3500000000000000000 : ℝ)+2*(128252282359/70000000000000 : ℝ)*(11279/100000 : ℝ)=(5000351689264649/5000000000000000 : ℝ) by norm_num, show 1+2*(14271738642481009/100000000000000000000 : ℝ)=(50014271738642481009/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17546897628196763/50000000000000000000 : ℝ)+(14271738642481009/100000000000000000000 : ℝ) ≤ ((3498799624992527139/3500000000000000000 : ℝ)+(128252282359/70000000000000 : ℝ)*((14079/100000 : ℝ)+(11279/100000 : ℝ)))^(4155/1024 : ℝ) := by
    rw [show (3498799624992527139/3500000000000000000 : ℝ)+(128252282359/70000000000000 : ℝ)*((14079/100000 : ℝ)+(11279/100000 : ℝ))=(5000608193829367/5000000000000000 : ℝ) by norm_num, show 1+(17546897628196763/50000000000000000000 : ℝ)+(14271738642481009/100000000000000000000 : ℝ)=(20009873106779774907/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17546897628196763/50000000000000000000 : ℝ) ≤ ((3498799624992527139/3500000000000000000 : ℝ)+2*(128252282359/70000000000000 : ℝ)*(14079/100000 : ℝ))^(4155/1024 : ℝ) := by
    rw [show (3498799624992527139/3500000000000000000 : ℝ)+2*(128252282359/70000000000000 : ℝ)*(14079/100000 : ℝ)=(1000172939678817/1000000000000000 : ℝ) by norm_num, show 1+2*(17546897628196763/50000000000000000000 : ℝ)=(25017546897628196763/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3498799624992527139/3500000000000000000 : ℝ)*(X 1 0+X 2 0)+(128252282359/70000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4155/1024 : ℝ)) (lo := (11279/100000 : ℝ)) (hi := (14079/100000 : ℝ)) (c := (3498799624992527139/3500000000000000000 : ℝ)) (alpha := (128252282359/70000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3498799624992527139/3500000000000000000 : ℝ)*(X 0 1+X 2 1)+(128252282359/70000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4155/1024 : ℝ)) (lo := (11279/100000 : ℝ)) (hi := (14079/100000 : ℝ)) (c := (3498799624992527139/3500000000000000000 : ℝ)) (alpha := (128252282359/70000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3498799624992527139/3500000000000000000 : ℝ)*(X 0 2+X 1 2)+(128252282359/70000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4155/1024 : ℝ)) (lo := (11279/100000 : ℝ)) (hi := (14079/100000 : ℝ)) (c := (3498799624992527139/3500000000000000000 : ℝ)) (alpha := (128252282359/70000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2178382963/10000000000 : ℝ)*X 0 0+(2696931863/5000000000 : ℝ)*X 0 1+(5264966453/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336235209/2500000000 : ℝ)*X 1 0+(-280471747/1250000000 : ℝ)*X 1 1+(658120769/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068988233/2000000000 : ℝ)*X 2 0+(2632482837/5000000000 : ℝ)*X 2 1+(-560943543/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2184022389/5000000000 : ℝ)*X 0 0+(4242294707/10000000000 : ℝ)*X 0 1+(2248763823/5000000000 : ℝ)*X 0 2+(2184022389/5000000000 : ℝ)*X 1 0+(4242294707/10000000000 : ℝ)*X 1 1+(2248763823/5000000000 : ℝ)*X 1 2+(2184022389/5000000000 : ℝ)*X 2 0+(4242294707/10000000000 : ℝ)*X 2 1+(2248763823/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-272298497/1250000000 : ℝ)*X 0 0+(2632645767/5000000000 : ℝ)*X 0 1+(84274023/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((664042841/1250000000 : ℝ)*X 1 0+(-528800661/2500000000 : ℝ)*X 1 1+(1078707491/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656171381/5000000000 : ℝ)*X 2 0+(5393537379/10000000000 : ℝ)*X 2 1+(-1057601351/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((174722213/400000000 : ℝ)*X 0 0+(2248441347/5000000000 : ℝ)*X 0 1+(4242941419/10000000000 : ℝ)*X 0 2+(174722213/400000000 : ℝ)*X 1 0+(2248441347/5000000000 : ℝ)*X 1 1+(4242941419/10000000000 : ℝ)*X 1 2+(174722213/400000000 : ℝ)*X 2 0+(2248441347/5000000000 : ℝ)*X 2 1+(4242941419/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (412736942295379636038868167/43750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (215828759/12500000000000 : ℝ)*(base19) + (2197426461/100000000000000 : ℝ)*(base23) + (56882601/50000000000000 : ℝ)*(upper2) + (225595109/100000000000000 : ℝ)*(upper3) + (11737129/10000000000000 : ℝ)*(upper4) + (1459528237259083/25000000000000 : ℝ)*(major0) + (1459528237259083/25000000000000 : ℝ)*(major1) + (1459528237259083/25000000000000 : ℝ)*(major2) + (193953744895409/2500000000000 : ℝ)*(sp0) + (7758175948635997/100000000000000 : ℝ)*(sp1) + (7758175477839607/100000000000000 : ℝ)*(sp2) + (391801516022107/10000000000000 : ℝ)*(sp3) + (27879449709/100000000000000 : ℝ)*(sp4) + (1309924771/4000000000000 : ℝ)*(sp7) + (1959023954170173/50000000000000 : ℝ)*(f.failure) + (7758177675266069/100000000000000 : ℝ)*(f.sum) + (232115308207/218750000000000000000000000 : ℝ)*base66 + (336835556916603537/87500000000000000000000000000000 : ℝ)*base67 + (953894756054103537/87500000000000000000000000000000 : ℝ)*base69 + (807960842579103537/87500000000000000000000000000000 : ℝ)*base71 + (746462807297/875000000000000000000000000 : ℝ)*base73 + (481901659654103537/87500000000000000000000000000000 : ℝ)*base75 + (645486584566603537/87500000000000000000000000000000 : ℝ)*base77 + (1002288006116603537/87500000000000000000000000000000 : ℝ)*base79 + (178207934539/437500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (1865663/1000000000000000000000 : ℝ)*base89 + (1865663/1000000000000000000000 : ℝ)*base91 + (1865663/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1614381478542752697409211163/175000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3931929/195312500000 : ℝ)*(base19) + (512586509/25000000000000 : ℝ)*(base23) + (46567747/25000000000000 : ℝ)*(upper3) + (10229991/100000000000000 : ℝ)*(lower4) + (124163309/50000000000000 : ℝ)*(upper5) + (5867719088632739/100000000000000 : ℝ)*(major0) + (5867719088632739/100000000000000 : ℝ)*(major1) + (5867719088632739/100000000000000 : ℝ)*(major2) + (7076055587/12500000000000 : ℝ)*(sp1) + (12849734047/25000000000000 : ℝ)*(sp2) + (1949380205792777/25000000000000 : ℝ)*(sp4) + (1559492440315753/20000000000000 : ℝ)*(sp5) + (1949366843472221/25000000000000 : ℝ)*(sp6) + (3937917046593123/100000000000000 : ℝ)*(sp7) + (3937917046593123/100000000000000 : ℝ)*(f.failure) + (1949380205792777/25000000000000 : ℝ)*(f.sum) + (4591915566801/3500000000000000000000000000 : ℝ)*base65 + (1624289108473546279/350000000000000000000000000000000 : ℝ)*base68 + (3091141726123546279/350000000000000000000000000000000 : ℝ)*base70 + (3263533090576453721/350000000000000000000000000000000 : ℝ)*base71 + (1494083630301/3500000000000000000000000000 : ℝ)*base73 + (8025551587973546279/350000000000000000000000000000000 : ℝ)*base76 + (3720612142376453721/350000000000000000000000000000000 : ℝ)*base77 + (4563311235073546279/350000000000000000000000000000000 : ℝ)*base80 + (15188082664199/3500000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (17777887/2000000000000000000000 : ℝ)*base90 + (17777887/2000000000000000000000 : ℝ)*base92 + (17777887/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1118_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29801131/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14079/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11279/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11313/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3511/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1118_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1118_s7_0 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-108920601/500000000 : ℝ)*x 0 + (1348376527/2500000000 : ℝ)*x 1 + (5265305129/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (108920601/500000000 : ℝ)^8311 ≤ (13234633479329/100000000000000 : ℝ)^6263 := by
    have hnat : (108920601 : ℕ)^8311*100000000000000^6263 ≤ 13234633479329^6263*500000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108920601 500000000 13234633479329 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348376527/2500000000 : ℝ)^8311 ≤ (44075078238691/100000000000000 : ℝ)^6263 := by
    have hnat : (1348376527 : ℕ)^8311*100000000000000^6263 ≤ 44075078238691^6263*2500000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348376527 2500000000 44075078238691 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265305129/10000000000 : ℝ)^8311 ≤ (426902882633/1000000000000 : ℝ)^6263 := by
    have hnat : (5265305129 : ℕ)^8311*1000000000000^6263 ≤ 426902882633^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265305129 10000000000 426902882633 1000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-108920601/500000000 : ℝ), (1348376527/2500000000 : ℝ), (5265305129/10000000000 : ℝ)] ![(13234633479329/100000000000000 : ℝ), (44075078238691/100000000000000 : ℝ), (426902882633/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-108920601/500000000 : ℝ)|^8311 ≤ (13234633479329/100000000000000 : ℝ)^6263
        have hw : |(-108920601/500000000 : ℝ)|=(108920601/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348376527/2500000000 : ℝ)|^8311 ≤ (44075078238691/100000000000000 : ℝ)^6263
        have hw : |(1348376527/2500000000 : ℝ)|=(1348376527/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265305129/10000000000 : ℝ)|^8311 ≤ (426902882633/1000000000000 : ℝ)^6263
        have hw : |(5265305129/10000000000 : ℝ)|=(5265305129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1118_s7_1 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (10689703/20000000 : ℝ)*x 0 + (-560861119/2500000000 : ℝ)*x 1 + (658163153/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10689703/20000000 : ℝ)^8311 ≤ (43548243459763/100000000000000 : ℝ)^6263 := by
    have hnat : (10689703 : ℕ)^8311*100000000000000^6263 ≤ 43548243459763^6263*20000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10689703 20000000 43548243459763 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (560861119/2500000000 : ℝ)^8311 ≤ (6880733618623/50000000000000 : ℝ)^6263 := by
    have hnat : (560861119 : ℕ)^8311*50000000000000^6263 ≤ 6880733618623^6263*2500000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560861119 2500000000 6880733618623 50000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658163153/1250000000 : ℝ)^8311 ≤ (8538057857083/20000000000000 : ℝ)^6263 := by
    have hnat : (658163153 : ℕ)^8311*20000000000000^6263 ≤ 8538057857083^6263*1250000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658163153 1250000000 8538057857083 20000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(10689703/20000000 : ℝ), (-560861119/2500000000 : ℝ), (658163153/1250000000 : ℝ)] ![(43548243459763/100000000000000 : ℝ), (6880733618623/50000000000000 : ℝ), (8538057857083/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(10689703/20000000 : ℝ)|^8311 ≤ (43548243459763/100000000000000 : ℝ)^6263
        have hw : |(10689703/20000000 : ℝ)|=(10689703/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-560861119/2500000000 : ℝ)|^8311 ≤ (6880733618623/50000000000000 : ℝ)^6263
        have hw : |(-560861119/2500000000 : ℝ)|=(560861119/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658163153/1250000000 : ℝ)|^8311 ≤ (8538057857083/20000000000000 : ℝ)^6263
        have hw : |(658163153/1250000000 : ℝ)|=(658163153/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1118_s7_2 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068970343/2000000000 : ℝ)*x 0 + (5265305071/10000000000 : ℝ)*x 1 + (-2243444393/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068970343/2000000000 : ℝ)^8311 ≤ (21774122892171/50000000000000 : ℝ)^6263 := by
    have hnat : (1068970343 : ℕ)^8311*50000000000000^6263 ≤ 21774122892171^6263*2000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068970343 2000000000 21774122892171 50000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265305071/10000000000 : ℝ)^8311 ≤ (42690287639271/100000000000000 : ℝ)^6263 := by
    have hnat : (5265305071 : ℕ)^8311*100000000000000^6263 ≤ 42690287639271^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265305071 10000000000 42690287639271 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2243444393/10000000000 : ℝ)^8311 ≤ (430045830051/3125000000000 : ℝ)^6263 := by
    have hnat : (2243444393 : ℕ)^8311*3125000000000^6263 ≤ 430045830051^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2243444393 10000000000 430045830051 3125000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068970343/2000000000 : ℝ), (5265305071/10000000000 : ℝ), (-2243444393/10000000000 : ℝ)] ![(21774122892171/50000000000000 : ℝ), (42690287639271/100000000000000 : ℝ), (430045830051/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068970343/2000000000 : ℝ)|^8311 ≤ (21774122892171/50000000000000 : ℝ)^6263
        have hw : |(1068970343/2000000000 : ℝ)|=(1068970343/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265305071/10000000000 : ℝ)|^8311 ≤ (42690287639271/100000000000000 : ℝ)^6263
        have hw : |(5265305071/10000000000 : ℝ)|=(5265305071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2243444393/10000000000 : ℝ)|^8311 ≤ (430045830051/3125000000000 : ℝ)^6263
        have hw : |(-2243444393/10000000000 : ℝ)|=(2243444393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1118_s7_3 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4368063217/10000000000 : ℝ)*x 0 + (4242982487/10000000000 : ℝ)*x 1 + (2248417291/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4368063217/10000000000 : ℝ)^8311 ≤ (8329203183281/25000000000000 : ℝ)^6263 := by
    have hnat : (4368063217 : ℕ)^8311*25000000000000^6263 ≤ 8329203183281^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4368063217 10000000000 8329203183281 25000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4242982487/10000000000 : ℝ)^8311 ≤ (32056772408317/100000000000000 : ℝ)^6263 := by
    have hnat : (4242982487 : ℕ)^8311*100000000000000^6263 ≤ 32056772408317^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4242982487 10000000000 32056772408317 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2248417291/5000000000 : ℝ)^8311 ≤ (34626414846283/100000000000000 : ℝ)^6263 := by
    have hnat : (2248417291 : ℕ)^8311*100000000000000^6263 ≤ 34626414846283^6263*5000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248417291 5000000000 34626414846283 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4368063217/10000000000 : ℝ), (4242982487/10000000000 : ℝ), (2248417291/5000000000 : ℝ)] ![(8329203183281/25000000000000 : ℝ), (32056772408317/100000000000000 : ℝ), (34626414846283/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4368063217/10000000000 : ℝ)|^8311 ≤ (8329203183281/25000000000000 : ℝ)^6263
        have hw : |(4368063217/10000000000 : ℝ)|=(4368063217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4242982487/10000000000 : ℝ)|^8311 ≤ (32056772408317/100000000000000 : ℝ)^6263
        have hw : |(4242982487/10000000000 : ℝ)|=(4242982487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2248417291/5000000000 : ℝ)|^8311 ≤ (34626414846283/100000000000000 : ℝ)^6263
        have hw : |(2248417291/5000000000 : ℝ)|=(2248417291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1118_s7_4 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-544604257/2500000000 : ℝ)*x 0 + (5265627193/10000000000 : ℝ)*x 1 + (5393182839/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (544604257/2500000000 : ℝ)^8311 ≤ (13234673853837/100000000000000 : ℝ)^6263 := by
    have hnat : (544604257 : ℕ)^8311*100000000000000^6263 ≤ 13234673853837^6263*2500000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544604257 2500000000 13234673853837 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265627193/10000000000 : ℝ)^8311 ≤ (8538750684097/20000000000000 : ℝ)^6263 := by
    have hnat : (5265627193 : ℕ)^8311*20000000000000^6263 ≤ 8538750684097^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265627193 10000000000 8538750684097 20000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393182839/10000000000 : ℝ)^8311 ≤ (44071572717543/100000000000000 : ℝ)^6263 := by
    have hnat : (5393182839 : ℕ)^8311*100000000000000^6263 ≤ 44071572717543^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393182839 10000000000 44071572717543 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-544604257/2500000000 : ℝ), (5265627193/10000000000 : ℝ), (5393182839/10000000000 : ℝ)] ![(13234673853837/100000000000000 : ℝ), (8538750684097/20000000000000 : ℝ), (44071572717543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-544604257/2500000000 : ℝ)|^8311 ≤ (13234673853837/100000000000000 : ℝ)^6263
        have hw : |(-544604257/2500000000 : ℝ)|=(544604257/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265627193/10000000000 : ℝ)|^8311 ≤ (8538750684097/20000000000000 : ℝ)^6263
        have hw : |(5265627193/10000000000 : ℝ)|=(5265627193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393182839/10000000000 : ℝ)|^8311 ≤ (44071572717543/100000000000000 : ℝ)^6263
        have hw : |(5393182839/10000000000 : ℝ)|=(5393182839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1118_s7_5 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656214777/5000000000 : ℝ)*x 0 + (-66111463/312500000 : ℝ)*x 1 + (53931829/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656214777/5000000000 : ℝ)^8311 ≤ (21599022829083/50000000000000 : ℝ)^6263 := by
    have hnat : (2656214777 : ℕ)^8311*50000000000000^6263 ≤ 21599022829083^6263*5000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656214777 5000000000 21599022829083 50000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (66111463/312500000 : ℝ)^8311 ≤ (12730380951603/100000000000000 : ℝ)^6263 := by
    have hnat : (66111463 : ℕ)^8311*100000000000000^6263 ≤ 12730380951603^6263*312500000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66111463 312500000 12730380951603 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (53931829/100000000 : ℝ)^8311 ≤ (44071573379019/100000000000000 : ℝ)^6263 := by
    have hnat : (53931829 : ℕ)^8311*100000000000000^6263 ≤ 44071573379019^6263*100000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53931829 100000000 44071573379019 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656214777/5000000000 : ℝ), (-66111463/312500000 : ℝ), (53931829/100000000 : ℝ)] ![(21599022829083/50000000000000 : ℝ), (12730380951603/100000000000000 : ℝ), (44071573379019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656214777/5000000000 : ℝ)|^8311 ≤ (21599022829083/50000000000000 : ℝ)^6263
        have hw : |(2656214777/5000000000 : ℝ)|=(2656214777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-66111463/312500000 : ℝ)|^8311 ≤ (12730380951603/100000000000000 : ℝ)^6263
        have hw : |(-66111463/312500000 : ℝ)|=(66111463/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(53931829/100000000 : ℝ)|^8311 ≤ (44071573379019/100000000000000 : ℝ)^6263
        have hw : |(53931829/100000000 : ℝ)|=(53931829/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1118_s7_6 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328107399/2500000000 : ℝ)*x 0 + (5393182831/10000000000 : ℝ)*x 1 + (-2115566853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328107399/2500000000 : ℝ)^8311 ≤ (43198046111367/100000000000000 : ℝ)^6263 := by
    have hnat : (1328107399 : ℕ)^8311*100000000000000^6263 ≤ 43198046111367^6263*2500000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328107399 2500000000 43198046111367 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393182831/10000000000 : ℝ)^8311 ≤ (5508946578849/12500000000000 : ℝ)^6263 := by
    have hnat : (5393182831 : ℕ)^8311*12500000000000^6263 ≤ 5508946578849^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393182831 10000000000 5508946578849 12500000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2115566853/10000000000 : ℝ)^8311 ≤ (2546076249411/20000000000000 : ℝ)^6263 := by
    have hnat : (2115566853 : ℕ)^8311*20000000000000^6263 ≤ 2546076249411^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115566853 10000000000 2546076249411 20000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328107399/2500000000 : ℝ), (5393182831/10000000000 : ℝ), (-2115566853/10000000000 : ℝ)] ![(43198046111367/100000000000000 : ℝ), (5508946578849/12500000000000 : ℝ), (2546076249411/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328107399/2500000000 : ℝ)|^8311 ≤ (43198046111367/100000000000000 : ℝ)^6263
        have hw : |(1328107399/2500000000 : ℝ)|=(1328107399/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393182831/10000000000 : ℝ)|^8311 ≤ (5508946578849/12500000000000 : ℝ)^6263
        have hw : |(5393182831/10000000000 : ℝ)|=(5393182831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2115566853/10000000000 : ℝ)|^8311 ≤ (2546076249411/20000000000000 : ℝ)^6263
        have hw : |(-2115566853/10000000000 : ℝ)|=(2115566853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1118_s7_7 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4368072957/10000000000 : ℝ)*x 0 + (4496197021/10000000000 : ℝ)*x 1 + (848724483/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4368072957/10000000000 : ℝ)^8311 ≤ (33316911316689/100000000000000 : ℝ)^6263 := by
    have hnat : (4368072957 : ℕ)^8311*100000000000000^6263 ≤ 33316911316689^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4368072957 10000000000 33316911316689 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4496197021/10000000000 : ℝ)^8311 ≤ (2163743769699/6250000000000 : ℝ)^6263 := by
    have hnat : (4496197021 : ℕ)^8311*6250000000000^6263 ≤ 2163743769699^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4496197021 10000000000 2163743769699 6250000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (848724483/2000000000 : ℝ)^8311 ≤ (32063188362401/100000000000000 : ℝ)^6263 := by
    have hnat : (848724483 : ℕ)^8311*100000000000000^6263 ≤ 32063188362401^6263*2000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848724483 2000000000 32063188362401 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4368072957/10000000000 : ℝ), (4496197021/10000000000 : ℝ), (848724483/2000000000 : ℝ)] ![(33316911316689/100000000000000 : ℝ), (2163743769699/6250000000000 : ℝ), (32063188362401/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4368072957/10000000000 : ℝ)|^8311 ≤ (33316911316689/100000000000000 : ℝ)^6263
        have hw : |(4368072957/10000000000 : ℝ)|=(4368072957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4496197021/10000000000 : ℝ)|^8311 ≤ (2163743769699/6250000000000 : ℝ)^6263
        have hw : |(4496197021/10000000000 : ℝ)|=(4496197021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(848724483/2000000000 : ℝ)|^8311 ≤ (32063188362401/100000000000000 : ℝ)^6263
        have hw : |(848724483/2000000000 : ℝ)|=(848724483/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1118_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29801131/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3511/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11313/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11321/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3509/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3511/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11313/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3511/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11313/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3511/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11313/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3511/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11313/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3511/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11313/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3511/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11313/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11313/100000 : ℝ) ^ (4155/1024 : ℝ) ≤ (3611777357777699/25000000000000000000 : ℝ) := by
    have hpowers : (11313/100000 : ℝ)^4155 ≤ (3611777357777699/25000000000000000000 : ℝ)^1024 := by
      have hnat : (11313 : ℕ)^4155*25000000000000000000^1024 ≤ 3611777357777699^1024*100000^4155 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11313 100000 3611777357777699 25000000000000000000 4155 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11313/100000 : ℝ)) (X := (3611777357777699/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4155 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3511/25000 : ℝ) ^ (4155/1024 : ℝ) ≤ (8685285732198987/25000000000000000000 : ℝ) := by
    have hpowers : (3511/25000 : ℝ)^4155 ≤ (8685285732198987/25000000000000000000 : ℝ)^1024 := by
      have hnat : (3511 : ℕ)^4155*25000000000000000000^1024 ≤ 8685285732198987^1024*25000^4155 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3511 25000 8685285732198987 25000000000000000000 4155 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3511/25000 : ℝ)) (X := (8685285732198987/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4155 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503611777357777699/12500000000000000000 : ℝ) ≤ (10000712020687389/10000000000000000 : ℝ) ^ (4155/1024 : ℝ) := by
    have hpowers : (12503611777357777699/12500000000000000000 : ℝ)^1024 ≤ (10000712020687389/10000000000000000 : ℝ)^4155 := by
      have hnat : (12503611777357777699 : ℕ)^1024*10000000000000000^4155 ≤ 10000712020687389^4155*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503611777357777699 12500000000000000000 10000712020687389 10000000000000000 1024 4155 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000712020687389/10000000000000000 : ℝ)) (X := (12503611777357777699/12500000000000000000 : ℝ)) (by norm_num) 4155 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12506148531544988343/12500000000000000000 : ℝ) ≤ (10001212020175801/10000000000000000 : ℝ) ^ (4155/1024 : ℝ) := by
    have hpowers : (12506148531544988343/12500000000000000000 : ℝ)^1024 ≤ (10001212020175801/10000000000000000 : ℝ)^4155 := by
      have hnat : (12506148531544988343 : ℕ)^1024*10000000000000000^4155 ≤ 10001212020175801^4155*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506148531544988343 12500000000000000000 10001212020175801 10000000000000000 1024 4155 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001212020175801/10000000000000000 : ℝ)) (X := (12506148531544988343/12500000000000000000 : ℝ)) (by norm_num) 4155 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508685285732198987/12500000000000000000 : ℝ) ≤ (10001712019664213/10000000000000000 : ℝ) ^ (4155/1024 : ℝ) := by
    have hpowers : (12508685285732198987/12500000000000000000 : ℝ)^1024 ≤ (10001712019664213/10000000000000000 : ℝ)^4155 := by
      have hnat : (12508685285732198987 : ℕ)^1024*10000000000000000^4155 ≤ 10001712019664213^4155*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508685285732198987 12500000000000000000 10001712019664213 10000000000000000 1024 4155 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001712019664213/10000000000000000 : ℝ)) (X := (12508685285732198987/12500000000000000000 : ℝ)) (by norm_num) 4155 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3611777357777699/25000000000000000000 : ℝ) ≤ ((27300631540072449447/27310000000000000000 : ℝ)+2*(124999872103/68275000000000 : ℝ)*(11313/100000 : ℝ))^(4155/1024 : ℝ) := by
    rw [show (27300631540072449447/27310000000000000000 : ℝ)+2*(124999872103/68275000000000 : ℝ)*(11313/100000 : ℝ)=(10000712020687389/10000000000000000 : ℝ) by norm_num, show 1+2*(3611777357777699/25000000000000000000 : ℝ)=(12503611777357777699/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8685285732198987/25000000000000000000 : ℝ)+(3611777357777699/25000000000000000000 : ℝ) ≤ ((27300631540072449447/27310000000000000000 : ℝ)+(124999872103/68275000000000 : ℝ)*((3511/25000 : ℝ)+(11313/100000 : ℝ)))^(4155/1024 : ℝ) := by
    rw [show (27300631540072449447/27310000000000000000 : ℝ)+(124999872103/68275000000000 : ℝ)*((3511/25000 : ℝ)+(11313/100000 : ℝ))=(10001212020175801/10000000000000000 : ℝ) by norm_num, show 1+(8685285732198987/25000000000000000000 : ℝ)+(3611777357777699/25000000000000000000 : ℝ)=(12506148531544988343/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8685285732198987/25000000000000000000 : ℝ) ≤ ((27300631540072449447/27310000000000000000 : ℝ)+2*(124999872103/68275000000000 : ℝ)*(3511/25000 : ℝ))^(4155/1024 : ℝ) := by
    rw [show (27300631540072449447/27310000000000000000 : ℝ)+2*(124999872103/68275000000000 : ℝ)*(3511/25000 : ℝ)=(10001712019664213/10000000000000000 : ℝ) by norm_num, show 1+2*(8685285732198987/25000000000000000000 : ℝ)=(12508685285732198987/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27300631540072449447/27310000000000000000 : ℝ)*(X 1 0+X 2 0)+(124999872103/68275000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4155/1024 : ℝ)) (lo := (11313/100000 : ℝ)) (hi := (3511/25000 : ℝ)) (c := (27300631540072449447/27310000000000000000 : ℝ)) (alpha := (124999872103/68275000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27300631540072449447/27310000000000000000 : ℝ)*(X 0 1+X 2 1)+(124999872103/68275000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4155/1024 : ℝ)) (lo := (11313/100000 : ℝ)) (hi := (3511/25000 : ℝ)) (c := (27300631540072449447/27310000000000000000 : ℝ)) (alpha := (124999872103/68275000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27300631540072449447/27310000000000000000 : ℝ)*(X 0 2+X 1 2)+(124999872103/68275000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4155/1024 : ℝ)) (lo := (11313/100000 : ℝ)) (hi := (3511/25000 : ℝ)) (c := (27300631540072449447/27310000000000000000 : ℝ)) (alpha := (124999872103/68275000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-108920601/500000000 : ℝ)*X 0 0+(1348376527/2500000000 : ℝ)*X 0 1+(5265305129/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((10689703/20000000 : ℝ)*X 1 0+(-560861119/2500000000 : ℝ)*X 1 1+(658163153/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068970343/2000000000 : ℝ)*X 2 0+(5265305071/10000000000 : ℝ)*X 2 1+(-2243444393/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4368063217/10000000000 : ℝ)*X 0 0+(4242982487/10000000000 : ℝ)*X 0 1+(2248417291/5000000000 : ℝ)*X 0 2+(4368063217/10000000000 : ℝ)*X 1 0+(4242982487/10000000000 : ℝ)*X 1 1+(2248417291/5000000000 : ℝ)*X 1 2+(4368063217/10000000000 : ℝ)*X 2 0+(4242982487/10000000000 : ℝ)*X 2 1+(2248417291/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-544604257/2500000000 : ℝ)*X 0 0+(5265627193/10000000000 : ℝ)*X 0 1+(5393182839/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656214777/5000000000 : ℝ)*X 1 0+(-66111463/312500000 : ℝ)*X 1 1+(53931829/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328107399/2500000000 : ℝ)*X 2 0+(5393182831/10000000000 : ℝ)*X 2 1+(-2115566853/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4368072957/10000000000 : ℝ)*X 0 0+(4496197021/10000000000 : ℝ)*X 0 1+(848724483/2000000000 : ℝ)*X 0 2+(4368072957/10000000000 : ℝ)*X 1 0+(4496197021/10000000000 : ℝ)*X 1 1+(848724483/2000000000 : ℝ)*X 1 2+(4368072957/10000000000 : ℝ)*X 2 0+(4496197021/10000000000 : ℝ)*X 2 1+(848724483/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2971044761490688503074197977/1365500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (269210259/50000000000000 : ℝ)*(base19) + (158771029/25000000000000 : ℝ)*(base23) + (5802053/5000000000000 : ℝ)*(lower2) + (880913/12500000000000 : ℝ)*(upper3) + (18635379/50000000000000 : ℝ)*(upper5) + (5869806193877003/100000000000000 : ℝ)*(major0) + (5869806193877003/100000000000000 : ℝ)*(major1) + (5869806193877003/100000000000000 : ℝ)*(major2) + (7800269401185189/100000000000000 : ℝ)*(sp0) + (3900147020799813/50000000000000 : ℝ)*(sp1) + (1950073486234007/25000000000000 : ℝ)*(sp2) + (984827152127963/25000000000000 : ℝ)*(sp3) + (6294708739/25000000000000 : ℝ)*(sp4) + (4563347791/50000000000000 : ℝ)*(sp7) + (1969658867603717/50000000000000 : ℝ)*(f.failure) + (1560058916004029/20000000000000 : ℝ)*(f.sum) + (1231278650593/6827500000000000000000000000 : ℝ)*base65 + (16604597307669032659/2731000000000000000000000000000000 : ℝ)*base68 + (7616093326647967341/2731000000000000000000000000000000 : ℝ)*base69 + (4950986897378967341/2731000000000000000000000000000000 : ℝ)*base71 + (12448111081443/6827500000000000000000000000 : ℝ)*base73 + (10179978632818967341/2731000000000000000000000000000000 : ℝ)*base75 + (53480257476241032659/2731000000000000000000000000000000 : ℝ)*base78 + (7111939051622967341/2731000000000000000000000000000000 : ℝ)*base79 + (11423888994393/6827500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (3596073/1000000000000000000000 : ℝ)*base90 + (3596073/1000000000000000000000 : ℝ)*base92 + (3596073/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7532206283471189758800147057/1365500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (80912867/10000000000000 : ℝ)*(base19) + (507484257/50000000000000 : ℝ)*(base23) + (96040631/100000000000000 : ℝ)*(upper3) + (8870409/12500000000000 : ℝ)*(lower4) + (50446431/50000000000000 : ℝ)*(upper5) + (5899470247790959/100000000000000 : ℝ)*(major0) + (5899470247790959/100000000000000 : ℝ)*(major1) + (5899470247790959/100000000000000 : ℝ)*(major2) + (25378347247/100000000000000 : ℝ)*(sp1) + (13531262053/50000000000000 : ℝ)*(sp2) + (3919857285529009/50000000000000 : ℝ)*(sp4) + (78396883835821/1000000000000 : ℝ)*(sp5) + (3919843246782699/50000000000000 : ℝ)*(sp6) + (197961287032729/5000000000000 : ℝ)*(sp7) + (197961287032729/5000000000000 : ℝ)*(f.failure) + (3919857285529009/50000000000000 : ℝ)*(f.sum) + (2100077177029/426718750000000000000000000 : ℝ)*base65 + (21015841690412050327/2731000000000000000000000000000000 : ℝ)*base68 + (10258635188600050327/2731000000000000000000000000000000 : ℝ)*base70 + (32156429943098050327/2731000000000000000000000000000000 : ℝ)*base72 + (3454501066783/3413750000000000000000000000 : ℝ)*base74 + (9795062210806050327/2731000000000000000000000000000000 : ℝ)*base76 + (23978333277736050327/2731000000000000000000000000000000 : ℝ)*base78 + (8697228656902050327/2731000000000000000000000000000000 : ℝ)*base80 + (10718658035521/1706875000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (783501/100000000000000000000 : ℝ)*base90 + (783501/100000000000000000000 : ℝ)*base92 + (783501/100000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1118_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29801131/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3511/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11313/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11321/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3509/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1118_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1118_s8_0 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-544604509/2500000000 : ℝ)*x 0 + (215736973/400000000 : ℝ)*x 1 + (105307661/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (544604509/2500000000 : ℝ)^8311 ≤ (661734099017/5000000000000 : ℝ)^6263 := by
    have hnat : (544604509 : ℕ)^8311*5000000000000^6263 ≤ 661734099017^6263*2500000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544604509 2500000000 661734099017 5000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215736973/400000000 : ℝ)^8311 ≤ (22037095689671/50000000000000 : ℝ)^6263 := by
    have hnat : (215736973 : ℕ)^8311*50000000000000^6263 ≤ 22037095689671^6263*400000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215736973 400000000 22037095689671 50000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105307661/200000000 : ℝ)^8311 ≤ (21345563313033/50000000000000 : ℝ)^6263 := by
    have hnat : (105307661 : ℕ)^8311*50000000000000^6263 ≤ 21345563313033^6263*200000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105307661 200000000 21345563313033 50000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-544604509/2500000000 : ℝ), (215736973/400000000 : ℝ), (105307661/200000000 : ℝ)] ![(661734099017/5000000000000 : ℝ), (22037095689671/50000000000000 : ℝ), (21345563313033/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-544604509/2500000000 : ℝ)|^8311 ≤ (661734099017/5000000000000 : ℝ)^6263
        have hw : |(-544604509/2500000000 : ℝ)|=(544604509/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(215736973/400000000 : ℝ)|^8311 ≤ (22037095689671/50000000000000 : ℝ)^6263
        have hw : |(215736973/400000000 : ℝ)|=(215736973/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(105307661/200000000 : ℝ)|^8311 ≤ (21345563313033/50000000000000 : ℝ)^6263
        have hw : |(105307661/200000000 : ℝ)|=(105307661/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1118_s8_1 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344831379/10000000000 : ℝ)*x 0 + (-1121684167/5000000000 : ℝ)*x 1 + (5265383049/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344831379/10000000000 : ℝ)^8311 ≤ (2721751619483/6250000000000 : ℝ)^6263 := by
    have hnat : (5344831379 : ℕ)^8311*6250000000000^6263 ≤ 2721751619483^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344831379 10000000000 2721751619483 6250000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1121684167/5000000000 : ℝ)^8311 ≤ (3440211862671/25000000000000 : ℝ)^6263 := by
    have hnat : (1121684167 : ℕ)^8311*25000000000000^6263 ≤ 3440211862671^6263*5000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121684167 5000000000 3440211862671 25000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265383049/10000000000 : ℝ)^8311 ≤ (42691126615307/100000000000000 : ℝ)^6263 := by
    have hnat : (5265383049 : ℕ)^8311*100000000000000^6263 ≤ 42691126615307^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265383049 10000000000 42691126615307 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344831379/10000000000 : ℝ), (-1121684167/5000000000 : ℝ), (5265383049/10000000000 : ℝ)] ![(2721751619483/6250000000000 : ℝ), (3440211862671/25000000000000 : ℝ), (42691126615307/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344831379/10000000000 : ℝ)|^8311 ≤ (2721751619483/6250000000000 : ℝ)^6263
        have hw : |(5344831379/10000000000 : ℝ)|=(5344831379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1121684167/5000000000 : ℝ)|^8311 ≤ (3440211862671/25000000000000 : ℝ)^6263
        have hw : |(-1121684167/5000000000 : ℝ)|=(1121684167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265383049/10000000000 : ℝ)|^8311 ≤ (42691126615307/100000000000000 : ℝ)^6263
        have hw : |(5265383049/10000000000 : ℝ)|=(5265383049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1118_s8_2 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344831379/10000000000 : ℝ)*x 0 + (105307661/200000000 : ℝ)*x 1 + (-1121684167/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344831379/10000000000 : ℝ)^8311 ≤ (2721751619483/6250000000000 : ℝ)^6263 := by
    have hnat : (5344831379 : ℕ)^8311*6250000000000^6263 ≤ 2721751619483^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344831379 10000000000 2721751619483 6250000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (105307661/200000000 : ℝ)^8311 ≤ (21345563313033/50000000000000 : ℝ)^6263 := by
    have hnat : (105307661 : ℕ)^8311*50000000000000^6263 ≤ 21345563313033^6263*200000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105307661 200000000 21345563313033 50000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1121684167/5000000000 : ℝ)^8311 ≤ (3440211862671/25000000000000 : ℝ)^6263 := by
    have hnat : (1121684167 : ℕ)^8311*25000000000000^6263 ≤ 3440211862671^6263*5000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121684167 5000000000 3440211862671 25000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344831379/10000000000 : ℝ), (105307661/200000000 : ℝ), (-1121684167/5000000000 : ℝ)] ![(2721751619483/6250000000000 : ℝ), (21345563313033/50000000000000 : ℝ), (3440211862671/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344831379/10000000000 : ℝ)|^8311 ≤ (2721751619483/6250000000000 : ℝ)^6263
        have hw : |(5344831379/10000000000 : ℝ)|=(5344831379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(105307661/200000000 : ℝ)|^8311 ≤ (21345563313033/50000000000000 : ℝ)^6263
        have hw : |(105307661/200000000 : ℝ)|=(105307661/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1121684167/5000000000 : ℝ)|^8311 ≤ (3440211862671/25000000000000 : ℝ)^6263
        have hw : |(-1121684167/5000000000 : ℝ)|=(1121684167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1118_s8_3 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (873613441/2000000000 : ℝ)*x 0 + (132598123/312500000 : ℝ)*x 1 + (4496676143/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (873613441/2000000000 : ℝ)^8311 ≤ (33316853097721/100000000000000 : ℝ)^6263 := by
    have hnat : (873613441 : ℕ)^8311*100000000000000^6263 ≤ 33316853097721^6263*2000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873613441 2000000000 33316853097721 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (132598123/312500000 : ℝ)^8311 ≤ (32058350971491/100000000000000 : ℝ)^6263 := by
    have hnat : (132598123 : ℕ)^8311*100000000000000^6263 ≤ 32058350971491^6263*312500000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132598123 312500000 32058350971491 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4496676143/10000000000 : ℝ)^8311 ≤ (34624795905077/100000000000000 : ℝ)^6263 := by
    have hnat : (4496676143 : ℕ)^8311*100000000000000^6263 ≤ 34624795905077^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4496676143 10000000000 34624795905077 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(873613441/2000000000 : ℝ), (132598123/312500000 : ℝ), (4496676143/10000000000 : ℝ)] ![(33316853097721/100000000000000 : ℝ), (32058350971491/100000000000000 : ℝ), (34624795905077/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(873613441/2000000000 : ℝ)|^8311 ≤ (33316853097721/100000000000000 : ℝ)^6263
        have hw : |(873613441/2000000000 : ℝ)|=(873613441/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(132598123/312500000 : ℝ)|^8311 ≤ (32058350971491/100000000000000 : ℝ)^6263
        have hw : |(132598123/312500000 : ℝ)|=(132598123/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4496676143/10000000000 : ℝ)|^8311 ≤ (34624795905077/100000000000000 : ℝ)^6263
        have hw : |(4496676143/10000000000 : ℝ)|=(4496676143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1118_s8_4 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-544605857/2500000000 : ℝ)*x 0 + (2632852369/5000000000 : ℝ)*x 1 + (269655057/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (544605857/2500000000 : ℝ)^8311 ≤ (13234725450697/100000000000000 : ℝ)^6263 := by
    have hnat : (544605857 : ℕ)^8311*100000000000000^6263 ≤ 13234725450697^6263*2500000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544605857 2500000000 13234725450697 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632852369/5000000000 : ℝ)^8311 ≤ (21347293877247/50000000000000 : ℝ)^6263 := by
    have hnat : (2632852369 : ℕ)^8311*50000000000000^6263 ≤ 21347293877247^6263*5000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632852369 5000000000 21347293877247 50000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269655057/500000000 : ℝ)^8311 ≤ (44070686786457/100000000000000 : ℝ)^6263 := by
    have hnat : (269655057 : ℕ)^8311*100000000000000^6263 ≤ 44070686786457^6263*500000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269655057 500000000 44070686786457 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-544605857/2500000000 : ℝ), (2632852369/5000000000 : ℝ), (269655057/500000000 : ℝ)] ![(13234725450697/100000000000000 : ℝ), (21347293877247/50000000000000 : ℝ), (44070686786457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-544605857/2500000000 : ℝ)|^8311 ≤ (13234725450697/100000000000000 : ℝ)^6263
        have hw : |(-544605857/2500000000 : ℝ)|=(544605857/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632852369/5000000000 : ℝ)|^8311 ≤ (21347293877247/50000000000000 : ℝ)^6263
        have hw : |(2632852369/5000000000 : ℝ)|=(2632852369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269655057/500000000 : ℝ)|^8311 ≤ (44070686786457/100000000000000 : ℝ)^6263
        have hw : |(269655057/500000000 : ℝ)|=(269655057/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1118_s8_5 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312449851/10000000000 : ℝ)*x 0 + (-528912309/2500000000 : ℝ)*x 1 + (539310201/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312449851/10000000000 : ℝ)^8311 ≤ (43198264673191/100000000000000 : ℝ)^6263 := by
    have hnat : (5312449851 : ℕ)^8311*100000000000000^6263 ≤ 43198264673191^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312449851 10000000000 43198264673191 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (528912309/2500000000 : ℝ)^8311 ≤ (3182759773891/25000000000000 : ℝ)^6263 := by
    have hnat : (528912309 : ℕ)^8311*25000000000000^6263 ≤ 3182759773891^6263*2500000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528912309 2500000000 3182759773891 25000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539310201/1000000000 : ℝ)^8311 ≤ (44070696220577/100000000000000 : ℝ)^6263 := by
    have hnat : (539310201 : ℕ)^8311*100000000000000^6263 ≤ 44070696220577^6263*1000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539310201 1000000000 44070696220577 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312449851/10000000000 : ℝ), (-528912309/2500000000 : ℝ), (539310201/1000000000 : ℝ)] ![(43198264673191/100000000000000 : ℝ), (3182759773891/25000000000000 : ℝ), (44070696220577/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312449851/10000000000 : ℝ)|^8311 ≤ (43198264673191/100000000000000 : ℝ)^6263
        have hw : |(5312449851/10000000000 : ℝ)|=(5312449851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-528912309/2500000000 : ℝ)|^8311 ≤ (3182759773891/25000000000000 : ℝ)^6263
        have hw : |(-528912309/2500000000 : ℝ)|=(528912309/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539310201/1000000000 : ℝ)|^8311 ≤ (44070696220577/100000000000000 : ℝ)^6263
        have hw : |(539310201/1000000000 : ℝ)|=(539310201/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1118_s8_6 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312449891/10000000000 : ℝ)*x 0 + (84267219/156250000 : ℝ)*x 1 + (-1057824587/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312449891/10000000000 : ℝ)^8311 ≤ (43198265104811/100000000000000 : ℝ)^6263 := by
    have hnat : (5312449891 : ℕ)^8311*100000000000000^6263 ≤ 43198265104811^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312449891 10000000000 43198265104811 100000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84267219/156250000 : ℝ)^8311 ≤ (1101767407141/2500000000000 : ℝ)^6263 := by
    have hnat : (84267219 : ℕ)^8311*2500000000000^6263 ≤ 1101767407141^6263*156250000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84267219 156250000 1101767407141 2500000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1057824587/5000000000 : ℝ)^8311 ≤ (3182759650119/25000000000000 : ℝ)^6263 := by
    have hnat : (1057824587 : ℕ)^8311*25000000000000^6263 ≤ 3182759650119^6263*5000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057824587 5000000000 3182759650119 25000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312449891/10000000000 : ℝ), (84267219/156250000 : ℝ), (-1057824587/5000000000 : ℝ)] ![(43198265104811/100000000000000 : ℝ), (1101767407141/2500000000000 : ℝ), (3182759650119/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312449891/10000000000 : ℝ)|^8311 ≤ (43198265104811/100000000000000 : ℝ)^6263
        have hw : |(5312449891/10000000000 : ℝ)|=(5312449891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(84267219/156250000 : ℝ)|^8311 ≤ (1101767407141/2500000000000 : ℝ)^6263
        have hw : |(84267219/156250000 : ℝ)|=(84267219/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1057824587/5000000000 : ℝ)|^8311 ≤ (3182759650119/25000000000000 : ℝ)^6263
        have hw : |(-1057824587/5000000000 : ℝ)|=(1057824587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1118_s8_7 (p : ℝ) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4368076387/10000000000 : ℝ)*x 0 + (899208097/2000000000 : ℝ)*x 1 + (4243778473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4368076387/10000000000 : ℝ)^8311 ≤ (16658473016753/50000000000000 : ℝ)^6263 := by
    have hnat : (4368076387 : ℕ)^8311*50000000000000^6263 ≤ 16658473016753^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4368076387 10000000000 16658473016753 50000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (899208097/2000000000 : ℝ)^8311 ≤ (1730915044651/5000000000000 : ℝ)^6263 := by
    have hnat : (899208097 : ℕ)^8311*5000000000000^6263 ≤ 1730915044651^6263*2000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899208097 2000000000 1730915044651 5000000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4243778473/10000000000 : ℝ)^8311 ≤ (4008094132083/12500000000000 : ℝ)^6263 := by
    have hnat : (4243778473 : ℕ)^8311*12500000000000^6263 ≤ 4008094132083^6263*10000000000^8311 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4243778473 10000000000 4008094132083 12500000000000 8311 6263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8311/2048 : ℝ)) 8311 6263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4368076387/10000000000 : ℝ), (899208097/2000000000 : ℝ), (4243778473/10000000000 : ℝ)] ![(16658473016753/50000000000000 : ℝ), (1730915044651/5000000000000 : ℝ), (4008094132083/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4368076387/10000000000 : ℝ)|^8311 ≤ (16658473016753/50000000000000 : ℝ)^6263
        have hw : |(4368076387/10000000000 : ℝ)|=(4368076387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(899208097/2000000000 : ℝ)|^8311 ≤ (1730915044651/5000000000000 : ℝ)^6263
        have hw : |(899208097/2000000000 : ℝ)|=(899208097/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4243778473/10000000000 : ℝ)|^8311 ≤ (4008094132083/12500000000000 : ℝ)^6263
        have hw : |(4243778473/10000000000 : ℝ)|=(4243778473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1118_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29801131/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3509/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11321/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5661/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7017/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3509/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11321/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3509/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11321/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3509/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11321/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3509/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11321/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3509/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11321/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3509/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11321/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11321/100000 : ℝ) ^ (4155/1024 : ℝ) ≤ (1448860805760419/10000000000000000000 : ℝ) := by
    have hpowers : (11321/100000 : ℝ)^4155 ≤ (1448860805760419/10000000000000000000 : ℝ)^1024 := by
      have hnat : (11321 : ℕ)^4155*10000000000000000000^1024 ≤ 1448860805760419^1024*100000^4155 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11321 100000 1448860805760419 10000000000000000000 4155 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11321/100000 : ℝ)) (X := (1448860805760419/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4155 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3509/25000 : ℝ) ^ (4155/1024 : ℝ) ≤ (34660913054897813/100000000000000000000 : ℝ) := by
    have hpowers : (3509/25000 : ℝ)^4155 ≤ (34660913054897813/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3509 : ℕ)^4155*100000000000000000000^1024 ≤ 34660913054897813^1024*25000^4155 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3509 25000 34660913054897813 100000000000000000000 4155 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3509/25000 : ℝ)) (X := (34660913054897813/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4155 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5001448860805760419/5000000000000000000 : ℝ) ≤ (10000714065709297/10000000000000000 : ℝ) ^ (4155/1024 : ℝ) := by
    have hpowers : (5001448860805760419/5000000000000000000 : ℝ)^1024 ≤ (10000714065709297/10000000000000000 : ℝ)^4155 := by
      have hnat : (5001448860805760419 : ℕ)^1024*10000000000000000^4155 ≤ 10000714065709297^4155*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001448860805760419 5000000000000000000 10000714065709297 10000000000000000 1024 4155 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000714065709297/10000000000000000 : ℝ)) (X := (5001448860805760419/5000000000000000000 : ℝ)) (by norm_num) 4155 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100049149521112502003/100000000000000000000 : ℝ) ≤ (10001211065997489/10000000000000000 : ℝ) ^ (4155/1024 : ℝ) := by
    have hpowers : (100049149521112502003/100000000000000000000 : ℝ)^1024 ≤ (10001211065997489/10000000000000000 : ℝ)^4155 := by
      have hnat : (100049149521112502003 : ℕ)^1024*10000000000000000^4155 ≤ 10001211065997489^4155*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100049149521112502003 100000000000000000000 10001211065997489 10000000000000000 1024 4155 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001211065997489/10000000000000000 : ℝ)) (X := (100049149521112502003/100000000000000000000 : ℝ)) (by norm_num) 4155 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034660913054897813/50000000000000000000 : ℝ) ≤ (10001708066285681/10000000000000000 : ℝ) ^ (4155/1024 : ℝ) := by
    have hpowers : (50034660913054897813/50000000000000000000 : ℝ)^1024 ≤ (10001708066285681/10000000000000000 : ℝ)^4155 := by
      have hnat : (50034660913054897813 : ℕ)^1024*10000000000000000^4155 ≤ 10001708066285681^4155*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034660913054897813 50000000000000000000 10001708066285681 10000000000000000 1024 4155 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001708066285681/10000000000000000 : ℝ)) (X := (50034660913054897813/50000000000000000000 : ℝ)) (by norm_num) 4155 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1448860805760419/10000000000000000000 : ℝ) ≤ ((27140685607875498091/27150000000000000000 : ℝ)+2*(7765629503/4242187500000 : ℝ)*(11321/100000 : ℝ))^(4155/1024 : ℝ) := by
    rw [show (27140685607875498091/27150000000000000000 : ℝ)+2*(7765629503/4242187500000 : ℝ)*(11321/100000 : ℝ)=(10000714065709297/10000000000000000 : ℝ) by norm_num, show 1+2*(1448860805760419/10000000000000000000 : ℝ)=(5001448860805760419/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34660913054897813/100000000000000000000 : ℝ)+(1448860805760419/10000000000000000000 : ℝ) ≤ ((27140685607875498091/27150000000000000000 : ℝ)+(7765629503/4242187500000 : ℝ)*((3509/25000 : ℝ)+(11321/100000 : ℝ)))^(4155/1024 : ℝ) := by
    rw [show (27140685607875498091/27150000000000000000 : ℝ)+(7765629503/4242187500000 : ℝ)*((3509/25000 : ℝ)+(11321/100000 : ℝ))=(10001211065997489/10000000000000000 : ℝ) by norm_num, show 1+(34660913054897813/100000000000000000000 : ℝ)+(1448860805760419/10000000000000000000 : ℝ)=(100049149521112502003/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34660913054897813/100000000000000000000 : ℝ) ≤ ((27140685607875498091/27150000000000000000 : ℝ)+2*(7765629503/4242187500000 : ℝ)*(3509/25000 : ℝ))^(4155/1024 : ℝ) := by
    rw [show (27140685607875498091/27150000000000000000 : ℝ)+2*(7765629503/4242187500000 : ℝ)*(3509/25000 : ℝ)=(10001708066285681/10000000000000000 : ℝ) by norm_num, show 1+2*(34660913054897813/100000000000000000000 : ℝ)=(50034660913054897813/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27140685607875498091/27150000000000000000 : ℝ)*(X 1 0+X 2 0)+(7765629503/4242187500000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4155/1024 : ℝ)) (lo := (11321/100000 : ℝ)) (hi := (3509/25000 : ℝ)) (c := (27140685607875498091/27150000000000000000 : ℝ)) (alpha := (7765629503/4242187500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27140685607875498091/27150000000000000000 : ℝ)*(X 0 1+X 2 1)+(7765629503/4242187500000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4155/1024 : ℝ)) (lo := (11321/100000 : ℝ)) (hi := (3509/25000 : ℝ)) (c := (27140685607875498091/27150000000000000000 : ℝ)) (alpha := (7765629503/4242187500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27140685607875498091/27150000000000000000 : ℝ)*(X 0 2+X 1 2)+(7765629503/4242187500000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4155/1024 : ℝ)) (lo := (11321/100000 : ℝ)) (hi := (3509/25000 : ℝ)) (c := (27140685607875498091/27150000000000000000 : ℝ)) (alpha := (7765629503/4242187500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-544604509/2500000000 : ℝ)*X 0 0+(215736973/400000000 : ℝ)*X 0 1+(105307661/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344831379/10000000000 : ℝ)*X 1 0+(-1121684167/5000000000 : ℝ)*X 1 1+(5265383049/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344831379/10000000000 : ℝ)*X 2 0+(105307661/200000000 : ℝ)*X 2 1+(-1121684167/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((873613441/2000000000 : ℝ)*X 0 0+(132598123/312500000 : ℝ)*X 0 1+(4496676143/10000000000 : ℝ)*X 0 2+(873613441/2000000000 : ℝ)*X 1 0+(132598123/312500000 : ℝ)*X 1 1+(4496676143/10000000000 : ℝ)*X 1 2+(873613441/2000000000 : ℝ)*X 2 0+(132598123/312500000 : ℝ)*X 2 1+(4496676143/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-544605857/2500000000 : ℝ)*X 0 0+(2632852369/5000000000 : ℝ)*X 0 1+(269655057/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312449851/10000000000 : ℝ)*X 1 0+(-528912309/2500000000 : ℝ)*X 1 1+(539310201/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312449891/10000000000 : ℝ)*X 2 0+(84267219/156250000 : ℝ)*X 2 1+(-1057824587/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4368076387/10000000000 : ℝ)*X 0 0+(899208097/2000000000 : ℝ)*X 0 1+(4243778473/10000000000 : ℝ)*X 0 2+(4368076387/10000000000 : ℝ)*X 1 0+(899208097/2000000000 : ℝ)*X 1 1+(4243778473/10000000000 : ℝ)*X 1 2+(4368076387/10000000000 : ℝ)*X 2 0+(899208097/2000000000 : ℝ)*X 2 1+(4243778473/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1118_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (39109987615803099388127/4525000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1719831923/100000000000000 : ℝ)*(base19) + (400650951/25000000000000 : ℝ)*(base23) + (62656453/100000000000000 : ℝ)*(lower2) + (218077733/100000000000000 : ℝ)*(upper3) + (132079801/100000000000000 : ℝ)*(upper5) + (2938583878924747/50000000000000 : ℝ)*(major0) + (2938583878924747/50000000000000 : ℝ)*(major1) + (2938583878924747/50000000000000 : ℝ)*(major2) + (3905015206698741/50000000000000 : ℝ)*(sp0) + (976259414137567/12500000000000 : ℝ)*(sp1) + (1562015086065731/20000000000000 : ℝ)*(sp2) + (493029096411227/12500000000000 : ℝ)*(sp3) + (46619534977/100000000000000 : ℝ)*(sp4) + (794480427/3125000000000 : ℝ)*(sp7) + (98606454866587/2500000000000 : ℝ)*(f.failure) + (7810077032932459/100000000000000 : ℝ)*(f.sum) + (24729075038587/3393750000000000000000000000 : ℝ)*base65 + (3232462982172147341/452500000000000000000000000000000 : ℝ)*base68 + (3846821846642147341/452500000000000000000000000000000 : ℝ)*base70 + (4720891548077852659/452500000000000000000000000000000 : ℝ)*base71 + (2367878856347/848437500000000000000000000 : ℝ)*base74 + (5893551920402147341/452500000000000000000000000000000 : ℝ)*base76 + (5204004937375352659/452500000000000000000000000000000 : ℝ)*base77 + (1786609516842852659/452500000000000000000000000000000 : ℝ)*base79 + (7399716855299/6787500000000000000000000000 : ℝ)*base81 + (290103/50000000000000000000 : ℝ)*base90 + (290103/50000000000000000000 : ℝ)*base92 + (290103/50000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (635333810491024620093/4525000000000000000000000000 : ℝ) := by norm_num
    linear_combination (323331851/100000000000000 : ℝ)*(base19) + (349339669/20000000000000 : ℝ)*(base23) + (34447557/5000000000000 : ℝ)*(lower1) + (591646001/100000000000000 : ℝ)*(upper2) + (142905767/100000000000000 : ℝ)*(upper3) + (5906788092817629/100000000000000 : ℝ)*(major0) + (5906788092817629/100000000000000 : ℝ)*(major1) + (5906788092817629/100000000000000 : ℝ)*(major2) + (20553805313/50000000000000 : ℝ)*(sp2) + (16513961837/100000000000000 : ℝ)*(sp3) + (7849439321305267/100000000000000 : ℝ)*(sp4) + (7849438997973417/100000000000000 : ℝ)*(sp5) + (981174558374537/12500000000000 : ℝ)*(sp6) + (991030086421993/25000000000000 : ℝ)*(sp7) + (3964136859649809/100000000000000 : ℝ)*(f.failure) + (7849439321305267/100000000000000 : ℝ)*(f.sum) + (17868860353069/4525000000000000000000000000 : ℝ)*base66 + (6864676699535815413/905000000000000000000000000000000 : ℝ)*base67 + (265874346209184587/905000000000000000000000000000000 : ℝ)*base70 + (2145828845254184587/905000000000000000000000000000000 : ℝ)*base72 + (175774843633/141406250000000000000000000 : ℝ)*base73 + (273900423840815413/905000000000000000000000000000000 : ℝ)*base75 + (7901819513430815413/905000000000000000000000000000000 : ℝ)*base77 + (10127754426414184587/905000000000000000000000000000000 : ℝ)*base80 + (3042369274719/4525000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (7866021/2000000000000000000000 : ℝ)*base90 + (7866021/2000000000000000000000 : ℝ)*base92 + (7866021/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1118_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29801131/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3509/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11321/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5661/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7017/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1118_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1118_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29801131/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14079/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11279/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5661/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7017/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1118_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1118_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1118_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4155/1024 : ℝ) ≤ p) (hpb : p ≤ (8311/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29801131/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14079/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11279/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5661/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7017/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1118_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
