-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1634_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:00:55.348975+00:00
-- url     : https://prove2.me/submissions/3f8f7217-4318-4c6a-8ad7-51186dc2690b

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
theorem support_rectangle_w1634_s3_0 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-411409341/2500000000 : ℝ)*x 0 + (5452446109/10000000000 : ℝ)*x 1 + (518264249/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (411409341/2500000000 : ℝ)^4855 ≤ (5079671634931/50000000000000 : ℝ)^3831 := by
    have hnat : (411409341 : ℕ)^4855*50000000000000^3831 ≤ 5079671634931^3831*2500000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      411409341 2500000000 5079671634931 50000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5452446109/10000000000 : ℝ)^4855 ≤ (11591084586301/25000000000000 : ℝ)^3831 := by
    have hnat : (5452446109 : ℕ)^4855*25000000000000^3831 ≤ 11591084586301^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5452446109 10000000000 11591084586301 25000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (518264249/1000000000 : ℝ)^4855 ≤ (8695263674373/20000000000000 : ℝ)^3831 := by
    have hnat : (518264249 : ℕ)^4855*20000000000000^3831 ≤ 8695263674373^3831*1000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518264249 1000000000 8695263674373 20000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-411409341/2500000000 : ℝ), (5452446109/10000000000 : ℝ), (518264249/1000000000 : ℝ)] ![(5079671634931/50000000000000 : ℝ), (11591084586301/25000000000000 : ℝ), (8695263674373/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-411409341/2500000000 : ℝ)|^4855 ≤ (5079671634931/50000000000000 : ℝ)^3831
        have hw : |(-411409341/2500000000 : ℝ)|=(411409341/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5452446109/10000000000 : ℝ)|^4855 ≤ (11591084586301/25000000000000 : ℝ)^3831
        have hw : |(5452446109/10000000000 : ℝ)|=(5452446109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(518264249/1000000000 : ℝ)|^4855 ≤ (8695263674373/20000000000000 : ℝ)^3831
        have hw : |(518264249/1000000000 : ℝ)|=(518264249/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1634_s3_1 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (66877199/125000000 : ℝ)*x 0 + (-89231097/500000000 : ℝ)*x 1 + (1036527093/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66877199/125000000 : ℝ)^4855 ≤ (45265019333257/100000000000000 : ℝ)^3831 := by
    have hnat : (66877199 : ℕ)^4855*100000000000000^3831 ≤ 45265019333257^3831*125000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66877199 125000000 45265019333257 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (89231097/500000000 : ℝ)^4855 ≤ (11258736959919/100000000000000 : ℝ)^3831 := by
    have hnat : (89231097 : ℕ)^4855*100000000000000^3831 ≤ 11258736959919^3831*500000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89231097 500000000 11258736959919 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1036527093/2000000000 : ℝ)^4855 ≤ (8695248737667/20000000000000 : ℝ)^3831 := by
    have hnat : (1036527093 : ℕ)^4855*20000000000000^3831 ≤ 8695248737667^3831*2000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036527093 2000000000 8695248737667 20000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66877199/125000000 : ℝ), (-89231097/500000000 : ℝ), (1036527093/2000000000 : ℝ)] ![(45265019333257/100000000000000 : ℝ), (11258736959919/100000000000000 : ℝ), (8695248737667/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66877199/125000000 : ℝ)|^4855 ≤ (45265019333257/100000000000000 : ℝ)^3831
        have hw : |(66877199/125000000 : ℝ)|=(66877199/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-89231097/500000000 : ℝ)|^4855 ≤ (11258736959919/100000000000000 : ℝ)^3831
        have hw : |(-89231097/500000000 : ℝ)|=(89231097/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1036527093/2000000000 : ℝ)|^4855 ≤ (8695248737667/20000000000000 : ℝ)^3831
        have hw : |(1036527093/2000000000 : ℝ)|=(1036527093/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1634_s3_2 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (535016809/1000000000 : ℝ)*x 0 + (207305609/400000000 : ℝ)*x 1 + (-27884783/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535016809/1000000000 : ℝ)^4855 ≤ (28290584613/62500000000 : ℝ)^3831 := by
    have hnat : (535016809 : ℕ)^4855*62500000000^3831 ≤ 28290584613^3831*1000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535016809 1000000000 28290584613 62500000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (207305609/400000000 : ℝ)^4855 ≤ (10869073573101/25000000000000 : ℝ)^3831 := by
    have hnat : (207305609 : ℕ)^4855*25000000000000^3831 ≤ 10869073573101^3831*400000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207305609 400000000 10869073573101 25000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (27884783/156250000 : ℝ)^4855 ≤ (2814692578807/25000000000000 : ℝ)^3831 := by
    have hnat : (27884783 : ℕ)^4855*25000000000000^3831 ≤ 2814692578807^3831*156250000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27884783 156250000 2814692578807 25000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535016809/1000000000 : ℝ), (207305609/400000000 : ℝ), (-27884783/156250000 : ℝ)] ![(28290584613/62500000000 : ℝ), (10869073573101/25000000000000 : ℝ), (2814692578807/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535016809/1000000000 : ℝ)|^4855 ≤ (28290584613/62500000000 : ℝ)^3831
        have hw : |(535016809/1000000000 : ℝ)|=(535016809/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(207305609/400000000 : ℝ)|^4855 ≤ (10869073573101/25000000000000 : ℝ)^3831
        have hw : |(207305609/400000000 : ℝ)|=(207305609/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-27884783/156250000 : ℝ)|^4855 ≤ (2814692578807/25000000000000 : ℝ)^3831
        have hw : |(-27884783/156250000 : ℝ)|=(27884783/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1634_s3_3 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4193149547/10000000000 : ℝ)*x 0 + (1930747723/5000000000 : ℝ)*x 1 + (4545518943/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4193149547/10000000000 : ℝ)^4855 ≤ (33239002249159/100000000000000 : ℝ)^3831 := by
    have hnat : (4193149547 : ℕ)^4855*100000000000000^3831 ≤ 33239002249159^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4193149547 10000000000 33239002249159 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1930747723/5000000000 : ℝ)^4855 ≤ (29943193463731/100000000000000 : ℝ)^3831 := by
    have hnat : (1930747723 : ℕ)^4855*100000000000000^3831 ≤ 29943193463731^3831*5000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1930747723 5000000000 29943193463731 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4545518943/10000000000 : ℝ)^4855 ≤ (1472712171291/4000000000000 : ℝ)^3831 := by
    have hnat : (4545518943 : ℕ)^4855*4000000000000^3831 ≤ 1472712171291^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4545518943 10000000000 1472712171291 4000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4193149547/10000000000 : ℝ), (1930747723/5000000000 : ℝ), (4545518943/10000000000 : ℝ)] ![(33239002249159/100000000000000 : ℝ), (29943193463731/100000000000000 : ℝ), (1472712171291/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4193149547/10000000000 : ℝ)|^4855 ≤ (33239002249159/100000000000000 : ℝ)^3831
        have hw : |(4193149547/10000000000 : ℝ)|=(4193149547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1930747723/5000000000 : ℝ)|^4855 ≤ (29943193463731/100000000000000 : ℝ)^3831
        have hw : |(1930747723/5000000000 : ℝ)|=(1930747723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4545518943/10000000000 : ℝ)|^4855 ≤ (1472712171291/4000000000000 : ℝ)^3831
        have hw : |(4545518943/10000000000 : ℝ)|=(4545518943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1634_s3_4 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-411424759/2500000000 : ℝ)*x 0 + (5184670167/10000000000 : ℝ)*x 1 + (545040077/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (411424759/2500000000 : ℝ)^4855 ≤ (10159825771493/100000000000000 : ℝ)^3831 := by
    have hnat : (411424759 : ℕ)^4855*100000000000000^3831 ≤ 10159825771493^3831*2500000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      411424759 2500000000 10159825771493 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5184670167/10000000000 : ℝ)^4855 ≤ (21748937977563/50000000000000 : ℝ)^3831 := by
    have hnat : (5184670167 : ℕ)^4855*50000000000000^3831 ≤ 21748937977563^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184670167 10000000000 21748937977563 50000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (545040077/1000000000 : ℝ)^4855 ≤ (46342298258891/100000000000000 : ℝ)^3831 := by
    have hnat : (545040077 : ℕ)^4855*100000000000000^3831 ≤ 46342298258891^3831*1000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545040077 1000000000 46342298258891 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-411424759/2500000000 : ℝ), (5184670167/10000000000 : ℝ), (545040077/1000000000 : ℝ)] ![(10159825771493/100000000000000 : ℝ), (21748937977563/50000000000000 : ℝ), (46342298258891/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-411424759/2500000000 : ℝ)|^4855 ≤ (10159825771493/100000000000000 : ℝ)^3831
        have hw : |(-411424759/2500000000 : ℝ)|=(411424759/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5184670167/10000000000 : ℝ)|^4855 ≤ (21748937977563/50000000000000 : ℝ)^3831
        have hw : |(5184670167/10000000000 : ℝ)|=(5184670167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(545040077/1000000000 : ℝ)|^4855 ≤ (46342298258891/100000000000000 : ℝ)^3831
        have hw : |(545040077/1000000000 : ℝ)|=(545040077/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1634_s3_5 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (659779721/1250000000 : ℝ)*x 0 + (-1516863093/10000000000 : ℝ)*x 1 + (340650049/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (659779721/1250000000 : ℝ)^4855 ≤ (5561887041623/12500000000000 : ℝ)^3831 := by
    have hnat : (659779721 : ℕ)^4855*12500000000000^3831 ≤ 5561887041623^3831*1250000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659779721 1250000000 5561887041623 12500000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1516863093/10000000000 : ℝ)^4855 ≤ (4581302621297/50000000000000 : ℝ)^3831 := by
    have hnat : (1516863093 : ℕ)^4855*50000000000000^3831 ≤ 4581302621297^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1516863093 10000000000 4581302621297 50000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (340650049/625000000 : ℝ)^4855 ≤ (2896393650609/6250000000000 : ℝ)^3831 := by
    have hnat : (340650049 : ℕ)^4855*6250000000000^3831 ≤ 2896393650609^3831*625000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340650049 625000000 2896393650609 6250000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(659779721/1250000000 : ℝ), (-1516863093/10000000000 : ℝ), (340650049/625000000 : ℝ)] ![(5561887041623/12500000000000 : ℝ), (4581302621297/50000000000000 : ℝ), (2896393650609/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(659779721/1250000000 : ℝ)|^4855 ≤ (5561887041623/12500000000000 : ℝ)^3831
        have hw : |(659779721/1250000000 : ℝ)|=(659779721/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1516863093/10000000000 : ℝ)|^4855 ≤ (4581302621297/50000000000000 : ℝ)^3831
        have hw : |(-1516863093/10000000000 : ℝ)|=(1516863093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(340650049/625000000 : ℝ)|^4855 ≤ (2896393650609/6250000000000 : ℝ)^3831
        have hw : |(340650049/625000000 : ℝ)|=(340650049/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1634_s3_6 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (527823781/1000000000 : ℝ)*x 0 + (5450400863/10000000000 : ℝ)*x 1 + (-1516862923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527823781/1000000000 : ℝ)^4855 ≤ (44495096781677/100000000000000 : ℝ)^3831 := by
    have hnat : (527823781 : ℕ)^4855*100000000000000^3831 ≤ 44495096781677^3831*1000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527823781 1000000000 44495096781677 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5450400863/10000000000 : ℝ)^4855 ≤ (46342299260987/100000000000000 : ℝ)^3831 := by
    have hnat : (5450400863 : ℕ)^4855*100000000000000^3831 ≤ 46342299260987^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5450400863 10000000000 46342299260987 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1516862923/10000000000 : ℝ)^4855 ≤ (9162603941231/100000000000000 : ℝ)^3831 := by
    have hnat : (1516862923 : ℕ)^4855*100000000000000^3831 ≤ 9162603941231^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1516862923 10000000000 9162603941231 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(527823781/1000000000 : ℝ), (5450400863/10000000000 : ℝ), (-1516862923/10000000000 : ℝ)] ![(44495096781677/100000000000000 : ℝ), (46342299260987/100000000000000 : ℝ), (9162603941231/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(527823781/1000000000 : ℝ)|^4855 ≤ (44495096781677/100000000000000 : ℝ)^3831
        have hw : |(527823781/1000000000 : ℝ)|=(527823781/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5450400863/10000000000 : ℝ)|^4855 ≤ (46342299260987/100000000000000 : ℝ)^3831
        have hw : |(5450400863/10000000000 : ℝ)|=(5450400863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1516862923/10000000000 : ℝ)|^4855 ≤ (9162603941231/100000000000000 : ℝ)^3831
        have hw : |(-1516862923/10000000000 : ℝ)|=(1516862923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1634_s3_7 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (838663847/2000000000 : ℝ)*x 0 + (2270185529/5000000000 : ℝ)*x 1 + (1933348741/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (838663847/2000000000 : ℝ)^4855 ≤ (33240706910803/100000000000000 : ℝ)^3831 := by
    have hnat : (838663847 : ℕ)^4855*100000000000000^3831 ≤ 33240706910803^3831*2000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      838663847 2000000000 33240706910803 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2270185529/5000000000 : ℝ)^4855 ≤ (18382485075267/50000000000000 : ℝ)^3831 := by
    have hnat : (2270185529 : ℕ)^4855*50000000000000^3831 ≤ 18382485075267^3831*5000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2270185529 5000000000 18382485075267 50000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1933348741/5000000000 : ℝ)^4855 ≤ (29994322921113/100000000000000 : ℝ)^3831 := by
    have hnat : (1933348741 : ℕ)^4855*100000000000000^3831 ≤ 29994322921113^3831*5000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1933348741 5000000000 29994322921113 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(838663847/2000000000 : ℝ), (2270185529/5000000000 : ℝ), (1933348741/5000000000 : ℝ)] ![(33240706910803/100000000000000 : ℝ), (18382485075267/50000000000000 : ℝ), (29994322921113/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(838663847/2000000000 : ℝ)|^4855 ≤ (33240706910803/100000000000000 : ℝ)^3831
        have hw : |(838663847/2000000000 : ℝ)|=(838663847/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2270185529/5000000000 : ℝ)|^4855 ≤ (18382485075267/50000000000000 : ℝ)^3831
        have hw : |(2270185529/5000000000 : ℝ)|=(2270185529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1933348741/5000000000 : ℝ)|^4855 ≤ (29994322921113/100000000000000 : ℝ)^3831
        have hw : |(1933348741/5000000000 : ℝ)|=(1933348741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1634_s3_8 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-3466379/2000000000 : ℝ)*x 0 + (3031564799/5000000000 : ℝ)*x 1 + (5504604893/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3466379/2000000000 : ℝ)^4855 ≤ (1980106599/6250000000000 : ℝ)^3831 := by
    have hnat : (3466379 : ℕ)^4855*6250000000000^3831 ≤ 1980106599^3831*2000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3466379 2000000000 1980106599 6250000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3031564799/5000000000 : ℝ)^4855 ≤ (26520592090109/50000000000000 : ℝ)^3831 := by
    have hnat : (3031564799 : ℕ)^4855*50000000000000^3831 ≤ 26520592090109^3831*5000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3031564799 5000000000 26520592090109 50000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5504604893/10000000000 : ℝ)^4855 ≤ (23463567052507/50000000000000 : ℝ)^3831 := by
    have hnat : (5504604893 : ℕ)^4855*50000000000000^3831 ≤ 23463567052507^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5504604893 10000000000 23463567052507 50000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3466379/2000000000 : ℝ), (3031564799/5000000000 : ℝ), (5504604893/10000000000 : ℝ)] ![(1980106599/6250000000000 : ℝ), (26520592090109/50000000000000 : ℝ), (23463567052507/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3466379/2000000000 : ℝ)|^4855 ≤ (1980106599/6250000000000 : ℝ)^3831
        have hw : |(-3466379/2000000000 : ℝ)|=(3466379/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3031564799/5000000000 : ℝ)|^4855 ≤ (26520592090109/50000000000000 : ℝ)^3831
        have hw : |(3031564799/5000000000 : ℝ)|=(3031564799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5504604893/10000000000 : ℝ)|^4855 ≤ (23463567052507/50000000000000 : ℝ)^3831
        have hw : |(5504604893/10000000000 : ℝ)|=(5504604893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1634_s3_9 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1062094177/10000000000 : ℝ)*x 0 + (-1034340293/2500000000 : ℝ)*x 1 + (851622287/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062094177/10000000000 : ℝ)^4855 ≤ (5832612047481/100000000000000 : ℝ)^3831 := by
    have hnat : (1062094177 : ℕ)^4855*100000000000000^3831 ≤ 5832612047481^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062094177 10000000000 5832612047481 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1034340293/2500000000 : ℝ)^4855 ≤ (1633978147101/5000000000000 : ℝ)^3831 := by
    have hnat : (1034340293 : ℕ)^4855*5000000000000^3831 ≤ 1633978147101^3831*2500000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034340293 2500000000 1633978147101 5000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (851622287/1250000000 : ℝ)^4855 ≤ (30743912502381/50000000000000 : ℝ)^3831 := by
    have hnat : (851622287 : ℕ)^4855*50000000000000^3831 ≤ 30743912502381^3831*1250000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      851622287 1250000000 30743912502381 50000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062094177/10000000000 : ℝ), (-1034340293/2500000000 : ℝ), (851622287/1250000000 : ℝ)] ![(5832612047481/100000000000000 : ℝ), (1633978147101/5000000000000 : ℝ), (30743912502381/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062094177/10000000000 : ℝ)|^4855 ≤ (5832612047481/100000000000000 : ℝ)^3831
        have hw : |(1062094177/10000000000 : ℝ)|=(1062094177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1034340293/2500000000 : ℝ)|^4855 ≤ (1633978147101/5000000000000 : ℝ)^3831
        have hw : |(-1034340293/2500000000 : ℝ)|=(1034340293/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(851622287/1250000000 : ℝ)|^4855 ≤ (30743912502381/50000000000000 : ℝ)^3831
        have hw : |(851622287/1250000000 : ℝ)|=(851622287/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1634_s3_10 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1217451929/10000000000 : ℝ)*x 0 + (3582716647/5000000000 : ℝ)*x 1 + (-1806325777/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1217451929/10000000000 : ℝ)^4855 ≤ (693424804289/10000000000000 : ℝ)^3831 := by
    have hnat : (1217451929 : ℕ)^4855*10000000000000^3831 ≤ 693424804289^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1217451929 10000000000 693424804289 10000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3582716647/5000000000 : ℝ)^4855 ≤ (2048329320189/3125000000000 : ℝ)^3831 := by
    have hnat : (3582716647 : ℕ)^4855*3125000000000^3831 ≤ 2048329320189^3831*5000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3582716647 5000000000 2048329320189 3125000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1806325777/5000000000 : ℝ)^4855 ≤ (3439901711633/12500000000000 : ℝ)^3831 := by
    have hnat : (1806325777 : ℕ)^4855*12500000000000^3831 ≤ 3439901711633^3831*5000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1806325777 5000000000 3439901711633 12500000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1217451929/10000000000 : ℝ), (3582716647/5000000000 : ℝ), (-1806325777/5000000000 : ℝ)] ![(693424804289/10000000000000 : ℝ), (2048329320189/3125000000000 : ℝ), (3439901711633/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1217451929/10000000000 : ℝ)|^4855 ≤ (693424804289/10000000000000 : ℝ)^3831
        have hw : |(1217451929/10000000000 : ℝ)|=(1217451929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3582716647/5000000000 : ℝ)|^4855 ≤ (2048329320189/3125000000000 : ℝ)^3831
        have hw : |(3582716647/5000000000 : ℝ)|=(3582716647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1806325777/5000000000 : ℝ)|^4855 ≤ (3439901711633/12500000000000 : ℝ)^3831
        have hw : |(-1806325777/5000000000 : ℝ)|=(1806325777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1634_s3_11 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (759857929/5000000000 : ℝ)*x 0 + (670111901/1250000000 : ℝ)*x 1 + (2683038179/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (759857929/5000000000 : ℝ)^4855 ≤ (9184448870353/100000000000000 : ℝ)^3831 := by
    have hnat : (759857929 : ℕ)^4855*100000000000000^3831 ≤ 9184448870353^3831*5000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      759857929 5000000000 9184448870353 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (670111901/1250000000 : ℝ)^4855 ≤ (4537998122099/10000000000000 : ℝ)^3831 := by
    have hnat : (670111901 : ℕ)^4855*10000000000000^3831 ≤ 4537998122099^3831*1250000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      670111901 1250000000 4537998122099 10000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2683038179/5000000000 : ℝ)^4855 ≤ (22717784947901/50000000000000 : ℝ)^3831 := by
    have hnat : (2683038179 : ℕ)^4855*50000000000000^3831 ≤ 22717784947901^3831*5000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2683038179 5000000000 22717784947901 50000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(759857929/5000000000 : ℝ), (670111901/1250000000 : ℝ), (2683038179/5000000000 : ℝ)] ![(9184448870353/100000000000000 : ℝ), (4537998122099/10000000000000 : ℝ), (22717784947901/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(759857929/5000000000 : ℝ)|^4855 ≤ (9184448870353/100000000000000 : ℝ)^3831
        have hw : |(759857929/5000000000 : ℝ)|=(759857929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(670111901/1250000000 : ℝ)|^4855 ≤ (4537998122099/10000000000000 : ℝ)^3831
        have hw : |(670111901/1250000000 : ℝ)|=(670111901/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2683038179/5000000000 : ℝ)|^4855 ≤ (22717784947901/50000000000000 : ℝ)^3831
        have hw : |(2683038179/5000000000 : ℝ)|=(2683038179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1634_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (17675869/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (41/250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10491/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (661/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8153/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (41/250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10491/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (41/250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10491/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (41/250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10491/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (41/250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10491/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (41/250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10491/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (41/250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10491/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10491/100000 : ℝ) ^ (4851/1024 : ℝ) ≤ (2297794835571847/100000000000000000000 : ℝ) := by
    have hpowers : (10491/100000 : ℝ)^4851 ≤ (2297794835571847/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10491 : ℕ)^4851*100000000000000000000^1024 ≤ 2297794835571847^1024*100000^4851 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10491 100000 2297794835571847 100000000000000000000 4851 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10491/100000 : ℝ)) (X := (2297794835571847/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4851 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (41/250 : ℝ) ^ (4851/1024 : ℝ) ≤ (9537753307253173/50000000000000000000 : ℝ) := by
    have hpowers : (41/250 : ℝ)^4851 ≤ (9537753307253173/50000000000000000000 : ℝ)^1024 := by
      have hnat : (41 : ℕ)^4851*50000000000000000000^1024 ≤ 9537753307253173^1024*250^4851 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        41 250 9537753307253173 50000000000000000000 4851 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (41/250 : ℝ)) (X := (9537753307253173/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4851 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002297794835571847/50000000000000000000 : ℝ) ≤ (2500024251693051/2500000000000000 : ℝ) ^ (4851/1024 : ℝ) := by
    have hpowers : (50002297794835571847/50000000000000000000 : ℝ)^1024 ≤ (2500024251693051/2500000000000000 : ℝ)^4851 := by
      have hnat : (50002297794835571847 : ℕ)^1024*2500000000000000^4851 ≤ 2500024251693051^4851*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002297794835571847 50000000000000000000 2500024251693051 2500000000000000 1024 4851 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500024251693051/2500000000000000 : ℝ)) (X := (50002297794835571847/50000000000000000000 : ℝ)) (by norm_num) 4851 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100021373301450078193/100000000000000000000 : ℝ) ≤ (625028195753109/625000000000000 : ℝ) ^ (4851/1024 : ℝ) := by
    have hpowers : (100021373301450078193/100000000000000000000 : ℝ)^1024 ≤ (625028195753109/625000000000000 : ℝ)^4851 := by
      have hnat : (100021373301450078193 : ℕ)^1024*625000000000000^4851 ≤ 625028195753109^4851*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100021373301450078193 100000000000000000000 625028195753109 625000000000000 1024 4851 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625028195753109/625000000000000 : ℝ)) (X := (100021373301450078193/100000000000000000000 : ℝ)) (by norm_num) 4851 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25009537753307253173/25000000000000000000 : ℝ) ≤ (2500201314331821/2500000000000000 : ℝ) ^ (4851/1024 : ℝ) := by
    have hpowers : (25009537753307253173/25000000000000000000 : ℝ)^1024 ≤ (2500201314331821/2500000000000000 : ℝ)^4851 := by
      have hnat : (25009537753307253173 : ℕ)^1024*2500000000000000^4851 ≤ 2500201314331821^4851*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25009537753307253173 25000000000000000000 2500201314331821 2500000000000000 1024 4851 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500201314331821/2500000000000000 : ℝ)) (X := (25009537753307253173/25000000000000000000 : ℝ)) (by norm_num) 4851 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2297794835571847/100000000000000000000 : ℝ) ≤ ((14770785739110902289/14772500000000000000 : ℝ)+2*(17706263877/29545000000000 : ℝ)*(10491/100000 : ℝ))^(4851/1024 : ℝ) := by
    rw [show (14770785739110902289/14772500000000000000 : ℝ)+2*(17706263877/29545000000000 : ℝ)*(10491/100000 : ℝ)=(2500024251693051/2500000000000000 : ℝ) by norm_num, show 1+2*(2297794835571847/100000000000000000000 : ℝ)=(50002297794835571847/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9537753307253173/50000000000000000000 : ℝ)+(2297794835571847/100000000000000000000 : ℝ) ≤ ((14770785739110902289/14772500000000000000 : ℝ)+(17706263877/29545000000000 : ℝ)*((41/250 : ℝ)+(10491/100000 : ℝ)))^(4851/1024 : ℝ) := by
    rw [show (14770785739110902289/14772500000000000000 : ℝ)+(17706263877/29545000000000 : ℝ)*((41/250 : ℝ)+(10491/100000 : ℝ))=(625028195753109/625000000000000 : ℝ) by norm_num, show 1+(9537753307253173/50000000000000000000 : ℝ)+(2297794835571847/100000000000000000000 : ℝ)=(100021373301450078193/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9537753307253173/50000000000000000000 : ℝ) ≤ ((14770785739110902289/14772500000000000000 : ℝ)+2*(17706263877/29545000000000 : ℝ)*(41/250 : ℝ))^(4851/1024 : ℝ) := by
    rw [show (14770785739110902289/14772500000000000000 : ℝ)+2*(17706263877/29545000000000 : ℝ)*(41/250 : ℝ)=(2500201314331821/2500000000000000 : ℝ) by norm_num, show 1+2*(9537753307253173/50000000000000000000 : ℝ)=(25009537753307253173/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14770785739110902289/14772500000000000000 : ℝ)*(X 1 0+X 2 0)+(17706263877/29545000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4851/1024 : ℝ)) (lo := (10491/100000 : ℝ)) (hi := (41/250 : ℝ)) (c := (14770785739110902289/14772500000000000000 : ℝ)) (alpha := (17706263877/29545000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14770785739110902289/14772500000000000000 : ℝ)*(X 0 1+X 2 1)+(17706263877/29545000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4851/1024 : ℝ)) (lo := (10491/100000 : ℝ)) (hi := (41/250 : ℝ)) (c := (14770785739110902289/14772500000000000000 : ℝ)) (alpha := (17706263877/29545000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14770785739110902289/14772500000000000000 : ℝ)*(X 0 2+X 1 2)+(17706263877/29545000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4851/1024 : ℝ)) (lo := (10491/100000 : ℝ)) (hi := (41/250 : ℝ)) (c := (14770785739110902289/14772500000000000000 : ℝ)) (alpha := (17706263877/29545000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-411409341/2500000000 : ℝ)*X 0 0+(5452446109/10000000000 : ℝ)*X 0 1+(518264249/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((66877199/125000000 : ℝ)*X 1 0+(-89231097/500000000 : ℝ)*X 1 1+(1036527093/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((535016809/1000000000 : ℝ)*X 2 0+(207305609/400000000 : ℝ)*X 2 1+(-27884783/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4193149547/10000000000 : ℝ)*X 0 0+(1930747723/5000000000 : ℝ)*X 0 1+(4545518943/10000000000 : ℝ)*X 0 2+(4193149547/10000000000 : ℝ)*X 1 0+(1930747723/5000000000 : ℝ)*X 1 1+(4545518943/10000000000 : ℝ)*X 1 2+(4193149547/10000000000 : ℝ)*X 2 0+(1930747723/5000000000 : ℝ)*X 2 1+(4545518943/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-411424759/2500000000 : ℝ)*X 0 0+(5184670167/10000000000 : ℝ)*X 0 1+(545040077/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((659779721/1250000000 : ℝ)*X 1 0+(-1516863093/10000000000 : ℝ)*X 1 1+(340650049/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((527823781/1000000000 : ℝ)*X 2 0+(5450400863/10000000000 : ℝ)*X 2 1+(-1516862923/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((838663847/2000000000 : ℝ)*X 0 0+(2270185529/5000000000 : ℝ)*X 0 1+(1933348741/5000000000 : ℝ)*X 0 2+(838663847/2000000000 : ℝ)*X 1 0+(2270185529/5000000000 : ℝ)*X 1 1+(1933348741/5000000000 : ℝ)*X 1 2+(838663847/2000000000 : ℝ)*X 2 0+(2270185529/5000000000 : ℝ)*X 2 1+(1933348741/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-3466379/2000000000 : ℝ)*X 0 0+(3031564799/5000000000 : ℝ)*X 0 1+(5504604893/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_s3_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1062094177/10000000000 : ℝ)*X 1 0+(-1034340293/2500000000 : ℝ)*X 1 1+(851622287/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_s3_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1217451929/10000000000 : ℝ)*X 2 0+(3582716647/5000000000 : ℝ)*X 2 1+(-1806325777/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_s3_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((759857929/5000000000 : ℝ)*X 0 0+(670111901/1250000000 : ℝ)*X 0 1+(2683038179/5000000000 : ℝ)*X 0 2+(759857929/5000000000 : ℝ)*X 1 0+(670111901/1250000000 : ℝ)*X 1 1+(2683038179/5000000000 : ℝ)*X 1 2+(759857929/5000000000 : ℝ)*X 2 0+(670111901/1250000000 : ℝ)*X 2 1+(2683038179/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_s3_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (175148439277147389482426499/19437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13735411/100000000000000 : ℝ)*(upper2) + (921539339/100000000000000 : ℝ)*(lower4) + (1292101676385357/50000000000000 : ℝ)*(major0) + (1292101676385357/50000000000000 : ℝ)*(major1) + (1292101676385357/50000000000000 : ℝ)*(major2) + (463299251435923/12500000000000 : ℝ)*(sp0) + (926578976263197/25000000000000 : ℝ)*(sp1) + (926582144232279/25000000000000 : ℝ)*(sp2) + (1461971666404797/100000000000000 : ℝ)*(sp3) + (90970614267/100000000000000 : ℝ)*(sp5) + (8274740293/10000000000000 : ℝ)*(sp6) + (4682888567/20000000000000 : ℝ)*(sp7) + (17312844663/100000000000000 : ℝ)*(sp8) + (444866499/10000000000000 : ℝ)*(sp9) + (1461995080847631/100000000000000 : ℝ)*(f.failure) + (1853205662166023/50000000000000 : ℝ)*(f.sum) + (407740076181/62200000000000000000000000 : ℝ)*base66 + (170751897873308833/38875000000000000000000000000000 : ℝ)*base68 + (351732323725558833/38875000000000000000000000000000 : ℝ)*base70 + (35350748540691167/38875000000000000000000000000000 : ℝ)*base71 + (1231367095723/311000000000000000000000000 : ℝ)*base74 + (94036160904566167/38875000000000000000000000000000 : ℝ)*base75 + (1014315479711441167/38875000000000000000000000000000 : ℝ)*base77 + (53518157506691167/38875000000000000000000000000000 : ℝ)*base79 + (1247082111701/311000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base86 + (5483661/1000000000000000000000 : ℝ)*base90 + (5483661/1000000000000000000000 : ℝ)*base92 + (5483661/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1212963709482107615930799813/73862500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8859033/6250000000000 : ℝ)*(lower5) + (524761735891461/20000000000000 : ℝ)*(major0) + (524761735891461/20000000000000 : ℝ)*(major1) + (524761735891461/20000000000000 : ℝ)*(major2) + (3159227673/100000000000000 : ℝ)*(sp1) + (8303723917/100000000000000 : ℝ)*(sp2) + (1881606239284287/50000000000000 : ℝ)*(sp4) + (3763211439110883/100000000000000 : ℝ)*(sp5) + (376320613801697/10000000000000 : ℝ)*(sp6) + (1484399509961097/100000000000000 : ℝ)*(sp7) + (112554949/4000000000000 : ℝ)*(sp8) + (10845371/1562500000000 : ℝ)*(sp9) + (850701413/100000000000000 : ℝ)*(sp10) + (502278509/25000000000000 : ℝ)*(sp11) + (1484401519075133/100000000000000 : ℝ)*(f.failure) + (37632152924423/1000000000000 : ℝ)*(f.sum) + (4671039833739/1477250000000000000000000000 : ℝ)*base66 + (3006927102104054229/295450000000000000000000000000000 : ℝ)*base67 + (1453290713092804229/295450000000000000000000000000000 : ℝ)*base69 + (113251052950204229/295450000000000000000000000000000 : ℝ)*base71 + (8058643585977/5909000000000000000000000000 : ℝ)*base73 + (1194874033193395771/295450000000000000000000000000000 : ℝ)*base76 + (2172609076963454229/295450000000000000000000000000000 : ℝ)*base77 + (544378991747004229/295450000000000000000000000000000 : ℝ)*base79 + (831106713447/2954500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (2065577/1000000000000000000000 : ℝ)*base89 + (2065577/1000000000000000000000 : ℝ)*base91 + (2065577/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1634_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (17675869/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (41/250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10491/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (661/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8153/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1634_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1634_s4_0 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1645697227/10000000000 : ℝ)*x 0 + (2726060459/5000000000 : ℝ)*x 1 + (5182928063/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1645697227/10000000000 : ℝ)^4855 ≤ (5079905809199/50000000000000 : ℝ)^3831 := by
    have hnat : (1645697227 : ℕ)^4855*50000000000000^3831 ≤ 5079905809199^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1645697227 10000000000 5079905809199 50000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2726060459/5000000000 : ℝ)^4855 ≤ (46360834016607/100000000000000 : ℝ)^3831 := by
    have hnat : (2726060459 : ℕ)^4855*100000000000000^3831 ≤ 46360834016607^3831*5000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2726060459 5000000000 46360834016607 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5182928063/10000000000 : ℝ)^4855 ≤ (8695870870411/20000000000000 : ℝ)^3831 := by
    have hnat : (5182928063 : ℕ)^4855*20000000000000^3831 ≤ 8695870870411^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182928063 10000000000 8695870870411 20000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1645697227/10000000000 : ℝ), (2726060459/5000000000 : ℝ), (5182928063/10000000000 : ℝ)] ![(5079905809199/50000000000000 : ℝ), (46360834016607/100000000000000 : ℝ), (8695870870411/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1645697227/10000000000 : ℝ)|^4855 ≤ (5079905809199/50000000000000 : ℝ)^3831
        have hw : |(-1645697227/10000000000 : ℝ)|=(1645697227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2726060459/5000000000 : ℝ)|^4855 ≤ (46360834016607/100000000000000 : ℝ)^3831
        have hw : |(2726060459/5000000000 : ℝ)|=(2726060459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5182928063/10000000000 : ℝ)|^4855 ≤ (8695870870411/20000000000000 : ℝ)^3831
        have hw : |(5182928063/10000000000 : ℝ)|=(5182928063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1634_s4_1 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350080767/10000000000 : ℝ)*x 0 + (-1784360463/10000000000 : ℝ)*x 1 + (2591464033/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350080767/10000000000 : ℝ)^4855 ≤ (45263999114783/100000000000000 : ℝ)^3831 := by
    have hnat : (5350080767 : ℕ)^4855*100000000000000^3831 ≤ 45263999114783^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350080767 10000000000 45263999114783 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1784360463/10000000000 : ℝ)^4855 ≤ (1125664648233/10000000000000 : ℝ)^3831 := by
    have hnat : (1784360463 : ℕ)^4855*10000000000000^3831 ≤ 1125664648233^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1784360463 10000000000 1125664648233 10000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2591464033/5000000000 : ℝ)^4855 ≤ (43479354383949/100000000000000 : ℝ)^3831 := by
    have hnat : (2591464033 : ℕ)^4855*100000000000000^3831 ≤ 43479354383949^3831*5000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591464033 5000000000 43479354383949 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350080767/10000000000 : ℝ), (-1784360463/10000000000 : ℝ), (2591464033/5000000000 : ℝ)] ![(45263999114783/100000000000000 : ℝ), (1125664648233/10000000000000 : ℝ), (43479354383949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350080767/10000000000 : ℝ)|^4855 ≤ (45263999114783/100000000000000 : ℝ)^3831
        have hw : |(5350080767/10000000000 : ℝ)|=(5350080767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1784360463/10000000000 : ℝ)|^4855 ≤ (1125664648233/10000000000000 : ℝ)^3831
        have hw : |(-1784360463/10000000000 : ℝ)|=(1784360463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2591464033/5000000000 : ℝ)|^4855 ≤ (43479354383949/100000000000000 : ℝ)^3831
        have hw : |(2591464033/5000000000 : ℝ)|=(2591464033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1634_s4_2 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350080763/10000000000 : ℝ)*x 0 + (647866009/1250000000 : ℝ)*x 1 + (-1784360461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350080763/10000000000 : ℝ)^4855 ≤ (5657999883987/12500000000000 : ℝ)^3831 := by
    have hnat : (5350080763 : ℕ)^4855*12500000000000^3831 ≤ 5657999883987^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350080763 10000000000 5657999883987 12500000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (647866009/1250000000 : ℝ)^4855 ≤ (43479354447737/100000000000000 : ℝ)^3831 := by
    have hnat : (647866009 : ℕ)^4855*100000000000000^3831 ≤ 43479354447737^3831*1250000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647866009 1250000000 43479354447737 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1784360461/10000000000 : ℝ)^4855 ≤ (562832323317/5000000000000 : ℝ)^3831 := by
    have hnat : (1784360461 : ℕ)^4855*5000000000000^3831 ≤ 562832323317^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1784360461 10000000000 562832323317 5000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350080763/10000000000 : ℝ), (647866009/1250000000 : ℝ), (-1784360461/10000000000 : ℝ)] ![(5657999883987/12500000000000 : ℝ), (43479354447737/100000000000000 : ℝ), (562832323317/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350080763/10000000000 : ℝ)|^4855 ≤ (5657999883987/12500000000000 : ℝ)^3831
        have hw : |(5350080763/10000000000 : ℝ)|=(5350080763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(647866009/1250000000 : ℝ)|^4855 ≤ (43479354447737/100000000000000 : ℝ)^3831
        have hw : |(647866009/1250000000 : ℝ)|=(647866009/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1784360461/10000000000 : ℝ)|^4855 ≤ (562832323317/5000000000000 : ℝ)^3831
        have hw : |(-1784360461/10000000000 : ℝ)|=(1784360461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1634_s4_3 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4193192711/10000000000 : ℝ)*x 0 + (1931138667/5000000000 : ℝ)*x 1 + (1136182031/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4193192711/10000000000 : ℝ)^4855 ≤ (1038732370839/3125000000000 : ℝ)^3831 := by
    have hnat : (4193192711 : ℕ)^4855*3125000000000^3831 ≤ 1038732370839^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4193192711 10000000000 1038732370839 3125000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1931138667/5000000000 : ℝ)^4855 ≤ (14975438631149/50000000000000 : ℝ)^3831 := by
    have hnat : (1931138667 : ℕ)^4855*50000000000000^3831 ≤ 14975438631149^3831*5000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1931138667 5000000000 14975438631149 50000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1136182031/2500000000 : ℝ)^4855 ≤ (3680968685341/10000000000000 : ℝ)^3831 := by
    have hnat : (1136182031 : ℕ)^4855*10000000000000^3831 ≤ 3680968685341^3831*2500000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1136182031 2500000000 3680968685341 10000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4193192711/10000000000 : ℝ), (1931138667/5000000000 : ℝ), (1136182031/2500000000 : ℝ)] ![(1038732370839/3125000000000 : ℝ), (14975438631149/50000000000000 : ℝ), (3680968685341/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4193192711/10000000000 : ℝ)|^4855 ≤ (1038732370839/3125000000000 : ℝ)^3831
        have hw : |(4193192711/10000000000 : ℝ)|=(4193192711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1931138667/5000000000 : ℝ)|^4855 ≤ (14975438631149/50000000000000 : ℝ)^3831
        have hw : |(1931138667/5000000000 : ℝ)|=(1931138667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1136182031/2500000000 : ℝ)|^4855 ≤ (3680968685341/10000000000000 : ℝ)^3831
        have hw : |(1136182031/2500000000 : ℝ)|=(1136182031/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1634_s4_4 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-12857529/78125000 : ℝ)*x 0 + (5184948953/10000000000 : ℝ)*x 1 + (2725039359/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (12857529/78125000 : ℝ)^4855 ≤ (10160331780633/100000000000000 : ℝ)^3831 := by
    have hnat : (12857529 : ℕ)^4855*100000000000000^3831 ≤ 10160331780633^3831*78125000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12857529 78125000 10160331780633 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5184948953/10000000000 : ℝ)^4855 ≤ (2175042004541/5000000000000 : ℝ)^3831 := by
    have hnat : (5184948953 : ℕ)^4855*5000000000000^3831 ≤ 2175042004541^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184948953 10000000000 2175042004541 5000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2725039359/5000000000 : ℝ)^4855 ≤ (46338828104609/100000000000000 : ℝ)^3831 := by
    have hnat : (2725039359 : ℕ)^4855*100000000000000^3831 ≤ 46338828104609^3831*5000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2725039359 5000000000 46338828104609 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-12857529/78125000 : ℝ), (5184948953/10000000000 : ℝ), (2725039359/5000000000 : ℝ)] ![(10160331780633/100000000000000 : ℝ), (2175042004541/5000000000000 : ℝ), (46338828104609/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-12857529/78125000 : ℝ)|^4855 ≤ (10160331780633/100000000000000 : ℝ)^3831
        have hw : |(-12857529/78125000 : ℝ)|=(12857529/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5184948953/10000000000 : ℝ)|^4855 ≤ (2175042004541/5000000000000 : ℝ)^3831
        have hw : |(5184948953/10000000000 : ℝ)|=(5184948953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2725039359/5000000000 : ℝ)|^4855 ≤ (46338828104609/100000000000000 : ℝ)^3831
        have hw : |(2725039359/5000000000 : ℝ)|=(2725039359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1634_s4_5 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5278314109/10000000000 : ℝ)*x 0 + (-189651229/1250000000 : ℝ)*x 1 + (5450078751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5278314109/10000000000 : ℝ)^4855 ≤ (44495911898713/100000000000000 : ℝ)^3831 := by
    have hnat : (5278314109 : ℕ)^4855*100000000000000^3831 ≤ 44495911898713^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5278314109 10000000000 44495911898713 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (189651229/1250000000 : ℝ)^4855 ≤ (9165259638097/100000000000000 : ℝ)^3831 := by
    have hnat : (189651229 : ℕ)^4855*100000000000000^3831 ≤ 9165259638097^3831*1250000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      189651229 1250000000 9165259638097 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5450078751/10000000000 : ℝ)^4855 ≤ (9267765692037/20000000000000 : ℝ)^3831 := by
    have hnat : (5450078751 : ℕ)^4855*20000000000000^3831 ≤ 9267765692037^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5450078751 10000000000 9267765692037 20000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5278314109/10000000000 : ℝ), (-189651229/1250000000 : ℝ), (5450078751/10000000000 : ℝ)] ![(44495911898713/100000000000000 : ℝ), (9165259638097/100000000000000 : ℝ), (9267765692037/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5278314109/10000000000 : ℝ)|^4855 ≤ (44495911898713/100000000000000 : ℝ)^3831
        have hw : |(5278314109/10000000000 : ℝ)|=(5278314109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-189651229/1250000000 : ℝ)|^4855 ≤ (9165259638097/100000000000000 : ℝ)^3831
        have hw : |(-189651229/1250000000 : ℝ)|=(189651229/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5450078751/10000000000 : ℝ)|^4855 ≤ (9267765692037/20000000000000 : ℝ)^3831
        have hw : |(5450078751/10000000000 : ℝ)|=(5450078751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1634_s4_6 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2639157073/5000000000 : ℝ)*x 0 + (2725039397/5000000000 : ℝ)*x 1 + (-758604859/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2639157073/5000000000 : ℝ)^4855 ≤ (5561989036749/12500000000000 : ℝ)^3831 := by
    have hnat : (2639157073 : ℕ)^4855*12500000000000^3831 ≤ 5561989036749^3831*5000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639157073 5000000000 5561989036749 12500000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2725039397/5000000000 : ℝ)^4855 ≤ (46338828923513/100000000000000 : ℝ)^3831 := by
    have hnat : (2725039397 : ℕ)^4855*100000000000000^3831 ≤ 46338828923513^3831*5000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2725039397 5000000000 46338828923513 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (758604859/5000000000 : ℝ)^4855 ≤ (1833051753073/20000000000000 : ℝ)^3831 := by
    have hnat : (758604859 : ℕ)^4855*20000000000000^3831 ≤ 1833051753073^3831*5000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      758604859 5000000000 1833051753073 20000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2639157073/5000000000 : ℝ), (2725039397/5000000000 : ℝ), (-758604859/5000000000 : ℝ)] ![(5561989036749/12500000000000 : ℝ), (46338828923513/100000000000000 : ℝ), (1833051753073/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2639157073/5000000000 : ℝ)|^4855 ≤ (5561989036749/12500000000000 : ℝ)^3831
        have hw : |(2639157073/5000000000 : ℝ)|=(2639157073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2725039397/5000000000 : ℝ)|^4855 ≤ (46338828923513/100000000000000 : ℝ)^3831
        have hw : |(2725039397/5000000000 : ℝ)|=(2725039397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-758604859/5000000000 : ℝ)|^4855 ≤ (1833051753073/20000000000000 : ℝ)^3831
        have hw : |(-758604859/5000000000 : ℝ)|=(758604859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1634_s4_7 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (524170139/1250000000 : ℝ)*x 0 + (907920963/2000000000 : ℝ)*x 1 + (3867454503/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (524170139/1250000000 : ℝ)^4855 ≤ (16620563802029/50000000000000 : ℝ)^3831 := by
    have hnat : (524170139 : ℕ)^4855*50000000000000^3831 ≤ 16620563802029^3831*1250000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524170139 1250000000 16620563802029 50000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (907920963/2000000000 : ℝ)^4855 ≤ (36757107360517/100000000000000 : ℝ)^3831 := by
    have hnat : (907920963 : ℕ)^4855*100000000000000^3831 ≤ 36757107360517^3831*2000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      907920963 2000000000 36757107360517 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3867454503/10000000000 : ℝ)^4855 ≤ (30001765016623/100000000000000 : ℝ)^3831 := by
    have hnat : (3867454503 : ℕ)^4855*100000000000000^3831 ≤ 30001765016623^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3867454503 10000000000 30001765016623 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(524170139/1250000000 : ℝ), (907920963/2000000000 : ℝ), (3867454503/10000000000 : ℝ)] ![(16620563802029/50000000000000 : ℝ), (36757107360517/100000000000000 : ℝ), (30001765016623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(524170139/1250000000 : ℝ)|^4855 ≤ (16620563802029/50000000000000 : ℝ)^3831
        have hw : |(524170139/1250000000 : ℝ)|=(524170139/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(907920963/2000000000 : ℝ)|^4855 ≤ (36757107360517/100000000000000 : ℝ)^3831
        have hw : |(907920963/2000000000 : ℝ)|=(907920963/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3867454503/10000000000 : ℝ)|^4855 ≤ (30001765016623/100000000000000 : ℝ)^3831
        have hw : |(3867454503/10000000000 : ℝ)|=(3867454503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1634_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (17675869/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8153/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (661/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (10583/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16299/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8153/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (661/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8153/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (661/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8153/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (661/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8153/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (661/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8153/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (661/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8153/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (661/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (661/6250 : ℝ) ^ (4851/1024 : ℝ) ≤ (298416895074031/12500000000000000000 : ℝ) := by
    have hpowers : (661/6250 : ℝ)^4851 ≤ (298416895074031/12500000000000000000 : ℝ)^1024 := by
      have hnat : (661 : ℕ)^4851*12500000000000000000^1024 ≤ 298416895074031^1024*6250^4851 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        661 6250 298416895074031 12500000000000000000 4851 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (661/6250 : ℝ)) (X := (298416895074031/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4851 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8153/50000 : ℝ) ^ (4851/1024 : ℝ) ≤ (9281535502045363/50000000000000000000 : ℝ) := by
    have hpowers : (8153/50000 : ℝ)^4851 ≤ (9281535502045363/50000000000000000000 : ℝ)^1024 := by
      have hnat : (8153 : ℕ)^4851*50000000000000000000^1024 ≤ 9281535502045363^1024*50000^4851 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8153 50000 9281535502045363 50000000000000000000 4851 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8153/50000 : ℝ)) (X := (9281535502045363/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4851 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250298416895074031/6250000000000000000 : ℝ) ≤ (5000050393427413/5000000000000000 : ℝ) ^ (4851/1024 : ℝ) := by
    have hpowers : (6250298416895074031/6250000000000000000 : ℝ)^1024 ≤ (5000050393427413/5000000000000000 : ℝ)^4851 := by
      have hnat : (6250298416895074031 : ℕ)^1024*5000000000000000^4851 ≤ 5000050393427413^4851*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250298416895074031 6250000000000000000 5000050393427413 5000000000000000 1024 4851 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000050393427413/5000000000000000 : ℝ)) (X := (6250298416895074031/6250000000000000000 : ℝ)) (by norm_num) 4851 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50010475203082341487/50000000000000000000 : ℝ) ≤ (10000442206622203/10000000000000000 : ℝ) ^ (4851/1024 : ℝ) := by
    have hpowers : (50010475203082341487/50000000000000000000 : ℝ)^1024 ≤ (10000442206622203/10000000000000000 : ℝ)^4851 := by
      have hnat : (50010475203082341487 : ℕ)^1024*10000000000000000^4851 ≤ 10000442206622203^4851*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010475203082341487 50000000000000000000 10000442206622203 10000000000000000 1024 4851 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000442206622203/10000000000000000 : ℝ)) (X := (50010475203082341487/50000000000000000000 : ℝ)) (by norm_num) 4851 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25009281535502045363/25000000000000000000 : ℝ) ≤ (500039181319479/500000000000000 : ℝ) ^ (4851/1024 : ℝ) := by
    have hpowers : (25009281535502045363/25000000000000000000 : ℝ)^1024 ≤ (500039181319479/500000000000000 : ℝ)^4851 := by
      have hnat : (25009281535502045363 : ℕ)^1024*500000000000000^4851 ≤ 500039181319479^4851*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25009281535502045363 25000000000000000000 500039181319479 500000000000000 1024 4851 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500039181319479/500000000000000 : ℝ)) (X := (25009281535502045363/25000000000000000000 : ℝ)) (by norm_num) 4851 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(298416895074031/12500000000000000000 : ℝ) ≤ ((14323338949439648669/14325000000000000000 : ℝ)+2*(341419767377/573000000000000 : ℝ)*(661/6250 : ℝ))^(4851/1024 : ℝ) := by
    rw [show (14323338949439648669/14325000000000000000 : ℝ)+2*(341419767377/573000000000000 : ℝ)*(661/6250 : ℝ)=(5000050393427413/5000000000000000 : ℝ) by norm_num, show 1+2*(298416895074031/12500000000000000000 : ℝ)=(6250298416895074031/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9281535502045363/50000000000000000000 : ℝ)+(298416895074031/12500000000000000000 : ℝ) ≤ ((14323338949439648669/14325000000000000000 : ℝ)+(341419767377/573000000000000 : ℝ)*((8153/50000 : ℝ)+(661/6250 : ℝ)))^(4851/1024 : ℝ) := by
    rw [show (14323338949439648669/14325000000000000000 : ℝ)+(341419767377/573000000000000 : ℝ)*((8153/50000 : ℝ)+(661/6250 : ℝ))=(10000442206622203/10000000000000000 : ℝ) by norm_num, show 1+(9281535502045363/50000000000000000000 : ℝ)+(298416895074031/12500000000000000000 : ℝ)=(50010475203082341487/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9281535502045363/50000000000000000000 : ℝ) ≤ ((14323338949439648669/14325000000000000000 : ℝ)+2*(341419767377/573000000000000 : ℝ)*(8153/50000 : ℝ))^(4851/1024 : ℝ) := by
    rw [show (14323338949439648669/14325000000000000000 : ℝ)+2*(341419767377/573000000000000 : ℝ)*(8153/50000 : ℝ)=(500039181319479/500000000000000 : ℝ) by norm_num, show 1+2*(9281535502045363/50000000000000000000 : ℝ)=(25009281535502045363/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14323338949439648669/14325000000000000000 : ℝ)*(X 1 0+X 2 0)+(341419767377/573000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4851/1024 : ℝ)) (lo := (661/6250 : ℝ)) (hi := (8153/50000 : ℝ)) (c := (14323338949439648669/14325000000000000000 : ℝ)) (alpha := (341419767377/573000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14323338949439648669/14325000000000000000 : ℝ)*(X 0 1+X 2 1)+(341419767377/573000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4851/1024 : ℝ)) (lo := (661/6250 : ℝ)) (hi := (8153/50000 : ℝ)) (c := (14323338949439648669/14325000000000000000 : ℝ)) (alpha := (341419767377/573000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14323338949439648669/14325000000000000000 : ℝ)*(X 0 2+X 1 2)+(341419767377/573000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4851/1024 : ℝ)) (lo := (661/6250 : ℝ)) (hi := (8153/50000 : ℝ)) (c := (14323338949439648669/14325000000000000000 : ℝ)) (alpha := (341419767377/573000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1645697227/10000000000 : ℝ)*X 0 0+(2726060459/5000000000 : ℝ)*X 0 1+(5182928063/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350080767/10000000000 : ℝ)*X 1 0+(-1784360463/10000000000 : ℝ)*X 1 1+(2591464033/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350080763/10000000000 : ℝ)*X 2 0+(647866009/1250000000 : ℝ)*X 2 1+(-1784360461/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4193192711/10000000000 : ℝ)*X 0 0+(1931138667/5000000000 : ℝ)*X 0 1+(1136182031/2500000000 : ℝ)*X 0 2+(4193192711/10000000000 : ℝ)*X 1 0+(1931138667/5000000000 : ℝ)*X 1 1+(1136182031/2500000000 : ℝ)*X 1 2+(4193192711/10000000000 : ℝ)*X 2 0+(1931138667/5000000000 : ℝ)*X 2 1+(1136182031/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-12857529/78125000 : ℝ)*X 0 0+(5184948953/10000000000 : ℝ)*X 0 1+(2725039359/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5278314109/10000000000 : ℝ)*X 1 0+(-189651229/1250000000 : ℝ)*X 1 1+(5450078751/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2639157073/5000000000 : ℝ)*X 2 0+(2725039397/5000000000 : ℝ)*X 2 1+(-758604859/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((524170139/1250000000 : ℝ)*X 0 0+(907920963/2000000000 : ℝ)*X 0 1+(3867454503/10000000000 : ℝ)*X 0 2+(524170139/1250000000 : ℝ)*X 1 0+(907920963/2000000000 : ℝ)*X 1 1+(3867454503/10000000000 : ℝ)*X 1 2+(524170139/1250000000 : ℝ)*X 2 0+(907920963/2000000000 : ℝ)*X 2 1+(3867454503/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (198538933278115558277129199/59687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (519114479/100000000000000 : ℝ)*(base19) + (475065983/100000000000000 : ℝ)*(base23) + (22080373/100000000000000 : ℝ)*(lower2) + (165979/200000000000 : ℝ)*(upper3) + (27293469/50000000000000 : ℝ)*(upper5) + (1295033571370129/50000000000000 : ℝ)*(major0) + (1295033571370129/50000000000000 : ℝ)*(major1) + (1295033571370129/50000000000000 : ℝ)*(major2) + (928703849948397/25000000000000 : ℝ)*(sp0) + (116088161757271/3125000000000 : ℝ)*(sp1) + (232176326267573/6250000000000 : ℝ)*(sp2) + (146530962090777/10000000000000 : ℝ)*(sp3) + (3147776781/50000000000000 : ℝ)*(sp4) + (28583487/1000000000000 : ℝ)*(sp7) + (146531247925647/10000000000000 : ℝ)*(f.failure) + (3714821695347151/100000000000000 : ℝ)*(f.sum) + (56504307299617/14325000000000000000000000000 : ℝ)*base66 + (6297985103449533301/716250000000000000000000000000000 : ℝ)*base67 + (1406138640237033301/716250000000000000000000000000000 : ℝ)*base69 + (2134833151315466699/716250000000000000000000000000000 : ℝ)*base72 + (18104127588833/14325000000000000000000000000 : ℝ)*base73 + (1465573930467033301/716250000000000000000000000000000 : ℝ)*base75 + (455304650584533301/716250000000000000000000000000000 : ℝ)*base77 + (929151497202033301/716250000000000000000000000000000 : ℝ)*base79 + (58783771234267/14325000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (112243/100000000000000000000 : ℝ)*base89 + (112243/100000000000000000000 : ℝ)*base91 + (112243/100000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (56141403531244139414489/4775000000000000000000000000 : ℝ) := by norm_num
    linear_combination (886155211/50000000000000 : ℝ)*(base19) + (483323251/25000000000000 : ℝ)*(base23) + (5382181/1000000000000 : ℝ)*(lower1) + (56123169/20000000000000 : ℝ)*(upper3) + (115161/250000000000 : ℝ)*(lower4) + (120143817/50000000000000 : ℝ)*(upper5) + (1314867833693557/50000000000000 : ℝ)*(major0) + (1314867833693557/50000000000000 : ℝ)*(major1) + (1314867833693557/50000000000000 : ℝ)*(major2) + (3476814027/100000000000000 : ℝ)*(sp2) + (1885858135785763/50000000000000 : ℝ)*(sp4) + (235732156203819/6250000000000 : ℝ)*(sp5) + (1885855430732247/50000000000000 : ℝ)*(sp6) + (476081494813/32000000000 : ℝ)*(sp7) + (476081494813/32000000000 : ℝ)*(f.failure) + (1885858135785763/50000000000000 : ℝ)*(f.sum) + (42964775949389/14325000000000000000000000000 : ℝ)*base65 + (8962087850522599367/716250000000000000000000000000000 : ℝ)*base68 + (2405339422639900633/716250000000000000000000000000000 : ℝ)*base69 + (18665570448471349367/716250000000000000000000000000000 : ℝ)*base72 + (12671809621643/7162500000000000000000000000 : ℝ)*base74 + (23267794815895099367/716250000000000000000000000000000 : ℝ)*base76 + (1375048405407400633/716250000000000000000000000000000 : ℝ)*base77 + (1927280142169900633/716250000000000000000000000000000 : ℝ)*base79 + (34652153065711/14325000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (2697/320000000000000000 : ℝ)*base89 + (2697/320000000000000000 : ℝ)*base91 + (2697/320000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1634_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (17675869/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8153/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (661/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10583/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16299/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1634_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1634_s5_0 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-51428169/312500000 : ℝ)*x 0 + (5452095863/10000000000 : ℝ)*x 1 + (5182950383/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (51428169/312500000 : ℝ)^4855 ≤ (79373783823/781250000000 : ℝ)^3831 := by
    have hnat : (51428169 : ℕ)^4855*781250000000^3831 ≤ 79373783823^3831*312500000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51428169 312500000 79373783823 781250000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5452095863/10000000000 : ℝ)^4855 ≤ (23180282010411/50000000000000 : ℝ)^3831 := by
    have hnat : (5452095863 : ℕ)^4855*50000000000000^3831 ≤ 23180282010411^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5452095863 10000000000 23180282010411 50000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5182950383/10000000000 : ℝ)^4855 ≤ (43479591642051/100000000000000 : ℝ)^3831 := by
    have hnat : (5182950383 : ℕ)^4855*100000000000000^3831 ≤ 43479591642051^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182950383 10000000000 43479591642051 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-51428169/312500000 : ℝ), (5452095863/10000000000 : ℝ), (5182950383/10000000000 : ℝ)] ![(79373783823/781250000000 : ℝ), (23180282010411/50000000000000 : ℝ), (43479591642051/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-51428169/312500000 : ℝ)|^4855 ≤ (79373783823/781250000000 : ℝ)^3831
        have hw : |(-51428169/312500000 : ℝ)|=(51428169/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5452095863/10000000000 : ℝ)|^4855 ≤ (23180282010411/50000000000000 : ℝ)^3831
        have hw : |(5452095863/10000000000 : ℝ)|=(5452095863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5182950383/10000000000 : ℝ)|^4855 ≤ (43479591642051/100000000000000 : ℝ)^3831
        have hw : |(5182950383/10000000000 : ℝ)|=(5182950383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1634_s5_1 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350074321/10000000000 : ℝ)*x 0 + (-4460849/25000000 : ℝ)*x 1 + (323934391/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350074321/10000000000 : ℝ)^4855 ≤ (45263930001759/100000000000000 : ℝ)^3831 := by
    have hnat : (5350074321 : ℕ)^4855*100000000000000^3831 ≤ 45263930001759^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350074321 10000000000 45263930001759 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4460849/25000000 : ℝ)^4855 ≤ (11256479688647/100000000000000 : ℝ)^3831 := by
    have hnat : (4460849 : ℕ)^4855*100000000000000^3831 ≤ 11256479688647^3831*25000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4460849 25000000 11256479688647 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (323934391/625000000 : ℝ)^4855 ≤ (21739795145939/50000000000000 : ℝ)^3831 := by
    have hnat : (323934391 : ℕ)^4855*50000000000000^3831 ≤ 21739795145939^3831*625000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323934391 625000000 21739795145939 50000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350074321/10000000000 : ℝ), (-4460849/25000000 : ℝ), (323934391/625000000 : ℝ)] ![(45263930001759/100000000000000 : ℝ), (11256479688647/100000000000000 : ℝ), (21739795145939/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350074321/10000000000 : ℝ)|^4855 ≤ (45263930001759/100000000000000 : ℝ)^3831
        have hw : |(5350074321/10000000000 : ℝ)|=(5350074321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4460849/25000000 : ℝ)|^4855 ≤ (11256479688647/100000000000000 : ℝ)^3831
        have hw : |(-4460849/25000000 : ℝ)|=(4460849/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(323934391/625000000 : ℝ)|^4855 ≤ (21739795145939/50000000000000 : ℝ)^3831
        have hw : |(323934391/625000000 : ℝ)|=(323934391/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1634_s5_2 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-822884003/5000000000 : ℝ)*x 0 + (1036994009/2000000000 : ℝ)*x 1 + (1362513697/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (822884003/5000000000 : ℝ)^4855 ≤ (5080182688011/50000000000000 : ℝ)^3831 := by
    have hnat : (822884003 : ℕ)^4855*50000000000000^3831 ≤ 5080182688011^3831*5000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      822884003 5000000000 5080182688011 50000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036994009/2000000000 : ℝ)^4855 ≤ (43501064348973/100000000000000 : ℝ)^3831 := by
    have hnat : (1036994009 : ℕ)^4855*100000000000000^3831 ≤ 43501064348973^3831*2000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036994009 2000000000 43501064348973 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1362513697/2500000000 : ℝ)^4855 ≤ (23169285128889/50000000000000 : ℝ)^3831 := by
    have hnat : (1362513697 : ℕ)^4855*50000000000000^3831 ≤ 23169285128889^3831*2500000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1362513697 2500000000 23169285128889 50000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-822884003/5000000000 : ℝ), (1036994009/2000000000 : ℝ), (1362513697/2500000000 : ℝ)] ![(5080182688011/50000000000000 : ℝ), (43501064348973/100000000000000 : ℝ), (23169285128889/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-822884003/5000000000 : ℝ)|^4855 ≤ (5080182688011/50000000000000 : ℝ)^3831
        have hw : |(-822884003/5000000000 : ℝ)|=(822884003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1036994009/2000000000 : ℝ)|^4855 ≤ (43501064348973/100000000000000 : ℝ)^3831
        have hw : |(1036994009/2000000000 : ℝ)|=(1036994009/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1362513697/2500000000 : ℝ)|^4855 ≤ (23169285128889/50000000000000 : ℝ)^3831
        have hw : |(1362513697/2500000000 : ℝ)|=(1362513697/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1634_s5_3 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2639160111/5000000000 : ℝ)*x 0 + (-1517235321/10000000000 : ℝ)*x 1 + (5450054579/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2639160111/5000000000 : ℝ)^4855 ≤ (8899195441043/20000000000000 : ℝ)^3831 := by
    have hnat : (2639160111 : ℕ)^4855*20000000000000^3831 ≤ 8899195441043^3831*5000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639160111 5000000000 8899195441043 20000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1517235321/10000000000 : ℝ)^4855 ≤ (9165454770763/100000000000000 : ℝ)^3831 := by
    have hnat : (1517235321 : ℕ)^4855*100000000000000^3831 ≤ 9165454770763^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1517235321 10000000000 9165454770763 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5450054579/10000000000 : ℝ)^4855 ≤ (9267713601159/20000000000000 : ℝ)^3831 := by
    have hnat : (5450054579 : ℕ)^4855*20000000000000^3831 ≤ 9267713601159^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5450054579 10000000000 9267713601159 20000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2639160111/5000000000 : ℝ), (-1517235321/10000000000 : ℝ), (5450054579/10000000000 : ℝ)] ![(8899195441043/20000000000000 : ℝ), (9165454770763/100000000000000 : ℝ), (9267713601159/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2639160111/5000000000 : ℝ)|^4855 ≤ (8899195441043/20000000000000 : ℝ)^3831
        have hw : |(2639160111/5000000000 : ℝ)|=(2639160111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1517235321/10000000000 : ℝ)|^4855 ≤ (9165454770763/100000000000000 : ℝ)^3831
        have hw : |(-1517235321/10000000000 : ℝ)|=(1517235321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5450054579/10000000000 : ℝ)|^4855 ≤ (9267713601159/20000000000000 : ℝ)^3831
        have hw : |(5450054579/10000000000 : ℝ)|=(5450054579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1634_s5_4 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (527832007/1000000000 : ℝ)*x 0 + (1090010917/2000000000 : ℝ)*x 1 + (-60689421/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527832007/1000000000 : ℝ)^4855 ≤ (22247987790683/50000000000000 : ℝ)^3831 := by
    have hnat : (527832007 : ℕ)^4855*50000000000000^3831 ≤ 22247987790683^3831*1000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527832007 1000000000 22247987790683 50000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1090010917/2000000000 : ℝ)^4855 ≤ (9267713614089/20000000000000 : ℝ)^3831 := by
    have hnat : (1090010917 : ℕ)^4855*20000000000000^3831 ≤ 9267713614089^3831*2000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090010917 2000000000 9267713614089 20000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (60689421/400000000 : ℝ)^4855 ≤ (4582728166251/50000000000000 : ℝ)^3831 := by
    have hnat : (60689421 : ℕ)^4855*50000000000000^3831 ≤ 4582728166251^3831*400000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      60689421 400000000 4582728166251 50000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(527832007/1000000000 : ℝ), (1090010917/2000000000 : ℝ), (-60689421/400000000 : ℝ)] ![(22247987790683/50000000000000 : ℝ), (9267713614089/20000000000000 : ℝ), (4582728166251/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(527832007/1000000000 : ℝ)|^4855 ≤ (22247987790683/50000000000000 : ℝ)^3831
        have hw : |(527832007/1000000000 : ℝ)|=(527832007/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1090010917/2000000000 : ℝ)|^4855 ≤ (9267713614089/20000000000000 : ℝ)^3831
        have hw : |(1090010917/2000000000 : ℝ)|=(1090010917/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-60689421/400000000 : ℝ)|^4855 ≤ (4582728166251/50000000000000 : ℝ)^3831
        have hw : |(-60689421/400000000 : ℝ)|=(60689421/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1634_s5_5 (p : ℝ) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4193363999/10000000000 : ℝ)*x 0 + (4539546243/10000000000 : ℝ)*x 1 + (241719543/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4193363999/10000000000 : ℝ)^4855 ≤ (1038786143959/3125000000000 : ℝ)^3831 := by
    have hnat : (4193363999 : ℕ)^4855*3125000000000^3831 ≤ 1038786143959^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4193363999 10000000000 1038786143959 3125000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4539546243/10000000000 : ℝ)^4855 ≤ (36756506339491/100000000000000 : ℝ)^3831 := by
    have hnat : (4539546243 : ℕ)^4855*100000000000000^3831 ≤ 36756506339491^3831*10000000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4539546243 10000000000 36756506339491 100000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (241719543/625000000 : ℝ)^4855 ≤ (7500584258949/25000000000000 : ℝ)^3831 := by
    have hnat : (241719543 : ℕ)^4855*25000000000000^3831 ≤ 7500584258949^3831*625000000^4855 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      241719543 625000000 7500584258949 25000000000000 4855 3831 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4855/1024 : ℝ)) 4855 3831 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4193363999/10000000000 : ℝ), (4539546243/10000000000 : ℝ), (241719543/625000000 : ℝ)] ![(1038786143959/3125000000000 : ℝ), (36756506339491/100000000000000 : ℝ), (7500584258949/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4193363999/10000000000 : ℝ)|^4855 ≤ (1038786143959/3125000000000 : ℝ)^3831
        have hw : |(4193363999/10000000000 : ℝ)|=(4193363999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4539546243/10000000000 : ℝ)|^4855 ≤ (36756506339491/100000000000000 : ℝ)^3831
        have hw : |(4539546243/10000000000 : ℝ)|=(4539546243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(241719543/625000000 : ℝ)|^4855 ≤ (7500584258949/25000000000000 : ℝ)^3831
        have hw : |(241719543/625000000 : ℝ)|=(241719543/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1634_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (17675869/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16299/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10583/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10583/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8149/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16299/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10583/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16299/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10583/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16299/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10583/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16299/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10583/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16299/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10583/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16299/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10583/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10583/100000 : ℝ) ^ (4851/1024 : ℝ) ≤ (1197414966461471/50000000000000000000 : ℝ) := by
    have hpowers : (10583/100000 : ℝ)^4851 ≤ (1197414966461471/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10583 : ℕ)^4851*50000000000000000000^1024 ≤ 1197414966461471^1024*100000^4851 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10583 100000 1197414966461471 50000000000000000000 4851 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10583/100000 : ℝ)) (X := (1197414966461471/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4851 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16299/100000 : ℝ) ^ (4851/1024 : ℝ) ≤ (18525349990466021/100000000000000000000 : ℝ) := by
    have hpowers : (16299/100000 : ℝ)^4851 ≤ (18525349990466021/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16299 : ℕ)^4851*100000000000000000000^1024 ≤ 18525349990466021^1024*100000^4851 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16299 100000 18525349990466021 100000000000000000000 4851 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16299/100000 : ℝ)) (X := (18525349990466021/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4851 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25001197414966461471/25000000000000000000 : ℝ) ≤ (2500025275814483/2500000000000000 : ℝ) ^ (4851/1024 : ℝ) := by
    have hpowers : (25001197414966461471/25000000000000000000 : ℝ)^1024 ≤ (2500025275814483/2500000000000000 : ℝ)^4851 := by
      have hnat : (25001197414966461471 : ℕ)^1024*2500000000000000^4851 ≤ 2500025275814483^4851*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001197414966461471 25000000000000000000 2500025275814483 2500000000000000 1024 4851 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500025275814483/2500000000000000 : ℝ)) (X := (25001197414966461471/25000000000000000000 : ℝ)) (by norm_num) 4851 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100020920179923388963/100000000000000000000 : ℝ) ≤ (2000088313736067/2000000000000000 : ℝ) ^ (4851/1024 : ℝ) := by
    have hpowers : (100020920179923388963/100000000000000000000 : ℝ)^1024 ≤ (2000088313736067/2000000000000000 : ℝ)^4851 := by
      have hnat : (100020920179923388963 : ℕ)^1024*2000000000000000^4851 ≤ 2000088313736067^4851*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100020920179923388963 100000000000000000000 2000088313736067 2000000000000000 1024 4851 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000088313736067/2000000000000000 : ℝ)) (X := (100020920179923388963/100000000000000000000 : ℝ)) (by norm_num) 4851 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50018525349990466021/50000000000000000000 : ℝ) ≤ (5000391017051369/5000000000000000 : ℝ) ^ (4851/1024 : ℝ) := by
    have hpowers : (50018525349990466021/50000000000000000000 : ℝ)^1024 ≤ (5000391017051369/5000000000000000 : ℝ)^4851 := by
      have hnat : (50018525349990466021 : ℕ)^1024*5000000000000000^4851 ≤ 5000391017051369^4851*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018525349990466021 50000000000000000000 5000391017051369 5000000000000000 1024 4851 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000391017051369/5000000000000000 : ℝ)) (X := (50018525349990466021/50000000000000000000 : ℝ)) (by norm_num) 4851 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1197414966461471/50000000000000000000 : ℝ) ≤ ((28576685807545878707/28580000000000000000 : ℝ)+2*(340465422403/571600000000000 : ℝ)*(10583/100000 : ℝ))^(4851/1024 : ℝ) := by
    rw [show (28576685807545878707/28580000000000000000 : ℝ)+2*(340465422403/571600000000000 : ℝ)*(10583/100000 : ℝ)=(2500025275814483/2500000000000000 : ℝ) by norm_num, show 1+2*(1197414966461471/50000000000000000000 : ℝ)=(25001197414966461471/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18525349990466021/100000000000000000000 : ℝ)+(1197414966461471/50000000000000000000 : ℝ) ≤ ((28576685807545878707/28580000000000000000 : ℝ)+(340465422403/571600000000000 : ℝ)*((16299/100000 : ℝ)+(10583/100000 : ℝ)))^(4851/1024 : ℝ) := by
    rw [show (28576685807545878707/28580000000000000000 : ℝ)+(340465422403/571600000000000 : ℝ)*((16299/100000 : ℝ)+(10583/100000 : ℝ))=(2000088313736067/2000000000000000 : ℝ) by norm_num, show 1+(18525349990466021/100000000000000000000 : ℝ)+(1197414966461471/50000000000000000000 : ℝ)=(100020920179923388963/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18525349990466021/100000000000000000000 : ℝ) ≤ ((28576685807545878707/28580000000000000000 : ℝ)+2*(340465422403/571600000000000 : ℝ)*(16299/100000 : ℝ))^(4851/1024 : ℝ) := by
    rw [show (28576685807545878707/28580000000000000000 : ℝ)+2*(340465422403/571600000000000 : ℝ)*(16299/100000 : ℝ)=(5000391017051369/5000000000000000 : ℝ) by norm_num, show 1+2*(18525349990466021/100000000000000000000 : ℝ)=(50018525349990466021/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (28576685807545878707/28580000000000000000 : ℝ)*(X 1 0+X 2 0)+(340465422403/571600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4851/1024 : ℝ)) (lo := (10583/100000 : ℝ)) (hi := (16299/100000 : ℝ)) (c := (28576685807545878707/28580000000000000000 : ℝ)) (alpha := (340465422403/571600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (28576685807545878707/28580000000000000000 : ℝ)*(X 0 1+X 2 1)+(340465422403/571600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4851/1024 : ℝ)) (lo := (10583/100000 : ℝ)) (hi := (16299/100000 : ℝ)) (c := (28576685807545878707/28580000000000000000 : ℝ)) (alpha := (340465422403/571600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (28576685807545878707/28580000000000000000 : ℝ)*(X 0 2+X 1 2)+(340465422403/571600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4851/1024 : ℝ)) (lo := (10583/100000 : ℝ)) (hi := (16299/100000 : ℝ)) (c := (28576685807545878707/28580000000000000000 : ℝ)) (alpha := (340465422403/571600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-51428169/312500000 : ℝ)*X 0 0+(5452095863/10000000000 : ℝ)*X 0 1+(5182950383/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350074321/10000000000 : ℝ)*X 1 0+(-4460849/25000000 : ℝ)*X 1 1+(323934391/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((-822884003/5000000000 : ℝ)*X 0 0+(1036994009/2000000000 : ℝ)*X 0 1+(1362513697/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_s5_2 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2639160111/5000000000 : ℝ)*X 1 0+(-1517235321/10000000000 : ℝ)*X 1 1+(5450054579/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_s5_3 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((527832007/1000000000 : ℝ)*X 2 0+(1090010917/2000000000 : ℝ)*X 2 1+(-60689421/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_s5_4 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4193363999/10000000000 : ℝ)*X 0 0+(4539546243/10000000000 : ℝ)*X 0 1+(241719543/625000000 : ℝ)*X 0 2+(4193363999/10000000000 : ℝ)*X 1 0+(4539546243/10000000000 : ℝ)*X 1 1+(241719543/625000000 : ℝ)*X 1 2+(4193363999/10000000000 : ℝ)*X 2 0+(4539546243/10000000000 : ℝ)*X 2 1+(241719543/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1634_s5_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9283849018174748660970066729/1429000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (206951471/20000000000000 : ℝ)*(base19) + (956116089/100000000000000 : ℝ)*(base23) + (102048243/50000000000000 : ℝ)*(lower1) + (67237091/100000000000000 : ℝ)*(upper2) + (59582277/20000000000000 : ℝ)*(upper5) + (2630195805999151/100000000000000 : ℝ)*(major0) + (2630195805999151/100000000000000 : ℝ)*(major1) + (2630195805999151/100000000000000 : ℝ)*(major2) + (32666691/25000000000000 : ℝ)*(sp0) + (7164240537/100000000000000 : ℝ)*(sp1) + (943094068315491/25000000000000 : ℝ)*(sp2) + (943092051232709/25000000000000 : ℝ)*(sp3) + (1886187723906319/50000000000000 : ℝ)*(sp4) + (744007495755697/50000000000000 : ℝ)*(sp5) + (744007495755697/50000000000000 : ℝ)*(f.failure) + (471547050491091/12500000000000 : ℝ)*(f.sum) + (6812216576053/28580000000000000000000000000 : ℝ)*base65 + (3970591246148372243/2858000000000000000000000000000000 : ℝ)*base68 + (2150207694255627757/2858000000000000000000000000000000 : ℝ)*base69 + (3301698012033627757/2858000000000000000000000000000000 : ℝ)*base71 + (38698348956027/28580000000000000000000000000 : ℝ)*base74 + (28185093801120372243/2858000000000000000000000000000000 : ℝ)*base76 + (13264889813155627757/2858000000000000000000000000000000 : ℝ)*base77 + (11065405291407627757/2858000000000000000000000000000000 : ℝ)*base79 + (38276306266907/28580000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (1175693/500000000000000000000 : ℝ)*base89 + (1175693/500000000000000000000 : ℝ)*base91 + (1175693/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1634_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (17675869/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16299/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10583/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10583/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8149/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1634_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1634_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (17675869/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (41/250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10491/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10583/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8149/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1634_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1634_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1634_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4851/1024 : ℝ) ≤ p) (hpb : p ≤ (4855/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (17675869/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (41/250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10491/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10583/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8149/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1634_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
