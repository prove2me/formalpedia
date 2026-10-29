-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1370_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:20:36.371792+00:00
-- url     : https://prove2.me/submissions/9c12ef40-54a9-42c1-9086-d13b690ad23e

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
theorem support_rectangle_w1370_s6_0 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-126251461/625000000 : ℝ)*x 0 + (1352818381/2500000000 : ℝ)*x 1 + (5245419139/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (126251461/625000000 : ℝ)^2165 ≤ (1538535744219/12500000000000 : ℝ)^1653 := by
    have hnat : (126251461 : ℕ)^2165*12500000000000^1653 ≤ 1538535744219^1653*625000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126251461 625000000 1538535744219 12500000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352818381/2500000000 : ℝ)^2165 ≤ (22369779830479/50000000000000 : ℝ)^1653 := by
    have hnat : (1352818381 : ℕ)^2165*50000000000000^1653 ≤ 22369779830479^1653*2500000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352818381 2500000000 22369779830479 50000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245419139/10000000000 : ℝ)^2165 ≤ (42952154378513/100000000000000 : ℝ)^1653 := by
    have hnat : (5245419139 : ℕ)^2165*100000000000000^1653 ≤ 42952154378513^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245419139 10000000000 42952154378513 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-126251461/625000000 : ℝ), (1352818381/2500000000 : ℝ), (5245419139/10000000000 : ℝ)] ![(1538535744219/12500000000000 : ℝ), (22369779830479/50000000000000 : ℝ), (42952154378513/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-126251461/625000000 : ℝ)|^2165 ≤ (1538535744219/12500000000000 : ℝ)^1653
        have hw : |(-126251461/625000000 : ℝ)|=(126251461/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352818381/2500000000 : ℝ)|^2165 ≤ (22369779830479/50000000000000 : ℝ)^1653
        have hw : |(1352818381/2500000000 : ℝ)|=(1352818381/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245419139/10000000000 : ℝ)|^2165 ≤ (42952154378513/100000000000000 : ℝ)^1653
        have hw : |(5245419139/10000000000 : ℝ)|=(5245419139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_s6_1 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5348500063/10000000000 : ℝ)*x 0 + (-13153161/62500000 : ℝ)*x 1 + (2622709603/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348500063/10000000000 : ℝ)^2165 ≤ (5507628463937/12500000000000 : ℝ)^1653 := by
    have hnat : (5348500063 : ℕ)^2165*12500000000000^1653 ≤ 5507628463937^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348500063 10000000000 5507628463937 12500000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (13153161/62500000 : ℝ)^2165 ≤ (12986817172401/100000000000000 : ℝ)^1653 := by
    have hnat : (13153161 : ℕ)^2165*100000000000000^1653 ≤ 12986817172401^1653*62500000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13153161 62500000 12986817172401 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622709603/5000000000 : ℝ)^2165 ≤ (1718086203883/4000000000000 : ℝ)^1653 := by
    have hnat : (2622709603 : ℕ)^2165*4000000000000^1653 ≤ 1718086203883^1653*5000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622709603 5000000000 1718086203883 4000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348500063/10000000000 : ℝ), (-13153161/62500000 : ℝ), (2622709603/5000000000 : ℝ)] ![(5507628463937/12500000000000 : ℝ), (12986817172401/100000000000000 : ℝ), (1718086203883/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348500063/10000000000 : ℝ)|^2165 ≤ (5507628463937/12500000000000 : ℝ)^1653
        have hw : |(5348500063/10000000000 : ℝ)|=(5348500063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-13153161/62500000 : ℝ)|^2165 ≤ (12986817172401/100000000000000 : ℝ)^1653
        have hw : |(-13153161/62500000 : ℝ)|=(13153161/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622709603/5000000000 : ℝ)|^2165 ≤ (1718086203883/4000000000000 : ℝ)^1653
        have hw : |(2622709603/5000000000 : ℝ)|=(2622709603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_s6_2 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (66856251/125000000 : ℝ)*x 0 + (5245419107/10000000000 : ℝ)*x 1 + (-526126467/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66856251/125000000 : ℝ)^2165 ≤ (1101525697373/2500000000000 : ℝ)^1653 := by
    have hnat : (66856251 : ℕ)^2165*2500000000000^1653 ≤ 1101525697373^1653*125000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66856251 125000000 1101525697373 2500000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245419107/10000000000 : ℝ)^2165 ≤ (42952154035319/100000000000000 : ℝ)^1653 := by
    have hnat : (5245419107 : ℕ)^2165*100000000000000^1653 ≤ 42952154035319^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245419107 10000000000 42952154035319 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526126467/2500000000 : ℝ)^2165 ≤ (2597363609059/20000000000000 : ℝ)^1653 := by
    have hnat : (526126467 : ℕ)^2165*20000000000000^1653 ≤ 2597363609059^1653*2500000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526126467 2500000000 2597363609059 20000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66856251/125000000 : ℝ), (5245419107/10000000000 : ℝ), (-526126467/2500000000 : ℝ)] ![(1101525697373/2500000000000 : ℝ), (42952154035319/100000000000000 : ℝ), (2597363609059/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66856251/125000000 : ℝ)|^2165 ≤ (1101525697373/2500000000000 : ℝ)^1653
        have hw : |(66856251/125000000 : ℝ)|=(66856251/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245419107/10000000000 : ℝ)|^2165 ≤ (42952154035319/100000000000000 : ℝ)^1653
        have hw : |(5245419107/10000000000 : ℝ)|=(5245419107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-526126467/2500000000 : ℝ)|^2165 ≤ (2597363609059/20000000000000 : ℝ)^1653
        have hw : |(-526126467/2500000000 : ℝ)|=(526126467/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_s6_3 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (863869961/2000000000 : ℝ)*x 0 + (4147113279/10000000000 : ℝ)*x 1 + (4498170443/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (863869961/2000000000 : ℝ)^2165 ≤ (4162966601877/12500000000000 : ℝ)^1653 := by
    have hnat : (863869961 : ℕ)^2165*12500000000000^1653 ≤ 4162966601877^1653*2000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      863869961 2000000000 4162966601877 12500000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4147113279/10000000000 : ℝ)^2165 ≤ (15787616492167/50000000000000 : ℝ)^1653 := by
    have hnat : (4147113279 : ℕ)^2165*50000000000000^1653 ≤ 15787616492167^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4147113279 10000000000 15787616492167 50000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4498170443/10000000000 : ℝ)^2165 ≤ (8780258544641/25000000000000 : ℝ)^1653 := by
    have hnat : (4498170443 : ℕ)^2165*25000000000000^1653 ≤ 8780258544641^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4498170443 10000000000 8780258544641 25000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(863869961/2000000000 : ℝ), (4147113279/10000000000 : ℝ), (4498170443/10000000000 : ℝ)] ![(4162966601877/12500000000000 : ℝ), (15787616492167/50000000000000 : ℝ), (8780258544641/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(863869961/2000000000 : ℝ)|^2165 ≤ (4162966601877/12500000000000 : ℝ)^1653
        have hw : |(863869961/2000000000 : ℝ)|=(863869961/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4147113279/10000000000 : ℝ)|^2165 ≤ (15787616492167/50000000000000 : ℝ)^1653
        have hw : |(4147113279/10000000000 : ℝ)|=(4147113279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4498170443/10000000000 : ℝ)|^2165 ≤ (8780258544641/25000000000000 : ℝ)^1653
        have hw : |(4498170443/10000000000 : ℝ)|=(4498170443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_s6_4 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-505008827/2500000000 : ℝ)*x 0 + (5246014533/10000000000 : ℝ)*x 1 + (1352668757/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (505008827/2500000000 : ℝ)^2165 ≤ (3077095294079/25000000000000 : ℝ)^1653 := by
    have hnat : (505008827 : ℕ)^2165*25000000000000^1653 ≤ 3077095294079^1653*2500000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      505008827 2500000000 3077095294079 25000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246014533/10000000000 : ℝ)^2165 ≤ (42958539981159/100000000000000 : ℝ)^1653 := by
    have hnat : (5246014533 : ℕ)^2165*100000000000000^1653 ≤ 42958539981159^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246014533 10000000000 42958539981159 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1352668757/2500000000 : ℝ)^2165 ≤ (698954356629/1562500000000 : ℝ)^1653 := by
    have hnat : (1352668757 : ℕ)^2165*1562500000000^1653 ≤ 698954356629^1653*2500000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352668757 2500000000 698954356629 1562500000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-505008827/2500000000 : ℝ), (5246014533/10000000000 : ℝ), (1352668757/2500000000 : ℝ)] ![(3077095294079/25000000000000 : ℝ), (42958539981159/100000000000000 : ℝ), (698954356629/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-505008827/2500000000 : ℝ)|^2165 ≤ (3077095294079/25000000000000 : ℝ)^1653
        have hw : |(-505008827/2500000000 : ℝ)|=(505008827/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246014533/10000000000 : ℝ)|^2165 ≤ (42958539981159/100000000000000 : ℝ)^1653
        have hw : |(5246014533/10000000000 : ℝ)|=(5246014533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1352668757/2500000000 : ℝ)|^2165 ≤ (698954356629/1562500000000 : ℝ)^1653
        have hw : |(1352668757/2500000000 : ℝ)|=(1352668757/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_s6_5 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (10611289/20000000 : ℝ)*x 0 + (-969624951/5000000000 : ℝ)*x 1 + (5410675697/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10611289/20000000 : ℝ)^2165 ≤ (10899801428933/25000000000000 : ℝ)^1653 := by
    have hnat : (10611289 : ℕ)^2165*25000000000000^1653 ≤ 10899801428933^1653*20000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10611289 20000000 10899801428933 25000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (969624951/5000000000 : ℝ)^2165 ≤ (2333541641071/20000000000000 : ℝ)^1653 := by
    have hnat : (969624951 : ℕ)^2165*20000000000000^1653 ≤ 2333541641071^1653*5000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      969624951 5000000000 2333541641071 20000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5410675697/10000000000 : ℝ)^2165 ≤ (5591635758553/12500000000000 : ℝ)^1653 := by
    have hnat : (5410675697 : ℕ)^2165*12500000000000^1653 ≤ 5591635758553^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410675697 10000000000 5591635758553 12500000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(10611289/20000000 : ℝ), (-969624951/5000000000 : ℝ), (5410675697/10000000000 : ℝ)] ![(10899801428933/25000000000000 : ℝ), (2333541641071/20000000000000 : ℝ), (5591635758553/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(10611289/20000000 : ℝ)|^2165 ≤ (10899801428933/25000000000000 : ℝ)^1653
        have hw : |(10611289/20000000 : ℝ)|=(10611289/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-969624951/5000000000 : ℝ)|^2165 ≤ (2333541641071/20000000000000 : ℝ)^1653
        have hw : |(-969624951/5000000000 : ℝ)|=(969624951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5410675697/10000000000 : ℝ)|^2165 ≤ (5591635758553/12500000000000 : ℝ)^1653
        have hw : |(5410675697/10000000000 : ℝ)|=(5410675697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_s6_6 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305644537/10000000000 : ℝ)*x 0 + (1352668887/2500000000 : ℝ)*x 1 + (-387850011/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305644537/10000000000 : ℝ)^2165 ≤ (10899801528489/25000000000000 : ℝ)^1653 := by
    have hnat : (5305644537 : ℕ)^2165*25000000000000^1653 ≤ 10899801528489^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305644537 10000000000 10899801528489 25000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352668887/2500000000 : ℝ)^2165 ≤ (8946616891/20000000000 : ℝ)^1653 := by
    have hnat : (1352668887 : ℕ)^2165*20000000000^1653 ≤ 8946616891^1653*2500000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352668887 2500000000 8946616891 20000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (387850011/2000000000 : ℝ)^2165 ≤ (466708376441/4000000000000 : ℝ)^1653 := by
    have hnat : (387850011 : ℕ)^2165*4000000000000^1653 ≤ 466708376441^1653*2000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      387850011 2000000000 466708376441 4000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305644537/10000000000 : ℝ), (1352668887/2500000000 : ℝ), (-387850011/2000000000 : ℝ)] ![(10899801528489/25000000000000 : ℝ), (8946616891/20000000000 : ℝ), (466708376441/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305644537/10000000000 : ℝ)|^2165 ≤ (10899801528489/25000000000000 : ℝ)^1653
        have hw : |(5305644537/10000000000 : ℝ)|=(5305644537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352668887/2500000000 : ℝ)|^2165 ≤ (8946616891/20000000000 : ℝ)^1653
        have hw : |(1352668887/2500000000 : ℝ)|=(1352668887/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-387850011/2000000000 : ℝ)|^2165 ≤ (466708376441/4000000000000 : ℝ)^1653
        have hw : |(-387850011/2000000000 : ℝ)|=(387850011/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_s6_7 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4319375073/10000000000 : ℝ)*x 0 + (2248455139/5000000000 : ℝ)*x 1 + (4148379859/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4319375073/10000000000 : ℝ)^2165 ≤ (33303987985739/100000000000000 : ℝ)^1653 := by
    have hnat : (4319375073 : ℕ)^2165*100000000000000^1653 ≤ 33303987985739^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4319375073 10000000000 33303987985739 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2248455139/5000000000 : ℝ)^2165 ≤ (17554073987253/50000000000000 : ℝ)^1653 := by
    have hnat : (2248455139 : ℕ)^2165*50000000000000^1653 ≤ 17554073987253^1653*5000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248455139 5000000000 17554073987253 50000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4148379859/10000000000 : ℝ)^2165 ≤ (6317572803517/20000000000000 : ℝ)^1653 := by
    have hnat : (4148379859 : ℕ)^2165*20000000000000^1653 ≤ 6317572803517^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4148379859 10000000000 6317572803517 20000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4319375073/10000000000 : ℝ), (2248455139/5000000000 : ℝ), (4148379859/10000000000 : ℝ)] ![(33303987985739/100000000000000 : ℝ), (17554073987253/50000000000000 : ℝ), (6317572803517/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4319375073/10000000000 : ℝ)|^2165 ≤ (33303987985739/100000000000000 : ℝ)^1653
        have hw : |(4319375073/10000000000 : ℝ)|=(4319375073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2248455139/5000000000 : ℝ)|^2165 ≤ (17554073987253/50000000000000 : ℝ)^1653
        have hw : |(2248455139/5000000000 : ℝ)|=(2248455139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4148379859/10000000000 : ℝ)|^2165 ≤ (6317572803517/20000000000000 : ℝ)^1653
        have hw : |(4148379859/10000000000 : ℝ)|=(4148379859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1370_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155832971/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14731/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11207/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11213/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (589/4000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14731/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11207/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14731/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11207/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14731/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11207/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14731/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11207/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14731/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11207/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14731/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11207/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11207/100000 : ℝ) ^ (4329/1024 : ℝ) ≤ (4793460962454301/50000000000000000000 : ℝ) := by
    have hpowers : (11207/100000 : ℝ)^4329 ≤ (4793460962454301/50000000000000000000 : ℝ)^1024 := by
      have hnat : (11207 : ℕ)^4329*50000000000000000000^1024 ≤ 4793460962454301^1024*100000^4329 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11207 100000 4793460962454301 50000000000000000000 4329 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11207/100000 : ℝ)) (X := (4793460962454301/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4329 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14731/100000 : ℝ) ^ (4329/1024 : ℝ) ≤ (6091149445737083/20000000000000000000 : ℝ) := by
    have hpowers : (14731/100000 : ℝ)^4329 ≤ (6091149445737083/20000000000000000000 : ℝ)^1024 := by
      have hnat : (14731 : ℕ)^4329*20000000000000000000^1024 ≤ 6091149445737083^1024*100000^4329 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14731 100000 6091149445737083 20000000000000000000 4329 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14731/100000 : ℝ)) (X := (6091149445737083/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4329 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004793460962454301/25000000000000000000 : ℝ) ≤ (2000090702606667/2000000000000000 : ℝ) ^ (4329/1024 : ℝ) := by
    have hpowers : (25004793460962454301/25000000000000000000 : ℝ)^1024 ≤ (2000090702606667/2000000000000000 : ℝ)^4329 := by
      have hnat : (25004793460962454301 : ℕ)^1024*2000000000000000^4329 ≤ 2000090702606667^4329*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004793460962454301 25000000000000000000 2000090702606667 2000000000000000 1024 4329 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000090702606667/2000000000000000 : ℝ)) (X := (25004793460962454301/25000000000000000000 : ℝ)) (by norm_num) 4329 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100040042669153594017/100000000000000000000 : ℝ) ≤ (10000947041513243/10000000000000000 : ℝ) ^ (4329/1024 : ℝ) := by
    have hpowers : (100040042669153594017/100000000000000000000 : ℝ)^1024 ≤ (10000947041513243/10000000000000000 : ℝ)^4329 := by
      have hnat : (100040042669153594017 : ℕ)^1024*10000000000000000^4329 ≤ 10000947041513243^4329*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100040042669153594017 100000000000000000000 10000947041513243 10000000000000000 1024 4329 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000947041513243/10000000000000000 : ℝ)) (X := (100040042669153594017/100000000000000000000 : ℝ)) (by norm_num) 4329 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006091149445737083/10000000000000000000 : ℝ) ≤ (10001440569993151/10000000000000000 : ℝ) ^ (4329/1024 : ℝ) := by
    have hpowers : (10006091149445737083/10000000000000000000 : ℝ)^1024 ≤ (10001440569993151/10000000000000000 : ℝ)^4329 := by
      have hnat : (10006091149445737083 : ℕ)^1024*10000000000000000^4329 ≤ 10001440569993151^4329*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006091149445737083 10000000000000000000 10001440569993151 10000000000000000 1024 4329 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001440569993151/10000000000000000 : ℝ)) (X := (10006091149445737083/10000000000000000000 : ℝ)) (by norm_num) 4329 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4793460962454301/50000000000000000000 : ℝ) ≤ ((8807634058145203657/8810000000000000000 : ℝ)+2*(123382119977/88100000000000 : ℝ)*(11207/100000 : ℝ))^(4329/1024 : ℝ) := by
    rw [show (8807634058145203657/8810000000000000000 : ℝ)+2*(123382119977/88100000000000 : ℝ)*(11207/100000 : ℝ)=(2000090702606667/2000000000000000 : ℝ) by norm_num, show 1+2*(4793460962454301/50000000000000000000 : ℝ)=(25004793460962454301/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6091149445737083/20000000000000000000 : ℝ)+(4793460962454301/50000000000000000000 : ℝ) ≤ ((8807634058145203657/8810000000000000000 : ℝ)+(123382119977/88100000000000 : ℝ)*((14731/100000 : ℝ)+(11207/100000 : ℝ)))^(4329/1024 : ℝ) := by
    rw [show (8807634058145203657/8810000000000000000 : ℝ)+(123382119977/88100000000000 : ℝ)*((14731/100000 : ℝ)+(11207/100000 : ℝ))=(10000947041513243/10000000000000000 : ℝ) by norm_num, show 1+(6091149445737083/20000000000000000000 : ℝ)+(4793460962454301/50000000000000000000 : ℝ)=(100040042669153594017/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6091149445737083/20000000000000000000 : ℝ) ≤ ((8807634058145203657/8810000000000000000 : ℝ)+2*(123382119977/88100000000000 : ℝ)*(14731/100000 : ℝ))^(4329/1024 : ℝ) := by
    rw [show (8807634058145203657/8810000000000000000 : ℝ)+2*(123382119977/88100000000000 : ℝ)*(14731/100000 : ℝ)=(10001440569993151/10000000000000000 : ℝ) by norm_num, show 1+2*(6091149445737083/20000000000000000000 : ℝ)=(10006091149445737083/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8807634058145203657/8810000000000000000 : ℝ)*(X 1 0+X 2 0)+(123382119977/88100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4329/1024 : ℝ)) (lo := (11207/100000 : ℝ)) (hi := (14731/100000 : ℝ)) (c := (8807634058145203657/8810000000000000000 : ℝ)) (alpha := (123382119977/88100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8807634058145203657/8810000000000000000 : ℝ)*(X 0 1+X 2 1)+(123382119977/88100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4329/1024 : ℝ)) (lo := (11207/100000 : ℝ)) (hi := (14731/100000 : ℝ)) (c := (8807634058145203657/8810000000000000000 : ℝ)) (alpha := (123382119977/88100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8807634058145203657/8810000000000000000 : ℝ)*(X 0 2+X 1 2)+(123382119977/88100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4329/1024 : ℝ)) (lo := (11207/100000 : ℝ)) (hi := (14731/100000 : ℝ)) (c := (8807634058145203657/8810000000000000000 : ℝ)) (alpha := (123382119977/88100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-126251461/625000000 : ℝ)*X 0 0+(1352818381/2500000000 : ℝ)*X 0 1+(5245419139/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348500063/10000000000 : ℝ)*X 1 0+(-13153161/62500000 : ℝ)*X 1 1+(2622709603/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((66856251/125000000 : ℝ)*X 2 0+(5245419107/10000000000 : ℝ)*X 2 1+(-526126467/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((863869961/2000000000 : ℝ)*X 0 0+(4147113279/10000000000 : ℝ)*X 0 1+(4498170443/10000000000 : ℝ)*X 0 2+(863869961/2000000000 : ℝ)*X 1 0+(4147113279/10000000000 : ℝ)*X 1 1+(4498170443/10000000000 : ℝ)*X 1 2+(863869961/2000000000 : ℝ)*X 2 0+(4147113279/10000000000 : ℝ)*X 2 1+(4498170443/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-505008827/2500000000 : ℝ)*X 0 0+(5246014533/10000000000 : ℝ)*X 0 1+(1352668757/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((10611289/20000000 : ℝ)*X 1 0+(-969624951/5000000000 : ℝ)*X 1 1+(5410675697/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305644537/10000000000 : ℝ)*X 2 0+(1352668887/2500000000 : ℝ)*X 2 1+(-387850011/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4319375073/10000000000 : ℝ)*X 0 0+(2248455139/5000000000 : ℝ)*X 0 1+(4148379859/10000000000 : ℝ)*X 0 2+(4319375073/10000000000 : ℝ)*X 1 0+(2248455139/5000000000 : ℝ)*X 1 1+(4148379859/10000000000 : ℝ)*X 1 2+(4319375073/10000000000 : ℝ)*X 2 0+(2248455139/5000000000 : ℝ)*X 2 1+(4148379859/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14791030093713380342469/2202500000000000000000000000 : ℝ) := by norm_num
    linear_combination (330791683/25000000000000 : ℝ)*(base19) + (611637079/50000000000000 : ℝ)*(base23) + (15595261/20000000000000 : ℝ)*(lower2) + (109178217/50000000000000 : ℝ)*(upper3) + (2859741/20000000000000 : ℝ)*(lower4) + (2219503481833651/50000000000000 : ℝ)*(major0) + (2219503481833651/50000000000000 : ℝ)*(major1) + (2219503481833651/50000000000000 : ℝ)*(major2) + (6029419161629721/100000000000000 : ℝ)*(sp0) + (188420160581873/3125000000000 : ℝ)*(sp1) + (6029445238512509/100000000000000 : ℝ)*(sp2) + (35606889340297/1250000000000 : ℝ)*(sp3) + (13650078473/50000000000000 : ℝ)*(sp4) + (502952251/3125000000000 : ℝ)*(sp7) + (178035452605987/6250000000000 : ℝ)*(f.failure) + (6029446461786667/100000000000000 : ℝ)*(f.sum) + (12343834023447/2202500000000000000000000000 : ℝ)*base65 + (564870741794561707/440500000000000000000000000000000 : ℝ)*base67 + (1137720324856061707/440500000000000000000000000000000 : ℝ)*base69 + (1595528094518438293/440500000000000000000000000000000 : ℝ)*base72 + (1698876277613/2202500000000000000000000000 : ℝ)*base74 + (386989421158438293/440500000000000000000000000000000 : ℝ)*base76 + (2493463007774438293/440500000000000000000000000000000 : ℝ)*base78 + (5352486204534061707/440500000000000000000000000000000 : ℝ)*base79 + (3271717396937/2202500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (9097377/625000000000000000000 : ℝ)*base89 + (9097377/625000000000000000000 : ℝ)*base91 + (9097377/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (695595949434251053885077903/55062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (842954287/100000000000000 : ℝ)*(base19) + (576447443/50000000000000 : ℝ)*(base23) + (140030279/50000000000000 : ℝ)*(upper3) + (16987527/12500000000000 : ℝ)*(lower4) + (3585693/1562500000000 : ℝ)*(upper5) + (558892974950693/12500000000000 : ℝ)*(major0) + (558892974950693/12500000000000 : ℝ)*(major1) + (558892974950693/12500000000000 : ℝ)*(major2) + (6209604369/20000000000000 : ℝ)*(sp1) + (32465073609/100000000000000 : ℝ)*(sp2) + (1214619463990729/20000000000000 : ℝ)*(sp4) + (6073065428977513/100000000000000 : ℝ)*(sp5) + (121461274039703/2000000000000 : ℝ)*(sp6) + (57383797163253/2000000000000 : ℝ)*(sp7) + (57383797163253/2000000000000 : ℝ)*(f.failure) + (1214619463990729/20000000000000 : ℝ)*(f.sum) + (4421208623769/2202500000000000000000000000 : ℝ)*base65 + (636364574861240699/110125000000000000000000000000000 : ℝ)*base68 + (935673744601865699/110125000000000000000000000000000 : ℝ)*base70 + (1178442630448740699/110125000000000000000000000000000 : ℝ)*base72 + (2980534865991/2202500000000000000000000000 : ℝ)*base74 + (1255804992641759301/110125000000000000000000000000000 : ℝ)*base75 + (405704444509384301/110125000000000000000000000000000 : ℝ)*base77 + (241878828013490699/110125000000000000000000000000000 : ℝ)*base80 + (491851565269/550625000000000000000000000 : ℝ)*base82 + (985337/200000000000000000000 : ℝ)*base90 + (985337/200000000000000000000 : ℝ)*base92 + (985337/200000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1370_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155832971/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14731/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11207/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11213/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (589/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1370_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1370_s7_0 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-404005607/2000000000 : ℝ)*x 0 + (5411226013/10000000000 : ℝ)*x 1 + (2622731821/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (404005607/2000000000 : ℝ)^2165 ≤ (12308323134583/100000000000000 : ℝ)^1653 := by
    have hnat : (404005607 : ℕ)^2165*100000000000000^1653 ≤ 12308323134583^1653*2000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      404005607 2000000000 12308323134583 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5411226013/10000000000 : ℝ)^2165 ≤ (22369522589087/50000000000000 : ℝ)^1653 := by
    have hnat : (5411226013 : ℕ)^2165*50000000000000^1653 ≤ 22369522589087^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411226013 10000000000 22369522589087 50000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622731821/5000000000 : ℝ)^2165 ≤ (21476315832787/50000000000000 : ℝ)^1653 := by
    have hnat : (2622731821 : ℕ)^2165*50000000000000^1653 ≤ 21476315832787^1653*5000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622731821 5000000000 21476315832787 50000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-404005607/2000000000 : ℝ), (5411226013/10000000000 : ℝ), (2622731821/5000000000 : ℝ)] ![(12308323134583/100000000000000 : ℝ), (22369522589087/50000000000000 : ℝ), (21476315832787/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-404005607/2000000000 : ℝ)|^2165 ≤ (12308323134583/100000000000000 : ℝ)^1653
        have hw : |(-404005607/2000000000 : ℝ)|=(404005607/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5411226013/10000000000 : ℝ)|^2165 ≤ (22369522589087/50000000000000 : ℝ)^1653
        have hw : |(5411226013/10000000000 : ℝ)|=(5411226013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622731821/5000000000 : ℝ)|^2165 ≤ (21476315832787/50000000000000 : ℝ)^1653
        have hw : |(2622731821/5000000000 : ℝ)|=(2622731821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_s7_1 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5348488069/10000000000 : ℝ)*x 0 + (-210446279/1000000000 : ℝ)*x 1 + (655682957/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348488069/10000000000 : ℝ)^2165 ≤ (44060898300387/100000000000000 : ℝ)^1653 := by
    have hnat : (5348488069 : ℕ)^2165*100000000000000^1653 ≤ 44060898300387^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348488069 10000000000 44060898300387 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210446279/1000000000 : ℝ)^2165 ≤ (12986469874919/100000000000000 : ℝ)^1653 := by
    have hnat : (210446279 : ℕ)^2165*100000000000000^1653 ≤ 12986469874919^1653*1000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210446279 1000000000 12986469874919 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655682957/1250000000 : ℝ)^2165 ≤ (21476315907861/50000000000000 : ℝ)^1653 := by
    have hnat : (655682957 : ℕ)^2165*50000000000000^1653 ≤ 21476315907861^1653*1250000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655682957 1250000000 21476315907861 50000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348488069/10000000000 : ℝ), (-210446279/1000000000 : ℝ), (655682957/1250000000 : ℝ)] ![(44060898300387/100000000000000 : ℝ), (12986469874919/100000000000000 : ℝ), (21476315907861/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348488069/10000000000 : ℝ)|^2165 ≤ (44060898300387/100000000000000 : ℝ)^1653
        have hw : |(5348488069/10000000000 : ℝ)|=(5348488069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-210446279/1000000000 : ℝ)|^2165 ≤ (12986469874919/100000000000000 : ℝ)^1653
        have hw : |(-210446279/1000000000 : ℝ)|=(210446279/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(655682957/1250000000 : ℝ)|^2165 ≤ (21476315907861/50000000000000 : ℝ)^1653
        have hw : |(655682957/1250000000 : ℝ)|=(655682957/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_s7_2 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (41785063/78125000 : ℝ)*x 0 + (5245463649/10000000000 : ℝ)*x 1 + (-526115701/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41785063/78125000 : ℝ)^2165 ≤ (44060898246439/100000000000000 : ℝ)^1653 := by
    have hnat : (41785063 : ℕ)^2165*100000000000000^1653 ≤ 44060898246439^1653*78125000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41785063 78125000 44060898246439 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245463649/10000000000 : ℝ)^2165 ≤ (5369078967581/12500000000000 : ℝ)^1653 := by
    have hnat : (5245463649 : ℕ)^2165*12500000000000^1653 ≤ 5369078967581^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245463649 10000000000 5369078967581 12500000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526115701/2500000000 : ℝ)^2165 ≤ (12986469988071/100000000000000 : ℝ)^1653 := by
    have hnat : (526115701 : ℕ)^2165*100000000000000^1653 ≤ 12986469988071^1653*2500000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526115701 2500000000 12986469988071 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41785063/78125000 : ℝ), (5245463649/10000000000 : ℝ), (-526115701/2500000000 : ℝ)] ![(44060898246439/100000000000000 : ℝ), (5369078967581/12500000000000 : ℝ), (12986469988071/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41785063/78125000 : ℝ)|^2165 ≤ (44060898246439/100000000000000 : ℝ)^1653
        have hw : |(41785063/78125000 : ℝ)|=(41785063/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245463649/10000000000 : ℝ)|^2165 ≤ (5369078967581/12500000000000 : ℝ)^1653
        have hw : |(5245463649/10000000000 : ℝ)|=(5245463649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-526115701/2500000000 : ℝ)|^2165 ≤ (12986469988071/100000000000000 : ℝ)^1653
        have hw : |(-526115701/2500000000 : ℝ)|=(526115701/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_s7_3 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2159676547/5000000000 : ℝ)*x 0 + (4147210171/10000000000 : ℝ)*x 1 + (4498072711/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2159676547/5000000000 : ℝ)^2165 ≤ (16651883014597/50000000000000 : ℝ)^1653 := by
    have hnat : (2159676547 : ℕ)^2165*50000000000000^1653 ≤ 16651883014597^1653*5000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2159676547 5000000000 16651883014597 50000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4147210171/10000000000 : ℝ)^2165 ≤ (15788099601257/50000000000000 : ℝ)^1653 := by
    have hnat : (4147210171 : ℕ)^2165*50000000000000^1653 ≤ 15788099601257^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4147210171 10000000000 15788099601257 50000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4498072711/10000000000 : ℝ)^2165 ≤ (17560017374997/50000000000000 : ℝ)^1653 := by
    have hnat : (4498072711 : ℕ)^2165*50000000000000^1653 ≤ 17560017374997^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4498072711 10000000000 17560017374997 50000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2159676547/5000000000 : ℝ), (4147210171/10000000000 : ℝ), (4498072711/10000000000 : ℝ)] ![(16651883014597/50000000000000 : ℝ), (15788099601257/50000000000000 : ℝ), (17560017374997/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2159676547/5000000000 : ℝ)|^2165 ≤ (16651883014597/50000000000000 : ℝ)^1653
        have hw : |(2159676547/5000000000 : ℝ)|=(2159676547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4147210171/10000000000 : ℝ)|^2165 ≤ (15788099601257/50000000000000 : ℝ)^1653
        have hw : |(4147210171/10000000000 : ℝ)|=(4147210171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4498072711/10000000000 : ℝ)|^2165 ≤ (17560017374997/50000000000000 : ℝ)^1653
        have hw : |(4498072711/10000000000 : ℝ)|=(4498072711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_s7_4 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-126252493/625000000 : ℝ)*x 0 + (5246058223/10000000000 : ℝ)*x 1 + (2705314189/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (126252493/625000000 : ℝ)^2165 ≤ (307710443169/2500000000000 : ℝ)^1653 := by
    have hnat : (126252493 : ℕ)^2165*2500000000000^1653 ≤ 307710443169^1653*625000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126252493 625000000 307710443169 2500000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246058223/10000000000 : ℝ)^2165 ≤ (42959008565397/100000000000000 : ℝ)^1653 := by
    have hnat : (5246058223 : ℕ)^2165*100000000000000^1653 ≤ 42959008565397^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246058223 10000000000 42959008565397 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2705314189/5000000000 : ℝ)^2165 ≤ (8946514736457/20000000000000 : ℝ)^1653 := by
    have hnat : (2705314189 : ℕ)^2165*20000000000000^1653 ≤ 8946514736457^1653*5000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705314189 5000000000 8946514736457 20000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-126252493/625000000 : ℝ), (5246058223/10000000000 : ℝ), (2705314189/5000000000 : ℝ)] ![(307710443169/2500000000000 : ℝ), (42959008565397/100000000000000 : ℝ), (8946514736457/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-126252493/625000000 : ℝ)|^2165 ≤ (307710443169/2500000000000 : ℝ)^1653
        have hw : |(-126252493/625000000 : ℝ)|=(126252493/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246058223/10000000000 : ℝ)|^2165 ≤ (42959008565397/100000000000000 : ℝ)^1653
        have hw : |(5246058223/10000000000 : ℝ)|=(5246058223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2705314189/5000000000 : ℝ)|^2165 ≤ (8946514736457/20000000000000 : ℝ)^1653
        have hw : |(2705314189/5000000000 : ℝ)|=(2705314189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_s7_5 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1061131363/2000000000 : ℝ)*x 0 + (-387859609/2000000000 : ℝ)*x 1 + (270531421/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061131363/2000000000 : ℝ)^2165 ≤ (1743973530389/4000000000000 : ℝ)^1653 := by
    have hnat : (1061131363 : ℕ)^2165*4000000000000^1653 ≤ 1743973530389^1653*2000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061131363 2000000000 1743973530389 4000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (387859609/2000000000 : ℝ)^2165 ≤ (11668087582923/100000000000000 : ℝ)^1653 := by
    have hnat : (387859609 : ℕ)^2165*100000000000000^1653 ≤ 11668087582923^1653*2000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      387859609 2000000000 11668087582923 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270531421/500000000 : ℝ)^2165 ≤ (22366287068537/50000000000000 : ℝ)^1653 := by
    have hnat : (270531421 : ℕ)^2165*50000000000000^1653 ≤ 22366287068537^1653*500000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270531421 500000000 22366287068537 50000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061131363/2000000000 : ℝ), (-387859609/2000000000 : ℝ), (270531421/500000000 : ℝ)] ![(1743973530389/4000000000000 : ℝ), (11668087582923/100000000000000 : ℝ), (22366287068537/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061131363/2000000000 : ℝ)|^2165 ≤ (1743973530389/4000000000000 : ℝ)^1653
        have hw : |(1061131363/2000000000 : ℝ)|=(1061131363/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-387859609/2000000000 : ℝ)|^2165 ≤ (11668087582923/100000000000000 : ℝ)^1653
        have hw : |(-387859609/2000000000 : ℝ)|=(387859609/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(270531421/500000000 : ℝ)|^2165 ≤ (22366287068537/50000000000000 : ℝ)^1653
        have hw : |(270531421/500000000 : ℝ)|=(270531421/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_s7_6 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1326414207/2500000000 : ℝ)*x 0 + (5410628419/10000000000 : ℝ)*x 1 + (-1939298029/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326414207/2500000000 : ℝ)^2165 ≤ (21799669199821/50000000000000 : ℝ)^1653 := by
    have hnat : (1326414207 : ℕ)^2165*50000000000000^1653 ≤ 21799669199821^1653*2500000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326414207 2500000000 21799669199821 50000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5410628419/10000000000 : ℝ)^2165 ≤ (22366287063123/50000000000000 : ℝ)^1653 := by
    have hnat : (5410628419 : ℕ)^2165*50000000000000^1653 ≤ 22366287063123^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410628419 10000000000 22366287063123 50000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1939298029/10000000000 : ℝ)^2165 ≤ (11668087456839/100000000000000 : ℝ)^1653 := by
    have hnat : (1939298029 : ℕ)^2165*100000000000000^1653 ≤ 11668087456839^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1939298029 10000000000 11668087456839 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326414207/2500000000 : ℝ), (5410628419/10000000000 : ℝ), (-1939298029/10000000000 : ℝ)] ![(21799669199821/50000000000000 : ℝ), (22366287063123/50000000000000 : ℝ), (11668087456839/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326414207/2500000000 : ℝ)|^2165 ≤ (21799669199821/50000000000000 : ℝ)^1653
        have hw : |(1326414207/2500000000 : ℝ)|=(1326414207/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5410628419/10000000000 : ℝ)|^2165 ≤ (22366287063123/50000000000000 : ℝ)^1653
        have hw : |(5410628419/10000000000 : ℝ)|=(5410628419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1939298029/10000000000 : ℝ)|^2165 ≤ (11668087456839/100000000000000 : ℝ)^1653
        have hw : |(-1939298029/10000000000 : ℝ)|=(1939298029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_s7_7 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1079844547/2500000000 : ℝ)*x 0 + (281050891/625000000 : ℝ)*x 1 + (1037118789/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079844547/2500000000 : ℝ)^2165 ≤ (4163002430353/12500000000000 : ℝ)^1653 := by
    have hnat : (1079844547 : ℕ)^2165*12500000000000^1653 ≤ 4163002430353^1653*2500000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079844547 2500000000 4163002430353 12500000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (281050891/625000000 : ℝ)^2165 ≤ (8776791529481/25000000000000 : ℝ)^1653 := by
    have hnat : (281050891 : ℕ)^2165*25000000000000^1653 ≤ 8776791529481^1653*625000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281050891 625000000 8776791529481 25000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1037118789/2500000000 : ℝ)^2165 ≤ (3948601802509/12500000000000 : ℝ)^1653 := by
    have hnat : (1037118789 : ℕ)^2165*12500000000000^1653 ≤ 3948601802509^1653*2500000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037118789 2500000000 3948601802509 12500000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1079844547/2500000000 : ℝ), (281050891/625000000 : ℝ), (1037118789/2500000000 : ℝ)] ![(4163002430353/12500000000000 : ℝ), (8776791529481/25000000000000 : ℝ), (3948601802509/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1079844547/2500000000 : ℝ)|^2165 ≤ (4163002430353/12500000000000 : ℝ)^1653
        have hw : |(1079844547/2500000000 : ℝ)|=(1079844547/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(281050891/625000000 : ℝ)|^2165 ≤ (8776791529481/25000000000000 : ℝ)^1653
        have hw : |(281050891/625000000 : ℝ)|=(281050891/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1037118789/2500000000 : ℝ)|^2165 ≤ (3948601802509/12500000000000 : ℝ)^1653
        have hw : |(1037118789/2500000000 : ℝ)|=(1037118789/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1370_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155832971/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (589/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11213/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5607/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3681/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (589/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11213/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (589/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11213/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (589/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11213/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (589/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11213/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (589/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11213/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (589/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11213/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11213/100000 : ℝ) ^ (4329/1024 : ℝ) ≤ (4804319564349171/50000000000000000000 : ℝ) := by
    have hpowers : (11213/100000 : ℝ)^4329 ≤ (4804319564349171/50000000000000000000 : ℝ)^1024 := by
      have hnat : (11213 : ℕ)^4329*50000000000000000000^1024 ≤ 4804319564349171^1024*100000^4329 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11213 100000 4804319564349171 50000000000000000000 4329 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11213/100000 : ℝ)) (X := (4804319564349171/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4329 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (589/4000 : ℝ) ^ (4329/1024 : ℝ) ≤ (7600835022700547/25000000000000000000 : ℝ) := by
    have hpowers : (589/4000 : ℝ)^4329 ≤ (7600835022700547/25000000000000000000 : ℝ)^1024 := by
      have hnat : (589 : ℕ)^4329*25000000000000000000^1024 ≤ 7600835022700547^1024*4000^4329 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        589 4000 7600835022700547 25000000000000000000 4329 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (589/4000 : ℝ)) (X := (7600835022700547/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4329 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004804319564349171/25000000000000000000 : ℝ) ≤ (10000454540298671/10000000000000000 : ℝ) ^ (4329/1024 : ℝ) := by
    have hpowers : (25004804319564349171/25000000000000000000 : ℝ)^1024 ≤ (10000454540298671/10000000000000000 : ℝ)^4329 := by
      have hnat : (25004804319564349171 : ℕ)^1024*10000000000000000^4329 ≤ 10000454540298671^4329*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004804319564349171 25000000000000000000 10000454540298671 10000000000000000 1024 4329 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000454540298671/10000000000000000 : ℝ)) (X := (25004804319564349171/25000000000000000000 : ℝ)) (by norm_num) 4329 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10004001197921950053/10000000000000000000 : ℝ) ≤ (5000473157891153/5000000000000000 : ℝ) ^ (4329/1024 : ℝ) := by
    have hpowers : (10004001197921950053/10000000000000000000 : ℝ)^1024 ≤ (5000473157891153/5000000000000000 : ℝ)^4329 := by
      have hnat : (10004001197921950053 : ℕ)^1024*5000000000000000^4329 ≤ 5000473157891153^4329*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004001197921950053 10000000000000000000 5000473157891153 5000000000000000 1024 4329 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000473157891153/5000000000000000 : ℝ)) (X := (10004001197921950053/10000000000000000000 : ℝ)) (by norm_num) 4329 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507600835022700547/12500000000000000000 : ℝ) ≤ (10001438091265941/10000000000000000 : ℝ) ^ (4329/1024 : ℝ) := by
    have hpowers : (12507600835022700547/12500000000000000000 : ℝ)^1024 ≤ (10001438091265941/10000000000000000 : ℝ)^4329 := by
      have hnat : (12507600835022700547 : ℕ)^1024*10000000000000000^4329 ≤ 10001438091265941^4329*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507600835022700547 12500000000000000000 10001438091265941 10000000000000000 1024 4329 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001438091265941/10000000000000000 : ℝ)) (X := (12507600835022700547/12500000000000000000 : ℝ)) (by norm_num) 4329 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4804319564349171/50000000000000000000 : ℝ) ≤ ((17555283894266467021/17560000000000000000 : ℝ)+2*(98355096727/70240000000000 : ℝ)*(11213/100000 : ℝ))^(4329/1024 : ℝ) := by
    rw [show (17555283894266467021/17560000000000000000 : ℝ)+2*(98355096727/70240000000000 : ℝ)*(11213/100000 : ℝ)=(10000454540298671/10000000000000000 : ℝ) by norm_num, show 1+2*(4804319564349171/50000000000000000000 : ℝ)=(25004804319564349171/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7600835022700547/25000000000000000000 : ℝ)+(4804319564349171/50000000000000000000 : ℝ) ≤ ((17555283894266467021/17560000000000000000 : ℝ)+(98355096727/70240000000000 : ℝ)*((589/4000 : ℝ)+(11213/100000 : ℝ)))^(4329/1024 : ℝ) := by
    rw [show (17555283894266467021/17560000000000000000 : ℝ)+(98355096727/70240000000000 : ℝ)*((589/4000 : ℝ)+(11213/100000 : ℝ))=(5000473157891153/5000000000000000 : ℝ) by norm_num, show 1+(7600835022700547/25000000000000000000 : ℝ)+(4804319564349171/50000000000000000000 : ℝ)=(10004001197921950053/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7600835022700547/25000000000000000000 : ℝ) ≤ ((17555283894266467021/17560000000000000000 : ℝ)+2*(98355096727/70240000000000 : ℝ)*(589/4000 : ℝ))^(4329/1024 : ℝ) := by
    rw [show (17555283894266467021/17560000000000000000 : ℝ)+2*(98355096727/70240000000000 : ℝ)*(589/4000 : ℝ)=(10001438091265941/10000000000000000 : ℝ) by norm_num, show 1+2*(7600835022700547/25000000000000000000 : ℝ)=(12507600835022700547/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17555283894266467021/17560000000000000000 : ℝ)*(X 1 0+X 2 0)+(98355096727/70240000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4329/1024 : ℝ)) (lo := (11213/100000 : ℝ)) (hi := (589/4000 : ℝ)) (c := (17555283894266467021/17560000000000000000 : ℝ)) (alpha := (98355096727/70240000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17555283894266467021/17560000000000000000 : ℝ)*(X 0 1+X 2 1)+(98355096727/70240000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4329/1024 : ℝ)) (lo := (11213/100000 : ℝ)) (hi := (589/4000 : ℝ)) (c := (17555283894266467021/17560000000000000000 : ℝ)) (alpha := (98355096727/70240000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17555283894266467021/17560000000000000000 : ℝ)*(X 0 2+X 1 2)+(98355096727/70240000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4329/1024 : ℝ)) (lo := (11213/100000 : ℝ)) (hi := (589/4000 : ℝ)) (c := (17555283894266467021/17560000000000000000 : ℝ)) (alpha := (98355096727/70240000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-404005607/2000000000 : ℝ)*X 0 0+(5411226013/10000000000 : ℝ)*X 0 1+(2622731821/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348488069/10000000000 : ℝ)*X 1 0+(-210446279/1000000000 : ℝ)*X 1 1+(655682957/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((41785063/78125000 : ℝ)*X 2 0+(5245463649/10000000000 : ℝ)*X 2 1+(-526115701/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2159676547/5000000000 : ℝ)*X 0 0+(4147210171/10000000000 : ℝ)*X 0 1+(4498072711/10000000000 : ℝ)*X 0 2+(2159676547/5000000000 : ℝ)*X 1 0+(4147210171/10000000000 : ℝ)*X 1 1+(4498072711/10000000000 : ℝ)*X 1 2+(2159676547/5000000000 : ℝ)*X 2 0+(4147210171/10000000000 : ℝ)*X 2 1+(4498072711/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-126252493/625000000 : ℝ)*X 0 0+(5246058223/10000000000 : ℝ)*X 0 1+(2705314189/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1061131363/2000000000 : ℝ)*X 1 0+(-387859609/2000000000 : ℝ)*X 1 1+(270531421/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326414207/2500000000 : ℝ)*X 2 0+(5410628419/10000000000 : ℝ)*X 2 1+(-1939298029/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1079844547/2500000000 : ℝ)*X 0 0+(281050891/625000000 : ℝ)*X 0 1+(1037118789/2500000000 : ℝ)*X 0 2+(1079844547/2500000000 : ℝ)*X 1 0+(281050891/625000000 : ℝ)*X 1 1+(1037118789/2500000000 : ℝ)*X 1 2+(1079844547/2500000000 : ℝ)*X 2 0+(281050891/625000000 : ℝ)*X 2 1+(1037118789/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2799568839283043382819447153/439000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (592279463/50000000000000 : ℝ)*(base19) + (544076711/50000000000000 : ℝ)*(base23) + (48545979/100000000000000 : ℝ)*(lower2) + (89459511/50000000000000 : ℝ)*(upper3) + (92903299/100000000000000 : ℝ)*(upper5) + (2220731249696569/50000000000000 : ℝ)*(major0) + (2220731249696569/50000000000000 : ℝ)*(major1) + (2220731249696569/50000000000000 : ℝ)*(major2) + (6032758017942967/100000000000000 : ℝ)*(sp0) + (6032780611445251/100000000000000 : ℝ)*(sp1) + (1206556141570151/20000000000000 : ℝ)*(sp2) + (2850130144524111/100000000000000 : ℝ)*(sp3) + (2377806121/10000000000000 : ℝ)*(sp4) + (1284568631/10000000000000 : ℝ)*(sp7) + (142507149510521/5000000000000 : ℝ)*(f.failure) + (6032781796004177/100000000000000 : ℝ)*(f.sum) + (2084991910579/1756000000000000000000000000 : ℝ)*base65 + (721441600164899051/878000000000000000000000000000000 : ℝ)*base68 + (2254738062261100949/878000000000000000000000000000000 : ℝ)*base69 + (3433634318337100949/878000000000000000000000000000000 : ℝ)*base71 + (11473482107893/1756000000000000000000000000 : ℝ)*base74 + (12721222884625100949/878000000000000000000000000000000 : ℝ)*base75 + (8358619033459100949/878000000000000000000000000000000 : ℝ)*base77 + (11934445093696899051/878000000000000000000000000000000 : ℝ)*base80 + (1275298779347/1756000000000000000000000000 : ℝ)*base81 + (6812109/500000000000000000000 : ℝ)*base90 + (6812109/500000000000000000000 : ℝ)*base92 + (6812109/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8796007863492106106811/878000000000000000000000000 : ℝ) := by norm_num
    linear_combination (814001771/50000000000000 : ℝ)*(base19) + (364151647/20000000000000 : ℝ)*(base23) + (6981169/1250000000000 : ℝ)*(lower1) + (107089341/50000000000000 : ℝ)*(upper3) + (37301441/50000000000000 : ℝ)*(lower4) + (36771563/20000000000000 : ℝ)*(upper5) + (1118393704241127/25000000000000 : ℝ)*(major0) + (1118393704241127/25000000000000 : ℝ)*(major1) + (1118393704241127/25000000000000 : ℝ)*(major2) + (4615047701/100000000000000 : ℝ)*(sp2) + (1519099856764647/25000000000000 : ℝ)*(sp4) + (3038198899527523/50000000000000 : ℝ)*(sp5) + (6076392991252651/100000000000000 : ℝ)*(sp6) + (358843734116167/12500000000000 : ℝ)*(sp7) + (358843734116167/12500000000000 : ℝ)*(f.failure) + (1519099856764647/25000000000000 : ℝ)*(f.sum) + (5214635199743/878000000000000000000000000 : ℝ)*base66 + (7736979049450377333/439000000000000000000000000000000 : ℝ)*base68 + (165238896489622667/439000000000000000000000000000000 : ℝ)*base69 + (31130928418852377333/439000000000000000000000000000000 : ℝ)*base72 + (2038115476741/878000000000000000000000000 : ℝ)*base73 + (24867506788905622667/439000000000000000000000000000000 : ℝ)*base75 + (519613562330377333/439000000000000000000000000000000 : ℝ)*base78 + (4719189129783622667/439000000000000000000000000000000 : ℝ)*base79 + (666842237231/175600000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (12742157/1250000000000000000000 : ℝ)*base89 + (12742157/1250000000000000000000 : ℝ)*base91 + (12742157/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1370_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155832971/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (589/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11213/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5607/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3681/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1370_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1370_box_0 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-927480341/5000000000 : ℝ)*x 0 + (5388766623/10000000000 : ℝ)*x 1 + (5388766513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (927480341/5000000000 : ℝ)^2165 ≤ (11008009577009/100000000000000 : ℝ)^1653 := by
    have hnat : (927480341 : ℕ)^2165*100000000000000^1653 ≤ 11008009577009^1653*5000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      927480341 5000000000 11008009577009 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5388766623/10000000000 : ℝ)^2165 ≤ (44495995794657/100000000000000 : ℝ)^1653 := by
    have hnat : (5388766623 : ℕ)^2165*100000000000000^1653 ≤ 44495995794657^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5388766623 10000000000 44495995794657 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5388766513/10000000000 : ℝ)^2165 ≤ (22247997302517/50000000000000 : ℝ)^1653 := by
    have hnat : (5388766513 : ℕ)^2165*50000000000000^1653 ≤ 22247997302517^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5388766513 10000000000 22247997302517 50000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-927480341/5000000000 : ℝ), (5388766623/10000000000 : ℝ), (5388766513/10000000000 : ℝ)] ![(11008009577009/100000000000000 : ℝ), (44495995794657/100000000000000 : ℝ), (22247997302517/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-927480341/5000000000 : ℝ)|^2165 ≤ (11008009577009/100000000000000 : ℝ)^1653
        have hw : |(-927480341/5000000000 : ℝ)|=(927480341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5388766623/10000000000 : ℝ)|^2165 ≤ (44495995794657/100000000000000 : ℝ)^1653
        have hw : |(5388766623/10000000000 : ℝ)|=(5388766623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5388766513/10000000000 : ℝ)|^2165 ≤ (22247997302517/50000000000000 : ℝ)^1653
        have hw : |(5388766513/10000000000 : ℝ)|=(5388766513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_box_1 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (660689671/1250000000 : ℝ)*x 0 + (-99827513/500000000 : ℝ)*x 1 + (5388766351/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (660689671/1250000000 : ℝ)^2165 ≤ (43382708694979/100000000000000 : ℝ)^1653 := by
    have hnat : (660689671 : ℕ)^2165*100000000000000^1653 ≤ 43382708694979^1653*1250000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660689671 1250000000 43382708694979 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (99827513/500000000 : ℝ)^2165 ≤ (757581152683/6250000000000 : ℝ)^1653 := by
    have hnat : (99827513 : ℕ)^2165*6250000000000^1653 ≤ 757581152683^1653*500000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      99827513 500000000 757581152683 6250000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5388766351/10000000000 : ℝ)^2165 ≤ (11123998213261/25000000000000 : ℝ)^1653 := by
    have hnat : (5388766351 : ℕ)^2165*25000000000000^1653 ≤ 11123998213261^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5388766351 10000000000 11123998213261 25000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(660689671/1250000000 : ℝ), (-99827513/500000000 : ℝ), (5388766351/10000000000 : ℝ)] ![(43382708694979/100000000000000 : ℝ), (757581152683/6250000000000 : ℝ), (11123998213261/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(660689671/1250000000 : ℝ)|^2165 ≤ (43382708694979/100000000000000 : ℝ)^1653
        have hw : |(660689671/1250000000 : ℝ)|=(660689671/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-99827513/500000000 : ℝ)|^2165 ≤ (757581152683/6250000000000 : ℝ)^1653
        have hw : |(-99827513/500000000 : ℝ)|=(99827513/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5388766351/10000000000 : ℝ)|^2165 ≤ (11123998213261/25000000000000 : ℝ)^1653
        have hw : |(5388766351/10000000000 : ℝ)|=(5388766351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_box_2 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5285516871/10000000000 : ℝ)*x 0 + (5388766921/10000000000 : ℝ)*x 1 + (-499137539/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285516871/10000000000 : ℝ)^2165 ≤ (21691351676079/50000000000000 : ℝ)^1653 := by
    have hnat : (5285516871 : ℕ)^2165*50000000000000^1653 ≤ 21691351676079^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285516871 10000000000 21691351676079 50000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5388766921/10000000000 : ℝ)^2165 ≤ (44495999017453/100000000000000 : ℝ)^1653 := by
    have hnat : (5388766921 : ℕ)^2165*100000000000000^1653 ≤ 44495999017453^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5388766921 10000000000 44495999017453 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (499137539/2500000000 : ℝ)^2165 ≤ (12121297615963/100000000000000 : ℝ)^1653 := by
    have hnat : (499137539 : ℕ)^2165*100000000000000^1653 ≤ 12121297615963^1653*2500000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      499137539 2500000000 12121297615963 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285516871/10000000000 : ℝ), (5388766921/10000000000 : ℝ), (-499137539/2500000000 : ℝ)] ![(21691351676079/50000000000000 : ℝ), (44495999017453/100000000000000 : ℝ), (12121297615963/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285516871/10000000000 : ℝ)|^2165 ≤ (21691351676079/50000000000000 : ℝ)^1653
        have hw : |(5285516871/10000000000 : ℝ)|=(5285516871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5388766921/10000000000 : ℝ)|^2165 ≤ (44495999017453/100000000000000 : ℝ)^1653
        have hw : |(5388766921/10000000000 : ℝ)|=(5388766921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-499137539/2500000000 : ℝ)|^2165 ≤ (12121297615963/100000000000000 : ℝ)^1653
        have hw : |(-499137539/2500000000 : ℝ)|=(499137539/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_box_3 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4466903103/10000000000 : ℝ)*x 0 + (531175801/1250000000 : ℝ)*x 1 + (2124703339/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4466903103/10000000000 : ℝ)^2165 ≤ (34801631288001/100000000000000 : ℝ)^1653 := by
    have hnat : (4466903103 : ℕ)^2165*100000000000000^1653 ≤ 34801631288001^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4466903103 10000000000 34801631288001 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (531175801/1250000000 : ℝ)^2165 ≤ (32599182991059/100000000000000 : ℝ)^1653 := by
    have hnat : (531175801 : ℕ)^2165*100000000000000^1653 ≤ 32599182991059^1653*1250000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531175801 1250000000 32599182991059 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2124703339/5000000000 : ℝ)^2165 ≤ (16299592851959/50000000000000 : ℝ)^1653 := by
    have hnat : (2124703339 : ℕ)^2165*50000000000000^1653 ≤ 16299592851959^1653*5000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124703339 5000000000 16299592851959 50000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4466903103/10000000000 : ℝ), (531175801/1250000000 : ℝ), (2124703339/5000000000 : ℝ)] ![(34801631288001/100000000000000 : ℝ), (32599182991059/100000000000000 : ℝ), (16299592851959/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4466903103/10000000000 : ℝ)|^2165 ≤ (34801631288001/100000000000000 : ℝ)^1653
        have hw : |(4466903103/10000000000 : ℝ)|=(4466903103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(531175801/1250000000 : ℝ)|^2165 ≤ (32599182991059/100000000000000 : ℝ)^1653
        have hw : |(531175801/1250000000 : ℝ)|=(531175801/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2124703339/5000000000 : ℝ)|^2165 ≤ (16299592851959/50000000000000 : ℝ)^1653
        have hw : |(2124703339/5000000000 : ℝ)|=(2124703339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_box_4 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-546960413/2500000000 : ℝ)*x 0 + (164547231/312500000 : ℝ)*x 1 + (2632755871/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (546960413/2500000000 : ℝ)^2165 ≤ (13664460657381/100000000000000 : ℝ)^1653 := by
    have hnat : (546960413 : ℕ)^2165*100000000000000^1653 ≤ 13664460657381^1653*2500000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546960413 2500000000 13664460657381 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (164547231/312500000 : ℝ)^2165 ≤ (10791941947321/25000000000000 : ℝ)^1653 := by
    have hnat : (164547231 : ℕ)^2165*25000000000000^1653 ≤ 10791941947321^1653*312500000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164547231 312500000 10791941947321 25000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632755871/5000000000 : ℝ)^2165 ≤ (5395971443427/12500000000000 : ℝ)^1653 := by
    have hnat : (2632755871 : ℕ)^2165*12500000000000^1653 ≤ 5395971443427^1653*5000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632755871 5000000000 5395971443427 12500000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-546960413/2500000000 : ℝ), (164547231/312500000 : ℝ), (2632755871/5000000000 : ℝ)] ![(13664460657381/100000000000000 : ℝ), (10791941947321/25000000000000 : ℝ), (5395971443427/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-546960413/2500000000 : ℝ)|^2165 ≤ (13664460657381/100000000000000 : ℝ)^1653
        have hw : |(-546960413/2500000000 : ℝ)|=(546960413/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(164547231/312500000 : ℝ)|^2165 ≤ (10791941947321/25000000000000 : ℝ)^1653
        have hw : |(164547231/312500000 : ℝ)|=(164547231/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632755871/5000000000 : ℝ)|^2165 ≤ (5395971443427/12500000000000 : ℝ)^1653
        have hw : |(2632755871/5000000000 : ℝ)|=(2632755871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_box_5 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2685993843/5000000000 : ℝ)*x 0 + (-511550121/2500000000 : ℝ)*x 1 + (5265511427/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2685993843/5000000000 : ℝ)^2165 ≤ (44314623302449/100000000000000 : ℝ)^1653 := by
    have hnat : (2685993843 : ℕ)^2165*100000000000000^1653 ≤ 44314623302449^1653*5000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2685993843 5000000000 44314623302449 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (511550121/2500000000 : ℝ)^2165 ≤ (12517608515053/100000000000000 : ℝ)^1653 := by
    have hnat : (511550121 : ℕ)^2165*100000000000000^1653 ≤ 12517608515053^1653*2500000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      511550121 2500000000 12517608515053 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265511427/10000000000 : ℝ)^2165 ≤ (43167768165097/100000000000000 : ℝ)^1653 := by
    have hnat : (5265511427 : ℕ)^2165*100000000000000^1653 ≤ 43167768165097^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265511427 10000000000 43167768165097 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2685993843/5000000000 : ℝ), (-511550121/2500000000 : ℝ), (5265511427/10000000000 : ℝ)] ![(44314623302449/100000000000000 : ℝ), (12517608515053/100000000000000 : ℝ), (43167768165097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2685993843/5000000000 : ℝ)|^2165 ≤ (44314623302449/100000000000000 : ℝ)^1653
        have hw : |(2685993843/5000000000 : ℝ)|=(2685993843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-511550121/2500000000 : ℝ)|^2165 ≤ (12517608515053/100000000000000 : ℝ)^1653
        have hw : |(-511550121/2500000000 : ℝ)|=(511550121/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265511427/10000000000 : ℝ)|^2165 ≤ (43167768165097/100000000000000 : ℝ)^1653
        have hw : |(5265511427/10000000000 : ℝ)|=(5265511427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_box_6 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5371987387/10000000000 : ℝ)*x 0 + (210620459/400000000 : ℝ)*x 1 + (-255775103/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5371987387/10000000000 : ℝ)^2165 ≤ (1107865501799/2500000000000 : ℝ)^1653 := by
    have hnat : (5371987387 : ℕ)^2165*2500000000000^1653 ≤ 1107865501799^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5371987387 10000000000 1107865501799 2500000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210620459/400000000 : ℝ)^2165 ≤ (21583884340249/50000000000000 : ℝ)^1653 := by
    have hnat : (210620459 : ℕ)^2165*50000000000000^1653 ≤ 21583884340249^1653*400000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210620459 400000000 21583884340249 50000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (255775103/1250000000 : ℝ)^2165 ≤ (12517611239241/100000000000000 : ℝ)^1653 := by
    have hnat : (255775103 : ℕ)^2165*100000000000000^1653 ≤ 12517611239241^1653*1250000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      255775103 1250000000 12517611239241 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5371987387/10000000000 : ℝ), (210620459/400000000 : ℝ), (-255775103/1250000000 : ℝ)] ![(1107865501799/2500000000000 : ℝ), (21583884340249/50000000000000 : ℝ), (12517611239241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5371987387/10000000000 : ℝ)|^2165 ≤ (1107865501799/2500000000000 : ℝ)^1653
        have hw : |(5371987387/10000000000 : ℝ)|=(5371987387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(210620459/400000000 : ℝ)|^2165 ≤ (21583884340249/50000000000000 : ℝ)^1653
        have hw : |(210620459/400000000 : ℝ)|=(210620459/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-255775103/1250000000 : ℝ)|^2165 ≤ (12517611239241/100000000000000 : ℝ)^1653
        have hw : |(-255775103/1250000000 : ℝ)|=(255775103/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_box_7 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4170837041/10000000000 : ℝ)*x 0 + (2198693449/5000000000 : ℝ)*x 1 + (4397386897/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4170837041/10000000000 : ℝ)^2165 ≤ (15906008765417/50000000000000 : ℝ)^1653 := by
    have hnat : (4170837041 : ℕ)^2165*50000000000000^1653 ≤ 15906008765417^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4170837041 10000000000 15906008765417 50000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2198693449/5000000000 : ℝ)^2165 ≤ (17046995618061/50000000000000 : ℝ)^1653 := by
    have hnat : (2198693449 : ℕ)^2165*50000000000000^1653 ≤ 17046995618061^1653*5000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2198693449 5000000000 17046995618061 50000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4397386897/10000000000 : ℝ)^2165 ≤ (34093991225967/100000000000000 : ℝ)^1653 := by
    have hnat : (4397386897 : ℕ)^2165*100000000000000^1653 ≤ 34093991225967^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4397386897 10000000000 34093991225967 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4170837041/10000000000 : ℝ), (2198693449/5000000000 : ℝ), (4397386897/10000000000 : ℝ)] ![(15906008765417/50000000000000 : ℝ), (17046995618061/50000000000000 : ℝ), (34093991225967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4170837041/10000000000 : ℝ)|^2165 ≤ (15906008765417/50000000000000 : ℝ)^1653
        have hw : |(4170837041/10000000000 : ℝ)|=(4170837041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2198693449/5000000000 : ℝ)|^2165 ≤ (17046995618061/50000000000000 : ℝ)^1653
        have hw : |(2198693449/5000000000 : ℝ)|=(2198693449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4397386897/10000000000 : ℝ)|^2165 ≤ (34093991225967/100000000000000 : ℝ)^1653
        have hw : |(4397386897/10000000000 : ℝ)|=(4397386897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_box_8 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2117865857/10000000000 : ℝ)*x 0 + (2590264403/5000000000 : ℝ)*x 1 + (270138691/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2117865857/10000000000 : ℝ)^2165 ≤ (327372604033/2500000000000 : ℝ)^1653 := by
    have hnat : (2117865857 : ℕ)^2165*2500000000000^1653 ≤ 327372604033^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117865857 10000000000 327372604033 2500000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2590264403/5000000000 : ℝ)^2165 ≤ (42257554715251/100000000000000 : ℝ)^1653 := by
    have hnat : (2590264403 : ℕ)^2165*100000000000000^1653 ≤ 42257554715251^1653*5000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590264403 5000000000 42257554715251 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270138691/500000000 : ℝ)^2165 ≤ (22323770557151/50000000000000 : ℝ)^1653 := by
    have hnat : (270138691 : ℕ)^2165*50000000000000^1653 ≤ 22323770557151^1653*500000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270138691 500000000 22323770557151 50000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2117865857/10000000000 : ℝ), (2590264403/5000000000 : ℝ), (270138691/500000000 : ℝ)] ![(327372604033/2500000000000 : ℝ), (42257554715251/100000000000000 : ℝ), (22323770557151/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2117865857/10000000000 : ℝ)|^2165 ≤ (327372604033/2500000000000 : ℝ)^1653
        have hw : |(-2117865857/10000000000 : ℝ)|=(2117865857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2590264403/5000000000 : ℝ)|^2165 ≤ (42257554715251/100000000000000 : ℝ)^1653
        have hw : |(2590264403/5000000000 : ℝ)|=(2590264403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(270138691/500000000 : ℝ)|^2165 ≤ (22323770557151/50000000000000 : ℝ)^1653
        have hw : |(270138691/500000000 : ℝ)|=(270138691/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_box_9 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5275685899/10000000000 : ℝ)*x 0 + (-79631069/400000000 : ℝ)*x 1 + (2701386871/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275685899/10000000000 : ℝ)^2165 ≤ (2704815591539/6250000000000 : ℝ)^1653 := by
    have hnat : (5275685899 : ℕ)^2165*6250000000000^1653 ≤ 2704815591539^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275685899 10000000000 2704815591539 6250000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (79631069/400000000 : ℝ)^2165 ≤ (3018852559299/25000000000000 : ℝ)^1653 := by
    have hnat : (79631069 : ℕ)^2165*25000000000000^1653 ≤ 3018852559299^1653*400000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79631069 400000000 3018852559299 25000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2701386871/5000000000 : ℝ)^2165 ≤ (44647540270073/100000000000000 : ℝ)^1653 := by
    have hnat : (2701386871 : ℕ)^2165*100000000000000^1653 ≤ 44647540270073^1653*5000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701386871 5000000000 44647540270073 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275685899/10000000000 : ℝ), (-79631069/400000000 : ℝ), (2701386871/5000000000 : ℝ)] ![(2704815591539/6250000000000 : ℝ), (3018852559299/25000000000000 : ℝ), (44647540270073/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275685899/10000000000 : ℝ)|^2165 ≤ (2704815591539/6250000000000 : ℝ)^1653
        have hw : |(5275685899/10000000000 : ℝ)|=(5275685899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-79631069/400000000 : ℝ)|^2165 ≤ (3018852559299/25000000000000 : ℝ)^1653
        have hw : |(-79631069/400000000 : ℝ)|=(79631069/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2701386871/5000000000 : ℝ)|^2165 ≤ (44647540270073/100000000000000 : ℝ)^1653
        have hw : |(2701386871/5000000000 : ℝ)|=(2701386871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_box_10 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5275685599/10000000000 : ℝ)*x 0 + (2701386651/5000000000 : ℝ)*x 1 + (-1990777731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275685599/10000000000 : ℝ)^2165 ≤ (270481539009/625000000000 : ℝ)^1653 := by
    have hnat : (5275685599 : ℕ)^2165*625000000000^1653 ≤ 270481539009^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275685599 10000000000 270481539009 625000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2701386651/5000000000 : ℝ)^2165 ≤ (22323767753877/50000000000000 : ℝ)^1653 := by
    have hnat : (2701386651 : ℕ)^2165*50000000000000^1653 ≤ 22323767753877^1653*5000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701386651 5000000000 22323767753877 50000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1990777731/10000000000 : ℝ)^2165 ≤ (12075418229323/100000000000000 : ℝ)^1653 := by
    have hnat : (1990777731 : ℕ)^2165*100000000000000^1653 ≤ 12075418229323^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1990777731 10000000000 12075418229323 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275685599/10000000000 : ℝ), (2701386651/5000000000 : ℝ), (-1990777731/10000000000 : ℝ)] ![(270481539009/625000000000 : ℝ), (22323767753877/50000000000000 : ℝ), (12075418229323/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275685599/10000000000 : ℝ)|^2165 ≤ (270481539009/625000000000 : ℝ)^1653
        have hw : |(5275685599/10000000000 : ℝ)|=(5275685599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2701386651/5000000000 : ℝ)|^2165 ≤ (22323767753877/50000000000000 : ℝ)^1653
        have hw : |(2701386651/5000000000 : ℝ)|=(2701386651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1990777731/10000000000 : ℝ)|^2165 ≤ (12075418229323/100000000000000 : ℝ)^1653
        have hw : |(-1990777731/10000000000 : ℝ)|=(1990777731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_box_11 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4499991249/10000000000 : ℝ)*x 0 + (4232574741/10000000000 : ℝ)*x 1 + (4232575497/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4499991249/10000000000 : ℝ)^2165 ≤ (35139655364363/100000000000000 : ℝ)^1653 := by
    have hnat : (4499991249 : ℕ)^2165*100000000000000^1653 ≤ 35139655364363^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4499991249 10000000000 35139655364363 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4232574741/10000000000 : ℝ)^2165 ≤ (32430168520263/100000000000000 : ℝ)^1653 := by
    have hnat : (4232574741 : ℕ)^2165*100000000000000^1653 ≤ 32430168520263^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4232574741 10000000000 32430168520263 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4232575497/10000000000 : ℝ)^2165 ≤ (32430176106937/100000000000000 : ℝ)^1653 := by
    have hnat : (4232575497 : ℕ)^2165*100000000000000^1653 ≤ 32430176106937^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4232575497 10000000000 32430176106937 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4499991249/10000000000 : ℝ), (4232574741/10000000000 : ℝ), (4232575497/10000000000 : ℝ)] ![(35139655364363/100000000000000 : ℝ), (32430168520263/100000000000000 : ℝ), (32430176106937/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4499991249/10000000000 : ℝ)|^2165 ≤ (35139655364363/100000000000000 : ℝ)^1653
        have hw : |(4499991249/10000000000 : ℝ)|=(4499991249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4232574741/10000000000 : ℝ)|^2165 ≤ (32430168520263/100000000000000 : ℝ)^1653
        have hw : |(4232574741/10000000000 : ℝ)|=(4232574741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4232575497/10000000000 : ℝ)|^2165 ≤ (32430176106937/100000000000000 : ℝ)^1653
        have hw : |(4232575497/10000000000 : ℝ)|=(4232575497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_box_12 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1925220667/10000000000 : ℝ)*x 0 + (5471605349/10000000000 : ℝ)*x 1 + (5254420623/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1925220667/10000000000 : ℝ)^2165 ≤ (11557279201323/100000000000000 : ℝ)^1653 := by
    have hnat : (1925220667 : ℕ)^2165*100000000000000^1653 ≤ 11557279201323^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1925220667 10000000000 11557279201323 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5471605349/10000000000 : ℝ)^2165 ≤ (11348500377/25000000000 : ℝ)^1653 := by
    have hnat : (5471605349 : ℕ)^2165*25000000000^1653 ≤ 11348500377^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5471605349 10000000000 11348500377 25000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5254420623/10000000000 : ℝ)^2165 ≤ (43048719274409/100000000000000 : ℝ)^1653 := by
    have hnat : (5254420623 : ℕ)^2165*100000000000000^1653 ≤ 43048719274409^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254420623 10000000000 43048719274409 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1925220667/10000000000 : ℝ), (5471605349/10000000000 : ℝ), (5254420623/10000000000 : ℝ)] ![(11557279201323/100000000000000 : ℝ), (11348500377/25000000000 : ℝ), (43048719274409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1925220667/10000000000 : ℝ)|^2165 ≤ (11557279201323/100000000000000 : ℝ)^1653
        have hw : |(-1925220667/10000000000 : ℝ)|=(1925220667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5471605349/10000000000 : ℝ)|^2165 ≤ (11348500377/25000000000 : ℝ)^1653
        have hw : |(5471605349/10000000000 : ℝ)|=(5471605349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5254420623/10000000000 : ℝ)|^2165 ≤ (43048719274409/100000000000000 : ℝ)^1653
        have hw : |(5254420623/10000000000 : ℝ)|=(5254420623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_box_13 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5379766049/10000000000 : ℝ)*x 0 + (-2050566147/10000000000 : ℝ)*x 1 + (2627210291/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5379766049/10000000000 : ℝ)^2165 ≤ (44398681999111/100000000000000 : ℝ)^1653 := by
    have hnat : (5379766049 : ℕ)^2165*100000000000000^1653 ≤ 44398681999111^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5379766049 10000000000 44398681999111 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2050566147/10000000000 : ℝ)^2165 ≤ (6276299575813/50000000000000 : ℝ)^1653 := by
    have hnat : (2050566147 : ℕ)^2165*50000000000000^1653 ≤ 6276299575813^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2050566147 10000000000 6276299575813 50000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2627210291/5000000000 : ℝ)^2165 ≤ (21524359417229/50000000000000 : ℝ)^1653 := by
    have hnat : (2627210291 : ℕ)^2165*50000000000000^1653 ≤ 21524359417229^1653*5000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627210291 5000000000 21524359417229 50000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5379766049/10000000000 : ℝ), (-2050566147/10000000000 : ℝ), (2627210291/5000000000 : ℝ)] ![(44398681999111/100000000000000 : ℝ), (6276299575813/50000000000000 : ℝ), (21524359417229/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5379766049/10000000000 : ℝ)|^2165 ≤ (44398681999111/100000000000000 : ℝ)^1653
        have hw : |(5379766049/10000000000 : ℝ)|=(5379766049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2050566147/10000000000 : ℝ)|^2165 ≤ (6276299575813/50000000000000 : ℝ)^1653
        have hw : |(-2050566147/10000000000 : ℝ)|=(2050566147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2627210291/5000000000 : ℝ)|^2165 ≤ (21524359417229/50000000000000 : ℝ)^1653
        have hw : |(2627210291/5000000000 : ℝ)|=(2627210291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_box_14 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5379766029/10000000000 : ℝ)*x 0 + (525442063/1000000000 : ℝ)*x 1 + (-2050566111/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5379766029/10000000000 : ℝ)^2165 ≤ (2774917611433/6250000000000 : ℝ)^1653 := by
    have hnat : (5379766029 : ℕ)^2165*6250000000000^1653 ≤ 2774917611433^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5379766029 10000000000 2774917611433 6250000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (525442063/1000000000 : ℝ)^2165 ≤ (21524359674761/50000000000000 : ℝ)^1653 := by
    have hnat : (525442063 : ℕ)^2165*50000000000000^1653 ≤ 21524359674761^1653*1000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525442063 1000000000 21524359674761 50000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2050566111/10000000000 : ℝ)^2165 ≤ (784537428937/6250000000000 : ℝ)^1653 := by
    have hnat : (2050566111 : ℕ)^2165*6250000000000^1653 ≤ 784537428937^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2050566111 10000000000 784537428937 6250000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5379766029/10000000000 : ℝ), (525442063/1000000000 : ℝ), (-2050566111/10000000000 : ℝ)] ![(2774917611433/6250000000000 : ℝ), (21524359674761/50000000000000 : ℝ), (784537428937/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5379766029/10000000000 : ℝ)|^2165 ≤ (2774917611433/6250000000000 : ℝ)^1653
        have hw : |(5379766029/10000000000 : ℝ)|=(5379766029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(525442063/1000000000 : ℝ)|^2165 ≤ (21524359674761/50000000000000 : ℝ)^1653
        have hw : |(525442063/1000000000 : ℝ)|=(525442063/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2050566111/10000000000 : ℝ)|^2165 ≤ (784537428937/6250000000000 : ℝ)^1653
        have hw : |(-2050566111/10000000000 : ℝ)|=(2050566111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_box_15 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4143746607/10000000000 : ℝ)*x 0 + (1102673089/2500000000 : ℝ)*x 1 + (1102673087/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4143746607/10000000000 : ℝ)^2165 ≤ (15770832243369/50000000000000 : ℝ)^1653 := by
    have hnat : (4143746607 : ℕ)^2165*50000000000000^1653 ≤ 15770832243369^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4143746607 10000000000 15770832243369 50000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1102673089/2500000000 : ℝ)^2165 ≤ (34229167787923/100000000000000 : ℝ)^1653 := by
    have hnat : (1102673089 : ℕ)^2165*100000000000000^1653 ≤ 34229167787923^1653*2500000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102673089 2500000000 34229167787923 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1102673087/2500000000 : ℝ)^2165 ≤ (34229167706609/100000000000000 : ℝ)^1653 := by
    have hnat : (1102673087 : ℕ)^2165*100000000000000^1653 ≤ 34229167706609^1653*2500000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102673087 2500000000 34229167706609 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4143746607/10000000000 : ℝ), (1102673089/2500000000 : ℝ), (1102673087/2500000000 : ℝ)] ![(15770832243369/50000000000000 : ℝ), (34229167787923/100000000000000 : ℝ), (34229167706609/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4143746607/10000000000 : ℝ)|^2165 ≤ (15770832243369/50000000000000 : ℝ)^1653
        have hw : |(4143746607/10000000000 : ℝ)|=(4143746607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1102673089/2500000000 : ℝ)|^2165 ≤ (34229167787923/100000000000000 : ℝ)^1653
        have hw : |(1102673089/2500000000 : ℝ)|=(1102673089/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1102673087/2500000000 : ℝ)|^2165 ≤ (34229167706609/100000000000000 : ℝ)^1653
        have hw : |(1102673087/2500000000 : ℝ)|=(1102673087/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1370_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155832971/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3681/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5607/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62867/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(14749/25000 : ℝ) ∧ (80117/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84461/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3681/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5607/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3681/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5607/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3681/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5607/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3681/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5607/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3681/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5607/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3681/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5607/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5607/50000 : ℝ) ^ (4329/1024 : ℝ) ≤ (2403065577764103/25000000000000000000 : ℝ) := by
    have hpowers : (5607/50000 : ℝ)^4329 ≤ (2403065577764103/25000000000000000000 : ℝ)^1024 := by
      have hnat : (5607 : ℕ)^4329*25000000000000000000^1024 ≤ 2403065577764103^1024*50000^4329 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5607 50000 2403065577764103 25000000000000000000 4329 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5607/50000 : ℝ)) (X := (2403065577764103/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4329 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3681/25000 : ℝ) ^ (4329/1024 : ℝ) ≤ (3799326533231997/12500000000000000000 : ℝ) := by
    have hpowers : (3681/25000 : ℝ)^4329 ≤ (3799326533231997/12500000000000000000 : ℝ)^1024 := by
      have hnat : (3681 : ℕ)^4329*12500000000000000000^1024 ≤ 3799326533231997^1024*25000^4329 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3681 25000 3799326533231997 12500000000000000000 4329 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3681/25000 : ℝ)) (X := (3799326533231997/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4329 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502403065577764103/12500000000000000000 : ℝ) ≤ (1250056838960263/1250000000000000 : ℝ) ^ (4329/1024 : ℝ) := by
    have hpowers : (12502403065577764103/12500000000000000000 : ℝ)^1024 ≤ (1250056838960263/1250000000000000 : ℝ)^4329 := by
      have hnat : (12502403065577764103 : ℕ)^1024*1250000000000000^4329 ≤ 1250056838960263^4329*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502403065577764103 12500000000000000000 1250056838960263 1250000000000000 1024 4329 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250056838960263/1250000000000000 : ℝ)) (X := (12502403065577764103/12500000000000000000 : ℝ)) (by norm_num) 4329 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25010001718644228097/25000000000000000000 : ℝ) ≤ (5000473097535899/5000000000000000 : ℝ) ^ (4329/1024 : ℝ) := by
    have hpowers : (25010001718644228097/25000000000000000000 : ℝ)^1024 ≤ (5000473097535899/5000000000000000 : ℝ)^4329 := by
      have hnat : (25010001718644228097 : ℕ)^1024*5000000000000000^4329 ≤ 5000473097535899^4329*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25010001718644228097 25000000000000000000 5000473097535899 5000000000000000 1024 4329 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000473097535899/5000000000000000 : ℝ)) (X := (25010001718644228097/25000000000000000000 : ℝ)) (by norm_num) 4329 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6253799326533231997/6250000000000000000 : ℝ) ≤ (2500359419615373/2500000000000000 : ℝ) ^ (4329/1024 : ℝ) := by
    have hpowers : (6253799326533231997/6250000000000000000 : ℝ)^1024 ≤ (2500359419615373/2500000000000000 : ℝ)^4329 := by
      have hnat : (6253799326533231997 : ℕ)^1024*2500000000000000^4329 ≤ 2500359419615373^4329*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253799326533231997 6250000000000000000 2500359419615373 2500000000000000 1024 4329 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500359419615373/2500000000000000 : ℝ)) (X := (6253799326533231997/6250000000000000000 : ℝ)) (by norm_num) 4329 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2403065577764103/25000000000000000000 : ℝ) ≤ ((487369070118612889/487500000000000000 : ℝ)+2*(245741694847/175500000000000 : ℝ)*(5607/50000 : ℝ))^(4329/1024 : ℝ) := by
    rw [show (487369070118612889/487500000000000000 : ℝ)+2*(245741694847/175500000000000 : ℝ)*(5607/50000 : ℝ)=(1250056838960263/1250000000000000 : ℝ) by norm_num, show 1+2*(2403065577764103/25000000000000000000 : ℝ)=(12502403065577764103/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3799326533231997/12500000000000000000 : ℝ)+(2403065577764103/25000000000000000000 : ℝ) ≤ ((487369070118612889/487500000000000000 : ℝ)+(245741694847/175500000000000 : ℝ)*((3681/25000 : ℝ)+(5607/50000 : ℝ)))^(4329/1024 : ℝ) := by
    rw [show (487369070118612889/487500000000000000 : ℝ)+(245741694847/175500000000000 : ℝ)*((3681/25000 : ℝ)+(5607/50000 : ℝ))=(5000473097535899/5000000000000000 : ℝ) by norm_num, show 1+(3799326533231997/12500000000000000000 : ℝ)+(2403065577764103/25000000000000000000 : ℝ)=(25010001718644228097/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3799326533231997/12500000000000000000 : ℝ) ≤ ((487369070118612889/487500000000000000 : ℝ)+2*(245741694847/175500000000000 : ℝ)*(3681/25000 : ℝ))^(4329/1024 : ℝ) := by
    rw [show (487369070118612889/487500000000000000 : ℝ)+2*(245741694847/175500000000000 : ℝ)*(3681/25000 : ℝ)=(2500359419615373/2500000000000000 : ℝ) by norm_num, show 1+2*(3799326533231997/12500000000000000000 : ℝ)=(6253799326533231997/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (487369070118612889/487500000000000000 : ℝ)*(X 1 0+X 2 0)+(245741694847/175500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4329/1024 : ℝ)) (lo := (5607/50000 : ℝ)) (hi := (3681/25000 : ℝ)) (c := (487369070118612889/487500000000000000 : ℝ)) (alpha := (245741694847/175500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (487369070118612889/487500000000000000 : ℝ)*(X 0 1+X 2 1)+(245741694847/175500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4329/1024 : ℝ)) (lo := (5607/50000 : ℝ)) (hi := (3681/25000 : ℝ)) (c := (487369070118612889/487500000000000000 : ℝ)) (alpha := (245741694847/175500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (487369070118612889/487500000000000000 : ℝ)*(X 0 2+X 1 2)+(245741694847/175500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4329/1024 : ℝ)) (lo := (5607/50000 : ℝ)) (hi := (3681/25000 : ℝ)) (c := (487369070118612889/487500000000000000 : ℝ)) (alpha := (245741694847/175500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-927480341/5000000000 : ℝ)*X 0 0+(5388766623/10000000000 : ℝ)*X 0 1+(5388766513/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((660689671/1250000000 : ℝ)*X 1 0+(-99827513/500000000 : ℝ)*X 1 1+(5388766351/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5285516871/10000000000 : ℝ)*X 2 0+(5388766921/10000000000 : ℝ)*X 2 1+(-499137539/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4466903103/10000000000 : ℝ)*X 0 0+(531175801/1250000000 : ℝ)*X 0 1+(2124703339/5000000000 : ℝ)*X 0 2+(4466903103/10000000000 : ℝ)*X 1 0+(531175801/1250000000 : ℝ)*X 1 1+(2124703339/5000000000 : ℝ)*X 1 2+(4466903103/10000000000 : ℝ)*X 2 0+(531175801/1250000000 : ℝ)*X 2 1+(2124703339/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-546960413/2500000000 : ℝ)*X 0 0+(164547231/312500000 : ℝ)*X 0 1+(2632755871/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2685993843/5000000000 : ℝ)*X 1 0+(-511550121/2500000000 : ℝ)*X 1 1+(5265511427/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5371987387/10000000000 : ℝ)*X 2 0+(210620459/400000000 : ℝ)*X 2 1+(-255775103/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4170837041/10000000000 : ℝ)*X 0 0+(2198693449/5000000000 : ℝ)*X 0 1+(4397386897/10000000000 : ℝ)*X 0 2+(4170837041/10000000000 : ℝ)*X 1 0+(2198693449/5000000000 : ℝ)*X 1 1+(4397386897/10000000000 : ℝ)*X 1 2+(4170837041/10000000000 : ℝ)*X 2 0+(2198693449/5000000000 : ℝ)*X 2 1+(4397386897/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2117865857/10000000000 : ℝ)*X 0 0+(2590264403/5000000000 : ℝ)*X 0 1+(270138691/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5275685899/10000000000 : ℝ)*X 1 0+(-79631069/400000000 : ℝ)*X 1 1+(2701386871/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5275685599/10000000000 : ℝ)*X 2 0+(2701386651/5000000000 : ℝ)*X 2 1+(-1990777731/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4499991249/10000000000 : ℝ)*X 0 0+(4232574741/10000000000 : ℝ)*X 0 1+(4232575497/10000000000 : ℝ)*X 0 2+(4499991249/10000000000 : ℝ)*X 1 0+(4232574741/10000000000 : ℝ)*X 1 1+(4232575497/10000000000 : ℝ)*X 1 2+(4499991249/10000000000 : ℝ)*X 2 0+(4232574741/10000000000 : ℝ)*X 2 1+(4232575497/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1925220667/10000000000 : ℝ)*X 0 0+(5471605349/10000000000 : ℝ)*X 0 1+(5254420623/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5379766049/10000000000 : ℝ)*X 1 0+(-2050566147/10000000000 : ℝ)*X 1 1+(2627210291/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5379766029/10000000000 : ℝ)*X 2 0+(525442063/1000000000 : ℝ)*X 2 1+(-2050566111/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4143746607/10000000000 : ℝ)*X 0 0+(1102673089/2500000000 : ℝ)*X 0 1+(1102673087/2500000000 : ℝ)*X 0 2+(4143746607/10000000000 : ℝ)*X 1 0+(1102673089/2500000000 : ℝ)*X 1 1+(1102673087/2500000000 : ℝ)*X 1 2+(4143746607/10000000000 : ℝ)*X 2 0+(1102673089/2500000000 : ℝ)*X 2 1+(1102673087/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62867/100000 : ℝ) ≤ (-5107773028836213130422798835997/8125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (122162749/100000000000000 : ℝ)*(lower0) + (1702569/5000000000000 : ℝ)*(lower3) + (206037281/100000000000000 : ℝ)*(lower4) + (2951813490205973/100000000000000 : ℝ)*(major0) + (2951813490205973/100000000000000 : ℝ)*(major1) + (2951813490205973/100000000000000 : ℝ)*(major2) + (7015142199/100000000000000 : ℝ)*(sp1) + (4226570849/25000000000000 : ℝ)*(sp2) + (503794983813273/12500000000000 : ℝ)*(sp4) + (125948708183219/3125000000000 : ℝ)*(sp5) + (4030348770721811/100000000000000 : ℝ)*(sp6) + (1894211049374753/100000000000000 : ℝ)*(sp7) + (5806499023/100000000000000 : ℝ)*(sp12) + (20391813/390625000000 : ℝ)*(sp15) + (1894216269678881/100000000000000 : ℝ)*(f.failure) + (4030365677005207/100000000000000 : ℝ)*(f.sum) + (25957341685369/8775000000000000000000000000 : ℝ)*base66 + (1630567190092201027/438750000000000000000000000000000 : ℝ)*base68 + (1915746425314048973/438750000000000000000000000000000 : ℝ)*base69 + (1774616587942798973/438750000000000000000000000000000 : ℝ)*base71 + (49652288945119/8775000000000000000000000000 : ℝ)*base74 + (1052385403804048973/438750000000000000000000000000000 : ℝ)*base75 + (1579881764689048973/438750000000000000000000000000000 : ℝ)*base77 + (2245301037449701027/438750000000000000000000000000000 : ℝ)*base80 + (10746504913439/2193750000000000000000000000 : ℝ)*base81 + (57814549/10000000000000000000000 : ℝ)*base90 + (57814549/10000000000000000000000 : ℝ)*base92 + (57814549/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (14749/25000 : ℝ) ≤ (168525506144786108503945590893/285644531250000000000000000000 : ℝ) := by norm_num
    linear_combination (6919091/50000000000000 : ℝ)*(lower1) + (14728223/20000000000000 : ℝ)*(upper2) + (6048437/100000000000000 : ℝ)*(upper5) + (94419968331673/3125000000000 : ℝ)*(major0) + (94419968331673/3125000000000 : ℝ)*(major1) + (94419968331673/3125000000000 : ℝ)*(major2) + (204215775243041/5000000000000 : ℝ)*(sp0) + (2042131956337659/50000000000000 : ℝ)*(sp1) + (1021076748196239/25000000000000 : ℝ)*(sp2) + (1938895031660233/100000000000000 : ℝ)*(sp3) + (4516797617/50000000000000 : ℝ)*(sp6) + (804839949/100000000000000 : ℝ)*(sp7) + (52113704871/100000000000000 : ℝ)*(sp9) + (521519369/100000000000000 : ℝ)*(sp12) + (969447918250091/50000000000000 : ℝ)*(f.failure) + (4084316026380189/100000000000000 : ℝ)*(f.sum) + (13191138741617/8775000000000000000000000000 : ℝ)*base65 + (25722631077391279/27421875000000000000000000000000 : ℝ)*base68 + (3338641172925863/3427734375000000000000000000000 : ℝ)*base70 + (75622602401922529/27421875000000000000000000000000 : ℝ)*base72 + (62106044350033/8775000000000000000000000000 : ℝ)*base74 + (248652307344578779/27421875000000000000000000000000 : ℝ)*base76 + (27647476496832113/3427734375000000000000000000000 : ℝ)*base78 + (34629279590844077/13710937500000000000000000000000 : ℝ)*base80 + (23744439714133/8775000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (1550361/5000000000000000000000 : ℝ)*base89 + (1550361/5000000000000000000000 : ℝ)*base91 + (1550361/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (80117/100000 : ℝ) ≤ (390580653028289055013940333/487500000000000000000000000 : ℝ) := by norm_num
    linear_combination (76841/24414062500 : ℝ)*(upper0) + (233765993/100000000000000 : ℝ)*(upper2) + (547725787/100000000000000 : ℝ)*(lower5) + (3332303391717553/100000000000000 : ℝ)*(major0) + (3332303391717553/100000000000000 : ℝ)*(major1) + (3332303391717553/100000000000000 : ℝ)*(major2) + (12559214791/12500000000000 : ℝ)*(sp1) + (40597932809/50000000000000 : ℝ)*(sp3) + (2044633231/25000000000000 : ℝ)*(sp4) + (4499506470109351/100000000000000 : ℝ)*(sp8) + (449941846020207/10000000000000 : ℝ)*(sp9) + (2249759466960199/50000000000000 : ℝ)*(sp10) + (133643767763203/6250000000000 : ℝ)*(sp11) + (1071319531/25000000000000 : ℝ)*(sp12) + (1069190740038433/50000000000000 : ℝ)*(f.failure) + (2249759466960199/50000000000000 : ℝ)*(f.sum) + (13739412956467/4387500000000000000000000000 : ℝ)*base66 + (571771258682340553/438750000000000000000000000000000 : ℝ)*base67 + (1169511502490159447/438750000000000000000000000000000 : ℝ)*base70 + (1099131658865159447/438750000000000000000000000000000 : ℝ)*base72 + (618440567690159/8775000000000000000000000000 : ℝ)*base74 + (1561052901024840553/438750000000000000000000000000000 : ℝ)*base75 + (2313335765825159447/438750000000000000000000000000000 : ℝ)*base78 + (9296476299840553/438750000000000000000000000000000 : ℝ)*base79 + (420384026159/8775000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (18574443/5000000000000000000000 : ℝ)*base89 + (18574443/5000000000000000000000 : ℝ)*base91 + (18574443/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-84461/100000 : ℝ) ≤ (-10293332505045596211305380920209/12187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3243359/50000000000000 : ℝ)*(lower0) + (944393/20000000000000 : ℝ)*(lower2) + (13514153/100000000000000 : ℝ)*(upper5) + (1684556182348791/50000000000000 : ℝ)*(major0) + (1684556182348791/50000000000000 : ℝ)*(major1) + (1684556182348791/50000000000000 : ℝ)*(major2) + (291783523/50000000000000 : ℝ)*(sp4) + (17909572183/100000000000000 : ℝ)*(sp5) + (161520711/12500000000000 : ℝ)*(sp7) + (4557361/20000000000000 : ℝ)*(sp8) + (4604374561006173/100000000000000 : ℝ)*(sp12) + (4604357257787841/100000000000000 : ℝ)*(sp13) + (575546895920003/12500000000000 : ℝ)*(sp14) + (2162000974156747/100000000000000 : ℝ)*(sp15) + (432400453264487/20000000000000 : ℝ)*(f.failure) + (575546895920003/12500000000000 : ℝ)*(f.sum) + (500496823993/2925000000000000000000000000 : ℝ)*base65 + (2517401232499398403/73125000000000000000000000000000 : ℝ)*base68 + (511127141021898403/73125000000000000000000000000000 : ℝ)*base70 + (671017752820023403/73125000000000000000000000000000 : ℝ)*base72 + (26423730925907/2925000000000000000000000000 : ℝ)*base74 + (534042584936898403/73125000000000000000000000000000 : ℝ)*base76 + (690533056590648403/73125000000000000000000000000000 : ℝ)*base78 + (420621043172523403/73125000000000000000000000000000 : ℝ)*base80 + (953340813209/1462500000000000000000000000 : ℝ)*base81 + (18000877/2000000000000000000000 : ℝ)*base89 + (18000877/2000000000000000000000 : ℝ)*base91 + (18000877/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1370_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155832971/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3681/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5607/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62867/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14749/25000 : ℝ) else (80117/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84461/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1370_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1370_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155832971/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14731/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11207/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62867/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14749/25000 : ℝ) else (80117/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84461/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1370_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1370_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1370_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155832971/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14731/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11207/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62867/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14749/25000 : ℝ) else (80117/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84461/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1370_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
