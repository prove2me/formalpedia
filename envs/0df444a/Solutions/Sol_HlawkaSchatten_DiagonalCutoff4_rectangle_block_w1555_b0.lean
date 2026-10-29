-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1555_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:11:21.198532+00:00
-- url     : https://prove2.me/submissions/2b363f5b-dcdd-47f9-98c5-462cbd88df7f

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
theorem support_rectangle_w1555_s0_0 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1641162439/10000000000 : ℝ)*x 0 + (1470119959/2500000000 : ℝ)*x 1 + (974656739/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1641162439/10000000000 : ℝ)^4607 ≤ (9791440175419/100000000000000 : ℝ)^3583 := by
    have hnat : (1641162439 : ℕ)^4607*100000000000000^3583 ≤ 9791440175419^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1641162439 10000000000 9791440175419 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1470119959/2500000000 : ℝ)^4607 ≤ (2021027867501/4000000000000 : ℝ)^3583 := by
    have hnat : (1470119959 : ℕ)^4607*4000000000000^3583 ≤ 2021027867501^3583*2500000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1470119959 2500000000 2021027867501 4000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (974656739/2000000000 : ℝ)^4607 ≤ (7936572625227/20000000000000 : ℝ)^3583 := by
    have hnat : (974656739 : ℕ)^4607*20000000000000^3583 ≤ 7936572625227^3583*2000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      974656739 2000000000 7936572625227 20000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1641162439/10000000000 : ℝ), (1470119959/2500000000 : ℝ), (974656739/2000000000 : ℝ)] ![(9791440175419/100000000000000 : ℝ), (2021027867501/4000000000000 : ℝ), (7936572625227/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1641162439/10000000000 : ℝ)|^4607 ≤ (9791440175419/100000000000000 : ℝ)^3583
        have hw : |(-1641162439/10000000000 : ℝ)|=(1641162439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1470119959/2500000000 : ℝ)|^4607 ≤ (2021027867501/4000000000000 : ℝ)^3583
        have hw : |(1470119959/2500000000 : ℝ)|=(1470119959/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(974656739/2000000000 : ℝ)|^4607 ≤ (7936572625227/20000000000000 : ℝ)^3583
        have hw : |(974656739/2000000000 : ℝ)|=(974656739/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1555_s0_1 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1367171827/2500000000 : ℝ)*x 0 + (-550667683/2500000000 : ℝ)*x 1 + (2436641847/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1367171827/2500000000 : ℝ)^4607 ≤ (9204530487339/20000000000000 : ℝ)^3583 := by
    have hnat : (1367171827 : ℕ)^4607*20000000000000^3583 ≤ 9204530487339^3583*2500000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1367171827 2500000000 9204530487339 20000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (550667683/2500000000 : ℝ)^4607 ≤ (7147242212001/50000000000000 : ℝ)^3583 := by
    have hnat : (550667683 : ℕ)^4607*50000000000000^3583 ≤ 7147242212001^3583*2500000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550667683 2500000000 7147242212001 50000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2436641847/5000000000 : ℝ)^4607 ≤ (2480178944729/6250000000000 : ℝ)^3583 := by
    have hnat : (2436641847 : ℕ)^4607*6250000000000^3583 ≤ 2480178944729^3583*5000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2436641847 5000000000 2480178944729 6250000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1367171827/2500000000 : ℝ), (-550667683/2500000000 : ℝ), (2436641847/5000000000 : ℝ)] ![(9204530487339/20000000000000 : ℝ), (7147242212001/50000000000000 : ℝ), (2480178944729/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1367171827/2500000000 : ℝ)|^4607 ≤ (9204530487339/20000000000000 : ℝ)^3583
        have hw : |(1367171827/2500000000 : ℝ)|=(1367171827/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-550667683/2500000000 : ℝ)|^4607 ≤ (7147242212001/50000000000000 : ℝ)^3583
        have hw : |(-550667683/2500000000 : ℝ)|=(550667683/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2436641847/5000000000 : ℝ)|^4607 ≤ (2480178944729/6250000000000 : ℝ)^3583
        have hw : |(2436641847/5000000000 : ℝ)|=(2436641847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1555_s0_2 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5468687347/10000000000 : ℝ)*x 0 + (4873283649/10000000000 : ℝ)*x 1 + (-1101335369/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5468687347/10000000000 : ℝ)^4607 ≤ (23011326429353/50000000000000 : ℝ)^3583 := by
    have hnat : (5468687347 : ℕ)^4607*50000000000000^3583 ≤ 23011326429353^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5468687347 10000000000 23011326429353 50000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4873283649/10000000000 : ℝ)^4607 ≤ (9920715661127/25000000000000 : ℝ)^3583 := by
    have hnat : (4873283649 : ℕ)^4607*25000000000000^3583 ≤ 9920715661127^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4873283649 10000000000 9920715661127 25000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1101335369/5000000000 : ℝ)^4607 ≤ (3573621118517/25000000000000 : ℝ)^3583 := by
    have hnat : (1101335369 : ℕ)^4607*25000000000000^3583 ≤ 3573621118517^3583*5000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101335369 5000000000 3573621118517 25000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5468687347/10000000000 : ℝ), (4873283649/10000000000 : ℝ), (-1101335369/5000000000 : ℝ)] ![(23011326429353/50000000000000 : ℝ), (9920715661127/25000000000000 : ℝ), (3573621118517/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5468687347/10000000000 : ℝ)|^4607 ≤ (23011326429353/50000000000000 : ℝ)^3583
        have hw : |(5468687347/10000000000 : ℝ)|=(5468687347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4873283649/10000000000 : ℝ)|^4607 ≤ (9920715661127/25000000000000 : ℝ)^3583
        have hw : |(4873283649/10000000000 : ℝ)|=(4873283649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1101335369/5000000000 : ℝ)|^4607 ≤ (3573621118517/25000000000000 : ℝ)^3583
        have hw : |(-1101335369/5000000000 : ℝ)|=(1101335369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1555_s0_3 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2066871071/5000000000 : ℝ)*x 0 + (3092410431/10000000000 : ℝ)*x 1 + (1361420917/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2066871071/5000000000 : ℝ)^4607 ≤ (6422832675613/20000000000000 : ℝ)^3583 := by
    have hnat : (2066871071 : ℕ)^4607*20000000000000^3583 ≤ 6422832675613^3583*5000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2066871071 5000000000 6422832675613 20000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3092410431/10000000000 : ℝ)^4607 ≤ (1381997033317/6250000000000 : ℝ)^3583 := by
    have hnat : (3092410431 : ℕ)^4607*6250000000000^3583 ≤ 1381997033317^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3092410431 10000000000 1381997033317 6250000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1361420917/2500000000 : ℝ)^4607 ≤ (45773884083761/100000000000000 : ℝ)^3583 := by
    have hnat : (1361420917 : ℕ)^4607*100000000000000^3583 ≤ 45773884083761^3583*2500000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1361420917 2500000000 45773884083761 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2066871071/5000000000 : ℝ), (3092410431/10000000000 : ℝ), (1361420917/2500000000 : ℝ)] ![(6422832675613/20000000000000 : ℝ), (1381997033317/6250000000000 : ℝ), (45773884083761/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2066871071/5000000000 : ℝ)|^4607 ≤ (6422832675613/20000000000000 : ℝ)^3583
        have hw : |(2066871071/5000000000 : ℝ)|=(2066871071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3092410431/10000000000 : ℝ)|^4607 ≤ (1381997033317/6250000000000 : ℝ)^3583
        have hw : |(3092410431/10000000000 : ℝ)|=(3092410431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1361420917/2500000000 : ℝ)|^4607 ≤ (45773884083761/100000000000000 : ℝ)^3583
        have hw : |(1361420917/2500000000 : ℝ)|=(1361420917/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1555_s0_4 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-328866379/2000000000 : ℝ)*x 0 + (4898750797/10000000000 : ℝ)*x 1 + (5854107733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (328866379/2000000000 : ℝ)^4607 ≤ (9815760586771/100000000000000 : ℝ)^3583 := by
    have hnat : (328866379 : ℕ)^4607*100000000000000^3583 ≤ 9815760586771^3583*2000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328866379 2000000000 9815760586771 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4898750797/10000000000 : ℝ)^4607 ≤ (39949706256619/100000000000000 : ℝ)^3583 := by
    have hnat : (4898750797 : ℕ)^4607*100000000000000^3583 ≤ 39949706256619^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4898750797 10000000000 39949706256619 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5854107733/10000000000 : ℝ)^4607 ≤ (50234533135489/100000000000000 : ℝ)^3583 := by
    have hnat : (5854107733 : ℕ)^4607*100000000000000^3583 ≤ 50234533135489^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5854107733 10000000000 50234533135489 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-328866379/2000000000 : ℝ), (4898750797/10000000000 : ℝ), (5854107733/10000000000 : ℝ)] ![(9815760586771/100000000000000 : ℝ), (39949706256619/100000000000000 : ℝ), (50234533135489/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-328866379/2000000000 : ℝ)|^4607 ≤ (9815760586771/100000000000000 : ℝ)^3583
        have hw : |(-328866379/2000000000 : ℝ)|=(328866379/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4898750797/10000000000 : ℝ)|^4607 ≤ (39949706256619/100000000000000 : ℝ)^3583
        have hw : |(4898750797/10000000000 : ℝ)|=(4898750797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5854107733/10000000000 : ℝ)|^4607 ≤ (50234533135489/100000000000000 : ℝ)^3583
        have hw : |(5854107733/10000000000 : ℝ)|=(5854107733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1555_s0_5 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (32458573/62500000 : ℝ)*x 0 + (-152730879/1250000000 : ℝ)*x 1 + (14635269/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (32458573/62500000 : ℝ)^4607 ≤ (43065207581793/100000000000000 : ℝ)^3583 := by
    have hnat : (32458573 : ℕ)^4607*100000000000000^3583 ≤ 43065207581793^3583*62500000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32458573 62500000 43065207581793 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (152730879/1250000000 : ℝ)^4607 ≤ (6700260739221/100000000000000 : ℝ)^3583 := by
    have hnat : (152730879 : ℕ)^4607*100000000000000^3583 ≤ 6700260739221^3583*1250000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      152730879 1250000000 6700260739221 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (14635269/25000000 : ℝ)^4607 ≤ (10046906333607/20000000000000 : ℝ)^3583 := by
    have hnat : (14635269 : ℕ)^4607*20000000000000^3583 ≤ 10046906333607^3583*25000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14635269 25000000 10046906333607 20000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(32458573/62500000 : ℝ), (-152730879/1250000000 : ℝ), (14635269/25000000 : ℝ)] ![(43065207581793/100000000000000 : ℝ), (6700260739221/100000000000000 : ℝ), (10046906333607/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(32458573/62500000 : ℝ)|^4607 ≤ (43065207581793/100000000000000 : ℝ)^3583
        have hw : |(32458573/62500000 : ℝ)|=(32458573/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-152730879/1250000000 : ℝ)|^4607 ≤ (6700260739221/100000000000000 : ℝ)^3583
        have hw : |(-152730879/1250000000 : ℝ)|=(152730879/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(14635269/25000000 : ℝ)|^4607 ≤ (10046906333607/20000000000000 : ℝ)^3583
        have hw : |(14635269/25000000 : ℝ)|=(14635269/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1555_s0_6 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2596685769/5000000000 : ℝ)*x 0 + (2927054007/5000000000 : ℝ)*x 1 + (-610923299/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2596685769/5000000000 : ℝ)^4607 ≤ (8613041213551/20000000000000 : ℝ)^3583 := by
    have hnat : (2596685769 : ℕ)^4607*20000000000000^3583 ≤ 8613041213551^3583*5000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2596685769 5000000000 8613041213551 20000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2927054007/5000000000 : ℝ)^4607 ≤ (50234536235901/100000000000000 : ℝ)^3583 := by
    have hnat : (2927054007 : ℕ)^4607*100000000000000^3583 ≤ 50234536235901^3583*5000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2927054007 5000000000 50234536235901 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (610923299/5000000000 : ℝ)^4607 ≤ (3350128839559/50000000000000 : ℝ)^3583 := by
    have hnat : (610923299 : ℕ)^4607*50000000000000^3583 ≤ 3350128839559^3583*5000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      610923299 5000000000 3350128839559 50000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2596685769/5000000000 : ℝ), (2927054007/5000000000 : ℝ), (-610923299/5000000000 : ℝ)] ![(8613041213551/20000000000000 : ℝ), (50234536235901/100000000000000 : ℝ), (3350128839559/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2596685769/5000000000 : ℝ)|^4607 ≤ (8613041213551/20000000000000 : ℝ)^3583
        have hw : |(2596685769/5000000000 : ℝ)|=(2596685769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2927054007/5000000000 : ℝ)|^4607 ≤ (50234536235901/100000000000000 : ℝ)^3583
        have hw : |(2927054007/5000000000 : ℝ)|=(2927054007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-610923299/5000000000 : ℝ)|^4607 ≤ (3350128839559/50000000000000 : ℝ)^3583
        have hw : |(-610923299/5000000000 : ℝ)|=(610923299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1555_s0_7 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4141146407/10000000000 : ℝ)*x 0 + (5386180603/10000000000 : ℝ)*x 1 + (3154027549/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4141146407/10000000000 : ℝ)^4607 ≤ (4023517993779/12500000000000 : ℝ)^3583 := by
    have hnat : (4141146407 : ℕ)^4607*12500000000000^3583 ≤ 4023517993779^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4141146407 10000000000 4023517993779 12500000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5386180603/10000000000 : ℝ)^4607 ≤ (45131794403111/100000000000000 : ℝ)^3583 := by
    have hnat : (5386180603 : ℕ)^4607*100000000000000^3583 ≤ 45131794403111^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386180603 10000000000 45131794403111 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3154027549/10000000000 : ℝ)^4607 ≤ (708751925903/3125000000000 : ℝ)^3583 := by
    have hnat : (3154027549 : ℕ)^4607*3125000000000^3583 ≤ 708751925903^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3154027549 10000000000 708751925903 3125000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4141146407/10000000000 : ℝ), (5386180603/10000000000 : ℝ), (3154027549/10000000000 : ℝ)] ![(4023517993779/12500000000000 : ℝ), (45131794403111/100000000000000 : ℝ), (708751925903/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4141146407/10000000000 : ℝ)|^4607 ≤ (4023517993779/12500000000000 : ℝ)^3583
        have hw : |(4141146407/10000000000 : ℝ)|=(4141146407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5386180603/10000000000 : ℝ)|^4607 ≤ (45131794403111/100000000000000 : ℝ)^3583
        have hw : |(5386180603/10000000000 : ℝ)|=(5386180603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3154027549/10000000000 : ℝ)|^4607 ≤ (708751925903/3125000000000 : ℝ)^3583
        have hw : |(3154027549/10000000000 : ℝ)|=(3154027549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1555_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41705747/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (673/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (24939/100000 : ℝ)*pair X 0 0 := by
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
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (4605/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4605 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4605*1^1024 ≤ 0^1024*1^4605 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4605 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4605 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4605/1024 : ℝ) ≤ (811719174782615613/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4605 ≤ (811719174782615613/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4605*50000000000000000000^1024 ≤ 811719174782615613^1024*5^4605 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 811719174782615613 50000000000000000000 4605 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (811719174782615613/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4605 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4605/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4605 := by
      have hnat : (1 : ℕ)^1024*1^4605 ≤ 1^4605*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4605 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4605 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50811719174782615613/50000000000000000000 : ℝ) ≤ (5017937104098883/5000000000000000 : ℝ) ^ (4605/1024 : ℝ) := by
    have hpowers : (50811719174782615613/50000000000000000000 : ℝ)^1024 ≤ (5017937104098883/5000000000000000 : ℝ)^4605 := by
      have hnat : (50811719174782615613 : ℕ)^1024*5000000000000000^4605 ≤ 5017937104098883^4605*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50811719174782615613 50000000000000000000 5017937104098883 5000000000000000 1024 4605 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5017937104098883/5000000000000000 : ℝ)) (X := (50811719174782615613/50000000000000000000 : ℝ)) (by norm_num) 4605 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25811719174782615613/25000000000000000000 : ℝ) ≤ (2517937104098883/2500000000000000 : ℝ) ^ (4605/1024 : ℝ) := by
    have hpowers : (25811719174782615613/25000000000000000000 : ℝ)^1024 ≤ (2517937104098883/2500000000000000 : ℝ)^4605 := by
      have hnat : (25811719174782615613 : ℕ)^1024*2500000000000000^4605 ≤ 2517937104098883^4605*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25811719174782615613 25000000000000000000 2517937104098883 2500000000000000 1024 4605 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2517937104098883/2500000000000000 : ℝ)) (X := (25811719174782615613/25000000000000000000 : ℝ)) (by norm_num) 4605 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(17937104098883/2000000000000000 : ℝ)*(0 : ℝ))^(4605/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(17937104098883/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(811719174782615613/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(17937104098883/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4605/1024 : ℝ) := by
    rw [show (1 : ℝ)+(17937104098883/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5017937104098883/5000000000000000 : ℝ) by norm_num, show 1+(811719174782615613/50000000000000000000 : ℝ)+(0 : ℝ)=(50811719174782615613/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(811719174782615613/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(17937104098883/2000000000000000 : ℝ)*(2/5 : ℝ))^(4605/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(17937104098883/2000000000000000 : ℝ)*(2/5 : ℝ)=(2517937104098883/2500000000000000 : ℝ) by norm_num, show 1+2*(811719174782615613/50000000000000000000 : ℝ)=(25811719174782615613/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(17937104098883/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4605/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (17937104098883/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(17937104098883/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4605/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (17937104098883/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(17937104098883/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4605/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (17937104098883/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1641162439/10000000000 : ℝ)*X 0 0+(1470119959/2500000000 : ℝ)*X 0 1+(974656739/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1367171827/2500000000 : ℝ)*X 1 0+(-550667683/2500000000 : ℝ)*X 1 1+(2436641847/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5468687347/10000000000 : ℝ)*X 2 0+(4873283649/10000000000 : ℝ)*X 2 1+(-1101335369/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2066871071/5000000000 : ℝ)*X 0 0+(3092410431/10000000000 : ℝ)*X 0 1+(1361420917/2500000000 : ℝ)*X 0 2+(2066871071/5000000000 : ℝ)*X 1 0+(3092410431/10000000000 : ℝ)*X 1 1+(1361420917/2500000000 : ℝ)*X 1 2+(2066871071/5000000000 : ℝ)*X 2 0+(3092410431/10000000000 : ℝ)*X 2 1+(1361420917/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-328866379/2000000000 : ℝ)*X 0 0+(4898750797/10000000000 : ℝ)*X 0 1+(5854107733/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((32458573/62500000 : ℝ)*X 1 0+(-152730879/1250000000 : ℝ)*X 1 1+(14635269/25000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2596685769/5000000000 : ℝ)*X 2 0+(2927054007/5000000000 : ℝ)*X 2 1+(-610923299/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4141146407/10000000000 : ℝ)*X 0 0+(5386180603/10000000000 : ℝ)*X 0 1+(3154027549/10000000000 : ℝ)*X 0 2+(4141146407/10000000000 : ℝ)*X 1 0+(5386180603/10000000000 : ℝ)*X 1 1+(3154027549/10000000000 : ℝ)*X 1 2+(4141146407/10000000000 : ℝ)*X 2 0+(5386180603/10000000000 : ℝ)*X 2 1+(3154027549/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (30746099452384651656669/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (24288903/100000000000000 : ℝ)*(base1) + (503636517/100000000000000 : ℝ)*(base19) + (63839637/12500000000000 : ℝ)*(base23) + (1609213/2500000000000 : ℝ)*(upper3) + (4036163/6250000000000 : ℝ)*(upper5) + (354450132044481/50000000000000 : ℝ)*(major0) + (354450132044481/50000000000000 : ℝ)*(major1) + (354450132044481/50000000000000 : ℝ)*(major2) + (62053563882757/6250000000000 : ℝ)*(sp0) + (496429174358823/50000000000000 : ℝ)*(sp1) + (496429170818533/50000000000000 : ℝ)*(sp2) + (212470388905641/50000000000000 : ℝ)*(sp3) + (927259477/50000000000000 : ℝ)*(sp4) + (791733971/100000000000000 : ℝ)*(sp7) + (106235398458539/25000000000000 : ℝ)*(f.failure) + (992858852354163/100000000000000 : ℝ)*(f.sum) + (3173583735277/50000000000000000000000000000 : ℝ)*base66 + (279985924085277/100000000000000000000000000000 : ℝ)*base68 + (1126183479285277/100000000000000000000000000000 : ℝ)*base70 + (618147542485277/100000000000000000000000000000 : ℝ)*base72 + (152404469264723/50000000000000000000000000000 : ℝ)*base73 + (1244127399485277/100000000000000000000000000000 : ℝ)*base76 + (352604235885277/100000000000000000000000000000 : ℝ)*base78 + (196548110485277/100000000000000000000000000000 : ℝ)*base80 + (263886758935277/50000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (5023633/625000000000000000000 : ℝ)*base89 + (5023633/625000000000000000000 : ℝ)*base91 + (5023633/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (91895094387365008494477/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (465591079/50000000000000 : ℝ)*(base19) + (103081489/10000000000000 : ℝ)*(base23) + (60169457/50000000000000 : ℝ)*(base39) + (6138147/5000000000000 : ℝ)*(upper3) + (188753831/100000000000000 : ℝ)*(upper5) + (149472650664027/20000000000000 : ℝ)*(major0) + (149472650664027/20000000000000 : ℝ)*(major1) + (747363132981221/100000000000000 : ℝ)*(major2) + (1271245903/50000000000000 : ℝ)*(sp1) + (1365487887/50000000000000 : ℝ)*(sp2) + (1046728470796023/100000000000000 : ℝ)*(sp4) + (52336249856103/5000000000000 : ℝ)*(sp5) + (1046724829344273/100000000000000 : ℝ)*(sp6) + (447997762346839/100000000000000 : ℝ)*(sp7) + (447997762346839/100000000000000 : ℝ)*(f.failure) + (1046728591134937/100000000000000 : ℝ)*(f.sum) + (120937779153663/50000000000000000000000000000 : ℝ)*base66 + (124633716476143/200000000000000000000000000000 : ℝ)*base67 + (65112880181841/40000000000000000000000000000 : ℝ)*base69 + (557420738123857/200000000000000000000000000000 : ℝ)*base72 + (6721614996337/50000000000000000000000000000 : ℝ)*base73 + (213771980018159/40000000000000000000000000000 : ℝ)*base76 + (56586218018159/40000000000000000000000000000 : ℝ)*base78 + (58921936381841/40000000000000000000000000000 : ℝ)*base79 + (5742756081841/20000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (18583733/2500000000000000000000 : ℝ)*base89 + (18583733/2500000000000000000000 : ℝ)*base91 + (18583733/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1555_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41705747/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (673/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (24939/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1555_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1555_s1_0 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1783586799/10000000000 : ℝ)*x 0 + (2771761467/5000000000 : ℝ)*x 1 + (2559256411/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1783586799/10000000000 : ℝ)^4607 ≤ (5448646367177/50000000000000 : ℝ)^3583 := by
    have hnat : (1783586799 : ℕ)^4607*50000000000000^3583 ≤ 5448646367177^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1783586799 10000000000 5448646367177 50000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2771761467/5000000000 : ℝ)^4607 ≤ (11708503310003/25000000000000 : ℝ)^3583 := by
    have hnat : (2771761467 : ℕ)^4607*25000000000000^3583 ≤ 11708503310003^3583*5000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2771761467 5000000000 11708503310003 25000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2559256411/5000000000 : ℝ)^4607 ≤ (1320896687801/3125000000000 : ℝ)^3583 := by
    have hnat : (2559256411 : ℕ)^4607*3125000000000^3583 ≤ 1320896687801^3583*5000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2559256411 5000000000 1320896687801 3125000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1783586799/10000000000 : ℝ), (2771761467/5000000000 : ℝ), (2559256411/5000000000 : ℝ)] ![(5448646367177/50000000000000 : ℝ), (11708503310003/25000000000000 : ℝ), (1320896687801/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1783586799/10000000000 : ℝ)|^4607 ≤ (5448646367177/50000000000000 : ℝ)^3583
        have hw : |(-1783586799/10000000000 : ℝ)|=(1783586799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2771761467/5000000000 : ℝ)|^4607 ≤ (11708503310003/25000000000000 : ℝ)^3583
        have hw : |(2771761467/5000000000 : ℝ)|=(2771761467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2559256411/5000000000 : ℝ)|^4607 ≤ (1320896687801/3125000000000 : ℝ)^3583
        have hw : |(2559256411/5000000000 : ℝ)|=(2559256411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1555_s1_1 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2689498891/5000000000 : ℝ)*x 0 + (-1003128039/5000000000 : ℝ)*x 1 + (51185127/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2689498891/5000000000 : ℝ)^4607 ≤ (1126360553309/2500000000000 : ℝ)^3583 := by
    have hnat : (2689498891 : ℕ)^4607*2500000000000^3583 ≤ 1126360553309^3583*5000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2689498891 5000000000 1126360553309 2500000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1003128039/5000000000 : ℝ)^4607 ≤ (3169221284423/25000000000000 : ℝ)^3583 := by
    have hnat : (1003128039 : ℕ)^4607*25000000000000^3583 ≤ 3169221284423^3583*5000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1003128039 5000000000 3169221284423 25000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (51185127/100000000 : ℝ)^4607 ≤ (1690747708569/4000000000000 : ℝ)^3583 := by
    have hnat : (51185127 : ℕ)^4607*4000000000000^3583 ≤ 1690747708569^3583*100000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51185127 100000000 1690747708569 4000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2689498891/5000000000 : ℝ), (-1003128039/5000000000 : ℝ), (51185127/100000000 : ℝ)] ![(1126360553309/2500000000000 : ℝ), (3169221284423/25000000000000 : ℝ), (1690747708569/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2689498891/5000000000 : ℝ)|^4607 ≤ (1126360553309/2500000000000 : ℝ)^3583
        have hw : |(2689498891/5000000000 : ℝ)|=(2689498891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1003128039/5000000000 : ℝ)|^4607 ≤ (3169221284423/25000000000000 : ℝ)^3583
        have hw : |(-1003128039/5000000000 : ℝ)|=(1003128039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(51185127/100000000 : ℝ)|^4607 ≤ (1690747708569/4000000000000 : ℝ)^3583
        have hw : |(51185127/100000000 : ℝ)|=(51185127/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1555_s1_2 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1344749449/2500000000 : ℝ)*x 0 + (1023702537/2000000000 : ℝ)*x 1 + (-2006256079/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1344749449/2500000000 : ℝ)^4607 ≤ (45054422283137/100000000000000 : ℝ)^3583 := by
    have hnat : (1344749449 : ℕ)^4607*100000000000000^3583 ≤ 45054422283137^3583*2500000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344749449 2500000000 45054422283137 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1023702537/2000000000 : ℝ)^4607 ≤ (21134346277477/50000000000000 : ℝ)^3583 := by
    have hnat : (1023702537 : ℕ)^4607*50000000000000^3583 ≤ 21134346277477^3583*2000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1023702537 2000000000 21134346277477 50000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2006256079/10000000000 : ℝ)^4607 ≤ (1584610643227/12500000000000 : ℝ)^3583 := by
    have hnat : (2006256079 : ℕ)^4607*12500000000000^3583 ≤ 1584610643227^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2006256079 10000000000 1584610643227 12500000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1344749449/2500000000 : ℝ), (1023702537/2000000000 : ℝ), (-2006256079/10000000000 : ℝ)] ![(45054422283137/100000000000000 : ℝ), (21134346277477/50000000000000 : ℝ), (1584610643227/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1344749449/2500000000 : ℝ)|^4607 ≤ (45054422283137/100000000000000 : ℝ)^3583
        have hw : |(1344749449/2500000000 : ℝ)|=(1344749449/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1023702537/2000000000 : ℝ)|^4607 ≤ (21134346277477/50000000000000 : ℝ)^3583
        have hw : |(1023702537/2000000000 : ℝ)|=(1023702537/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2006256079/10000000000 : ℝ)|^4607 ≤ (1584610643227/12500000000000 : ℝ)^3583
        have hw : |(-2006256079/10000000000 : ℝ)|=(2006256079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1555_s1_3 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (423392381/1000000000 : ℝ)*x 0 + (3761162277/10000000000 : ℝ)*x 1 + (4754181369/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (423392381/1000000000 : ℝ)^4607 ≤ (1324733197153/4000000000000 : ℝ)^3583 := by
    have hnat : (423392381 : ℕ)^4607*4000000000000^3583 ≤ 1324733197153^3583*1000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423392381 1000000000 1324733197153 4000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3761162277/10000000000 : ℝ)^4607 ≤ (7110361229363/25000000000000 : ℝ)^3583 := by
    have hnat : (3761162277 : ℕ)^4607*25000000000000^3583 ≤ 7110361229363^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3761162277 10000000000 7110361229363 25000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4754181369/10000000000 : ℝ)^4607 ≤ (9610056285069/25000000000000 : ℝ)^3583 := by
    have hnat : (4754181369 : ℕ)^4607*25000000000000^3583 ≤ 9610056285069^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4754181369 10000000000 9610056285069 25000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(423392381/1000000000 : ℝ), (3761162277/10000000000 : ℝ), (4754181369/10000000000 : ℝ)] ![(1324733197153/4000000000000 : ℝ), (7110361229363/25000000000000 : ℝ), (9610056285069/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(423392381/1000000000 : ℝ)|^4607 ≤ (1324733197153/4000000000000 : ℝ)^3583
        have hw : |(423392381/1000000000 : ℝ)|=(423392381/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3761162277/10000000000 : ℝ)|^4607 ≤ (7110361229363/25000000000000 : ℝ)^3583
        have hw : |(3761162277/10000000000 : ℝ)|=(3761162277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4754181369/10000000000 : ℝ)|^4607 ≤ (9610056285069/25000000000000 : ℝ)^3583
        have hw : |(4754181369/10000000000 : ℝ)|=(4754181369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1555_s1_4 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-891909041/5000000000 : ℝ)*x 0 + (2561493899/5000000000 : ℝ)*x 1 + (2769490239/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (891909041/5000000000 : ℝ)^4607 ≤ (10899109703411/100000000000000 : ℝ)^3583 := by
    have hnat : (891909041 : ℕ)^4607*100000000000000^3583 ≤ 10899109703411^3583*5000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      891909041 5000000000 10899109703411 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2561493899/5000000000 : ℝ)^4607 ≤ (21158107823211/50000000000000 : ℝ)^3583 := by
    have hnat : (2561493899 : ℕ)^4607*50000000000000^3583 ≤ 21158107823211^3583*5000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2561493899 5000000000 21158107823211 50000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2769490239/5000000000 : ℝ)^4607 ≤ (46784674643231/100000000000000 : ℝ)^3583 := by
    have hnat : (2769490239 : ℕ)^4607*100000000000000^3583 ≤ 46784674643231^3583*5000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2769490239 5000000000 46784674643231 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-891909041/5000000000 : ℝ), (2561493899/5000000000 : ℝ), (2769490239/5000000000 : ℝ)] ![(10899109703411/100000000000000 : ℝ), (21158107823211/50000000000000 : ℝ), (46784674643231/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-891909041/5000000000 : ℝ)|^4607 ≤ (10899109703411/100000000000000 : ℝ)^3583
        have hw : |(-891909041/5000000000 : ℝ)|=(891909041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2561493899/5000000000 : ℝ)|^4607 ≤ (21158107823211/50000000000000 : ℝ)^3583
        have hw : |(2561493899/5000000000 : ℝ)|=(2561493899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2769490239/5000000000 : ℝ)|^4607 ≤ (46784674643231/100000000000000 : ℝ)^3583
        have hw : |(2769490239/5000000000 : ℝ)|=(2769490239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1555_s1_5 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5266511127/10000000000 : ℝ)*x 0 + (-792895293/5000000000 : ℝ)*x 1 + (110779591/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5266511127/10000000000 : ℝ)^4607 ≤ (21923301110507/50000000000000 : ℝ)^3583 := by
    have hnat : (5266511127 : ℕ)^4607*50000000000000^3583 ≤ 21923301110507^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266511127 10000000000 21923301110507 50000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (792895293/5000000000 : ℝ)^4607 ≤ (9368733206951/100000000000000 : ℝ)^3583 := by
    have hnat : (792895293 : ℕ)^4607*100000000000000^3583 ≤ 9368733206951^3583*5000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      792895293 5000000000 9368733206951 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (110779591/200000000 : ℝ)^4607 ≤ (9356932912959/20000000000000 : ℝ)^3583 := by
    have hnat : (110779591 : ℕ)^4607*20000000000000^3583 ≤ 9356932912959^3583*200000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110779591 200000000 9356932912959 20000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5266511127/10000000000 : ℝ), (-792895293/5000000000 : ℝ), (110779591/200000000 : ℝ)] ![(21923301110507/50000000000000 : ℝ), (9368733206951/100000000000000 : ℝ), (9356932912959/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5266511127/10000000000 : ℝ)|^4607 ≤ (21923301110507/50000000000000 : ℝ)^3583
        have hw : |(5266511127/10000000000 : ℝ)|=(5266511127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-792895293/5000000000 : ℝ)|^4607 ≤ (9368733206951/100000000000000 : ℝ)^3583
        have hw : |(-792895293/5000000000 : ℝ)|=(792895293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(110779591/200000000 : ℝ)|^4607 ≤ (9356932912959/20000000000000 : ℝ)^3583
        have hw : |(110779591/200000000 : ℝ)|=(110779591/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1555_s1_6 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1053302609/2000000000 : ℝ)*x 0 + (1107795801/2000000000 : ℝ)*x 1 + (-1585788661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1053302609/2000000000 : ℝ)^4607 ≤ (8769324550619/20000000000000 : ℝ)^3583 := by
    have hnat : (1053302609 : ℕ)^4607*20000000000000^3583 ≤ 8769324550619^3583*2000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053302609 2000000000 8769324550619 20000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1107795801/2000000000 : ℝ)^4607 ≤ (23392329322943/50000000000000 : ℝ)^3583 := by
    have hnat : (1107795801 : ℕ)^4607*50000000000000^3583 ≤ 23392329322943^3583*2000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1107795801 2000000000 23392329322943 50000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1585788661/10000000000 : ℝ)^4607 ≤ (936871858393/10000000000000 : ℝ)^3583 := by
    have hnat : (1585788661 : ℕ)^4607*10000000000000^3583 ≤ 936871858393^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1585788661 10000000000 936871858393 10000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1053302609/2000000000 : ℝ), (1107795801/2000000000 : ℝ), (-1585788661/10000000000 : ℝ)] ![(8769324550619/20000000000000 : ℝ), (23392329322943/50000000000000 : ℝ), (936871858393/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1053302609/2000000000 : ℝ)|^4607 ≤ (8769324550619/20000000000000 : ℝ)^3583
        have hw : |(1053302609/2000000000 : ℝ)|=(1053302609/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1107795801/2000000000 : ℝ)|^4607 ≤ (23392329322943/50000000000000 : ℝ)^3583
        have hw : |(1107795801/2000000000 : ℝ)|=(1107795801/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1585788661/10000000000 : ℝ)|^4607 ≤ (936871858393/10000000000000 : ℝ)^3583
        have hw : |(-1585788661/10000000000 : ℝ)|=(1585788661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1555_s1_7 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2117232457/5000000000 : ℝ)*x 0 + (4743723849/10000000000 : ℝ)*x 1 + (1885888241/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2117232457/5000000000 : ℝ)^4607 ≤ (33123772266309/100000000000000 : ℝ)^3583 := by
    have hnat : (2117232457 : ℕ)^4607*100000000000000^3583 ≤ 33123772266309^3583*5000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117232457 5000000000 33123772266309 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4743723849/10000000000 : ℝ)^4607 ≤ (38331539120899/100000000000000 : ℝ)^3583 := by
    have hnat : (4743723849 : ℕ)^4607*100000000000000^3583 ≤ 38331539120899^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4743723849 10000000000 38331539120899 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1885888241/5000000000 : ℝ)^4607 ≤ (28544688589361/100000000000000 : ℝ)^3583 := by
    have hnat : (1885888241 : ℕ)^4607*100000000000000^3583 ≤ 28544688589361^3583*5000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1885888241 5000000000 28544688589361 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2117232457/5000000000 : ℝ), (4743723849/10000000000 : ℝ), (1885888241/5000000000 : ℝ)] ![(33123772266309/100000000000000 : ℝ), (38331539120899/100000000000000 : ℝ), (28544688589361/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2117232457/5000000000 : ℝ)|^4607 ≤ (33123772266309/100000000000000 : ℝ)^3583
        have hw : |(2117232457/5000000000 : ℝ)|=(2117232457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4743723849/10000000000 : ℝ)|^4607 ≤ (38331539120899/100000000000000 : ℝ)^3583
        have hw : |(4743723849/10000000000 : ℝ)|=(4743723849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1885888241/5000000000 : ℝ)|^4607 ≤ (28544688589361/100000000000000 : ℝ)^3583
        have hw : |(1885888241/5000000000 : ℝ)|=(1885888241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1555_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41705747/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (24939/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (673/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (8897/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3579/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (24939/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (673/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (24939/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (673/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (24939/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (673/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (24939/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (673/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (24939/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (673/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (24939/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (673/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (673/20000 : ℝ) ^ (4605/1024 : ℝ) ≤ (23754630638653/100000000000000000000 : ℝ) := by
    have hpowers : (673/20000 : ℝ)^4605 ≤ (23754630638653/100000000000000000000 : ℝ)^1024 := by
      have hnat : (673 : ℕ)^4605*100000000000000000000^1024 ≤ 23754630638653^1024*20000^4605 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        673 20000 23754630638653 100000000000000000000 4605 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (673/20000 : ℝ)) (X := (23754630638653/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4605 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (24939/100000 : ℝ) ^ (4605/1024 : ℝ) ≤ (193964662213847681/100000000000000000000 : ℝ) := by
    have hpowers : (24939/100000 : ℝ)^4605 ≤ (193964662213847681/100000000000000000000 : ℝ)^1024 := by
      have hnat : (24939 : ℕ)^4605*100000000000000000000^1024 ≤ 193964662213847681^1024*100000^4605 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24939 100000 193964662213847681 100000000000000000000 4605 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (24939/100000 : ℝ)) (X := (193964662213847681/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4605 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000023754630638653/50000000000000000000 : ℝ) ≤ (10000001056448959/10000000000000000 : ℝ) ^ (4605/1024 : ℝ) := by
    have hpowers : (50000023754630638653/50000000000000000000 : ℝ)^1024 ≤ (10000001056448959/10000000000000000 : ℝ)^4605 := by
      have hnat : (50000023754630638653 : ℕ)^1024*10000000000000000^4605 ≤ 10000001056448959^4605*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000023754630638653 50000000000000000000 10000001056448959 10000000000000000 1024 4605 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000001056448959/10000000000000000 : ℝ)) (X := (50000023754630638653/50000000000000000000 : ℝ)) (by norm_num) 4605 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50096994208422243167/50000000000000000000 : ℝ) ≤ (5002155206098971/5000000000000000 : ℝ) ^ (4605/1024 : ℝ) := by
    have hpowers : (50096994208422243167/50000000000000000000 : ℝ)^1024 ≤ (5002155206098971/5000000000000000 : ℝ)^4605 := by
      have hnat : (50096994208422243167 : ℕ)^1024*5000000000000000^4605 ≤ 5002155206098971^4605*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50096994208422243167 50000000000000000000 5002155206098971 5000000000000000 1024 4605 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002155206098971/5000000000000000 : ℝ)) (X := (50096994208422243167/50000000000000000000 : ℝ)) (by norm_num) 4605 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50193964662213847681/50000000000000000000 : ℝ) ≤ (400344790717877/400000000000000 : ℝ) ^ (4605/1024 : ℝ) := by
    have hpowers : (50193964662213847681/50000000000000000000 : ℝ)^1024 ≤ (400344790717877/400000000000000 : ℝ)^4605 := by
      have hnat : (50193964662213847681 : ℕ)^1024*400000000000000^4605 ≤ 400344790717877^4605*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50193964662213847681 50000000000000000000 400344790717877 400000000000000 1024 4605 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400344790717877/400000000000000 : ℝ)) (X := (50193964662213847681/50000000000000000000 : ℝ)) (by norm_num) 4605 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(23754630638653/100000000000000000000 : ℝ) ≤ ((53927755206909796469/53935000000000000000 : ℝ)+2*(4309355748983/2157400000000000 : ℝ)*(673/20000 : ℝ))^(4605/1024 : ℝ) := by
    rw [show (53927755206909796469/53935000000000000000 : ℝ)+2*(4309355748983/2157400000000000 : ℝ)*(673/20000 : ℝ)=(10000001056448959/10000000000000000 : ℝ) by norm_num, show 1+2*(23754630638653/100000000000000000000 : ℝ)=(50000023754630638653/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(193964662213847681/100000000000000000000 : ℝ)+(23754630638653/100000000000000000000 : ℝ) ≤ ((53927755206909796469/53935000000000000000 : ℝ)+(4309355748983/2157400000000000 : ℝ)*((24939/100000 : ℝ)+(673/20000 : ℝ)))^(4605/1024 : ℝ) := by
    rw [show (53927755206909796469/53935000000000000000 : ℝ)+(4309355748983/2157400000000000 : ℝ)*((24939/100000 : ℝ)+(673/20000 : ℝ))=(5002155206098971/5000000000000000 : ℝ) by norm_num, show 1+(193964662213847681/100000000000000000000 : ℝ)+(23754630638653/100000000000000000000 : ℝ)=(50096994208422243167/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(193964662213847681/100000000000000000000 : ℝ) ≤ ((53927755206909796469/53935000000000000000 : ℝ)+2*(4309355748983/2157400000000000 : ℝ)*(24939/100000 : ℝ))^(4605/1024 : ℝ) := by
    rw [show (53927755206909796469/53935000000000000000 : ℝ)+2*(4309355748983/2157400000000000 : ℝ)*(24939/100000 : ℝ)=(400344790717877/400000000000000 : ℝ) by norm_num, show 1+2*(193964662213847681/100000000000000000000 : ℝ)=(50193964662213847681/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (53927755206909796469/53935000000000000000 : ℝ)*(X 1 0+X 2 0)+(4309355748983/2157400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4605/1024 : ℝ)) (lo := (673/20000 : ℝ)) (hi := (24939/100000 : ℝ)) (c := (53927755206909796469/53935000000000000000 : ℝ)) (alpha := (4309355748983/2157400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (53927755206909796469/53935000000000000000 : ℝ)*(X 0 1+X 2 1)+(4309355748983/2157400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4605/1024 : ℝ)) (lo := (673/20000 : ℝ)) (hi := (24939/100000 : ℝ)) (c := (53927755206909796469/53935000000000000000 : ℝ)) (alpha := (4309355748983/2157400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (53927755206909796469/53935000000000000000 : ℝ)*(X 0 2+X 1 2)+(4309355748983/2157400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4605/1024 : ℝ)) (lo := (673/20000 : ℝ)) (hi := (24939/100000 : ℝ)) (c := (53927755206909796469/53935000000000000000 : ℝ)) (alpha := (4309355748983/2157400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1783586799/10000000000 : ℝ)*X 0 0+(2771761467/5000000000 : ℝ)*X 0 1+(2559256411/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2689498891/5000000000 : ℝ)*X 1 0+(-1003128039/5000000000 : ℝ)*X 1 1+(51185127/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1344749449/2500000000 : ℝ)*X 2 0+(1023702537/2000000000 : ℝ)*X 2 1+(-2006256079/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((423392381/1000000000 : ℝ)*X 0 0+(3761162277/10000000000 : ℝ)*X 0 1+(4754181369/10000000000 : ℝ)*X 0 2+(423392381/1000000000 : ℝ)*X 1 0+(3761162277/10000000000 : ℝ)*X 1 1+(4754181369/10000000000 : ℝ)*X 1 2+(423392381/1000000000 : ℝ)*X 2 0+(3761162277/10000000000 : ℝ)*X 2 1+(4754181369/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-891909041/5000000000 : ℝ)*X 0 0+(2561493899/5000000000 : ℝ)*X 0 1+(2769490239/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5266511127/10000000000 : ℝ)*X 1 0+(-792895293/5000000000 : ℝ)*X 1 1+(110779591/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1053302609/2000000000 : ℝ)*X 2 0+(1107795801/2000000000 : ℝ)*X 2 1+(-1585788661/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2117232457/5000000000 : ℝ)*X 0 0+(4743723849/10000000000 : ℝ)*X 0 1+(1885888241/5000000000 : ℝ)*X 0 2+(2117232457/5000000000 : ℝ)*X 1 0+(4743723849/10000000000 : ℝ)*X 1 1+(1885888241/5000000000 : ℝ)*X 1 2+(2117232457/5000000000 : ℝ)*X 2 0+(4743723849/10000000000 : ℝ)*X 2 1+(1885888241/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (252786138331289637360377607/40250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (33272207/50000000000000 : ℝ)*(base1) + (1026203203/100000000000000 : ℝ)*(base19) + (1032327129/100000000000000 : ℝ)*(base23) + (123144011/100000000000000 : ℝ)*(upper3) + (61874003/50000000000000 : ℝ)*(upper5) + (1679968291695733/100000000000000 : ℝ)*(major0) + (1679968291695733/100000000000000 : ℝ)*(major1) + (1679968291695733/100000000000000 : ℝ)*(major2) + (1176446250445749/50000000000000 : ℝ)*(sp0) + (1176449450252547/50000000000000 : ℝ)*(sp1) + (147056180898823/6250000000000 : ℝ)*(sp2) + (503516572974421/50000000000000 : ℝ)*(sp3) + (7492361213/100000000000000 : ℝ)*(sp4) + (646968641/20000000000000 : ℝ)*(sp7) + (503518223668231/50000000000000 : ℝ)*(f.failure) + (294112490838537/12500000000000 : ℝ)*(f.sum) + (6476508400203/1610000000000000000000000000 : ℝ)*base66 + (295337124860399131/80500000000000000000000000000000 : ℝ)*base67 + (413487514773899131/80500000000000000000000000000000 : ℝ)*base69 + (42912026063899131/80500000000000000000000000000000 : ℝ)*base71 + (468501869453/1610000000000000000000000000 : ℝ)*base74 + (244882268941100869/80500000000000000000000000000000 : ℝ)*base76 + (30820586353899131/80500000000000000000000000000000 : ℝ)*base77 + (237333144046600869/80500000000000000000000000000000 : ℝ)*base80 + (3154048344743/1610000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (8476443/1250000000000000000000 : ℝ)*base90 + (8476443/1250000000000000000000 : ℝ)*base92 + (8476443/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (185642121169551959264746299/26967500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (180689581/25000000000000 : ℝ)*(base19) + (491853451/25000000000000 : ℝ)*(base23) + (1140507/5000000000000 : ℝ)*(lower2) + (19868509/20000000000000 : ℝ)*(upper3) + (95020727/100000000000000 : ℝ)*(lower4) + (323423993/100000000000000 : ℝ)*(upper5) + (34327569358143/2000000000000 : ℝ)*(major0) + (34327569358143/2000000000000 : ℝ)*(major1) + (34327569358143/2000000000000 : ℝ)*(major2) + (2716412521/25000000000000 : ℝ)*(sp2) + (300486828020127/12500000000000 : ℝ)*(sp4) + (600973475350673/25000000000000 : ℝ)*(sp5) + (300485223887141/12500000000000 : ℝ)*(sp6) + (514431041094633/50000000000000 : ℝ)*(sp7) + (514431041094633/50000000000000 : ℝ)*(f.failure) + (300486828020127/12500000000000 : ℝ)*(f.sum) + (20697093106801/10787000000000000000000000000 : ℝ)*base65 + (887012115934282067/107870000000000000000000000000000 : ℝ)*base67 + (1051912957103822067/107870000000000000000000000000000 : ℝ)*base69 + (209419490590937933/107870000000000000000000000000000 : ℝ)*base72 + (6423459530431/10787000000000000000000000000 : ℝ)*base73 + (776811777671582067/107870000000000000000000000000000 : ℝ)*base75 + (320060863935262067/107870000000000000000000000000000 : ℝ)*base77 + (598154549391842067/107870000000000000000000000000000 : ℝ)*base79 + (40506402946029/10787000000000000000000000000 : ℝ)*base81 + (8044149/1250000000000000000000 : ℝ)*base90 + (8044149/1250000000000000000000 : ℝ)*base92 + (8044149/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1555_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41705747/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (24939/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (673/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8897/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3579/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1555_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1555_s2_0 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-901788831/5000000000 : ℝ)*x 0 + (680667639/1250000000 : ℝ)*x 1 + (1300921871/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (901788831/5000000000 : ℝ)^4607 ≤ (11054589752849/100000000000000 : ℝ)^3583 := by
    have hnat : (901788831 : ℕ)^4607*100000000000000^3583 ≤ 11054589752849^3583*5000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901788831 5000000000 11054589752849 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (680667639/1250000000 : ℝ)^4607 ≤ (45770181844907/100000000000000 : ℝ)^3583 := by
    have hnat : (680667639 : ℕ)^4607*100000000000000^3583 ≤ 45770181844907^3583*1250000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      680667639 1250000000 45770181844907 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1300921871/2500000000 : ℝ)^4607 ≤ (10793807096869/25000000000000 : ℝ)^3583 := by
    have hnat : (1300921871 : ℕ)^4607*25000000000000^3583 ≤ 10793807096869^3583*2500000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1300921871 2500000000 10793807096869 25000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-901788831/5000000000 : ℝ), (680667639/1250000000 : ℝ), (1300921871/2500000000 : ℝ)] ![(11054589752849/100000000000000 : ℝ), (45770181844907/100000000000000 : ℝ), (10793807096869/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-901788831/5000000000 : ℝ)|^4607 ≤ (11054589752849/100000000000000 : ℝ)^3583
        have hw : |(-901788831/5000000000 : ℝ)|=(901788831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(680667639/1250000000 : ℝ)|^4607 ≤ (45770181844907/100000000000000 : ℝ)^3583
        have hw : |(680667639/1250000000 : ℝ)|=(680667639/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1300921871/2500000000 : ℝ)|^4607 ≤ (10793807096869/25000000000000 : ℝ)^3583
        have hw : |(1300921871/2500000000 : ℝ)|=(1300921871/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1555_s2_1 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676869383/5000000000 : ℝ)*x 0 + (-963846457/5000000000 : ℝ)*x 1 + (208147493/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676869383/5000000000 : ℝ)^4607 ≤ (44782570438051/100000000000000 : ℝ)^3583 := by
    have hnat : (2676869383 : ℕ)^4607*100000000000000^3583 ≤ 44782570438051^3583*5000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676869383 5000000000 44782570438051 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (963846457/5000000000 : ℝ)^4607 ≤ (12042202860421/100000000000000 : ℝ)^3583 := by
    have hnat : (963846457 : ℕ)^4607*100000000000000^3583 ≤ 12042202860421^3583*5000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      963846457 5000000000 12042202860421 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (208147493/400000000 : ℝ)^4607 ≤ (43175226691217/100000000000000 : ℝ)^3583 := by
    have hnat : (208147493 : ℕ)^4607*100000000000000^3583 ≤ 43175226691217^3583*400000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208147493 400000000 43175226691217 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676869383/5000000000 : ℝ), (-963846457/5000000000 : ℝ), (208147493/400000000 : ℝ)] ![(44782570438051/100000000000000 : ℝ), (12042202860421/100000000000000 : ℝ), (43175226691217/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676869383/5000000000 : ℝ)|^4607 ≤ (44782570438051/100000000000000 : ℝ)^3583
        have hw : |(2676869383/5000000000 : ℝ)|=(2676869383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-963846457/5000000000 : ℝ)|^4607 ≤ (12042202860421/100000000000000 : ℝ)^3583
        have hw : |(-963846457/5000000000 : ℝ)|=(963846457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(208147493/400000000 : ℝ)|^4607 ≤ (43175226691217/100000000000000 : ℝ)^3583
        have hw : |(208147493/400000000 : ℝ)|=(208147493/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1555_s2_2 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676869127/5000000000 : ℝ)*x 0 + (650460969/1250000000 : ℝ)*x 1 + (-1927693033/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676869127/5000000000 : ℝ)^4607 ≤ (44782564931329/100000000000000 : ℝ)^3583 := by
    have hnat : (2676869127 : ℕ)^4607*100000000000000^3583 ≤ 44782564931329^3583*5000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676869127 5000000000 44782564931329 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (650460969/1250000000 : ℝ)^4607 ≤ (21587615623289/50000000000000 : ℝ)^3583 := by
    have hnat : (650460969 : ℕ)^4607*50000000000000^3583 ≤ 21587615623289^3583*1250000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      650460969 1250000000 21587615623289 50000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1927693033/10000000000 : ℝ)^4607 ≤ (12042203816263/100000000000000 : ℝ)^3583 := by
    have hnat : (1927693033 : ℕ)^4607*100000000000000^3583 ≤ 12042203816263^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1927693033 10000000000 12042203816263 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676869127/5000000000 : ℝ), (650460969/1250000000 : ℝ), (-1927693033/10000000000 : ℝ)] ![(44782564931329/100000000000000 : ℝ), (21587615623289/50000000000000 : ℝ), (12042203816263/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676869127/5000000000 : ℝ)|^4607 ≤ (44782564931329/100000000000000 : ℝ)^3583
        have hw : |(2676869127/5000000000 : ℝ)|=(2676869127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(650460969/1250000000 : ℝ)|^4607 ≤ (21587615623289/50000000000000 : ℝ)^3583
        have hw : |(650460969/1250000000 : ℝ)|=(650460969/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1927693033/10000000000 : ℝ)|^4607 ≤ (12042203816263/100000000000000 : ℝ)^3583
        have hw : |(-1927693033/10000000000 : ℝ)|=(1927693033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1555_s2_3 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2124189307/5000000000 : ℝ)*x 0 + (993438573/2500000000 : ℝ)*x 1 + (4538367661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2124189307/5000000000 : ℝ)^4607 ≤ (8315945562063/25000000000000 : ℝ)^3583 := by
    have hnat : (2124189307 : ℕ)^4607*25000000000000^3583 ≤ 8315945562063^3583*5000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124189307 5000000000 8315945562063 25000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (993438573/2500000000 : ℝ)^4607 ≤ (15262478206701/50000000000000 : ℝ)^3583 := by
    have hnat : (993438573 : ℕ)^4607*50000000000000^3583 ≤ 15262478206701^3583*2500000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      993438573 2500000000 15262478206701 50000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4538367661/10000000000 : ℝ)^4607 ≤ (36211261318129/100000000000000 : ℝ)^3583 := by
    have hnat : (4538367661 : ℕ)^4607*100000000000000^3583 ≤ 36211261318129^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4538367661 10000000000 36211261318129 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2124189307/5000000000 : ℝ), (993438573/2500000000 : ℝ), (4538367661/10000000000 : ℝ)] ![(8315945562063/25000000000000 : ℝ), (15262478206701/50000000000000 : ℝ), (36211261318129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2124189307/5000000000 : ℝ)|^4607 ≤ (8315945562063/25000000000000 : ℝ)^3583
        have hw : |(2124189307/5000000000 : ℝ)|=(2124189307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(993438573/2500000000 : ℝ)|^4607 ≤ (15262478206701/50000000000000 : ℝ)^3583
        have hw : |(993438573/2500000000 : ℝ)|=(993438573/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4538367661/10000000000 : ℝ)|^4607 ≤ (36211261318129/100000000000000 : ℝ)^3583
        have hw : |(4538367661/10000000000 : ℝ)|=(4538367661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1555_s2_4 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1803619901/10000000000 : ℝ)*x 0 + (1301285681/2500000000 : ℝ)*x 1 + (2721936857/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1803619901/10000000000 : ℝ)^4607 ≤ (11054922637881/100000000000000 : ℝ)^3583 := by
    have hnat : (1803619901 : ℕ)^4607*100000000000000^3583 ≤ 11054922637881^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1803619901 10000000000 11054922637881 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1301285681/2500000000 : ℝ)^4607 ≤ (21595376965599/50000000000000 : ℝ)^3583 := by
    have hnat : (1301285681 : ℕ)^4607*50000000000000^3583 ≤ 21595376965599^3583*2500000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1301285681 2500000000 21595376965599 50000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2721936857/5000000000 : ℝ)^4607 ≤ (22877161708187/50000000000000 : ℝ)^3583 := by
    have hnat : (2721936857 : ℕ)^4607*50000000000000^3583 ≤ 22877161708187^3583*5000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2721936857 5000000000 22877161708187 50000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1803619901/10000000000 : ℝ), (1301285681/2500000000 : ℝ), (2721936857/5000000000 : ℝ)] ![(11054922637881/100000000000000 : ℝ), (21595376965599/50000000000000 : ℝ), (22877161708187/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1803619901/10000000000 : ℝ)|^4607 ≤ (11054922637881/100000000000000 : ℝ)^3583
        have hw : |(-1803619901/10000000000 : ℝ)|=(1803619901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1301285681/2500000000 : ℝ)|^4607 ≤ (21595376965599/50000000000000 : ℝ)^3583
        have hw : |(1301285681/2500000000 : ℝ)|=(1301285681/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2721936857/5000000000 : ℝ)|^4607 ≤ (22877161708187/50000000000000 : ℝ)^3583
        have hw : |(2721936857/5000000000 : ℝ)|=(2721936857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1555_s2_5 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5289914073/10000000000 : ℝ)*x 0 + (-168750753/1000000000 : ℝ)*x 1 + (5443873523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289914073/10000000000 : ℝ)^4607 ≤ (44097288330017/100000000000000 : ℝ)^3583 := by
    have hnat : (5289914073 : ℕ)^4607*100000000000000^3583 ≤ 44097288330017^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289914073 10000000000 44097288330017 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (168750753/1000000000 : ℝ)^4607 ≤ (1268548787159/12500000000000 : ℝ)^3583 := by
    have hnat : (168750753 : ℕ)^4607*12500000000000^3583 ≤ 1268548787159^3583*1000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168750753 1000000000 1268548787159 12500000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5443873523/10000000000 : ℝ)^4607 ≤ (45754321352283/100000000000000 : ℝ)^3583 := by
    have hnat : (5443873523 : ℕ)^4607*100000000000000^3583 ≤ 45754321352283^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5443873523 10000000000 45754321352283 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289914073/10000000000 : ℝ), (-168750753/1000000000 : ℝ), (5443873523/10000000000 : ℝ)] ![(44097288330017/100000000000000 : ℝ), (1268548787159/12500000000000 : ℝ), (45754321352283/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289914073/10000000000 : ℝ)|^4607 ≤ (44097288330017/100000000000000 : ℝ)^3583
        have hw : |(5289914073/10000000000 : ℝ)|=(5289914073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-168750753/1000000000 : ℝ)|^4607 ≤ (1268548787159/12500000000000 : ℝ)^3583
        have hw : |(-168750753/1000000000 : ℝ)|=(168750753/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5443873523/10000000000 : ℝ)|^4607 ≤ (45754321352283/100000000000000 : ℝ)^3583
        have hw : |(5443873523/10000000000 : ℝ)|=(5443873523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1555_s2_6 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5289913099/10000000000 : ℝ)*x 0 + (1088775133/2000000000 : ℝ)*x 1 + (-52734559/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289913099/10000000000 : ℝ)^4607 ≤ (22048638945091/50000000000000 : ℝ)^3583 := by
    have hnat : (5289913099 : ℕ)^4607*50000000000000^3583 ≤ 22048638945091^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289913099 10000000000 22048638945091 50000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1088775133/2000000000 : ℝ)^4607 ≤ (11438586125091/25000000000000 : ℝ)^3583 := by
    have hnat : (1088775133 : ℕ)^4607*25000000000000^3583 ≤ 11438586125091^3583*2000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088775133 2000000000 11438586125091 25000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (52734559/312500000 : ℝ)^4607 ≤ (1268547200053/12500000000000 : ℝ)^3583 := by
    have hnat : (52734559 : ℕ)^4607*12500000000000^3583 ≤ 1268547200053^3583*312500000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52734559 312500000 1268547200053 12500000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289913099/10000000000 : ℝ), (1088775133/2000000000 : ℝ), (-52734559/312500000 : ℝ)] ![(22048638945091/50000000000000 : ℝ), (11438586125091/25000000000000 : ℝ), (1268547200053/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289913099/10000000000 : ℝ)|^4607 ≤ (22048638945091/50000000000000 : ℝ)^3583
        have hw : |(5289913099/10000000000 : ℝ)|=(5289913099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1088775133/2000000000 : ℝ)|^4607 ≤ (11438586125091/25000000000000 : ℝ)^3583
        have hw : |(1088775133/2000000000 : ℝ)|=(1088775133/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-52734559/312500000 : ℝ)|^4607 ≤ (1268547200053/12500000000000 : ℝ)^3583
        have hw : |(-52734559/312500000 : ℝ)|=(52734559/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1555_s2_7 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4248477849/10000000000 : ℝ)*x 0 + (566871003/1250000000 : ℝ)*x 1 + (795436709/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4248477849/10000000000 : ℝ)^4607 ≤ (6652956259153/20000000000000 : ℝ)^3583 := by
    have hnat : (4248477849 : ℕ)^4607*20000000000000^3583 ≤ 6652956259153^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4248477849 10000000000 6652956259153 20000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (566871003/1250000000 : ℝ)^4607 ≤ (36176387344951/100000000000000 : ℝ)^3583 := by
    have hnat : (566871003 : ℕ)^4607*100000000000000^3583 ≤ 36176387344951^3583*1250000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      566871003 1250000000 36176387344951 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (795436709/2000000000 : ℝ)^4607 ≤ (1909926959493/6250000000000 : ℝ)^3583 := by
    have hnat : (795436709 : ℕ)^4607*6250000000000^3583 ≤ 1909926959493^3583*2000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      795436709 2000000000 1909926959493 6250000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4248477849/10000000000 : ℝ), (566871003/1250000000 : ℝ), (795436709/2000000000 : ℝ)] ![(6652956259153/20000000000000 : ℝ), (36176387344951/100000000000000 : ℝ), (1909926959493/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4248477849/10000000000 : ℝ)|^4607 ≤ (6652956259153/20000000000000 : ℝ)^3583
        have hw : |(4248477849/10000000000 : ℝ)|=(4248477849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(566871003/1250000000 : ℝ)|^4607 ≤ (36176387344951/100000000000000 : ℝ)^3583
        have hw : |(566871003/1250000000 : ℝ)|=(566871003/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(795436709/2000000000 : ℝ)|^4607 ≤ (1909926959493/6250000000000 : ℝ)^3583
        have hw : |(795436709/2000000000 : ℝ)|=(795436709/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1555_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41705747/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3579/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8897/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2683/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15853/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3579/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8897/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3579/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8897/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3579/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8897/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3579/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8897/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3579/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8897/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3579/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8897/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base29 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0, f.sum]
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
  have hpowlo : (8897/100000 : ℝ) ^ (4605/1024 : ℝ) ≤ (1882238036623769/100000000000000000000 : ℝ) := by
    have hpowers : (8897/100000 : ℝ)^4605 ≤ (1882238036623769/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8897 : ℕ)^4605*100000000000000000000^1024 ≤ 1882238036623769^1024*100000^4605 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8897 100000 1882238036623769 100000000000000000000 4605 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8897/100000 : ℝ)) (X := (1882238036623769/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4605 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3579/20000 : ℝ) ^ (4605/1024 : ℝ) ≤ (43599541768736371/100000000000000000000 : ℝ) := by
    have hpowers : (3579/20000 : ℝ)^4605 ≤ (43599541768736371/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3579 : ℕ)^4605*100000000000000000000^1024 ≤ 43599541768736371^1024*20000^4605 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3579 20000 43599541768736371 100000000000000000000 4605 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3579/20000 : ℝ)) (X := (43599541768736371/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4605 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001882238036623769/50000000000000000000 : ℝ) ≤ (1250010463537127/1250000000000000 : ℝ) ^ (4605/1024 : ℝ) := by
    have hpowers : (50001882238036623769/50000000000000000000 : ℝ)^1024 ≤ (1250010463537127/1250000000000000 : ℝ)^4605 := by
      have hnat : (50001882238036623769 : ℕ)^1024*1250000000000000^4605 ≤ 1250010463537127^4605*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001882238036623769 50000000000000000000 1250010463537127 1250000000000000 1024 4605 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250010463537127/1250000000000000 : ℝ)) (X := (50001882238036623769/50000000000000000000 : ℝ)) (by norm_num) 4605 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (5002274088990268007/5000000000000000000 : ℝ) ≤ (2000202237171243/2000000000000000 : ℝ) ^ (4605/1024 : ℝ) := by
    have hpowers : (5002274088990268007/5000000000000000000 : ℝ)^1024 ≤ (2000202237171243/2000000000000000 : ℝ)^4605 := by
      have hnat : (5002274088990268007 : ℕ)^1024*2000000000000000^4605 ≤ 2000202237171243^4605*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002274088990268007 5000000000000000000 2000202237171243 2000000000000000 1024 4605 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000202237171243/2000000000000000 : ℝ)) (X := (5002274088990268007/5000000000000000000 : ℝ)) (by norm_num) 4605 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50043599541768736371/50000000000000000000 : ℝ) ≤ (5000969331707707/5000000000000000 : ℝ) ^ (4605/1024 : ℝ) := by
    have hpowers : (50043599541768736371/50000000000000000000 : ℝ)^1024 ≤ (5000969331707707/5000000000000000 : ℝ)^4605 := by
      have hnat : (50043599541768736371 : ℕ)^1024*5000000000000000^4605 ≤ 5000969331707707^4605*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50043599541768736371 50000000000000000000 5000969331707707 5000000000000000 1024 4605 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000969331707707/5000000000000000 : ℝ)) (X := (50043599541768736371/50000000000000000000 : ℝ)) (by norm_num) 4605 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1882238036623769/100000000000000000000 : ℝ) ≤ ((44982124835784081481/44990000000000000000 : ℝ)+2*(927477559199/899800000000000 : ℝ)*(8897/100000 : ℝ))^(4605/1024 : ℝ) := by
    rw [show (44982124835784081481/44990000000000000000 : ℝ)+2*(927477559199/899800000000000 : ℝ)*(8897/100000 : ℝ)=(1250010463537127/1250000000000000 : ℝ) by norm_num, show 1+2*(1882238036623769/100000000000000000000 : ℝ)=(50001882238036623769/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(43599541768736371/100000000000000000000 : ℝ)+(1882238036623769/100000000000000000000 : ℝ) ≤ ((44982124835784081481/44990000000000000000 : ℝ)+(927477559199/899800000000000 : ℝ)*((3579/20000 : ℝ)+(8897/100000 : ℝ)))^(4605/1024 : ℝ) := by
    rw [show (44982124835784081481/44990000000000000000 : ℝ)+(927477559199/899800000000000 : ℝ)*((3579/20000 : ℝ)+(8897/100000 : ℝ))=(2000202237171243/2000000000000000 : ℝ) by norm_num, show 1+(43599541768736371/100000000000000000000 : ℝ)+(1882238036623769/100000000000000000000 : ℝ)=(5002274088990268007/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(43599541768736371/100000000000000000000 : ℝ) ≤ ((44982124835784081481/44990000000000000000 : ℝ)+2*(927477559199/899800000000000 : ℝ)*(3579/20000 : ℝ))^(4605/1024 : ℝ) := by
    rw [show (44982124835784081481/44990000000000000000 : ℝ)+2*(927477559199/899800000000000 : ℝ)*(3579/20000 : ℝ)=(5000969331707707/5000000000000000 : ℝ) by norm_num, show 1+2*(43599541768736371/100000000000000000000 : ℝ)=(50043599541768736371/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (44982124835784081481/44990000000000000000 : ℝ)*(X 1 0+X 2 0)+(927477559199/899800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4605/1024 : ℝ)) (lo := (8897/100000 : ℝ)) (hi := (3579/20000 : ℝ)) (c := (44982124835784081481/44990000000000000000 : ℝ)) (alpha := (927477559199/899800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (44982124835784081481/44990000000000000000 : ℝ)*(X 0 1+X 2 1)+(927477559199/899800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4605/1024 : ℝ)) (lo := (8897/100000 : ℝ)) (hi := (3579/20000 : ℝ)) (c := (44982124835784081481/44990000000000000000 : ℝ)) (alpha := (927477559199/899800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (44982124835784081481/44990000000000000000 : ℝ)*(X 0 2+X 1 2)+(927477559199/899800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4605/1024 : ℝ)) (lo := (8897/100000 : ℝ)) (hi := (3579/20000 : ℝ)) (c := (44982124835784081481/44990000000000000000 : ℝ)) (alpha := (927477559199/899800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-901788831/5000000000 : ℝ)*X 0 0+(680667639/1250000000 : ℝ)*X 0 1+(1300921871/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676869383/5000000000 : ℝ)*X 1 0+(-963846457/5000000000 : ℝ)*X 1 1+(208147493/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676869127/5000000000 : ℝ)*X 2 0+(650460969/1250000000 : ℝ)*X 2 1+(-1927693033/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2124189307/5000000000 : ℝ)*X 0 0+(993438573/2500000000 : ℝ)*X 0 1+(4538367661/10000000000 : ℝ)*X 0 2+(2124189307/5000000000 : ℝ)*X 1 0+(993438573/2500000000 : ℝ)*X 1 1+(4538367661/10000000000 : ℝ)*X 1 2+(2124189307/5000000000 : ℝ)*X 2 0+(993438573/2500000000 : ℝ)*X 2 1+(4538367661/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1803619901/10000000000 : ℝ)*X 0 0+(1301285681/2500000000 : ℝ)*X 0 1+(2721936857/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5289914073/10000000000 : ℝ)*X 1 0+(-168750753/1000000000 : ℝ)*X 1 1+(5443873523/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5289913099/10000000000 : ℝ)*X 2 0+(1088775133/2000000000 : ℝ)*X 2 1+(-52734559/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4248477849/10000000000 : ℝ)*X 0 0+(566871003/1250000000 : ℝ)*X 0 1+(795436709/2000000000 : ℝ)*X 0 2+(4248477849/10000000000 : ℝ)*X 1 0+(566871003/1250000000 : ℝ)*X 1 1+(795436709/2000000000 : ℝ)*X 1 2+(4248477849/10000000000 : ℝ)*X 2 0+(566871003/1250000000 : ℝ)*X 2 1+(795436709/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2224986235504567348128884211/224950000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1445964099/100000000000000 : ℝ)*(base19) + (886138159/100000000000000 : ℝ)*(base23) + (42786399/25000000000000 : ℝ)*(lower2) + (9178637/3125000000000 : ℝ)*(upper3) + (83304711/100000000000000 : ℝ)*(lower4) + (295466387961741/10000000000000 : ℝ)*(major0) + (295466387961741/10000000000000 : ℝ)*(major1) + (295466387961741/10000000000000 : ℝ)*(major2) + (4138176394326529/100000000000000 : ℝ)*(sp0) + (4138188854904219/100000000000000 : ℝ)*(sp1) + (2069094707365079/50000000000000 : ℝ)*(sp2) + (885564525335547/50000000000000 : ℝ)*(sp3) + (3476635447/25000000000000 : ℝ)*(sp4) + (8077994537/100000000000000 : ℝ)*(sp7) + (177113712866563/10000000000000 : ℝ)*(f.failure) + (2069095150434159/50000000000000 : ℝ)*(f.sum) + (7760001194201/2249500000000000000000000000 : ℝ)*base65 + (1121428617637168421/449900000000000000000000000000000 : ℝ)*base67 + (280800648424268421/449900000000000000000000000000000 : ℝ)*base69 + (2273839690215868421/449900000000000000000000000000000 : ℝ)*base71 + (3067941356629/4499000000000000000000000000 : ℝ)*base73 + (911965130324968421/449900000000000000000000000000000 : ℝ)*base75 + (1601324501153668421/449900000000000000000000000000000 : ℝ)*base77 + (7490431643842768421/449900000000000000000000000000000 : ℝ)*base79 + (7897813411/1098388671875000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (3762439/250000000000000000000 : ℝ)*base90 + (3762439/250000000000000000000 : ℝ)*base92 + (3762439/250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (106198855164856621171969737/22495000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (238228331/100000000000000 : ℝ)*(base8) + (414108567/100000000000000 : ℝ)*(base21) + (45717699/50000000000000 : ℝ)*(base29) + (45433259/100000000000000 : ℝ)*(lower2) + (827963/1000000000000 : ℝ)*(lower4) + (25500727/20000000000000 : ℝ)*(upper5) + (1495406722495251/50000000000000 : ℝ)*(major0) + (29908135364259/1000000000000 : ℝ)*(major1) + (29908135364259/1000000000000 : ℝ)*(major2) + (6877355579/25000000000000 : ℝ)*(sp2) + (418882007890849/10000000000000 : ℝ)*(sp4) + (4188820225701423/100000000000000 : ℝ)*(sp5) + (4188792302170539/100000000000000 : ℝ)*(sp6) + (448201649587091/25000000000000 : ℝ)*(sp7) + (448201649587091/25000000000000 : ℝ)*(f.failure) + (209441015856841/5000000000000 : ℝ)*(f.sum) + (4271588185511/1124750000000000000000000000 : ℝ)*base66 + (416266888826802421/44990000000000000000000000000000 : ℝ)*base68 + (24272368320637579/44990000000000000000000000000000 : ℝ)*base69 + (3588518762520453269/2249500000000000000000000000000000 : ℝ)*base72 + (117141892303541/44990000000000000000000000000 : ℝ)*base74 + (221626950933773421/44990000000000000000000000000000 : ℝ)*base76 + (29761126879352546731/2249500000000000000000000000000000 : ℝ)*base77 + (8492503401833421/44990000000000000000000000000000 : ℝ)*base80 + (52946637014199/44990000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (3288023/625000000000000000000 : ℝ)*base90 + (3288023/625000000000000000000 : ℝ)*base92 + (3288023/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1555_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41705747/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3579/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8897/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2683/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15853/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1555_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1555_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41705747/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2683/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15853/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1555_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1555_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1555_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41705747/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2683/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15853/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1555_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
