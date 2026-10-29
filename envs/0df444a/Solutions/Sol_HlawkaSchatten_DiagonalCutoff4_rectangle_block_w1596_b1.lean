-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1596_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:37:49.604219+00:00
-- url     : https://prove2.me/submissions/27b13057-e3dd-4cec-a94d-23dd81807924

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
theorem support_rectangle_w1596_s3_0 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1739992167/10000000000 : ℝ)*x 0 + (5464633753/10000000000 : ℝ)*x 1 + (647326113/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1739992167/10000000000 : ℝ)^4703 ≤ (1069458364313/10000000000000 : ℝ)^3679 := by
    have hnat : (1739992167 : ℕ)^4703*10000000000000^3679 ≤ 1069458364313^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1739992167 10000000000 1069458364313 10000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5464633753/10000000000 : ℝ)^4703 ≤ (11546616235943/25000000000000 : ℝ)^3679 := by
    have hnat : (5464633753 : ℕ)^4703*25000000000000^3679 ≤ 11546616235943^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5464633753 10000000000 11546616235943 25000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (647326113/1250000000 : ℝ)^4703 ≤ (8623790279139/20000000000000 : ℝ)^3679 := by
    have hnat : (647326113 : ℕ)^4703*20000000000000^3679 ≤ 8623790279139^3679*1250000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647326113 1250000000 8623790279139 20000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1739992167/10000000000 : ℝ), (5464633753/10000000000 : ℝ), (647326113/1250000000 : ℝ)] ![(1069458364313/10000000000000 : ℝ), (11546616235943/25000000000000 : ℝ), (8623790279139/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1739992167/10000000000 : ℝ)|^4703 ≤ (1069458364313/10000000000000 : ℝ)^3679
        have hw : |(-1739992167/10000000000 : ℝ)|=(1739992167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5464633753/10000000000 : ℝ)|^4703 ≤ (11546616235943/25000000000000 : ℝ)^3679
        have hw : |(5464633753/10000000000 : ℝ)|=(5464633753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(647326113/1250000000 : ℝ)|^4703 ≤ (8623790279139/20000000000000 : ℝ)^3679
        have hw : |(647326113/1250000000 : ℝ)|=(647326113/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1596_s3_1 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5355745353/10000000000 : ℝ)*x 0 + (-471900001/2500000000 : ℝ)*x 1 + (647326113/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5355745353/10000000000 : ℝ)^4703 ≤ (22506637097731/50000000000000 : ℝ)^3679 := by
    have hnat : (5355745353 : ℕ)^4703*50000000000000^3679 ≤ 22506637097731^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5355745353 10000000000 22506637097731 50000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (471900001/2500000000 : ℝ)^4703 ≤ (11867774388409/100000000000000 : ℝ)^3679 := by
    have hnat : (471900001 : ℕ)^4703*100000000000000^3679 ≤ 11867774388409^3679*2500000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      471900001 2500000000 11867774388409 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (647326113/1250000000 : ℝ)^4703 ≤ (8623790279139/20000000000000 : ℝ)^3679 := by
    have hnat : (647326113 : ℕ)^4703*20000000000000^3679 ≤ 8623790279139^3679*1250000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647326113 1250000000 8623790279139 20000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5355745353/10000000000 : ℝ), (-471900001/2500000000 : ℝ), (647326113/1250000000 : ℝ)] ![(22506637097731/50000000000000 : ℝ), (11867774388409/100000000000000 : ℝ), (8623790279139/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5355745353/10000000000 : ℝ)|^4703 ≤ (22506637097731/50000000000000 : ℝ)^3679
        have hw : |(5355745353/10000000000 : ℝ)|=(5355745353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-471900001/2500000000 : ℝ)|^4703 ≤ (11867774388409/100000000000000 : ℝ)^3679
        have hw : |(-471900001/2500000000 : ℝ)|=(471900001/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(647326113/1250000000 : ℝ)|^4703 ≤ (8623790279139/20000000000000 : ℝ)^3679
        have hw : |(647326113/1250000000 : ℝ)|=(647326113/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1596_s3_2 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1071149071/2000000000 : ℝ)*x 0 + (647326113/1250000000 : ℝ)*x 1 + (-1887600003/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071149071/2000000000 : ℝ)^4703 ≤ (900265484339/2000000000000 : ℝ)^3679 := by
    have hnat : (1071149071 : ℕ)^4703*2000000000000^3679 ≤ 900265484339^3679*2000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071149071 2000000000 900265484339 2000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (647326113/1250000000 : ℝ)^4703 ≤ (8623790279139/20000000000000 : ℝ)^3679 := by
    have hnat : (647326113 : ℕ)^4703*20000000000000^3679 ≤ 8623790279139^3679*1250000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647326113 1250000000 8623790279139 20000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1887600003/10000000000 : ℝ)^4703 ≤ (2966943595093/25000000000000 : ℝ)^3679 := by
    have hnat : (1887600003 : ℕ)^4703*25000000000000^3679 ≤ 2966943595093^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1887600003 10000000000 2966943595093 25000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071149071/2000000000 : ℝ), (647326113/1250000000 : ℝ), (-1887600003/10000000000 : ℝ)] ![(900265484339/2000000000000 : ℝ), (8623790279139/20000000000000 : ℝ), (2966943595093/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071149071/2000000000 : ℝ)|^4703 ≤ (900265484339/2000000000000 : ℝ)^3679
        have hw : |(1071149071/2000000000 : ℝ)|=(1071149071/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(647326113/1250000000 : ℝ)|^4703 ≤ (8623790279139/20000000000000 : ℝ)^3679
        have hw : |(647326113/1250000000 : ℝ)|=(647326113/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1887600003/10000000000 : ℝ)|^4703 ≤ (2966943595093/25000000000000 : ℝ)^3679
        have hw : |(-1887600003/10000000000 : ℝ)|=(1887600003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1596_s3_3 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (844825621/2000000000 : ℝ)*x 0 + (972562999/2500000000 : ℝ)*x 1 + (2290086713/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (844825621/2000000000 : ℝ)^4703 ≤ (33232732193733/100000000000000 : ℝ)^3679 := by
    have hnat : (844825621 : ℕ)^4703*100000000000000^3679 ≤ 33232732193733^3679*2000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      844825621 2000000000 33232732193733 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (972562999/2500000000 : ℝ)^4703 ≤ (14956279560611/50000000000000 : ℝ)^3679 := by
    have hnat : (972562999 : ℕ)^4703*50000000000000^3679 ≤ 14956279560611^3679*2500000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      972562999 2500000000 14956279560611 50000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2290086713/5000000000 : ℝ)^4703 ≤ (18427354329861/50000000000000 : ℝ)^3679 := by
    have hnat : (2290086713 : ℕ)^4703*50000000000000^3679 ≤ 18427354329861^3679*5000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2290086713 5000000000 18427354329861 50000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(844825621/2000000000 : ℝ), (972562999/2500000000 : ℝ), (2290086713/5000000000 : ℝ)] ![(33232732193733/100000000000000 : ℝ), (14956279560611/50000000000000 : ℝ), (18427354329861/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(844825621/2000000000 : ℝ)|^4703 ≤ (33232732193733/100000000000000 : ℝ)^3679
        have hw : |(844825621/2000000000 : ℝ)|=(844825621/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(972562999/2500000000 : ℝ)|^4703 ≤ (14956279560611/50000000000000 : ℝ)^3679
        have hw : |(972562999/2500000000 : ℝ)|=(972562999/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2290086713/5000000000 : ℝ)|^4703 ≤ (18427354329861/50000000000000 : ℝ)^3679
        have hw : |(2290086713/5000000000 : ℝ)|=(2290086713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1596_s3_4 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-870033029/5000000000 : ℝ)*x 0 + (1295183291/2500000000 : ℝ)*x 1 + (5462487071/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (870033029/5000000000 : ℝ)^4703 ≤ (10695164214867/100000000000000 : ℝ)^3679 := by
    have hnat : (870033029 : ℕ)^4703*100000000000000^3679 ≤ 10695164214867^3679*5000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      870033029 5000000000 10695164214867 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1295183291/2500000000 : ℝ)^4703 ≤ (43141563070379/100000000000000 : ℝ)^3679 := by
    have hnat : (1295183291 : ℕ)^4703*100000000000000^3679 ≤ 43141563070379^3679*2500000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295183291 2500000000 43141563070379 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5462487071/10000000000 : ℝ)^4703 ≤ (46163272697027/100000000000000 : ℝ)^3679 := by
    have hnat : (5462487071 : ℕ)^4703*100000000000000^3679 ≤ 46163272697027^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5462487071 10000000000 46163272697027 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-870033029/5000000000 : ℝ), (1295183291/2500000000 : ℝ), (5462487071/10000000000 : ℝ)] ![(10695164214867/100000000000000 : ℝ), (43141563070379/100000000000000 : ℝ), (46163272697027/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-870033029/5000000000 : ℝ)|^4703 ≤ (10695164214867/100000000000000 : ℝ)^3679
        have hw : |(-870033029/5000000000 : ℝ)|=(870033029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1295183291/2500000000 : ℝ)|^4703 ≤ (43141563070379/100000000000000 : ℝ)^3679
        have hw : |(1295183291/2500000000 : ℝ)|=(1295183291/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5462487071/10000000000 : ℝ)|^4703 ≤ (46163272697027/100000000000000 : ℝ)^3679
        have hw : |(5462487071/10000000000 : ℝ)|=(5462487071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1596_s3_5 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1319996757/2500000000 : ℝ)*x 0 + (-1603721831/10000000000 : ℝ)*x 1 + (1365621769/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1319996757/2500000000 : ℝ)^4703 ≤ (44200934781603/100000000000000 : ℝ)^3679 := by
    have hnat : (1319996757 : ℕ)^4703*100000000000000^3679 ≤ 44200934781603^3679*2500000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319996757 2500000000 44200934781603 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1603721831/10000000000 : ℝ)^4703 ≤ (9635792450513/100000000000000 : ℝ)^3679 := by
    have hnat : (1603721831 : ℕ)^4703*100000000000000^3679 ≤ 9635792450513^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1603721831 10000000000 9635792450513 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1365621769/2500000000 : ℝ)^4703 ≤ (46163272751043/100000000000000 : ℝ)^3679 := by
    have hnat : (1365621769 : ℕ)^4703*100000000000000^3679 ≤ 46163272751043^3679*2500000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1365621769 2500000000 46163272751043 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1319996757/2500000000 : ℝ), (-1603721831/10000000000 : ℝ), (1365621769/2500000000 : ℝ)] ![(44200934781603/100000000000000 : ℝ), (9635792450513/100000000000000 : ℝ), (46163272751043/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1319996757/2500000000 : ℝ)|^4703 ≤ (44200934781603/100000000000000 : ℝ)^3679
        have hw : |(1319996757/2500000000 : ℝ)|=(1319996757/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1603721831/10000000000 : ℝ)|^4703 ≤ (9635792450513/100000000000000 : ℝ)^3679
        have hw : |(-1603721831/10000000000 : ℝ)|=(1603721831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1365621769/2500000000 : ℝ)|^4703 ≤ (46163272751043/100000000000000 : ℝ)^3679
        have hw : |(1365621769/2500000000 : ℝ)|=(1365621769/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1596_s3_6 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5279987033/10000000000 : ℝ)*x 0 + (2731243533/5000000000 : ℝ)*x 1 + (-1603721839/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5279987033/10000000000 : ℝ)^4703 ≤ (44200934835111/100000000000000 : ℝ)^3679 := by
    have hnat : (5279987033 : ℕ)^4703*100000000000000^3679 ≤ 44200934835111^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279987033 10000000000 44200934835111 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2731243533/5000000000 : ℝ)^4703 ≤ (46163272643011/100000000000000 : ℝ)^3679 := by
    have hnat : (2731243533 : ℕ)^4703*100000000000000^3679 ≤ 46163272643011^3679*5000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2731243533 5000000000 46163272643011 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1603721839/10000000000 : ℝ)^4703 ≤ (9635792511959/100000000000000 : ℝ)^3679 := by
    have hnat : (1603721839 : ℕ)^4703*100000000000000^3679 ≤ 9635792511959^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1603721839 10000000000 9635792511959 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5279987033/10000000000 : ℝ), (2731243533/5000000000 : ℝ), (-1603721839/10000000000 : ℝ)] ![(44200934835111/100000000000000 : ℝ), (46163272643011/100000000000000 : ℝ), (9635792511959/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5279987033/10000000000 : ℝ)|^4703 ≤ (44200934835111/100000000000000 : ℝ)^3679
        have hw : |(5279987033/10000000000 : ℝ)|=(5279987033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2731243533/5000000000 : ℝ)|^4703 ≤ (46163272643011/100000000000000 : ℝ)^3679
        have hw : |(2731243533/5000000000 : ℝ)|=(2731243533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1603721839/10000000000 : ℝ)|^4703 ≤ (9635792511959/100000000000000 : ℝ)^3679
        have hw : |(-1603721839/10000000000 : ℝ)|=(1603721839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1596_s3_7 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4224306321/10000000000 : ℝ)*x 0 + (571881187/1250000000 : ℝ)*x 1 + (1947714999/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4224306321/10000000000 : ℝ)^4703 ≤ (16617262273063/50000000000000 : ℝ)^3679 := by
    have hnat : (4224306321 : ℕ)^4703*50000000000000^3679 ≤ 16617262273063^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4224306321 10000000000 16617262273063 50000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (571881187/1250000000 : ℝ)^4703 ≤ (736040218857/2000000000000 : ℝ)^3679 := by
    have hnat : (571881187 : ℕ)^4703*2000000000000^3679 ≤ 736040218857^3679*1250000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      571881187 1250000000 736040218857 2000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1947714999/5000000000 : ℝ)^4703 ≤ (29963464497759/100000000000000 : ℝ)^3679 := by
    have hnat : (1947714999 : ℕ)^4703*100000000000000^3679 ≤ 29963464497759^3679*5000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1947714999 5000000000 29963464497759 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4224306321/10000000000 : ℝ), (571881187/1250000000 : ℝ), (1947714999/5000000000 : ℝ)] ![(16617262273063/50000000000000 : ℝ), (736040218857/2000000000000 : ℝ), (29963464497759/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4224306321/10000000000 : ℝ)|^4703 ≤ (16617262273063/50000000000000 : ℝ)^3679
        have hw : |(4224306321/10000000000 : ℝ)|=(4224306321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(571881187/1250000000 : ℝ)|^4703 ≤ (736040218857/2000000000000 : ℝ)^3679
        have hw : |(571881187/1250000000 : ℝ)|=(571881187/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1947714999/5000000000 : ℝ)|^4703 ≤ (29963464497759/100000000000000 : ℝ)^3679
        have hw : |(1947714999/5000000000 : ℝ)|=(1947714999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1596_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170605157/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16557/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10167/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10323/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8191/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16557/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10167/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16557/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10167/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16557/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10167/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16557/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10167/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16557/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10167/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16557/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10167/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10167/100000 : ℝ) ^ (4699/1024 : ℝ) ≤ (2780607722019347/100000000000000000000 : ℝ) := by
    have hpowers : (10167/100000 : ℝ)^4699 ≤ (2780607722019347/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10167 : ℕ)^4699*100000000000000000000^1024 ≤ 2780607722019347^1024*100000^4699 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10167 100000 2780607722019347 100000000000000000000 4699 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10167/100000 : ℝ)) (X := (2780607722019347/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4699 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16557/100000 : ℝ) ^ (4699/1024 : ℝ) ≤ (3257770814709359/12500000000000000000 : ℝ) := by
    have hpowers : (16557/100000 : ℝ)^4699 ≤ (3257770814709359/12500000000000000000 : ℝ)^1024 := by
      have hnat : (16557 : ℕ)^4699*12500000000000000000^1024 ≤ 3257770814709359^1024*100000^4699 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16557 100000 3257770814709359 12500000000000000000 4699 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16557/100000 : ℝ)) (X := (3257770814709359/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4699 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002780607722019347/50000000000000000000 : ℝ) ≤ (5000060593326013/5000000000000000 : ℝ) ^ (4699/1024 : ℝ) := by
    have hpowers : (50002780607722019347/50000000000000000000 : ℝ)^1024 ≤ (5000060593326013/5000000000000000 : ℝ)^4699 := by
      have hnat : (50002780607722019347 : ℕ)^1024*5000000000000000^4699 ≤ 5000060593326013^4699*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002780607722019347 50000000000000000000 5000060593326013 5000000000000000 1024 4699 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000060593326013/5000000000000000 : ℝ)) (X := (50002780607722019347/50000000000000000000 : ℝ)) (by norm_num) 4699 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100028842774239694219/100000000000000000000 : ℝ) ≤ (10000628467125533/10000000000000000 : ℝ) ^ (4699/1024 : ℝ) := by
    have hpowers : (100028842774239694219/100000000000000000000 : ℝ)^1024 ≤ (10000628467125533/10000000000000000 : ℝ)^4699 := by
      have hnat : (100028842774239694219 : ℕ)^1024*10000000000000000^4699 ≤ 10000628467125533^4699*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100028842774239694219 100000000000000000000 10000628467125533 10000000000000000 1024 4699 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000628467125533/10000000000000000 : ℝ)) (X := (100028842774239694219/100000000000000000000 : ℝ)) (by norm_num) 4699 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6253257770814709359/6250000000000000000 : ℝ) ≤ (31253549211247/31250000000000 : ℝ) ^ (4699/1024 : ℝ) := by
    have hpowers : (6253257770814709359/6250000000000000000 : ℝ)^1024 ≤ (31253549211247/31250000000000 : ℝ)^4699 := by
      have hnat : (6253257770814709359 : ℕ)^1024*31250000000000^4699 ≤ 31253549211247^4699*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253257770814709359 6250000000000000000 31253549211247 31250000000000 1024 4699 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (31253549211247/31250000000000 : ℝ)) (X := (6253257770814709359/6250000000000000000 : ℝ)) (by norm_num) 4699 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2780607722019347/100000000000000000000 : ℝ) ≤ ((3549469963419897489/3550000000000000000 : ℝ)+2*(169093491169/213000000000000 : ℝ)*(10167/100000 : ℝ))^(4699/1024 : ℝ) := by
    rw [show (3549469963419897489/3550000000000000000 : ℝ)+2*(169093491169/213000000000000 : ℝ)*(10167/100000 : ℝ)=(5000060593326013/5000000000000000 : ℝ) by norm_num, show 1+2*(2780607722019347/100000000000000000000 : ℝ)=(50002780607722019347/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3257770814709359/12500000000000000000 : ℝ)+(2780607722019347/100000000000000000000 : ℝ) ≤ ((3549469963419897489/3550000000000000000 : ℝ)+(169093491169/213000000000000 : ℝ)*((16557/100000 : ℝ)+(10167/100000 : ℝ)))^(4699/1024 : ℝ) := by
    rw [show (3549469963419897489/3550000000000000000 : ℝ)+(169093491169/213000000000000 : ℝ)*((16557/100000 : ℝ)+(10167/100000 : ℝ))=(10000628467125533/10000000000000000 : ℝ) by norm_num, show 1+(3257770814709359/12500000000000000000 : ℝ)+(2780607722019347/100000000000000000000 : ℝ)=(100028842774239694219/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3257770814709359/12500000000000000000 : ℝ) ≤ ((3549469963419897489/3550000000000000000 : ℝ)+2*(169093491169/213000000000000 : ℝ)*(16557/100000 : ℝ))^(4699/1024 : ℝ) := by
    rw [show (3549469963419897489/3550000000000000000 : ℝ)+2*(169093491169/213000000000000 : ℝ)*(16557/100000 : ℝ)=(31253549211247/31250000000000 : ℝ) by norm_num, show 1+2*(3257770814709359/12500000000000000000 : ℝ)=(6253257770814709359/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3549469963419897489/3550000000000000000 : ℝ)*(X 1 0+X 2 0)+(169093491169/213000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4699/1024 : ℝ)) (lo := (10167/100000 : ℝ)) (hi := (16557/100000 : ℝ)) (c := (3549469963419897489/3550000000000000000 : ℝ)) (alpha := (169093491169/213000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3549469963419897489/3550000000000000000 : ℝ)*(X 0 1+X 2 1)+(169093491169/213000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4699/1024 : ℝ)) (lo := (10167/100000 : ℝ)) (hi := (16557/100000 : ℝ)) (c := (3549469963419897489/3550000000000000000 : ℝ)) (alpha := (169093491169/213000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3549469963419897489/3550000000000000000 : ℝ)*(X 0 2+X 1 2)+(169093491169/213000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4699/1024 : ℝ)) (lo := (10167/100000 : ℝ)) (hi := (16557/100000 : ℝ)) (c := (3549469963419897489/3550000000000000000 : ℝ)) (alpha := (169093491169/213000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1739992167/10000000000 : ℝ)*X 0 0+(5464633753/10000000000 : ℝ)*X 0 1+(647326113/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5355745353/10000000000 : ℝ)*X 1 0+(-471900001/2500000000 : ℝ)*X 1 1+(647326113/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1071149071/2000000000 : ℝ)*X 2 0+(647326113/1250000000 : ℝ)*X 2 1+(-1887600003/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((844825621/2000000000 : ℝ)*X 0 0+(972562999/2500000000 : ℝ)*X 0 1+(2290086713/5000000000 : ℝ)*X 0 2+(844825621/2000000000 : ℝ)*X 1 0+(972562999/2500000000 : ℝ)*X 1 1+(2290086713/5000000000 : ℝ)*X 1 2+(844825621/2000000000 : ℝ)*X 2 0+(972562999/2500000000 : ℝ)*X 2 1+(2290086713/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-870033029/5000000000 : ℝ)*X 0 0+(1295183291/2500000000 : ℝ)*X 0 1+(5462487071/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1319996757/2500000000 : ℝ)*X 1 0+(-1603721831/10000000000 : ℝ)*X 1 1+(1365621769/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5279987033/10000000000 : ℝ)*X 2 0+(2731243533/5000000000 : ℝ)*X 2 1+(-1603721839/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4224306321/10000000000 : ℝ)*X 0 0+(571881187/1250000000 : ℝ)*X 0 1+(1947714999/5000000000 : ℝ)*X 0 2+(4224306321/10000000000 : ℝ)*X 1 0+(571881187/1250000000 : ℝ)*X 1 1+(1947714999/5000000000 : ℝ)*X 1 2+(4224306321/10000000000 : ℝ)*X 2 0+(571881187/1250000000 : ℝ)*X 2 1+(1947714999/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (73498076793883683182508747/8875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1389566921/100000000000000 : ℝ)*(base19) + (325063951/25000000000000 : ℝ)*(base23) + (48532007/100000000000000 : ℝ)*(lower2) + (102910729/50000000000000 : ℝ)*(upper3) + (140345771/100000000000000 : ℝ)*(upper5) + (247284376857841/10000000000000 : ℝ)*(major0) + (247284376857841/10000000000000 : ℝ)*(major1) + (247284376857841/10000000000000 : ℝ)*(major2) + (1748108310079427/50000000000000 : ℝ)*(sp0) + (3496231580672881/100000000000000 : ℝ)*(sp1) + (1748115834991999/50000000000000 : ℝ)*(sp2) + (362361735104011/25000000000000 : ℝ)*(sp3) + (16350080949/100000000000000 : ℝ)*(sp4) + (1837612963/25000000000000 : ℝ)*(sp7) + (181181786358487/12500000000000 : ℝ)*(f.failure) + (1748116485119901/50000000000000 : ℝ)*(f.sum) + (1380551369749/1065000000000000000000000000 : ℝ)*base65 + (1427904789396966253/106500000000000000000000000000000 : ℝ)*base68 + (1232654859083466253/106500000000000000000000000000000 : ℝ)*base70 + (1057312797938466253/106500000000000000000000000000000 : ℝ)*base72 + (4272416913851/1065000000000000000000000000 : ℝ)*base74 + (373025828828033747/106500000000000000000000000000000 : ℝ)*base75 + (331404250068966253/106500000000000000000000000000000 : ℝ)*base78 + (492965411007966253/106500000000000000000000000000000 : ℝ)*base80 + (5343329957861/1065000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (7917459/1250000000000000000000 : ℝ)*base89 + (7917459/1250000000000000000000 : ℝ)*base91 + (7917459/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (298671050306288501371/71000000000000000000000000 : ℝ) := by norm_num
    linear_combination (132859503/20000000000000 : ℝ)*(base19) + (358394737/50000000000000 : ℝ)*(base23) + (90737127/100000000000000 : ℝ)*(upper3) + (22437127/100000000000000 : ℝ)*(lower4) + (87509813/100000000000000 : ℝ)*(upper5) + (50206078585337/2000000000000 : ℝ)*(major0) + (50206078585337/2000000000000 : ℝ)*(major1) + (50206078585337/2000000000000 : ℝ)*(major2) + (7484313573/100000000000000 : ℝ)*(sp1) + (3973416141/50000000000000 : ℝ)*(sp2) + (3549196200976727/100000000000000 : ℝ)*(sp4) + (3549188052365639/100000000000000 : ℝ)*(sp5) + (3549187537354971/100000000000000 : ℝ)*(sp6) + (294282303467163/20000000000000 : ℝ)*(sp7) + (294282303467163/20000000000000 : ℝ)*(f.failure) + (3549196200976727/100000000000000 : ℝ)*(f.sum) + (174156322829/53250000000000000000000000 : ℝ)*base65 + (65268573385193621/21300000000000000000000000000000 : ℝ)*base68 + (20542704260106379/21300000000000000000000000000000 : ℝ)*base69 + (174547694054406379/21300000000000000000000000000000 : ℝ)*base71 + (35548019027/106500000000000000000000000 : ℝ)*base74 + (297262645140593621/21300000000000000000000000000000 : ℝ)*base76 + (96565540024806379/21300000000000000000000000000000 : ℝ)*base77 + (200248159826993621/21300000000000000000000000000000 : ℝ)*base80 + (255059604919/106500000000000000000000000 : ℝ)*base81 + (12040409/2000000000000000000000 : ℝ)*base90 + (12040409/2000000000000000000000 : ℝ)*base92 + (12040409/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1596_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170605157/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16557/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10167/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10323/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8191/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1596_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1596_s4_0 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1740155341/10000000000 : ℝ)*x 0 + (85372343/156250000 : ℝ)*x 1 + (258965217/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1740155341/10000000000 : ℝ)^4703 ≤ (10695865732817/100000000000000 : ℝ)^3679 := by
    have hnat : (1740155341 : ℕ)^4703*100000000000000^3679 ≤ 10695865732817^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1740155341 10000000000 10695865732817 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (85372343/156250000 : ℝ)^4703 ≤ (23088890285017/50000000000000 : ℝ)^3679 := by
    have hnat : (85372343 : ℕ)^4703*50000000000000^3679 ≤ 23088890285017^3679*156250000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85372343 156250000 23088890285017 50000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (258965217/500000000 : ℝ)^4703 ≤ (8625270735289/20000000000000 : ℝ)^3679 := by
    have hnat : (258965217 : ℕ)^4703*20000000000000^3679 ≤ 8625270735289^3679*500000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258965217 500000000 8625270735289 20000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1740155341/10000000000 : ℝ), (85372343/156250000 : ℝ), (258965217/500000000 : ℝ)] ![(10695865732817/100000000000000 : ℝ), (23088890285017/50000000000000 : ℝ), (8625270735289/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1740155341/10000000000 : ℝ)|^4703 ≤ (10695865732817/100000000000000 : ℝ)^3679
        have hw : |(-1740155341/10000000000 : ℝ)|=(1740155341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(85372343/156250000 : ℝ)|^4703 ≤ (23088890285017/50000000000000 : ℝ)^3679
        have hw : |(85372343/156250000 : ℝ)|=(85372343/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(258965217/500000000 : ℝ)|^4703 ≤ (8625270735289/20000000000000 : ℝ)^3679
        have hw : |(258965217/500000000 : ℝ)|=(258965217/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1596_s4_1 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334720689/625000000 : ℝ)*x 0 + (-1886965527/10000000000 : ℝ)*x 1 + (2589652153/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334720689/625000000 : ℝ)^4703 ≤ (4501097145817/10000000000000 : ℝ)^3679 := by
    have hnat : (334720689 : ℕ)^4703*10000000000000^3679 ≤ 4501097145817^3679*625000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334720689 625000000 4501097145817 10000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1886965527/10000000000 : ℝ)^4703 ≤ (2965668802907/25000000000000 : ℝ)^3679 := by
    have hnat : (1886965527 : ℕ)^4703*25000000000000^3679 ≤ 2965668802907^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1886965527 10000000000 2965668802907 25000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2589652153/5000000000 : ℝ)^4703 ≤ (43126353314539/100000000000000 : ℝ)^3679 := by
    have hnat : (2589652153 : ℕ)^4703*100000000000000^3679 ≤ 43126353314539^3679*5000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2589652153 5000000000 43126353314539 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334720689/625000000 : ℝ), (-1886965527/10000000000 : ℝ), (2589652153/5000000000 : ℝ)] ![(4501097145817/10000000000000 : ℝ), (2965668802907/25000000000000 : ℝ), (43126353314539/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334720689/625000000 : ℝ)|^4703 ≤ (4501097145817/10000000000000 : ℝ)^3679
        have hw : |(334720689/625000000 : ℝ)|=(334720689/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1886965527/10000000000 : ℝ)|^4703 ≤ (2965668802907/25000000000000 : ℝ)^3679
        have hw : |(-1886965527/10000000000 : ℝ)|=(1886965527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2589652153/5000000000 : ℝ)|^4703 ≤ (43126353314539/100000000000000 : ℝ)^3679
        have hw : |(2589652153/5000000000 : ℝ)|=(2589652153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1596_s4_2 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334720689/625000000 : ℝ)*x 0 + (5179304291/10000000000 : ℝ)*x 1 + (-1886965547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334720689/625000000 : ℝ)^4703 ≤ (4501097145817/10000000000000 : ℝ)^3679 := by
    have hnat : (334720689 : ℕ)^4703*10000000000000^3679 ≤ 4501097145817^3679*625000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334720689 625000000 4501097145817 10000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5179304291/10000000000 : ℝ)^4703 ≤ (345010825239/800000000000 : ℝ)^3679 := by
    have hnat : (5179304291 : ℕ)^4703*800000000000^3679 ≤ 345010825239^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179304291 10000000000 345010825239 800000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1886965547/10000000000 : ℝ)^4703 ≤ (11862675372357/100000000000000 : ℝ)^3679 := by
    have hnat : (1886965547 : ℕ)^4703*100000000000000^3679 ≤ 11862675372357^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1886965547 10000000000 11862675372357 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334720689/625000000 : ℝ), (5179304291/10000000000 : ℝ), (-1886965547/10000000000 : ℝ)] ![(4501097145817/10000000000000 : ℝ), (345010825239/800000000000 : ℝ), (11862675372357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334720689/625000000 : ℝ)|^4703 ≤ (4501097145817/10000000000000 : ℝ)^3679
        have hw : |(334720689/625000000 : ℝ)|=(334720689/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5179304291/10000000000 : ℝ)|^4703 ≤ (345010825239/800000000000 : ℝ)^3679
        have hw : |(5179304291/10000000000 : ℝ)|=(5179304291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1886965547/10000000000 : ℝ)|^4703 ≤ (11862675372357/100000000000000 : ℝ)^3679
        have hw : |(-1886965547/10000000000 : ℝ)|=(1886965547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1596_s4_3 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4224232631/10000000000 : ℝ)*x 0 + (3892048821/10000000000 : ℝ)*x 1 + (4578354017/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4224232631/10000000000 : ℝ)^4703 ≤ (1038555732161/3125000000000 : ℝ)^3679 := by
    have hnat : (4224232631 : ℕ)^4703*3125000000000^3679 ≤ 1038555732161^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4224232631 10000000000 1038555732161 3125000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3892048821/10000000000 : ℝ)^4703 ≤ (29930221724737/100000000000000 : ℝ)^3679 := by
    have hnat : (3892048821 : ℕ)^4703*100000000000000^3679 ≤ 29930221724737^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3892048821 10000000000 29930221724737 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4578354017/10000000000 : ℝ)^4703 ≤ (18417997417069/50000000000000 : ℝ)^3679 := by
    have hnat : (4578354017 : ℕ)^4703*50000000000000^3679 ≤ 18417997417069^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4578354017 10000000000 18417997417069 50000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4224232631/10000000000 : ℝ), (3892048821/10000000000 : ℝ), (4578354017/10000000000 : ℝ)] ![(1038555732161/3125000000000 : ℝ), (29930221724737/100000000000000 : ℝ), (18417997417069/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4224232631/10000000000 : ℝ)|^4703 ≤ (1038555732161/3125000000000 : ℝ)^3679
        have hw : |(4224232631/10000000000 : ℝ)|=(4224232631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3892048821/10000000000 : ℝ)|^4703 ≤ (29930221724737/100000000000000 : ℝ)^3679
        have hw : |(3892048821/10000000000 : ℝ)|=(3892048821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4578354017/10000000000 : ℝ)|^4703 ≤ (18417997417069/50000000000000 : ℝ)^3679
        have hw : |(4578354017/10000000000 : ℝ)|=(4578354017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1596_s4_4 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-870114019/5000000000 : ℝ)*x 0 + (1036281281/2000000000 : ℝ)*x 1 + (1365426461/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (870114019/5000000000 : ℝ)^4703 ≤ (5348218468993/50000000000000 : ℝ)^3679 := by
    have hnat : (870114019 : ℕ)^4703*50000000000000^3679 ≤ 5348218468993^3679*5000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      870114019 5000000000 5348218468993 50000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036281281/2000000000 : ℝ)^4703 ≤ (43148729919357/100000000000000 : ℝ)^3679 := by
    have hnat : (1036281281 : ℕ)^4703*100000000000000^3679 ≤ 43148729919357^3679*2000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036281281 2000000000 43148729919357 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1365426461/2500000000 : ℝ)^4703 ≤ (46154833134033/100000000000000 : ℝ)^3679 := by
    have hnat : (1365426461 : ℕ)^4703*100000000000000^3679 ≤ 46154833134033^3679*2500000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1365426461 2500000000 46154833134033 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-870114019/5000000000 : ℝ), (1036281281/2000000000 : ℝ), (1365426461/2500000000 : ℝ)] ![(5348218468993/50000000000000 : ℝ), (43148729919357/100000000000000 : ℝ), (46154833134033/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-870114019/5000000000 : ℝ)|^4703 ≤ (5348218468993/50000000000000 : ℝ)^3679
        have hw : |(-870114019/5000000000 : ℝ)|=(870114019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1036281281/2000000000 : ℝ)|^4703 ≤ (43148729919357/100000000000000 : ℝ)^3679
        have hw : |(1036281281/2000000000 : ℝ)|=(1036281281/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1365426461/2500000000 : ℝ)|^4703 ≤ (46154833134033/100000000000000 : ℝ)^3679
        have hw : |(1365426461/2500000000 : ℝ)|=(1365426461/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1596_s4_5 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2640085573/5000000000 : ℝ)*x 0 + (-80228201/500000000 : ℝ)*x 1 + (5461705859/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2640085573/5000000000 : ℝ)^4703 ≤ (11050726281503/25000000000000 : ℝ)^3679 := by
    have hnat : (2640085573 : ℕ)^4703*25000000000000^3679 ≤ 11050726281503^3679*5000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640085573 5000000000 11050726281503 25000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (80228201/500000000 : ℝ)^4703 ≤ (964226156573/10000000000000 : ℝ)^3679 := by
    have hnat : (80228201 : ℕ)^4703*10000000000000^3679 ≤ 964226156573^3679*500000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80228201 500000000 964226156573 10000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5461705859/10000000000 : ℝ)^4703 ≤ (23077416648037/50000000000000 : ℝ)^3679 := by
    have hnat : (5461705859 : ℕ)^4703*50000000000000^3679 ≤ 23077416648037^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5461705859 10000000000 23077416648037 50000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2640085573/5000000000 : ℝ), (-80228201/500000000 : ℝ), (5461705859/10000000000 : ℝ)] ![(11050726281503/25000000000000 : ℝ), (964226156573/10000000000000 : ℝ), (23077416648037/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2640085573/5000000000 : ℝ)|^4703 ≤ (11050726281503/25000000000000 : ℝ)^3679
        have hw : |(2640085573/5000000000 : ℝ)|=(2640085573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-80228201/500000000 : ℝ)|^4703 ≤ (964226156573/10000000000000 : ℝ)^3679
        have hw : |(-80228201/500000000 : ℝ)|=(80228201/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5461705859/10000000000 : ℝ)|^4703 ≤ (23077416648037/50000000000000 : ℝ)^3679
        have hw : |(5461705859/10000000000 : ℝ)|=(5461705859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1596_s4_6 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5280171169/10000000000 : ℝ)*x 0 + (1092341169/2000000000 : ℝ)*x 1 + (-200570501/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5280171169/10000000000 : ℝ)^4703 ≤ (11050726343037/25000000000000 : ℝ)^3679 := by
    have hnat : (5280171169 : ℕ)^4703*25000000000000^3679 ≤ 11050726343037^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280171169 10000000000 11050726343037 25000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1092341169/2000000000 : ℝ)^4703 ≤ (11538708286209/25000000000000 : ℝ)^3679 := by
    have hnat : (1092341169 : ℕ)^4703*25000000000000^3679 ≤ 11538708286209^3679*2000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092341169 2000000000 11538708286209 25000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (200570501/1250000000 : ℝ)^4703 ≤ (2410565368387/25000000000000 : ℝ)^3679 := by
    have hnat : (200570501 : ℕ)^4703*25000000000000^3679 ≤ 2410565368387^3679*1250000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200570501 1250000000 2410565368387 25000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5280171169/10000000000 : ℝ), (1092341169/2000000000 : ℝ), (-200570501/1250000000 : ℝ)] ![(11050726343037/25000000000000 : ℝ), (11538708286209/25000000000000 : ℝ), (2410565368387/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5280171169/10000000000 : ℝ)|^4703 ≤ (11050726343037/25000000000000 : ℝ)^3679
        have hw : |(5280171169/10000000000 : ℝ)|=(5280171169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1092341169/2000000000 : ℝ)|^4703 ≤ (11538708286209/25000000000000 : ℝ)^3679
        have hw : |(1092341169/2000000000 : ℝ)|=(1092341169/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-200570501/1250000000 : ℝ)|^4703 ≤ (2410565368387/25000000000000 : ℝ)^3679
        have hw : |(-200570501/1250000000 : ℝ)|=(200570501/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1596_s4_7 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4224408069/10000000000 : ℝ)*x 0 + (228664181/500000000 : ℝ)*x 1 + (3897172433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4224408069/10000000000 : ℝ)^4703 ≤ (16617773927329/50000000000000 : ℝ)^3679 := by
    have hnat : (4224408069 : ℕ)^4703*50000000000000^3679 ≤ 16617773927329^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4224408069 10000000000 16617773927329 50000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (228664181/500000000 : ℝ)^4703 ≤ (36783853369099/100000000000000 : ℝ)^3679 := by
    have hnat : (228664181 : ℕ)^4703*100000000000000^3679 ≤ 36783853369099^3679*500000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      228664181 500000000 36783853369099 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3897172433/10000000000 : ℝ)^4703 ≤ (5996119752167/20000000000000 : ℝ)^3679 := by
    have hnat : (3897172433 : ℕ)^4703*20000000000000^3679 ≤ 5996119752167^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3897172433 10000000000 5996119752167 20000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4224408069/10000000000 : ℝ), (228664181/500000000 : ℝ), (3897172433/10000000000 : ℝ)] ![(16617773927329/50000000000000 : ℝ), (36783853369099/100000000000000 : ℝ), (5996119752167/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4224408069/10000000000 : ℝ)|^4703 ≤ (16617773927329/50000000000000 : ℝ)^3679
        have hw : |(4224408069/10000000000 : ℝ)|=(4224408069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(228664181/500000000 : ℝ)|^4703 ≤ (36783853369099/100000000000000 : ℝ)^3679
        have hw : |(228664181/500000000 : ℝ)|=(228664181/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3897172433/10000000000 : ℝ)|^4703 ≤ (5996119752167/20000000000000 : ℝ)^3679
        have hw : |(3897172433/10000000000 : ℝ)|=(3897172433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1596_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170605157/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8191/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10323/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5169/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8183/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8191/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10323/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8191/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10323/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8191/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10323/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8191/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10323/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8191/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10323/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8191/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10323/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10323/100000 : ℝ) ^ (4699/1024 : ℝ) ≤ (745463507061783/25000000000000000000 : ℝ) := by
    have hpowers : (10323/100000 : ℝ)^4699 ≤ (745463507061783/25000000000000000000 : ℝ)^1024 := by
      have hnat : (10323 : ℕ)^4699*25000000000000000000^1024 ≤ 745463507061783^1024*100000^4699 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10323 100000 745463507061783 25000000000000000000 4699 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10323/100000 : ℝ)) (X := (745463507061783/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4699 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8191/50000 : ℝ) ^ (4699/1024 : ℝ) ≤ (1241092495089903/5000000000000000000 : ℝ) := by
    have hpowers : (8191/50000 : ℝ)^4699 ≤ (1241092495089903/5000000000000000000 : ℝ)^1024 := by
      have hnat : (8191 : ℕ)^4699*5000000000000000000^1024 ≤ 1241092495089903^1024*50000^4699 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8191 50000 1241092495089903 5000000000000000000 4699 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8191/50000 : ℝ)) (X := (1241092495089903/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4699 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500745463507061783/12500000000000000000 : ℝ) ≤ (2500032489330923/2500000000000000 : ℝ) ^ (4699/1024 : ℝ) := by
    have hpowers : (12500745463507061783/12500000000000000000 : ℝ)^1024 ≤ (2500032489330923/2500000000000000 : ℝ)^4699 := by
      have hnat : (12500745463507061783 : ℕ)^1024*2500000000000000^4699 ≤ 2500032489330923^4699*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500745463507061783 12500000000000000000 2500032489330923 2500000000000000 1024 4699 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500032489330923/2500000000000000 : ℝ)) (X := (12500745463507061783/12500000000000000000 : ℝ)) (by norm_num) 4699 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12503475462991255649/12500000000000000000 : ℝ) ≤ (625037864303391/625000000000000 : ℝ) ^ (4699/1024 : ℝ) := by
    have hpowers : (12503475462991255649/12500000000000000000 : ℝ)^1024 ≤ (625037864303391/625000000000000 : ℝ)^4699 := by
      have hnat : (12503475462991255649 : ℕ)^1024*625000000000000^4699 ≤ 625037864303391^4699*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503475462991255649 12500000000000000000 625037864303391 625000000000000 1024 4699 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625037864303391/625000000000000 : ℝ)) (X := (12503475462991255649/12500000000000000000 : ℝ)) (by norm_num) 4699 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501241092495089903/2500000000000000000 : ℝ) ≤ (500054085019241/500000000000000 : ℝ) ^ (4699/1024 : ℝ) := by
    have hpowers : (2501241092495089903/2500000000000000000 : ℝ)^1024 ≤ (500054085019241/500000000000000 : ℝ)^4699 := by
      have hnat : (2501241092495089903 : ℕ)^1024*500000000000000^4699 ≤ 500054085019241^4699*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501241092495089903 2500000000000000000 500054085019241 500000000000000 1024 4699 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500054085019241/500000000000000 : ℝ)) (X := (2501241092495089903/2500000000000000000 : ℝ)) (by norm_num) 4699 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(745463507061783/25000000000000000000 : ℝ) ≤ ((15145240641951056371/15147500000000000000 : ℝ)+2*(118967882641/151475000000000 : ℝ)*(10323/100000 : ℝ))^(4699/1024 : ℝ) := by
    rw [show (15145240641951056371/15147500000000000000 : ℝ)+2*(118967882641/151475000000000 : ℝ)*(10323/100000 : ℝ)=(2500032489330923/2500000000000000 : ℝ) by norm_num, show 1+2*(745463507061783/25000000000000000000 : ℝ)=(12500745463507061783/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1241092495089903/5000000000000000000 : ℝ)+(745463507061783/25000000000000000000 : ℝ) ≤ ((15145240641951056371/15147500000000000000 : ℝ)+(118967882641/151475000000000 : ℝ)*((8191/50000 : ℝ)+(10323/100000 : ℝ)))^(4699/1024 : ℝ) := by
    rw [show (15145240641951056371/15147500000000000000 : ℝ)+(118967882641/151475000000000 : ℝ)*((8191/50000 : ℝ)+(10323/100000 : ℝ))=(625037864303391/625000000000000 : ℝ) by norm_num, show 1+(1241092495089903/5000000000000000000 : ℝ)+(745463507061783/25000000000000000000 : ℝ)=(12503475462991255649/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1241092495089903/5000000000000000000 : ℝ) ≤ ((15145240641951056371/15147500000000000000 : ℝ)+2*(118967882641/151475000000000 : ℝ)*(8191/50000 : ℝ))^(4699/1024 : ℝ) := by
    rw [show (15145240641951056371/15147500000000000000 : ℝ)+2*(118967882641/151475000000000 : ℝ)*(8191/50000 : ℝ)=(500054085019241/500000000000000 : ℝ) by norm_num, show 1+2*(1241092495089903/5000000000000000000 : ℝ)=(2501241092495089903/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (15145240641951056371/15147500000000000000 : ℝ)*(X 1 0+X 2 0)+(118967882641/151475000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4699/1024 : ℝ)) (lo := (10323/100000 : ℝ)) (hi := (8191/50000 : ℝ)) (c := (15145240641951056371/15147500000000000000 : ℝ)) (alpha := (118967882641/151475000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (15145240641951056371/15147500000000000000 : ℝ)*(X 0 1+X 2 1)+(118967882641/151475000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4699/1024 : ℝ)) (lo := (10323/100000 : ℝ)) (hi := (8191/50000 : ℝ)) (c := (15145240641951056371/15147500000000000000 : ℝ)) (alpha := (118967882641/151475000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (15145240641951056371/15147500000000000000 : ℝ)*(X 0 2+X 1 2)+(118967882641/151475000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4699/1024 : ℝ)) (lo := (10323/100000 : ℝ)) (hi := (8191/50000 : ℝ)) (c := (15145240641951056371/15147500000000000000 : ℝ)) (alpha := (118967882641/151475000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1740155341/10000000000 : ℝ)*X 0 0+(85372343/156250000 : ℝ)*X 0 1+(258965217/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334720689/625000000 : ℝ)*X 1 0+(-1886965527/10000000000 : ℝ)*X 1 1+(2589652153/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((334720689/625000000 : ℝ)*X 2 0+(5179304291/10000000000 : ℝ)*X 2 1+(-1886965547/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4224232631/10000000000 : ℝ)*X 0 0+(3892048821/10000000000 : ℝ)*X 0 1+(4578354017/10000000000 : ℝ)*X 0 2+(4224232631/10000000000 : ℝ)*X 1 0+(3892048821/10000000000 : ℝ)*X 1 1+(4578354017/10000000000 : ℝ)*X 1 2+(4224232631/10000000000 : ℝ)*X 2 0+(3892048821/10000000000 : ℝ)*X 2 1+(4578354017/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-870114019/5000000000 : ℝ)*X 0 0+(1036281281/2000000000 : ℝ)*X 0 1+(1365426461/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2640085573/5000000000 : ℝ)*X 1 0+(-80228201/500000000 : ℝ)*X 1 1+(5461705859/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5280171169/10000000000 : ℝ)*X 2 0+(1092341169/2000000000 : ℝ)*X 2 1+(-200570501/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4224408069/10000000000 : ℝ)*X 0 0+(228664181/500000000 : ℝ)*X 0 1+(3897172433/10000000000 : ℝ)*X 0 2+(4224408069/10000000000 : ℝ)*X 1 0+(228664181/500000000 : ℝ)*X 1 1+(3897172433/10000000000 : ℝ)*X 1 2+(4224408069/10000000000 : ℝ)*X 2 0+(228664181/500000000 : ℝ)*X 2 1+(3897172433/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (238535718957167855454837/30295000000000000000000000000 : ℝ) := by norm_num
    linear_combination (274037449/20000000000000 : ℝ)*(base19) + (1300663931/100000000000000 : ℝ)*(base23) + (37233427/100000000000000 : ℝ)*(lower2) + (100912521/50000000000000 : ℝ)*(upper3) + (135940227/100000000000000 : ℝ)*(upper5) + (1242936522631537/50000000000000 : ℝ)*(major0) + (1242936522631537/50000000000000 : ℝ)*(major1) + (1242936522631537/50000000000000 : ℝ)*(major2) + (3514638623220501/100000000000000 : ℝ)*(sp0) + (27458227130729/781250000000 : ℝ)*(sp1) + (3514653142256627/100000000000000 : ℝ)*(sp2) + (728542079125913/50000000000000 : ℝ)*(sp3) + (1977462507/12500000000000 : ℝ)*(sp4) + (1806723729/25000000000000 : ℝ)*(sp7) + (728545692573371/50000000000000 : ℝ)*(f.failure) + (1757327221460279/50000000000000 : ℝ)*(f.sum) + (42833873708641/30295000000000000000000000000 : ℝ)*base65 + (1808219024348322227/757375000000000000000000000000000 : ℝ)*base67 + (212233302975322227/757375000000000000000000000000000 : ℝ)*base69 + (2180576089001677773/757375000000000000000000000000000 : ℝ)*base72 + (27973650364673/15147500000000000000000000000 : ℝ)*base73 + (6087463932948822227/757375000000000000000000000000000 : ℝ)*base75 + (2463701465131677773/757375000000000000000000000000000 : ℝ)*base78 + (5949407860361052773/757375000000000000000000000000000 : ℝ)*base80 + (32101119618059/30295000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (6525753/5000000000000000000000 : ℝ)*base90 + (6525753/5000000000000000000000 : ℝ)*base92 + (6525753/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4604672887937118372322928121/378687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (37600899/2000000000000 : ℝ)*(base19) + (2064863217/100000000000000 : ℝ)*(base23) + (601509621/100000000000000 : ℝ)*(lower1) + (257061467/100000000000000 : ℝ)*(upper3) + (74578953/100000000000000 : ℝ)*(lower4) + (250096073/100000000000000 : ℝ)*(upper5) + (2523314348541417/100000000000000 : ℝ)*(major0) + (2523314348541417/100000000000000 : ℝ)*(major1) + (2523314348541417/100000000000000 : ℝ)*(major2) + (1964282027/100000000000000 : ℝ)*(sp2) + (71351814667939/2000000000000 : ℝ)*(sp4) + (445948606669/12500000000 : ℝ)*(sp5) + (1783793352125853/50000000000000 : ℝ)*(sp6) + (369759389591813/25000000000000 : ℝ)*(sp7) + (369759389591813/25000000000000 : ℝ)*(f.failure) + (71351814667939/2000000000000 : ℝ)*(f.sum) + (29921156851057/7573750000000000000000000000 : ℝ)*base65 + (12246660410177582293/1514750000000000000000000000000000 : ℝ)*base68 + (13383272652336082293/1514750000000000000000000000000000 : ℝ)*base70 + (10640679135298082293/1514750000000000000000000000000000 : ℝ)*base72 + (41881779660403/7573750000000000000000000000 : ℝ)*base74 + (43567400812713917707/1514750000000000000000000000000000 : ℝ)*base75 + (6767430003237582293/1514750000000000000000000000000000 : ℝ)*base78 + (6262238637163332293/1514750000000000000000000000000000 : ℝ)*base80 + (273646579197017/30295000000000000000000000000 : ℝ)*base82 + (2220359/2500000000000000000000 : ℝ)*base90 + (2220359/2500000000000000000000 : ℝ)*base92 + (2220359/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1596_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170605157/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8191/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10323/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5169/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8183/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1596_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1596_s5_0 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-870084541/5000000000 : ℝ)*x 0 + (5463757589/10000000000 : ℝ)*x 1 + (1035873529/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (870084541/5000000000 : ℝ)^4703 ≤ (267399342501/2500000000000 : ℝ)^3679 := by
    have hnat : (870084541 : ℕ)^4703*2500000000000^3679 ≤ 267399342501^3679*5000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      870084541 5000000000 267399342501 2500000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5463757589/10000000000 : ℝ)^4703 ≤ (4617699876793/10000000000000 : ℝ)^3679 := by
    have hnat : (5463757589 : ℕ)^4703*10000000000000^3679 ≤ 4617699876793^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5463757589 10000000000 4617699876793 10000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1035873529/2000000000 : ℝ)^4703 ≤ (21563513757031/50000000000000 : ℝ)^3679 := by
    have hnat : (1035873529 : ℕ)^4703*50000000000000^3679 ≤ 21563513757031^3679*2000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035873529 2000000000 21563513757031 50000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-870084541/5000000000 : ℝ), (5463757589/10000000000 : ℝ), (1035873529/2000000000 : ℝ)] ![(267399342501/2500000000000 : ℝ), (4617699876793/10000000000000 : ℝ), (21563513757031/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-870084541/5000000000 : ℝ)|^4703 ≤ (267399342501/2500000000000 : ℝ)^3679
        have hw : |(-870084541/5000000000 : ℝ)|=(870084541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5463757589/10000000000 : ℝ)|^4703 ≤ (4617699876793/10000000000000 : ℝ)^3679
        have hw : |(5463757589/10000000000 : ℝ)|=(5463757589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1035873529/2000000000 : ℝ)|^4703 ≤ (21563513757031/50000000000000 : ℝ)^3679
        have hw : |(1035873529/2000000000 : ℝ)|=(1035873529/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1596_s5_1 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677756183/5000000000 : ℝ)*x 0 + (-1886906997/10000000000 : ℝ)*x 1 + (5179367329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677756183/5000000000 : ℝ)^4703 ≤ (22505385499503/50000000000000 : ℝ)^3679 := by
    have hnat : (2677756183 : ℕ)^4703*50000000000000^3679 ≤ 22505385499503^3679*5000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677756183 5000000000 22505385499503 50000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1886906997/10000000000 : ℝ)^4703 ≤ (5931102420327/50000000000000 : ℝ)^3679 := by
    have hnat : (1886906997 : ℕ)^4703*50000000000000^3679 ≤ 5931102420327^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1886906997 10000000000 5931102420327 50000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5179367329/10000000000 : ℝ)^4703 ≤ (5390878018807/12500000000000 : ℝ)^3679 := by
    have hnat : (5179367329 : ℕ)^4703*12500000000000^3679 ≤ 5390878018807^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179367329 10000000000 5390878018807 12500000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677756183/5000000000 : ℝ), (-1886906997/10000000000 : ℝ), (5179367329/10000000000 : ℝ)] ![(22505385499503/50000000000000 : ℝ), (5931102420327/50000000000000 : ℝ), (5390878018807/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677756183/5000000000 : ℝ)|^4703 ≤ (22505385499503/50000000000000 : ℝ)^3679
        have hw : |(2677756183/5000000000 : ℝ)|=(2677756183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1886906997/10000000000 : ℝ)|^4703 ≤ (5931102420327/50000000000000 : ℝ)^3679
        have hw : |(-1886906997/10000000000 : ℝ)|=(1886906997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5179367329/10000000000 : ℝ)|^4703 ≤ (5390878018807/12500000000000 : ℝ)^3679
        have hw : |(5179367329/10000000000 : ℝ)|=(5179367329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1596_s5_2 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267775609/500000000 : ℝ)*x 0 + (207174697/400000000 : ℝ)*x 1 + (-943453559/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267775609/500000000 : ℝ)^4703 ≤ (45010769000647/100000000000000 : ℝ)^3679 := by
    have hnat : (267775609 : ℕ)^4703*100000000000000^3679 ≤ 45010769000647^3679*500000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267775609 500000000 45010769000647 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (207174697/400000000 : ℝ)^4703 ≤ (43127025172311/100000000000000 : ℝ)^3679 := by
    have hnat : (207174697 : ℕ)^4703*100000000000000^3679 ≤ 43127025172311^3679*400000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207174697 400000000 43127025172311 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (943453559/5000000000 : ℝ)^4703 ≤ (2372441162611/20000000000000 : ℝ)^3679 := by
    have hnat : (943453559 : ℕ)^4703*20000000000000^3679 ≤ 2372441162611^3679*5000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      943453559 5000000000 2372441162611 20000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267775609/500000000 : ℝ), (207174697/400000000 : ℝ), (-943453559/5000000000 : ℝ)] ![(45010769000647/100000000000000 : ℝ), (43127025172311/100000000000000 : ℝ), (2372441162611/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267775609/500000000 : ℝ)|^4703 ≤ (45010769000647/100000000000000 : ℝ)^3679
        have hw : |(267775609/500000000 : ℝ)|=(267775609/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(207174697/400000000 : ℝ)|^4703 ≤ (43127025172311/100000000000000 : ℝ)^3679
        have hw : |(207174697/400000000 : ℝ)|=(207174697/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-943453559/5000000000 : ℝ)|^4703 ≤ (2372441162611/20000000000000 : ℝ)^3679
        have hw : |(-943453559/5000000000 : ℝ)|=(943453559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1596_s5_3 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4224241683/10000000000 : ℝ)*x 0 + (3892211781/10000000000 : ℝ)*x 1 + (2289094703/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4224241683/10000000000 : ℝ)^4703 ≤ (16616937233483/50000000000000 : ℝ)^3679 := by
    have hnat : (4224241683 : ℕ)^4703*50000000000000^3679 ≤ 16616937233483^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4224241683 10000000000 16616937233483 50000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3892211781/10000000000 : ℝ)^4703 ≤ (29931823716919/100000000000000 : ℝ)^3679 := by
    have hnat : (3892211781 : ℕ)^4703*100000000000000^3679 ≤ 29931823716919^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3892211781 10000000000 29931823716919 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2289094703/5000000000 : ℝ)^4703 ≤ (7366860360633/20000000000000 : ℝ)^3679 := by
    have hnat : (2289094703 : ℕ)^4703*20000000000000^3679 ≤ 7366860360633^3679*5000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2289094703 5000000000 7366860360633 20000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4224241683/10000000000 : ℝ), (3892211781/10000000000 : ℝ), (2289094703/5000000000 : ℝ)] ![(16616937233483/50000000000000 : ℝ), (29931823716919/100000000000000 : ℝ), (7366860360633/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4224241683/10000000000 : ℝ)|^4703 ≤ (16616937233483/50000000000000 : ℝ)^3679
        have hw : |(4224241683/10000000000 : ℝ)|=(4224241683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3892211781/10000000000 : ℝ)|^4703 ≤ (29931823716919/100000000000000 : ℝ)^3679
        have hw : |(3892211781/10000000000 : ℝ)|=(3892211781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2289094703/5000000000 : ℝ)|^4703 ≤ (7366860360633/20000000000000 : ℝ)^3679
        have hw : |(2289094703/5000000000 : ℝ)|=(2289094703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1596_s5_4 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-435060503/2500000000 : ℝ)*x 0 + (5181467823/10000000000 : ℝ)*x 1 + (1365408789/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (435060503/2500000000 : ℝ)^4703 ≤ (10696546737239/100000000000000 : ℝ)^3679 := by
    have hnat : (435060503 : ℕ)^4703*100000000000000^3679 ≤ 10696546737239^3679*2500000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435060503 2500000000 10696546737239 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5181467823/10000000000 : ℝ)^4703 ≤ (2157469187249/5000000000000 : ℝ)^3679 := by
    have hnat : (5181467823 : ℕ)^4703*5000000000000^3679 ≤ 2157469187249^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181467823 10000000000 2157469187249 5000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1365408789/2500000000 : ℝ)^4703 ≤ (23077034755533/50000000000000 : ℝ)^3679 := by
    have hnat : (1365408789 : ℕ)^4703*50000000000000^3679 ≤ 23077034755533^3679*2500000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1365408789 2500000000 23077034755533 50000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-435060503/2500000000 : ℝ), (5181467823/10000000000 : ℝ), (1365408789/2500000000 : ℝ)] ![(10696546737239/100000000000000 : ℝ), (2157469187249/5000000000000 : ℝ), (23077034755533/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-435060503/2500000000 : ℝ)|^4703 ≤ (10696546737239/100000000000000 : ℝ)^3679
        have hw : |(-435060503/2500000000 : ℝ)|=(435060503/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5181467823/10000000000 : ℝ)|^4703 ≤ (2157469187249/5000000000000 : ℝ)^3679
        have hw : |(5181467823/10000000000 : ℝ)|=(5181467823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1365408789/2500000000 : ℝ)|^4703 ≤ (23077034755533/50000000000000 : ℝ)^3679
        have hw : |(1365408789/2500000000 : ℝ)|=(1365408789/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1596_s5_5 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5280188087/10000000000 : ℝ)*x 0 + (-1604639643/10000000000 : ℝ)*x 1 + (54616353/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5280188087/10000000000 : ℝ)^4703 ≤ (22101543210801/50000000000000 : ℝ)^3679 := by
    have hnat : (5280188087 : ℕ)^4703*50000000000000^3679 ≤ 22101543210801^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280188087 10000000000 22101543210801 50000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1604639643/10000000000 : ℝ)^4703 ≤ (2410710623931/25000000000000 : ℝ)^3679 := by
    have hnat : (1604639643 : ℕ)^4703*25000000000000^3679 ≤ 2410710623931^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1604639643 10000000000 2410710623931 25000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (54616353/100000000 : ℝ)^4703 ≤ (1442314720833/3125000000000 : ℝ)^3679 := by
    have hnat : (54616353 : ℕ)^4703*3125000000000^3679 ≤ 1442314720833^3679*100000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54616353 100000000 1442314720833 3125000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5280188087/10000000000 : ℝ), (-1604639643/10000000000 : ℝ), (54616353/100000000 : ℝ)] ![(22101543210801/50000000000000 : ℝ), (2410710623931/25000000000000 : ℝ), (1442314720833/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5280188087/10000000000 : ℝ)|^4703 ≤ (22101543210801/50000000000000 : ℝ)^3679
        have hw : |(5280188087/10000000000 : ℝ)|=(5280188087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1604639643/10000000000 : ℝ)|^4703 ≤ (2410710623931/25000000000000 : ℝ)^3679
        have hw : |(-1604639643/10000000000 : ℝ)|=(1604639643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(54616353/100000000 : ℝ)|^4703 ≤ (1442314720833/3125000000000 : ℝ)^3679
        have hw : |(54616353/100000000 : ℝ)|=(54616353/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1596_s5_6 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5280188203/10000000000 : ℝ)*x 0 + (2730817733/5000000000 : ℝ)*x 1 + (-100289953/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5280188203/10000000000 : ℝ)^4703 ≤ (44203087662987/100000000000000 : ℝ)^3679 := by
    have hnat : (5280188203 : ℕ)^4703*100000000000000^3679 ≤ 44203087662987^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280188203 10000000000 44203087662987 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2730817733/5000000000 : ℝ)^4703 ≤ (9230814571981/20000000000000 : ℝ)^3679 := by
    have hnat : (2730817733 : ℕ)^4703*20000000000000^3679 ≤ 9230814571981^3679*5000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2730817733 5000000000 9230814571981 20000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (100289953/625000000 : ℝ)^4703 ≤ (1928567892269/20000000000000 : ℝ)^3679 := by
    have hnat : (100289953 : ℕ)^4703*20000000000000^3679 ≤ 1928567892269^3679*625000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100289953 625000000 1928567892269 20000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5280188203/10000000000 : ℝ), (2730817733/5000000000 : ℝ), (-100289953/625000000 : ℝ)] ![(44203087662987/100000000000000 : ℝ), (9230814571981/20000000000000 : ℝ), (1928567892269/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5280188203/10000000000 : ℝ)|^4703 ≤ (44203087662987/100000000000000 : ℝ)^3679
        have hw : |(5280188203/10000000000 : ℝ)|=(5280188203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2730817733/5000000000 : ℝ)|^4703 ≤ (9230814571981/20000000000000 : ℝ)^3679
        have hw : |(2730817733/5000000000 : ℝ)|=(2730817733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-100289953/625000000 : ℝ)|^4703 ≤ (1928567892269/20000000000000 : ℝ)^3679
        have hw : |(-100289953/625000000 : ℝ)|=(100289953/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1596_s5_7 (p : ℝ) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4224417287/10000000000 : ℝ)*x 0 + (4573123857/10000000000 : ℝ)*x 1 + (1948665021/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4224417287/10000000000 : ℝ)^4703 ≤ (207722753519/625000000000 : ℝ)^3679 := by
    have hnat : (4224417287 : ℕ)^4703*625000000000^3679 ≤ 207722753519^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4224417287 10000000000 207722753519 625000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4573123857/10000000000 : ℝ)^4703 ≤ (36782210706483/100000000000000 : ℝ)^3679 := by
    have hnat : (4573123857 : ℕ)^4703*100000000000000^3679 ≤ 36782210706483^3679*10000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4573123857 10000000000 36782210706483 100000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1948665021/5000000000 : ℝ)^4703 ≤ (2998214871669/10000000000000 : ℝ)^3679 := by
    have hnat : (1948665021 : ℕ)^4703*10000000000000^3679 ≤ 2998214871669^3679*5000000000^4703 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1948665021 5000000000 2998214871669 10000000000000 4703 3679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4703/1024 : ℝ)) 4703 3679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4224417287/10000000000 : ℝ), (4573123857/10000000000 : ℝ), (1948665021/5000000000 : ℝ)] ![(207722753519/625000000000 : ℝ), (36782210706483/100000000000000 : ℝ), (2998214871669/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4224417287/10000000000 : ℝ)|^4703 ≤ (207722753519/625000000000 : ℝ)^3679
        have hw : |(4224417287/10000000000 : ℝ)|=(4224417287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4573123857/10000000000 : ℝ)|^4703 ≤ (36782210706483/100000000000000 : ℝ)^3679
        have hw : |(4573123857/10000000000 : ℝ)|=(4573123857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1948665021/5000000000 : ℝ)|^4703 ≤ (2998214871669/10000000000000 : ℝ)^3679
        have hw : |(1948665021/5000000000 : ℝ)|=(1948665021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1596_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170605157/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8183/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5169/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10339/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4091/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8183/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5169/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8183/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5169/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8183/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5169/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8183/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5169/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8183/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5169/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8183/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5169/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5169/50000 : ℝ) ^ (4699/1024 : ℝ) ≤ (1500894360249779/50000000000000000000 : ℝ) := by
    have hpowers : (5169/50000 : ℝ)^4699 ≤ (1500894360249779/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5169 : ℕ)^4699*50000000000000000000^1024 ≤ 1500894360249779^1024*50000^4699 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5169 50000 1500894360249779 50000000000000000000 4699 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5169/50000 : ℝ)) (X := (1500894360249779/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4699 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8183/50000 : ℝ) ^ (4699/1024 : ℝ) ≤ (24710796586340143/100000000000000000000 : ℝ) := by
    have hpowers : (8183/50000 : ℝ)^4699 ≤ (24710796586340143/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8183 : ℕ)^4699*100000000000000000000^1024 ≤ 24710796586340143^1024*50000^4699 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8183 50000 24710796586340143 100000000000000000000 4699 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8183/50000 : ℝ)) (X := (24710796586340143/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4699 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25001500894360249779/25000000000000000000 : ℝ) ≤ (625008176631969/625000000000000 : ℝ) ^ (4699/1024 : ℝ) := by
    have hpowers : (25001500894360249779/25000000000000000000 : ℝ)^1024 ≤ (625008176631969/625000000000000 : ℝ)^4699 := by
      have hnat : (25001500894360249779 : ℕ)^1024*625000000000000^4699 ≤ 625008176631969^4699*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001500894360249779 25000000000000000000 625008176631969 625000000000000 1024 4699 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625008176631969/625000000000000 : ℝ)) (X := (25001500894360249779/25000000000000000000 : ℝ)) (by norm_num) 4699 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100027712585306839701/100000000000000000000 : ℝ) ≤ (312518870113749/312500000000000 : ℝ) ^ (4699/1024 : ℝ) := by
    have hpowers : (100027712585306839701/100000000000000000000 : ℝ)^1024 ≤ (312518870113749/312500000000000 : ℝ)^4699 := by
      have hnat : (100027712585306839701 : ℕ)^1024*312500000000000^4699 ≤ 312518870113749^4699*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100027712585306839701 100000000000000000000 312518870113749 312500000000000 1024 4699 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312518870113749/312500000000000 : ℝ)) (X := (100027712585306839701/100000000000000000000 : ℝ)) (by norm_num) 4699 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50024710796586340143/50000000000000000000 : ℝ) ≤ (625067303823027/625000000000000 : ℝ) ^ (4699/1024 : ℝ) := by
    have hpowers : (50024710796586340143/50000000000000000000 : ℝ)^1024 ≤ (625067303823027/625000000000000 : ℝ)^4699 := by
      have hnat : (50024710796586340143 : ℕ)^1024*625000000000000^4699 ≤ 625067303823027^4699*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024710796586340143 50000000000000000000 625067303823027 625000000000000 1024 4699 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625067303823027/625000000000000 : ℝ)) (X := (50024710796586340143/50000000000000000000 : ℝ)) (by norm_num) 4699 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1500894360249779/50000000000000000000 : ℝ) ≤ ((470867253979543941/470937500000000000 : ℝ)+2*(29563595529/37675000000000 : ℝ)*(5169/50000 : ℝ))^(4699/1024 : ℝ) := by
    rw [show (470867253979543941/470937500000000000 : ℝ)+2*(29563595529/37675000000000 : ℝ)*(5169/50000 : ℝ)=(625008176631969/625000000000000 : ℝ) by norm_num, show 1+2*(1500894360249779/50000000000000000000 : ℝ)=(25001500894360249779/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(24710796586340143/100000000000000000000 : ℝ)+(1500894360249779/50000000000000000000 : ℝ) ≤ ((470867253979543941/470937500000000000 : ℝ)+(29563595529/37675000000000 : ℝ)*((8183/50000 : ℝ)+(5169/50000 : ℝ)))^(4699/1024 : ℝ) := by
    rw [show (470867253979543941/470937500000000000 : ℝ)+(29563595529/37675000000000 : ℝ)*((8183/50000 : ℝ)+(5169/50000 : ℝ))=(312518870113749/312500000000000 : ℝ) by norm_num, show 1+(24710796586340143/100000000000000000000 : ℝ)+(1500894360249779/50000000000000000000 : ℝ)=(100027712585306839701/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(24710796586340143/100000000000000000000 : ℝ) ≤ ((470867253979543941/470937500000000000 : ℝ)+2*(29563595529/37675000000000 : ℝ)*(8183/50000 : ℝ))^(4699/1024 : ℝ) := by
    rw [show (470867253979543941/470937500000000000 : ℝ)+2*(29563595529/37675000000000 : ℝ)*(8183/50000 : ℝ)=(625067303823027/625000000000000 : ℝ) by norm_num, show 1+2*(24710796586340143/100000000000000000000 : ℝ)=(50024710796586340143/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (470867253979543941/470937500000000000 : ℝ)*(X 1 0+X 2 0)+(29563595529/37675000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4699/1024 : ℝ)) (lo := (5169/50000 : ℝ)) (hi := (8183/50000 : ℝ)) (c := (470867253979543941/470937500000000000 : ℝ)) (alpha := (29563595529/37675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (470867253979543941/470937500000000000 : ℝ)*(X 0 1+X 2 1)+(29563595529/37675000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4699/1024 : ℝ)) (lo := (5169/50000 : ℝ)) (hi := (8183/50000 : ℝ)) (c := (470867253979543941/470937500000000000 : ℝ)) (alpha := (29563595529/37675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (470867253979543941/470937500000000000 : ℝ)*(X 0 2+X 1 2)+(29563595529/37675000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4699/1024 : ℝ)) (lo := (5169/50000 : ℝ)) (hi := (8183/50000 : ℝ)) (c := (470867253979543941/470937500000000000 : ℝ)) (alpha := (29563595529/37675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-870084541/5000000000 : ℝ)*X 0 0+(5463757589/10000000000 : ℝ)*X 0 1+(1035873529/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2677756183/5000000000 : ℝ)*X 1 0+(-1886906997/10000000000 : ℝ)*X 1 1+(5179367329/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((267775609/500000000 : ℝ)*X 2 0+(207174697/400000000 : ℝ)*X 2 1+(-943453559/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4224241683/10000000000 : ℝ)*X 0 0+(3892211781/10000000000 : ℝ)*X 0 1+(2289094703/5000000000 : ℝ)*X 0 2+(4224241683/10000000000 : ℝ)*X 1 0+(3892211781/10000000000 : ℝ)*X 1 1+(2289094703/5000000000 : ℝ)*X 1 2+(4224241683/10000000000 : ℝ)*X 2 0+(3892211781/10000000000 : ℝ)*X 2 1+(2289094703/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-435060503/2500000000 : ℝ)*X 0 0+(5181467823/10000000000 : ℝ)*X 0 1+(1365408789/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5280188087/10000000000 : ℝ)*X 1 0+(-1604639643/10000000000 : ℝ)*X 1 1+(54616353/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5280188203/10000000000 : ℝ)*X 2 0+(2730817733/5000000000 : ℝ)*X 2 1+(-100289953/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4224417287/10000000000 : ℝ)*X 0 0+(4573123857/10000000000 : ℝ)*X 0 1+(1948665021/5000000000 : ℝ)*X 0 2+(4224417287/10000000000 : ℝ)*X 1 0+(4573123857/10000000000 : ℝ)*X 1 1+(1948665021/5000000000 : ℝ)*X 1 2+(4224417287/10000000000 : ℝ)*X 2 0+(4573123857/10000000000 : ℝ)*X 2 1+(1948665021/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1596_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2998494842268061782598023/267578125000000000000000000000 : ℝ) := by norm_num
    linear_combination (433130957/20000000000000 : ℝ)*(base19) + (5089797/250000000000 : ℝ)*(base23) + (2038109/50000000000000 : ℝ)*(lower2) + (263651131/100000000000000 : ℝ)*(upper3) + (2337409/1562500000000 : ℝ)*(upper5) + (2487071520335413/100000000000000 : ℝ)*(major0) + (2487071520335413/100000000000000 : ℝ)*(major1) + (2487071520335413/100000000000000 : ℝ)*(major2) + (703265017757347/20000000000000 : ℝ)*(sp0) + (1758173315832617/50000000000000 : ℝ)*(sp1) + (175817338070061/5000000000000 : ℝ)*(sp2) + (1457783260951997/100000000000000 : ℝ)*(sp3) + (4741706657/20000000000000 : ℝ)*(sp4) + (10608863681/100000000000000 : ℝ)*(sp7) + (728896934907839/50000000000000 : ℝ)*(f.failure) + (175817439866001/5000000000000 : ℝ)*(f.sum) + (203990126103/42812500000000000000000000 : ℝ)*base65 + (21766299735445897/4281250000000000000000000000000 : ℝ)*base68 + (21480826734664647/4281250000000000000000000000000 : ℝ)*base70 + (12628221144991603/4281250000000000000000000000000 : ℝ)*base71 + (658215026483/171250000000000000000000000 : ℝ)*base74 + (3192968384258397/4281250000000000000000000000000 : ℝ)*base76 + (13837349083366603/4281250000000000000000000000000 : ℝ)*base77 + (10260389113883397/4281250000000000000000000000000 : ℝ)*base80 + (395773108203/171250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (3125723/5000000000000000000000 : ℝ)*base89 + (3125723/5000000000000000000000 : ℝ)*base91 + (3125723/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (149928590902715109103076817/23546875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1044581133/100000000000000 : ℝ)*(base19) + (696632017/50000000000000 : ℝ)*(base23) + (62011707/25000000000000 : ℝ)*(lower1) + (17723411/25000000000000 : ℝ)*(upper2) + (138709929/50000000000000 : ℝ)*(upper3) + (11552659/10000000000000 : ℝ)*(upper5) + (631127731174433/25000000000000 : ℝ)*(major0) + (631127731174433/25000000000000 : ℝ)*(major1) + (631127731174433/25000000000000 : ℝ)*(major2) + (2383498063/25000000000000 : ℝ)*(sp2) + (446160338395651/12500000000000 : ℝ)*(sp4) + (142771266503363/4000000000000 : ℝ)*(sp5) + (3569271779908923/100000000000000 : ℝ)*(sp6) + (23120920781077/1562500000000 : ℝ)*(sp7) + (23120920781077/1562500000000 : ℝ)*(f.failure) + (446160338395651/12500000000000 : ℝ)*(f.sum) + (54782127093/470937500000000000000000000 : ℝ)*base66 + (120210686454035453/11773437500000000000000000000000 : ℝ)*base67 + (109213472347722953/11773437500000000000000000000000 : ℝ)*base69 + (38093545421086531/23546875000000000000000000000000 : ℝ)*base71 + (8725649924073/7535000000000000000000000000 : ℝ)*base74 + (225476225915191703/11773437500000000000000000000000 : ℝ)*base75 + (254730677336274031/23546875000000000000000000000000 : ℝ)*base77 + (39379666214369289/5886718750000000000000000000000 : ℝ)*base79 + (3010007561981/941875000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (2035911/156250000000000000000 : ℝ)*base90 + (2035911/156250000000000000000 : ℝ)*base92 + (2035911/156250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1596_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170605157/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8183/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5169/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10339/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4091/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1596_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1596_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170605157/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16557/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10167/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10339/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4091/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1596_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1596_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1596_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4699/1024 : ℝ) ≤ p) (hpb : p ≤ (4703/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170605157/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16557/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10167/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10339/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4091/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1596_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
