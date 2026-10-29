-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1410_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:48:43.018532+00:00
-- url     : https://prove2.me/submissions/b97bdec5-980e-4c4b-af25-2488eb86d98b

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
theorem support_rectangle_w1410_s0_0 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1769621283/10000000000 : ℝ)*x 0 + (746007647/1250000000 : ℝ)*x 1 + (4826872007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1769621283/10000000000 : ℝ)^2185 ≤ (1041606884681/10000000000000 : ℝ)^1673 := by
    have hnat : (1769621283 : ℕ)^2185*10000000000000^1673 ≤ 1041606884681^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1769621283 10000000000 1041606884681 10000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (746007647/1250000000 : ℝ)^2185 ≤ (50960060894981/100000000000000 : ℝ)^1673 := by
    have hnat : (746007647 : ℕ)^2185*100000000000000^1673 ≤ 50960060894981^1673*1250000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      746007647 1250000000 50960060894981 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4826872007/10000000000 : ℝ)^2185 ≤ (38623870239643/100000000000000 : ℝ)^1673 := by
    have hnat : (4826872007 : ℕ)^2185*100000000000000^1673 ≤ 38623870239643^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4826872007 10000000000 38623870239643 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1769621283/10000000000 : ℝ), (746007647/1250000000 : ℝ), (4826872007/10000000000 : ℝ)] ![(1041606884681/10000000000000 : ℝ), (50960060894981/100000000000000 : ℝ), (38623870239643/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1769621283/10000000000 : ℝ)|^2185 ≤ (1041606884681/10000000000000 : ℝ)^1673
        have hw : |(-1769621283/10000000000 : ℝ)|=(1769621283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(746007647/1250000000 : ℝ)|^2185 ≤ (50960060894981/100000000000000 : ℝ)^1673
        have hw : |(746007647/1250000000 : ℝ)|=(746007647/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4826872007/10000000000 : ℝ)|^2185 ≤ (38623870239643/100000000000000 : ℝ)^1673
        have hw : |(4826872007/10000000000 : ℝ)|=(4826872007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_s0_1 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5494214517/10000000000 : ℝ)*x 0 + (-96605159/400000000 : ℝ)*x 1 + (4826872313/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5494214517/10000000000 : ℝ)^2185 ≤ (45741151188083/100000000000000 : ℝ)^1673 := by
    have hnat : (5494214517 : ℕ)^2185*100000000000000^1673 ≤ 45741151188083^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5494214517 10000000000 45741151188083 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (96605159/400000000 : ℝ)^2185 ≤ (781748767821/5000000000000 : ℝ)^1673 := by
    have hnat : (96605159 : ℕ)^2185*5000000000000^1673 ≤ 781748767821^1673*400000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      96605159 400000000 781748767821 5000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4826872313/10000000000 : ℝ)^2185 ≤ (19311936718779/50000000000000 : ℝ)^1673 := by
    have hnat : (4826872313 : ℕ)^2185*50000000000000^1673 ≤ 19311936718779^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4826872313 10000000000 19311936718779 50000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5494214517/10000000000 : ℝ), (-96605159/400000000 : ℝ), (4826872313/10000000000 : ℝ)] ![(45741151188083/100000000000000 : ℝ), (781748767821/5000000000000 : ℝ), (19311936718779/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5494214517/10000000000 : ℝ)|^2185 ≤ (45741151188083/100000000000000 : ℝ)^1673
        have hw : |(5494214517/10000000000 : ℝ)|=(5494214517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-96605159/400000000 : ℝ)|^2185 ≤ (781748767821/5000000000000 : ℝ)^1673
        have hw : |(-96605159/400000000 : ℝ)|=(96605159/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4826872313/10000000000 : ℝ)|^2185 ≤ (19311936718779/50000000000000 : ℝ)^1673
        have hw : |(4826872313/10000000000 : ℝ)|=(4826872313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_s0_2 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (21976859/40000000 : ℝ)*x 0 + (965374437/2000000000 : ℝ)*x 1 + (-1207564417/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21976859/40000000 : ℝ)^2185 ≤ (714705526899/1562500000000 : ℝ)^1673 := by
    have hnat : (21976859 : ℕ)^2185*1562500000000^1673 ≤ 714705526899^1673*40000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21976859 40000000 714705526899 1562500000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (965374437/2000000000 : ℝ)^2185 ≤ (9655968024967/25000000000000 : ℝ)^1673 := by
    have hnat : (965374437 : ℕ)^2185*25000000000000^1673 ≤ 9655968024967^1673*2000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      965374437 2000000000 9655968024967 25000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1207564417/5000000000 : ℝ)^2185 ≤ (15634974164269/100000000000000 : ℝ)^1673 := by
    have hnat : (1207564417 : ℕ)^2185*100000000000000^1673 ≤ 15634974164269^1673*5000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1207564417 5000000000 15634974164269 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(21976859/40000000 : ℝ), (965374437/2000000000 : ℝ), (-1207564417/5000000000 : ℝ)] ![(714705526899/1562500000000 : ℝ), (9655968024967/25000000000000 : ℝ), (15634974164269/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(21976859/40000000 : ℝ)|^2185 ≤ (714705526899/1562500000000 : ℝ)^1673
        have hw : |(21976859/40000000 : ℝ)|=(21976859/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(965374437/2000000000 : ℝ)|^2185 ≤ (9655968024967/25000000000000 : ℝ)^1673
        have hw : |(965374437/2000000000 : ℝ)|=(965374437/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1207564417/5000000000 : ℝ)|^2185 ≤ (15634974164269/100000000000000 : ℝ)^1673
        have hw : |(-1207564417/5000000000 : ℝ)|=(1207564417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_s0_3 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4168738403/10000000000 : ℝ)*x 0 + (3103874711/10000000000 : ℝ)*x 1 + (2777736667/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4168738403/10000000000 : ℝ)^2185 ≤ (1594710985293/5000000000000 : ℝ)^1673 := by
    have hnat : (4168738403 : ℕ)^2185*5000000000000^1673 ≤ 1594710985293^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4168738403 10000000000 1594710985293 5000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3103874711/10000000000 : ℝ)^2185 ≤ (21697416850163/100000000000000 : ℝ)^1673 := by
    have hnat : (3103874711 : ℕ)^2185*100000000000000^1673 ≤ 21697416850163^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3103874711 10000000000 21697416850163 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2777736667/5000000000 : ℝ)^2185 ≤ (725130678649/1562500000000 : ℝ)^1673 := by
    have hnat : (2777736667 : ℕ)^2185*1562500000000^1673 ≤ 725130678649^1673*5000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2777736667 5000000000 725130678649 1562500000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4168738403/10000000000 : ℝ), (3103874711/10000000000 : ℝ), (2777736667/5000000000 : ℝ)] ![(1594710985293/5000000000000 : ℝ), (21697416850163/100000000000000 : ℝ), (725130678649/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4168738403/10000000000 : ℝ)|^2185 ≤ (1594710985293/5000000000000 : ℝ)^1673
        have hw : |(4168738403/10000000000 : ℝ)|=(4168738403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3103874711/10000000000 : ℝ)|^2185 ≤ (21697416850163/100000000000000 : ℝ)^1673
        have hw : |(3103874711/10000000000 : ℝ)|=(3103874711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2777736667/5000000000 : ℝ)|^2185 ≤ (725130678649/1562500000000 : ℝ)^1673
        have hw : |(2777736667/5000000000 : ℝ)|=(2777736667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_s0_4 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1773731363/10000000000 : ℝ)*x 0 + (4856111787/10000000000 : ℝ)*x 1 + (5937777/10000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1773731363/10000000000 : ℝ)^2185 ≤ (2611918966157/25000000000000 : ℝ)^1673 := by
    have hnat : (1773731363 : ℕ)^2185*25000000000000^1673 ≤ 2611918966157^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1773731363 10000000000 2611918966157 25000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4856111787/10000000000 : ℝ)^2185 ≤ (9732432338117/25000000000000 : ℝ)^1673 := by
    have hnat : (4856111787 : ℕ)^2185*25000000000000^1673 ≤ 9732432338117^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4856111787 10000000000 9732432338117 25000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5937777/10000000 : ℝ)^2185 ≤ (50622594767549/100000000000000 : ℝ)^1673 := by
    have hnat : (5937777 : ℕ)^2185*100000000000000^1673 ≤ 50622594767549^1673*10000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5937777 10000000 50622594767549 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1773731363/10000000000 : ℝ), (4856111787/10000000000 : ℝ), (5937777/10000000 : ℝ)] ![(2611918966157/25000000000000 : ℝ), (9732432338117/25000000000000 : ℝ), (50622594767549/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1773731363/10000000000 : ℝ)|^2185 ≤ (2611918966157/25000000000000 : ℝ)^1673
        have hw : |(-1773731363/10000000000 : ℝ)|=(1773731363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4856111787/10000000000 : ℝ)|^2185 ≤ (9732432338117/25000000000000 : ℝ)^1673
        have hw : |(4856111787/10000000000 : ℝ)|=(4856111787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5937777/10000000 : ℝ)|^2185 ≤ (50622594767549/100000000000000 : ℝ)^1673
        have hw : |(5937777/10000000 : ℝ)|=(5937777/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_s0_5 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2591414363/5000000000 : ℝ)*x 0 + (-260844819/2000000000 : ℝ)*x 1 + (742222121/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2591414363/5000000000 : ℝ)^2185 ≤ (42385151280861/100000000000000 : ℝ)^1673 := by
    have hnat : (2591414363 : ℕ)^2185*100000000000000^1673 ≤ 42385151280861^1673*5000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591414363 5000000000 42385151280861 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (260844819/2000000000 : ℝ)^2185 ≤ (3496127145759/50000000000000 : ℝ)^1673 := by
    have hnat : (260844819 : ℕ)^2185*50000000000000^1673 ≤ 3496127145759^1673*2000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260844819 2000000000 3496127145759 50000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (742222121/1250000000 : ℝ)^2185 ≤ (1265564860281/2500000000000 : ℝ)^1673 := by
    have hnat : (742222121 : ℕ)^2185*2500000000000^1673 ≤ 1265564860281^1673*1250000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      742222121 1250000000 1265564860281 2500000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2591414363/5000000000 : ℝ), (-260844819/2000000000 : ℝ), (742222121/1250000000 : ℝ)] ![(42385151280861/100000000000000 : ℝ), (3496127145759/50000000000000 : ℝ), (1265564860281/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2591414363/5000000000 : ℝ)|^2185 ≤ (42385151280861/100000000000000 : ℝ)^1673
        have hw : |(2591414363/5000000000 : ℝ)|=(2591414363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-260844819/2000000000 : ℝ)|^2185 ≤ (3496127145759/50000000000000 : ℝ)^1673
        have hw : |(-260844819/2000000000 : ℝ)|=(260844819/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(742222121/1250000000 : ℝ)|^2185 ≤ (1265564860281/2500000000000 : ℝ)^1673
        have hw : |(742222121/1250000000 : ℝ)|=(742222121/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_s0_6 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1295707179/2500000000 : ℝ)*x 0 + (5937777/10000000 : ℝ)*x 1 + (-1304224059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1295707179/2500000000 : ℝ)^2185 ≤ (21192575587027/50000000000000 : ℝ)^1673 := by
    have hnat : (1295707179 : ℕ)^2185*50000000000000^1673 ≤ 21192575587027^1673*2500000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295707179 2500000000 21192575587027 50000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5937777/10000000 : ℝ)^2185 ≤ (50622594767549/100000000000000 : ℝ)^1673 := by
    have hnat : (5937777 : ℕ)^2185*100000000000000^1673 ≤ 50622594767549^1673*10000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5937777 10000000 50622594767549 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1304224059/10000000000 : ℝ)^2185 ≤ (6992254039447/100000000000000 : ℝ)^1673 := by
    have hnat : (1304224059 : ℕ)^2185*100000000000000^1673 ≤ 6992254039447^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304224059 10000000000 6992254039447 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1295707179/2500000000 : ℝ), (5937777/10000000 : ℝ), (-1304224059/10000000000 : ℝ)] ![(21192575587027/50000000000000 : ℝ), (50622594767549/100000000000000 : ℝ), (6992254039447/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1295707179/2500000000 : ℝ)|^2185 ≤ (21192575587027/50000000000000 : ℝ)^1673
        have hw : |(1295707179/2500000000 : ℝ)|=(1295707179/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5937777/10000000 : ℝ)|^2185 ≤ (50622594767549/100000000000000 : ℝ)^1673
        have hw : |(5937777/10000000 : ℝ)|=(5937777/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1304224059/10000000000 : ℝ)|^2185 ≤ (6992254039447/100000000000000 : ℝ)^1673
        have hw : |(-1304224059/10000000000 : ℝ)|=(1304224059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_s0_7 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (522196111/1250000000 : ℝ)*x 0 + (5492657999/10000000000 : ℝ)*x 1 + (3168933923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (522196111/1250000000 : ℝ)^2185 ≤ (1599124230701/5000000000000 : ℝ)^1673 := by
    have hnat : (522196111 : ℕ)^2185*5000000000000^1673 ≤ 1599124230701^1673*1250000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522196111 1250000000 1599124230701 5000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5492657999/10000000000 : ℝ)^2185 ≤ (22862113802893/50000000000000 : ℝ)^1673 := by
    have hnat : (5492657999 : ℕ)^2185*50000000000000^1673 ≤ 22862113802893^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5492657999 10000000000 22862113802893 50000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3168933923/10000000000 : ℝ)^2185 ≤ (89173151067/400000000000 : ℝ)^1673 := by
    have hnat : (3168933923 : ℕ)^2185*400000000000^1673 ≤ 89173151067^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3168933923 10000000000 89173151067 400000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(522196111/1250000000 : ℝ), (5492657999/10000000000 : ℝ), (3168933923/10000000000 : ℝ)] ![(1599124230701/5000000000000 : ℝ), (22862113802893/50000000000000 : ℝ), (89173151067/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(522196111/1250000000 : ℝ)|^2185 ≤ (1599124230701/5000000000000 : ℝ)^1673
        have hw : |(522196111/1250000000 : ℝ)|=(522196111/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5492657999/10000000000 : ℝ)|^2185 ≤ (22862113802893/50000000000000 : ℝ)^1673
        have hw : |(5492657999/10000000000 : ℝ)|=(5492657999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3168933923/10000000000 : ℝ)|^2185 ≤ (89173151067/400000000000 : ℝ)^1673
        have hw : |(3168933923/10000000000 : ℝ)|=(3168933923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1410_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157414197/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1913/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2639/10000 : ℝ)*pair X 0 0 := by
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
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (4369/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4369 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4369*1^1024 ≤ 0^1024*1^4369 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4369 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4369 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4369/1024 : ℝ) ≤ (2005157713309135261/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4369 ≤ (2005157713309135261/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4369*100000000000000000000^1024 ≤ 2005157713309135261^1024*5^4369 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2005157713309135261 100000000000000000000 4369 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2005157713309135261/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4369 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4369/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4369 := by
      have hnat : (1 : ℕ)^1024*1^4369 ≤ 1^4369*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4369 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4369 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (102005157713309135261/100000000000000000000 : ℝ) ≤ (10046640056112523/10000000000000000 : ℝ) ^ (4369/1024 : ℝ) := by
    have hpowers : (102005157713309135261/100000000000000000000 : ℝ)^1024 ≤ (10046640056112523/10000000000000000 : ℝ)^4369 := by
      have hnat : (102005157713309135261 : ℕ)^1024*10000000000000000^4369 ≤ 10046640056112523^4369*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102005157713309135261 100000000000000000000 10046640056112523 10000000000000000 1024 4369 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10046640056112523/10000000000000000 : ℝ)) (X := (102005157713309135261/100000000000000000000 : ℝ)) (by norm_num) 4369 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (52005157713309135261/50000000000000000000 : ℝ) ≤ (5046640056112523/5000000000000000 : ℝ) ^ (4369/1024 : ℝ) := by
    have hpowers : (52005157713309135261/50000000000000000000 : ℝ)^1024 ≤ (5046640056112523/5000000000000000 : ℝ)^4369 := by
      have hnat : (52005157713309135261 : ℕ)^1024*5000000000000000^4369 ≤ 5046640056112523^4369*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52005157713309135261 50000000000000000000 5046640056112523 5000000000000000 1024 4369 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5046640056112523/5000000000000000 : ℝ)) (X := (52005157713309135261/50000000000000000000 : ℝ)) (by norm_num) 4369 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(46640056112523/4000000000000000 : ℝ)*(0 : ℝ))^(4369/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(46640056112523/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2005157713309135261/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(46640056112523/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4369/1024 : ℝ) := by
    rw [show (1 : ℝ)+(46640056112523/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10046640056112523/10000000000000000 : ℝ) by norm_num, show 1+(2005157713309135261/100000000000000000000 : ℝ)+(0 : ℝ)=(102005157713309135261/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2005157713309135261/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(46640056112523/4000000000000000 : ℝ)*(2/5 : ℝ))^(4369/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(46640056112523/4000000000000000 : ℝ)*(2/5 : ℝ)=(5046640056112523/5000000000000000 : ℝ) by norm_num, show 1+2*(2005157713309135261/100000000000000000000 : ℝ)=(52005157713309135261/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(46640056112523/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4369/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (46640056112523/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(46640056112523/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4369/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (46640056112523/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(46640056112523/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4369/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (46640056112523/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1769621283/10000000000 : ℝ)*X 0 0+(746007647/1250000000 : ℝ)*X 0 1+(4826872007/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5494214517/10000000000 : ℝ)*X 1 0+(-96605159/400000000 : ℝ)*X 1 1+(4826872313/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((21976859/40000000 : ℝ)*X 2 0+(965374437/2000000000 : ℝ)*X 2 1+(-1207564417/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4168738403/10000000000 : ℝ)*X 0 0+(3103874711/10000000000 : ℝ)*X 0 1+(2777736667/5000000000 : ℝ)*X 0 2+(4168738403/10000000000 : ℝ)*X 1 0+(3103874711/10000000000 : ℝ)*X 1 1+(2777736667/5000000000 : ℝ)*X 1 2+(4168738403/10000000000 : ℝ)*X 2 0+(3103874711/10000000000 : ℝ)*X 2 1+(2777736667/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1773731363/10000000000 : ℝ)*X 0 0+(4856111787/10000000000 : ℝ)*X 0 1+(5937777/10000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2591414363/5000000000 : ℝ)*X 1 0+(-260844819/2000000000 : ℝ)*X 1 1+(742222121/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1295707179/2500000000 : ℝ)*X 2 0+(5937777/10000000 : ℝ)*X 2 1+(-1304224059/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((522196111/1250000000 : ℝ)*X 0 0+(5492657999/10000000000 : ℝ)*X 0 1+(3168933923/10000000000 : ℝ)*X 0 2+(522196111/1250000000 : ℝ)*X 1 0+(5492657999/10000000000 : ℝ)*X 1 1+(3168933923/10000000000 : ℝ)*X 1 2+(522196111/1250000000 : ℝ)*X 2 0+(5492657999/10000000000 : ℝ)*X 2 1+(3168933923/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2024226945244833/1000000000000000000000 : ℝ) := by norm_num
    linear_combination (536180237/100000000000000 : ℝ)*(base19) + (526159469/100000000000000 : ℝ)*(base23) + (69948873/100000000000000 : ℝ)*(upper3) + (12961501/50000000000000 : ℝ)*(upper4) + (38228063/50000000000000 : ℝ)*(upper5) + (160522736055651/25000000000000 : ℝ)*(major0) + (160522736055651/25000000000000 : ℝ)*(major1) + (160522736055651/25000000000000 : ℝ)*(major2) + (438140353422051/50000000000000 : ℝ)*(sp0) + (87628227919939/10000000000000 : ℝ)*(sp1) + (438141144610079/50000000000000 : ℝ)*(sp2) + (101974506665023/25000000000000 : ℝ)*(sp3) + (84341421/4000000000000 : ℝ)*(sp4) + (195786251/20000000000000 : ℝ)*(sp7) + (407899005591347/100000000000000 : ℝ)*(f.failure) + (876282815379627/100000000000000 : ℝ)*(f.sum) + (262969942267473/50000000000000000000000000000 : ℝ)*base65 + (567425282382527/100000000000000000000000000000 : ℝ)*base68 + (291137134682527/100000000000000000000000000000 : ℝ)*base70 + (58639568582527/100000000000000000000000000000 : ℝ)*base72 + (31222300667473/50000000000000000000000000000 : ℝ)*base73 + (102408270282527/100000000000000000000000000000 : ℝ)*base76 + (299178155582527/100000000000000000000000000000 : ℝ)*base78 + (277424092682527/100000000000000000000000000000 : ℝ)*base80 + (107454929967473/50000000000000000000000000000 : ℝ)*base81 + (1846641/10000000000000000000000 : ℝ)*base90 + (1846641/10000000000000000000000 : ℝ)*base92 + (1846641/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (392259354281078703697167/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (178757349/10000000000000 : ℝ)*(base19) + (450652547/25000000000000 : ℝ)*(base23) + (104638887/100000000000000 : ℝ)*(base32) + (259686627/100000000000000 : ℝ)*(upper3) + (179942397/100000000000000 : ℝ)*(upper5) + (338710944819343/50000000000000 : ℝ)*(major0) + (338710944819343/50000000000000 : ℝ)*(major1) + (338710944819343/50000000000000 : ℝ)*(major2) + (417234001/10000000000000 : ℝ)*(sp1) + (4452303091/100000000000000 : ℝ)*(sp2) + (23112498462691/2500000000000 : ℝ)*(sp4) + (46224698929707/5000000000000 : ℝ)*(sp5) + (924493683594361/100000000000000 : ℝ)*(sp6) + (215171737312303/50000000000000 : ℝ)*(sp7) + (430343579263493/100000000000000 : ℝ)*(f.failure) + (23112498462691/2500000000000 : ℝ)*(f.sum) + (63127365867611/100000000000000000000000000000 : ℝ)*base66 + (1146711900132389/200000000000000000000000000000 : ℝ)*base67 + (1112990752667611/200000000000000000000000000000 : ℝ)*base70 + (599762672667611/200000000000000000000000000000 : ℝ)*base72 + (603894080532389/100000000000000000000000000000 : ℝ)*base73 + (130316882667611/200000000000000000000000000000 : ℝ)*base76 + (272222944132389/200000000000000000000000000000 : ℝ)*base77 + (337161730867611/200000000000000000000000000000 : ℝ)*base80 + (325908099567611/100000000000000000000000000000 : ℝ)*base82 + (2010121/10000000000000000000000 : ℝ)*base89 + (2010121/10000000000000000000000 : ℝ)*base91 + (2010121/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1410_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157414197/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1913/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2639/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1410_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1410_s1_0 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-388935301/2000000000 : ℝ)*x 0 + (5612932371/10000000000 : ℝ)*x 1 + (5069807881/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (388935301/2000000000 : ℝ)^2185 ≤ (5890854704709/50000000000000 : ℝ)^1673 := by
    have hnat : (388935301 : ℕ)^2185*50000000000000^1673 ≤ 5890854704709^1673*2000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      388935301 2000000000 5890854704709 50000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5612932371/10000000000 : ℝ)^2185 ≤ (23518119933041/50000000000000 : ℝ)^1673 := by
    have hnat : (5612932371 : ℕ)^2185*50000000000000^1673 ≤ 23518119933041^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5612932371 10000000000 23518119933041 50000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5069807881/10000000000 : ℝ)^2185 ≤ (5147756339073/12500000000000 : ℝ)^1673 := by
    have hnat : (5069807881 : ℕ)^2185*12500000000000^1673 ≤ 5147756339073^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5069807881 10000000000 5147756339073 12500000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-388935301/2000000000 : ℝ), (5612932371/10000000000 : ℝ), (5069807881/10000000000 : ℝ)] ![(5890854704709/50000000000000 : ℝ), (23518119933041/50000000000000 : ℝ), (5147756339073/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-388935301/2000000000 : ℝ)|^2185 ≤ (5890854704709/50000000000000 : ℝ)^1673
        have hw : |(-388935301/2000000000 : ℝ)|=(388935301/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5612932371/10000000000 : ℝ)|^2185 ≤ (23518119933041/50000000000000 : ℝ)^1673
        have hw : |(5612932371/10000000000 : ℝ)|=(5612932371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5069807881/10000000000 : ℝ)|^2185 ≤ (5147756339073/12500000000000 : ℝ)^1673
        have hw : |(5069807881/10000000000 : ℝ)|=(5069807881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_s1_1 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (269936317/500000000 : ℝ)*x 0 + (-1116448497/5000000000 : ℝ)*x 1 + (506980487/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (269936317/500000000 : ℝ)^2185 ≤ (8941132491033/20000000000000 : ℝ)^1673 := by
    have hnat : (269936317 : ℕ)^2185*20000000000000^1673 ≤ 8941132491033^1673*500000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269936317 500000000 8941132491033 20000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1116448497/5000000000 : ℝ)^2185 ≤ (14112318761521/100000000000000 : ℝ)^1673 := by
    have hnat : (1116448497 : ℕ)^2185*100000000000000^1673 ≤ 14112318761521^1673*5000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1116448497 5000000000 14112318761521 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (506980487/1000000000 : ℝ)^2185 ≤ (4118201876907/10000000000000 : ℝ)^1673 := by
    have hnat : (506980487 : ℕ)^2185*10000000000000^1673 ≤ 4118201876907^1673*1000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      506980487 1000000000 4118201876907 10000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(269936317/500000000 : ℝ), (-1116448497/5000000000 : ℝ), (506980487/1000000000 : ℝ)] ![(8941132491033/20000000000000 : ℝ), (14112318761521/100000000000000 : ℝ), (4118201876907/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(269936317/500000000 : ℝ)|^2185 ≤ (8941132491033/20000000000000 : ℝ)^1673
        have hw : |(269936317/500000000 : ℝ)|=(269936317/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1116448497/5000000000 : ℝ)|^2185 ≤ (14112318761521/100000000000000 : ℝ)^1673
        have hw : |(-1116448497/5000000000 : ℝ)|=(1116448497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(506980487/1000000000 : ℝ)|^2185 ≤ (4118201876907/10000000000000 : ℝ)^1673
        have hw : |(506980487/1000000000 : ℝ)|=(506980487/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_s1_2 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (337420289/625000000 : ℝ)*x 0 + (63372603/125000000 : ℝ)*x 1 + (-34888983/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (337420289/625000000 : ℝ)^2185 ≤ (44705643896617/100000000000000 : ℝ)^1673 := by
    have hnat : (337420289 : ℕ)^2185*100000000000000^1673 ≤ 44705643896617^1673*625000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337420289 625000000 44705643896617 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (63372603/125000000 : ℝ)^2185 ≤ (41182054521193/100000000000000 : ℝ)^1673 := by
    have hnat : (63372603 : ℕ)^2185*100000000000000^1673 ≤ 41182054521193^1673*125000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63372603 125000000 41182054521193 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (34888983/156250000 : ℝ)^2185 ≤ (3528075393969/25000000000000 : ℝ)^1673 := by
    have hnat : (34888983 : ℕ)^2185*25000000000000^1673 ≤ 3528075393969^1673*156250000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34888983 156250000 3528075393969 25000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(337420289/625000000 : ℝ), (63372603/125000000 : ℝ), (-34888983/156250000 : ℝ)] ![(44705643896617/100000000000000 : ℝ), (41182054521193/100000000000000 : ℝ), (3528075393969/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(337420289/625000000 : ℝ)|^2185 ≤ (44705643896617/100000000000000 : ℝ)^1673
        have hw : |(337420289/625000000 : ℝ)|=(337420289/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(63372603/125000000 : ℝ)|^2185 ≤ (41182054521193/100000000000000 : ℝ)^1673
        have hw : |(63372603/125000000 : ℝ)|=(63372603/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-34888983/156250000 : ℝ)|^2185 ≤ (3528075393969/25000000000000 : ℝ)^1673
        have hw : |(-34888983/156250000 : ℝ)|=(34888983/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_s1_3 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1070022181/2500000000 : ℝ)*x 0 + (1866234133/5000000000 : ℝ)*x 1 + (612407893/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070022181/2500000000 : ℝ)^2185 ≤ (33011378636731/100000000000000 : ℝ)^1673 := by
    have hnat : (1070022181 : ℕ)^2185*100000000000000^1673 ≤ 33011378636731^1673*2500000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070022181 2500000000 33011378636731 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1866234133/5000000000 : ℝ)^2185 ≤ (5521296528287/20000000000000 : ℝ)^1673 := by
    have hnat : (1866234133 : ℕ)^2185*20000000000000^1673 ≤ 5521296528287^1673*5000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1866234133 5000000000 5521296528287 20000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (612407893/1250000000 : ℝ)^2185 ≤ (39382138708229/100000000000000 : ℝ)^1673 := by
    have hnat : (612407893 : ℕ)^2185*100000000000000^1673 ≤ 39382138708229^1673*1250000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      612407893 1250000000 39382138708229 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070022181/2500000000 : ℝ), (1866234133/5000000000 : ℝ), (612407893/1250000000 : ℝ)] ![(33011378636731/100000000000000 : ℝ), (5521296528287/20000000000000 : ℝ), (39382138708229/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070022181/2500000000 : ℝ)|^2185 ≤ (33011378636731/100000000000000 : ℝ)^1673
        have hw : |(1070022181/2500000000 : ℝ)|=(1070022181/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1866234133/5000000000 : ℝ)|^2185 ≤ (5521296528287/20000000000000 : ℝ)^1673
        have hw : |(1866234133/5000000000 : ℝ)|=(1866234133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(612407893/1250000000 : ℝ)|^2185 ≤ (39382138708229/100000000000000 : ℝ)^1673
        have hw : |(612407893/1250000000 : ℝ)|=(612407893/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_s1_4 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-243137579/1250000000 : ℝ)*x 0 + (40610161/80000000 : ℝ)*x 1 + (1121271851/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (243137579/1250000000 : ℝ)^2185 ≤ (2946266361823/25000000000000 : ℝ)^1673 := by
    have hnat : (243137579 : ℕ)^2185*25000000000000^1673 ≤ 2946266361823^1673*1250000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      243137579 1250000000 2946266361823 25000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (40610161/80000000 : ℝ)^2185 ≤ (10312655408811/25000000000000 : ℝ)^1673 := by
    have hnat : (40610161 : ℕ)^2185*25000000000000^1673 ≤ 10312655408811^1673*80000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40610161 80000000 10312655408811 25000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1121271851/2000000000 : ℝ)^2185 ≤ (9392862580313/20000000000000 : ℝ)^1673 := by
    have hnat : (1121271851 : ℕ)^2185*20000000000000^1673 ≤ 9392862580313^1673*2000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121271851 2000000000 9392862580313 20000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-243137579/1250000000 : ℝ), (40610161/80000000 : ℝ), (1121271851/2000000000 : ℝ)] ![(2946266361823/25000000000000 : ℝ), (10312655408811/25000000000000 : ℝ), (9392862580313/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-243137579/1250000000 : ℝ)|^2185 ≤ (2946266361823/25000000000000 : ℝ)^1673
        have hw : |(-243137579/1250000000 : ℝ)|=(243137579/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(40610161/80000000 : ℝ)|^2185 ≤ (10312655408811/25000000000000 : ℝ)^1673
        have hw : |(40610161/80000000 : ℝ)|=(40610161/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1121271851/2000000000 : ℝ)|^2185 ≤ (9392862580313/20000000000000 : ℝ)^1673
        have hw : |(1121271851/2000000000 : ℝ)|=(1121271851/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_s1_5 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5257023383/10000000000 : ℝ)*x 0 + (-42408567/250000000 : ℝ)*x 1 + (1121271817/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5257023383/10000000000 : ℝ)^2185 ≤ (43179337201443/100000000000000 : ℝ)^1673 := by
    have hnat : (5257023383 : ℕ)^2185*100000000000000^1673 ≤ 43179337201443^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257023383 10000000000 43179337201443 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42408567/250000000 : ℝ)^2185 ≤ (1232043967893/12500000000000 : ℝ)^1673 := by
    have hnat : (42408567 : ℕ)^2185*12500000000000^1673 ≤ 1232043967893^1673*250000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42408567 250000000 1232043967893 12500000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1121271817/2000000000 : ℝ)^2185 ≤ (46964311041657/100000000000000 : ℝ)^1673 := by
    have hnat : (1121271817 : ℕ)^2185*100000000000000^1673 ≤ 46964311041657^1673*2000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121271817 2000000000 46964311041657 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5257023383/10000000000 : ℝ), (-42408567/250000000 : ℝ), (1121271817/2000000000 : ℝ)] ![(43179337201443/100000000000000 : ℝ), (1232043967893/12500000000000 : ℝ), (46964311041657/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5257023383/10000000000 : ℝ)|^2185 ≤ (43179337201443/100000000000000 : ℝ)^1673
        have hw : |(5257023383/10000000000 : ℝ)|=(5257023383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-42408567/250000000 : ℝ)|^2185 ≤ (1232043967893/12500000000000 : ℝ)^1673
        have hw : |(-42408567/250000000 : ℝ)|=(42408567/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1121271817/2000000000 : ℝ)|^2185 ≤ (46964311041657/100000000000000 : ℝ)^1673
        have hw : |(1121271817/2000000000 : ℝ)|=(1121271817/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_s1_6 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5257024023/10000000000 : ℝ)*x 0 + (5606359589/10000000000 : ℝ)*x 1 + (-1696341049/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5257024023/10000000000 : ℝ)^2185 ≤ (43179344066933/100000000000000 : ℝ)^1673 := by
    have hnat : (5257024023 : ℕ)^2185*100000000000000^1673 ≤ 43179344066933^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257024023 10000000000 43179344066933 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5606359589/10000000000 : ℝ)^2185 ≤ (23482158277869/50000000000000 : ℝ)^1673 := by
    have hnat : (5606359589 : ℕ)^2185*50000000000000^1673 ≤ 23482158277869^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5606359589 10000000000 23482158277869 50000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1696341049/10000000000 : ℝ)^2185 ≤ (61602121039/625000000000 : ℝ)^1673 := by
    have hnat : (1696341049 : ℕ)^2185*625000000000^1673 ≤ 61602121039^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1696341049 10000000000 61602121039 625000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5257024023/10000000000 : ℝ), (5606359589/10000000000 : ℝ), (-1696341049/10000000000 : ℝ)] ![(43179344066933/100000000000000 : ℝ), (23482158277869/50000000000000 : ℝ), (61602121039/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5257024023/10000000000 : ℝ)|^2185 ≤ (43179344066933/100000000000000 : ℝ)^1673
        have hw : |(5257024023/10000000000 : ℝ)|=(5257024023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5606359589/10000000000 : ℝ)|^2185 ≤ (23482158277869/50000000000000 : ℝ)^1673
        have hw : |(5606359589/10000000000 : ℝ)|=(5606359589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1696341049/10000000000 : ℝ)|^2185 ≤ (61602121039/625000000000 : ℝ)^1673
        have hw : |(-1696341049/10000000000 : ℝ)|=(1696341049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_s1_7 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1070250119/2500000000 : ℝ)*x 0 + (2442687829/5000000000 : ℝ)*x 1 + (1873297901/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070250119/2500000000 : ℝ)^2185 ≤ (4127570396723/12500000000000 : ℝ)^1673 := by
    have hnat : (1070250119 : ℕ)^2185*12500000000000^1673 ≤ 4127570396723^1673*2500000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070250119 2500000000 4127570396723 12500000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2442687829/5000000000 : ℝ)^2185 ≤ (19618202649149/50000000000000 : ℝ)^1673 := by
    have hnat : (2442687829 : ℕ)^2185*50000000000000^1673 ≤ 19618202649149^1673*5000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2442687829 5000000000 19618202649149 50000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1873297901/5000000000 : ℝ)^2185 ≤ (2774303151379/10000000000000 : ℝ)^1673 := by
    have hnat : (1873297901 : ℕ)^2185*10000000000000^1673 ≤ 2774303151379^1673*5000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1873297901 5000000000 2774303151379 10000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070250119/2500000000 : ℝ), (2442687829/5000000000 : ℝ), (1873297901/5000000000 : ℝ)] ![(4127570396723/12500000000000 : ℝ), (19618202649149/50000000000000 : ℝ), (2774303151379/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070250119/2500000000 : ℝ)|^2185 ≤ (4127570396723/12500000000000 : ℝ)^1673
        have hw : |(1070250119/2500000000 : ℝ)|=(1070250119/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2442687829/5000000000 : ℝ)|^2185 ≤ (19618202649149/50000000000000 : ℝ)^1673
        have hw : |(2442687829/5000000000 : ℝ)|=(2442687829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1873297901/5000000000 : ℝ)|^2185 ≤ (2774303151379/10000000000000 : ℝ)^1673
        have hw : |(1873297901/5000000000 : ℝ)|=(1873297901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1410_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157414197/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2639/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1913/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (7493/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9487/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2639/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1913/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2639/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1913/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2639/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1913/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2639/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1913/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2639/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1913/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2639/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1913/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1913/100000 : ℝ) ^ (4369/1024 : ℝ) ≤ (93280830051/2000000000000000000 : ℝ) := by
    have hpowers : (1913/100000 : ℝ)^4369 ≤ (93280830051/2000000000000000000 : ℝ)^1024 := by
      have hnat : (1913 : ℕ)^4369*2000000000000000000^1024 ≤ 93280830051^1024*100000^4369 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1913 100000 93280830051 2000000000000000000 4369 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1913/100000 : ℝ)) (X := (93280830051/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4369 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2639/10000 : ℝ) ^ (4369/1024 : ℝ) ≤ (85006553197755533/25000000000000000000 : ℝ) := by
    have hpowers : (2639/10000 : ℝ)^4369 ≤ (85006553197755533/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2639 : ℕ)^4369*25000000000000000000^1024 ≤ 85006553197755533^1024*10000^4369 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2639 10000 85006553197755533 25000000000000000000 4369 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2639/10000 : ℝ)) (X := (85006553197755533/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4369 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1000000093280830051/1000000000000000000 : ℝ) ≤ (5000000109315137/5000000000000000 : ℝ) ^ (4369/1024 : ℝ) := by
    have hpowers : (1000000093280830051/1000000000000000000 : ℝ)^1024 ≤ (5000000109315137/5000000000000000 : ℝ)^4369 := by
      have hnat : (1000000093280830051 : ℕ)^1024*5000000000000000^4369 ≤ 5000000109315137^4369*1000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000000093280830051 1000000000000000000 5000000109315137 5000000000000000 1024 4369 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000109315137/5000000000000000 : ℝ)) (X := (1000000093280830051/1000000000000000000 : ℝ)) (by norm_num) 4369 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50170015438416262341/50000000000000000000 : ℝ) ≤ (1250994905271729/1250000000000000 : ℝ) ^ (4369/1024 : ℝ) := by
    have hpowers : (50170015438416262341/50000000000000000000 : ℝ)^1024 ≤ (1250994905271729/1250000000000000 : ℝ)^4369 := by
      have hnat : (50170015438416262341 : ℕ)^1024*1250000000000000^4369 ≤ 1250994905271729^4369*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50170015438416262341 50000000000000000000 1250994905271729 1250000000000000 1024 4369 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250994905271729/1250000000000000 : ℝ)) (X := (50170015438416262341/50000000000000000000 : ℝ)) (by norm_num) 4369 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12585006553197755533/12500000000000000000 : ℝ) ≤ (1001591826571739/1000000000000000 : ℝ) ^ (4369/1024 : ℝ) := by
    have hpowers : (12585006553197755533/12500000000000000000 : ℝ)^1024 ≤ (1001591826571739/1000000000000000 : ℝ)^4369 := by
      have hnat : (12585006553197755533 : ℕ)^1024*1000000000000000^4369 ≤ 1001591826571739^4369*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12585006553197755533 12500000000000000000 1001591826571739 1000000000000000 1024 4369 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1001591826571739/1000000000000000 : ℝ)) (X := (12585006553197755533/12500000000000000000 : ℝ)) (by norm_num) 4369 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(93280830051/2000000000000000000 : ℝ) ≤ ((24473955412733556379/24477000000000000000 : ℝ)+2*(3979511771779/1223850000000000 : ℝ)*(1913/100000 : ℝ))^(4369/1024 : ℝ) := by
    rw [show (24473955412733556379/24477000000000000000 : ℝ)+2*(3979511771779/1223850000000000 : ℝ)*(1913/100000 : ℝ)=(5000000109315137/5000000000000000 : ℝ) by norm_num, show 1+2*(93280830051/2000000000000000000 : ℝ)=(1000000093280830051/1000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(85006553197755533/25000000000000000000 : ℝ)+(93280830051/2000000000000000000 : ℝ) ≤ ((24473955412733556379/24477000000000000000 : ℝ)+(3979511771779/1223850000000000 : ℝ)*((2639/10000 : ℝ)+(1913/100000 : ℝ)))^(4369/1024 : ℝ) := by
    rw [show (24473955412733556379/24477000000000000000 : ℝ)+(3979511771779/1223850000000000 : ℝ)*((2639/10000 : ℝ)+(1913/100000 : ℝ))=(1250994905271729/1250000000000000 : ℝ) by norm_num, show 1+(85006553197755533/25000000000000000000 : ℝ)+(93280830051/2000000000000000000 : ℝ)=(50170015438416262341/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(85006553197755533/25000000000000000000 : ℝ) ≤ ((24473955412733556379/24477000000000000000 : ℝ)+2*(3979511771779/1223850000000000 : ℝ)*(2639/10000 : ℝ))^(4369/1024 : ℝ) := by
    rw [show (24473955412733556379/24477000000000000000 : ℝ)+2*(3979511771779/1223850000000000 : ℝ)*(2639/10000 : ℝ)=(1001591826571739/1000000000000000 : ℝ) by norm_num, show 1+2*(85006553197755533/25000000000000000000 : ℝ)=(12585006553197755533/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (24473955412733556379/24477000000000000000 : ℝ)*(X 1 0+X 2 0)+(3979511771779/1223850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4369/1024 : ℝ)) (lo := (1913/100000 : ℝ)) (hi := (2639/10000 : ℝ)) (c := (24473955412733556379/24477000000000000000 : ℝ)) (alpha := (3979511771779/1223850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (24473955412733556379/24477000000000000000 : ℝ)*(X 0 1+X 2 1)+(3979511771779/1223850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4369/1024 : ℝ)) (lo := (1913/100000 : ℝ)) (hi := (2639/10000 : ℝ)) (c := (24473955412733556379/24477000000000000000 : ℝ)) (alpha := (3979511771779/1223850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (24473955412733556379/24477000000000000000 : ℝ)*(X 0 2+X 1 2)+(3979511771779/1223850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4369/1024 : ℝ)) (lo := (1913/100000 : ℝ)) (hi := (2639/10000 : ℝ)) (c := (24473955412733556379/24477000000000000000 : ℝ)) (alpha := (3979511771779/1223850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-388935301/2000000000 : ℝ)*X 0 0+(5612932371/10000000000 : ℝ)*X 0 1+(5069807881/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((269936317/500000000 : ℝ)*X 1 0+(-1116448497/5000000000 : ℝ)*X 1 1+(506980487/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((337420289/625000000 : ℝ)*X 2 0+(63372603/125000000 : ℝ)*X 2 1+(-34888983/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1070022181/2500000000 : ℝ)*X 0 0+(1866234133/5000000000 : ℝ)*X 0 1+(612407893/1250000000 : ℝ)*X 0 2+(1070022181/2500000000 : ℝ)*X 1 0+(1866234133/5000000000 : ℝ)*X 1 1+(612407893/1250000000 : ℝ)*X 1 2+(1070022181/2500000000 : ℝ)*X 2 0+(1866234133/5000000000 : ℝ)*X 2 1+(612407893/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-243137579/1250000000 : ℝ)*X 0 0+(40610161/80000000 : ℝ)*X 0 1+(1121271851/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5257023383/10000000000 : ℝ)*X 1 0+(-42408567/250000000 : ℝ)*X 1 1+(1121271817/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5257024023/10000000000 : ℝ)*X 2 0+(5606359589/10000000000 : ℝ)*X 2 1+(-1696341049/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1070250119/2500000000 : ℝ)*X 0 0+(2442687829/5000000000 : ℝ)*X 0 1+(1873297901/5000000000 : ℝ)*X 0 2+(1070250119/2500000000 : ℝ)*X 1 0+(2442687829/5000000000 : ℝ)*X 1 1+(1873297901/5000000000 : ℝ)*X 1 2+(1070250119/2500000000 : ℝ)*X 2 0+(2442687829/5000000000 : ℝ)*X 2 1+(1873297901/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (275696926935109133593900491/50993750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (161176957/100000000000000 : ℝ)*(base1) + (1488056891/100000000000000 : ℝ)*(base19) + (944613607/100000000000000 : ℝ)*(base23) + (301390121/50000000000000 : ℝ)*(upper5) + (337281853134529/25000000000000 : ℝ)*(major0) + (337281853134529/25000000000000 : ℝ)*(major1) + (337281853134529/25000000000000 : ℝ)*(major2) + (460298913763703/25000000000000 : ℝ)*(sp0) + (1841195823781551/100000000000000 : ℝ)*(sp1) + (368239591849221/20000000000000 : ℝ)*(sp2) + (53565870765391/6250000000000 : ℝ)*(sp3) + (1704990929/50000000000000 : ℝ)*(sp4) + (159202127/10000000000000 : ℝ)*(sp5) + (823788573/50000000000000 : ℝ)*(sp7) + (21426393525009/2500000000000 : ℝ)*(f.failure) + (3596091609101/195312500000 : ℝ)*(f.sum) + (92841728126747/30596250000000000000000000000 : ℝ)*base65 + (322866325460706503/203975000000000000000000000000000 : ℝ)*base68 + (845075665582406503/203975000000000000000000000000000 : ℝ)*base70 + (732511954133606503/203975000000000000000000000000000 : ℝ)*base72 + (211883003955889/61192500000000000000000000000 : ℝ)*base73 + (296122267760456503/203975000000000000000000000000000 : ℝ)*base76 + (261564334780643497/203975000000000000000000000000000 : ℝ)*base77 + (466749005010256503/203975000000000000000000000000000 : ℝ)*base80 + (76454386662317/30596250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1152773/250000000000000000000 : ℝ)*base89 + (1152773/250000000000000000000 : ℝ)*base91 + (1152773/250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (56834249684327187061714347/40795000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10375539/5000000000000 : ℝ)*(base1) + (29516929/5000000000000 : ℝ)*(base19) + (29480533/3125000000000 : ℝ)*(base23) + (5363667/100000000000000 : ℝ)*(upper3) + (88663777/50000000000000 : ℝ)*(upper5) + (138230540950331/10000000000000 : ℝ)*(major0) + (138230540950331/10000000000000 : ℝ)*(major1) + (138230540950331/10000000000000 : ℝ)*(major2) + (984073717/50000000000000 : ℝ)*(sp1) + (3272669317/50000000000000 : ℝ)*(sp2) + (188647836189837/10000000000000 : ℝ)*(sp4) + (235809449487697/12500000000000 : ℝ)*(sp5) + (18864706656719/1000000000000 : ℝ)*(sp6) + (43906620533467/5000000000000 : ℝ)*(sp7) + (878132618180119/100000000000000 : ℝ)*(f.failure) + (1886478154387591/100000000000000 : ℝ)*(f.sum) + (18155330934151/6119250000000000000000000000 : ℝ)*base66 + (548003868797569517/81590000000000000000000000000000 : ℝ)*base68 + (583895559462969517/81590000000000000000000000000000 : ℝ)*base70 + (476959134627989517/81590000000000000000000000000000 : ℝ)*base72 + (4134369651487/1529812500000000000000000000 : ℝ)*base74 + (512562009095069517/81590000000000000000000000000000 : ℝ)*base76 + (362130522963309517/81590000000000000000000000000000 : ℝ)*base78 + (223210152843469517/81590000000000000000000000000000 : ℝ)*base80 + (6418304807381/3059625000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (33749443/10000000000000000000000 : ℝ)*base89 + (33749443/10000000000000000000000 : ℝ)*base91 + (33749443/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1410_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157414197/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2639/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1913/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (7493/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9487/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1410_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1410_s2_0 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-989626031/5000000000 : ℝ)*x 0 + (5462519447/10000000000 : ℝ)*x 1 + (1299497067/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (989626031/5000000000 : ℝ)^2185 ≤ (3014007870817/25000000000000 : ℝ)^1673 := by
    have hnat : (989626031 : ℕ)^2185*25000000000000^1673 ≤ 3014007870817^1673*5000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      989626031 5000000000 3014007870817 25000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5462519447/10000000000 : ℝ)^2185 ≤ (2837301830577/6250000000000 : ℝ)^1673 := by
    have hnat : (5462519447 : ℕ)^2185*6250000000000^1673 ≤ 2837301830577^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5462519447 10000000000 2837301830577 6250000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1299497067/2500000000 : ℝ)^2185 ≤ (42547139214227/100000000000000 : ℝ)^1673 := by
    have hnat : (1299497067 : ℕ)^2185*100000000000000^1673 ≤ 42547139214227^1673*2500000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1299497067 2500000000 42547139214227 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-989626031/5000000000 : ℝ), (5462519447/10000000000 : ℝ), (1299497067/2500000000 : ℝ)] ![(3014007870817/25000000000000 : ℝ), (2837301830577/6250000000000 : ℝ), (42547139214227/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-989626031/5000000000 : ℝ)|^2185 ≤ (3014007870817/25000000000000 : ℝ)^1673
        have hw : |(-989626031/5000000000 : ℝ)|=(989626031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5462519447/10000000000 : ℝ)|^2185 ≤ (2837301830577/6250000000000 : ℝ)^1673
        have hw : |(5462519447/10000000000 : ℝ)|=(5462519447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1299497067/2500000000 : ℝ)|^2185 ≤ (42547139214227/100000000000000 : ℝ)^1673
        have hw : |(1299497067/2500000000 : ℝ)|=(1299497067/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_s2_1 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2680678581/5000000000 : ℝ)*x 0 + (-2115468827/10000000000 : ℝ)*x 1 + (1299497061/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2680678581/5000000000 : ℝ)^2185 ≤ (22150971680277/50000000000000 : ℝ)^1673 := by
    have hnat : (2680678581 : ℕ)^2185*50000000000000^1673 ≤ 22150971680277^1673*5000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2680678581 5000000000 22150971680277 50000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2115468827/10000000000 : ℝ)^2185 ≤ (82193235451/625000000000 : ℝ)^1673 := by
    have hnat : (2115468827 : ℕ)^2185*625000000000^1673 ≤ 82193235451^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115468827 10000000000 82193235451 625000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1299497061/2500000000 : ℝ)^2185 ≤ (42547138957659/100000000000000 : ℝ)^1673 := by
    have hnat : (1299497061 : ℕ)^2185*100000000000000^1673 ≤ 42547138957659^1673*2500000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1299497061 2500000000 42547138957659 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2680678581/5000000000 : ℝ), (-2115468827/10000000000 : ℝ), (1299497061/2500000000 : ℝ)] ![(22150971680277/50000000000000 : ℝ), (82193235451/625000000000 : ℝ), (42547138957659/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2680678581/5000000000 : ℝ)|^2185 ≤ (22150971680277/50000000000000 : ℝ)^1673
        have hw : |(2680678581/5000000000 : ℝ)|=(2680678581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2115468827/10000000000 : ℝ)|^2185 ≤ (82193235451/625000000000 : ℝ)^1673
        have hw : |(-2115468827/10000000000 : ℝ)|=(2115468827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1299497061/2500000000 : ℝ)|^2185 ≤ (42547138957659/100000000000000 : ℝ)^1673
        have hw : |(1299497061/2500000000 : ℝ)|=(1299497061/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_s2_2 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5361356909/10000000000 : ℝ)*x 0 + (5197988529/10000000000 : ℝ)*x 1 + (-2115468787/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5361356909/10000000000 : ℝ)^2185 ≤ (5537742578771/12500000000000 : ℝ)^1673 := by
    have hnat : (5361356909 : ℕ)^2185*12500000000000^1673 ≤ 5537742578771^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5361356909 10000000000 5537742578771 12500000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5197988529/10000000000 : ℝ)^2185 ≤ (42547142004399/100000000000000 : ℝ)^1673 := by
    have hnat : (5197988529 : ℕ)^2185*100000000000000^1673 ≤ 42547142004399^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5197988529 10000000000 42547142004399 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2115468787/10000000000 : ℝ)^2185 ≤ (6575458673699/50000000000000 : ℝ)^1673 := by
    have hnat : (2115468787 : ℕ)^2185*50000000000000^1673 ≤ 6575458673699^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115468787 10000000000 6575458673699 50000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5361356909/10000000000 : ℝ), (5197988529/10000000000 : ℝ), (-2115468787/10000000000 : ℝ)] ![(5537742578771/12500000000000 : ℝ), (42547142004399/100000000000000 : ℝ), (6575458673699/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5361356909/10000000000 : ℝ)|^2185 ≤ (5537742578771/12500000000000 : ℝ)^1673
        have hw : |(5361356909/10000000000 : ℝ)|=(5361356909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5197988529/10000000000 : ℝ)|^2185 ≤ (42547142004399/100000000000000 : ℝ)^1673
        have hw : |(5197988529/10000000000 : ℝ)|=(5197988529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2115468787/10000000000 : ℝ)|^2185 ≤ (6575458673699/50000000000000 : ℝ)^1673
        have hw : |(-2115468787/10000000000 : ℝ)|=(2115468787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_s2_3 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (860888841/2000000000 : ℝ)*x 0 + (1007196959/2500000000 : ℝ)*x 1 + (459707587/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (860888841/2000000000 : ℝ)^2185 ≤ (8314232252383/25000000000000 : ℝ)^1673 := by
    have hnat : (860888841 : ℕ)^2185*25000000000000^1673 ≤ 8314232252383^1673*2000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      860888841 2000000000 8314232252383 25000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1007196959/2500000000 : ℝ)^2185 ≤ (15251520230237/50000000000000 : ℝ)^1673 := by
    have hnat : (1007196959 : ℕ)^2185*50000000000000^1673 ≤ 15251520230237^1673*2500000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1007196959 2500000000 15251520230237 50000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (459707587/1000000000 : ℝ)^2185 ≤ (36240030514663/100000000000000 : ℝ)^1673 := by
    have hnat : (459707587 : ℕ)^2185*100000000000000^1673 ≤ 36240030514663^1673*1000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      459707587 1000000000 36240030514663 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(860888841/2000000000 : ℝ), (1007196959/2500000000 : ℝ), (459707587/1000000000 : ℝ)] ![(8314232252383/25000000000000 : ℝ), (15251520230237/50000000000000 : ℝ), (36240030514663/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(860888841/2000000000 : ℝ)|^2185 ≤ (8314232252383/25000000000000 : ℝ)^1673
        have hw : |(860888841/2000000000 : ℝ)|=(860888841/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1007196959/2500000000 : ℝ)|^2185 ≤ (15251520230237/50000000000000 : ℝ)^1673
        have hw : |(1007196959/2500000000 : ℝ)|=(1007196959/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(459707587/1000000000 : ℝ)|^2185 ≤ (36240030514663/100000000000000 : ℝ)^1673
        have hw : |(459707587/1000000000 : ℝ)|=(459707587/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_s2_4 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-197930099/1000000000 : ℝ)*x 0 + (2599765589/5000000000 : ℝ)*x 1 + (27304819/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (197930099/1000000000 : ℝ)^2185 ≤ (3014105180909/25000000000000 : ℝ)^1673 := by
    have hnat : (197930099 : ℕ)^2185*25000000000000^1673 ≤ 3014105180909^1673*1000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197930099 1000000000 3014105180909 25000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2599765589/5000000000 : ℝ)^2185 ≤ (21281817079911/50000000000000 : ℝ)^1673 := by
    have hnat : (2599765589 : ℕ)^2185*50000000000000^1673 ≤ 21281817079911^1673*5000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2599765589 5000000000 21281817079911 50000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (27304819/50000000 : ℝ)^2185 ≤ (2268997255111/5000000000000 : ℝ)^1673 := by
    have hnat : (27304819 : ℕ)^2185*5000000000000^1673 ≤ 2268997255111^1673*50000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27304819 50000000 2268997255111 5000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-197930099/1000000000 : ℝ), (2599765589/5000000000 : ℝ), (27304819/50000000 : ℝ)] ![(3014105180909/25000000000000 : ℝ), (21281817079911/50000000000000 : ℝ), (2268997255111/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-197930099/1000000000 : ℝ)|^2185 ≤ (3014105180909/25000000000000 : ℝ)^1673
        have hw : |(-197930099/1000000000 : ℝ)|=(197930099/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2599765589/5000000000 : ℝ)|^2185 ≤ (21281817079911/50000000000000 : ℝ)^1673
        have hw : |(2599765589/5000000000 : ℝ)|=(2599765589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(27304819/50000000 : ℝ)|^2185 ≤ (2268997255111/5000000000000 : ℝ)^1673
        have hw : |(27304819/50000000 : ℝ)|=(27304819/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_s2_5 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (66158691/125000000 : ℝ)*x 0 + (-1852493893/10000000000 : ℝ)*x 1 + (2730481763/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66158691/125000000 : ℝ)^2185 ≤ (21781199024541/50000000000000 : ℝ)^1673 := by
    have hnat : (66158691 : ℕ)^2185*50000000000000^1673 ≤ 21781199024541^1673*125000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66158691 125000000 21781199024541 50000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1852493893/10000000000 : ℝ)^2185 ≤ (11057659812797/100000000000000 : ℝ)^1673 := by
    have hnat : (1852493893 : ℕ)^2185*100000000000000^1673 ≤ 11057659812797^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1852493893 10000000000 11057659812797 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2730481763/5000000000 : ℝ)^2185 ≤ (9075988425699/20000000000000 : ℝ)^1673 := by
    have hnat : (2730481763 : ℕ)^2185*20000000000000^1673 ≤ 9075988425699^1673*5000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2730481763 5000000000 9075988425699 20000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66158691/125000000 : ℝ), (-1852493893/10000000000 : ℝ), (2730481763/5000000000 : ℝ)] ![(21781199024541/50000000000000 : ℝ), (11057659812797/100000000000000 : ℝ), (9075988425699/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66158691/125000000 : ℝ)|^2185 ≤ (21781199024541/50000000000000 : ℝ)^1673
        have hw : |(66158691/125000000 : ℝ)|=(66158691/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1852493893/10000000000 : ℝ)|^2185 ≤ (11057659812797/100000000000000 : ℝ)^1673
        have hw : |(-1852493893/10000000000 : ℝ)|=(1852493893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2730481763/5000000000 : ℝ)|^2185 ≤ (9075988425699/20000000000000 : ℝ)^1673
        have hw : |(2730481763/5000000000 : ℝ)|=(2730481763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_s2_6 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1058539343/2000000000 : ℝ)*x 0 + (5460963503/10000000000 : ℝ)*x 1 + (-370498389/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058539343/2000000000 : ℝ)^2185 ≤ (4356241347469/10000000000000 : ℝ)^1673 := by
    have hnat : (1058539343 : ℕ)^2185*10000000000000^1673 ≤ 4356241347469^1673*2000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058539343 2000000000 4356241347469 10000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5460963503/10000000000 : ℝ)^2185 ≤ (11344985469719/25000000000000 : ℝ)^1673 := by
    have hnat : (5460963503 : ℕ)^2185*25000000000000^1673 ≤ 11344985469719^1673*10000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5460963503 10000000000 11344985469719 25000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (370498389/2000000000 : ℝ)^2185 ≤ (11057644626537/100000000000000 : ℝ)^1673 := by
    have hnat : (370498389 : ℕ)^2185*100000000000000^1673 ≤ 11057644626537^1673*2000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      370498389 2000000000 11057644626537 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058539343/2000000000 : ℝ), (5460963503/10000000000 : ℝ), (-370498389/2000000000 : ℝ)] ![(4356241347469/10000000000000 : ℝ), (11344985469719/25000000000000 : ℝ), (11057644626537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058539343/2000000000 : ℝ)|^2185 ≤ (4356241347469/10000000000000 : ℝ)^1673
        have hw : |(1058539343/2000000000 : ℝ)|=(1058539343/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5460963503/10000000000 : ℝ)|^2185 ≤ (11344985469719/25000000000000 : ℝ)^1673
        have hw : |(5460963503/10000000000 : ℝ)|=(5460963503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-370498389/2000000000 : ℝ)|^2185 ≤ (11057644626537/100000000000000 : ℝ)^1673
        have hw : |(-370498389/2000000000 : ℝ)|=(370498389/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1410_s2_7 (p : ℝ) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ)) (x : Fin 3 → ℝ) :
    (172182019/400000000 : ℝ)*x 0 + (2296880843/5000000000 : ℝ)*x 1 + (2016064673/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (172182019/400000000 : ℝ)^2185 ≤ (1662900067523/5000000000000 : ℝ)^1673 := by
    have hnat : (172182019 : ℕ)^2185*5000000000000^1673 ≤ 1662900067523^1673*400000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172182019 400000000 1662900067523 5000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2296880843/5000000000 : ℝ)^2185 ≤ (36205911924299/100000000000000 : ℝ)^1673 := by
    have hnat : (2296880843 : ℕ)^2185*100000000000000^1673 ≤ 36205911924299^1673*5000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2296880843 5000000000 36205911924299 100000000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2016064673/5000000000 : ℝ)^2185 ≤ (3817010838043/12500000000000 : ℝ)^1673 := by
    have hnat : (2016064673 : ℕ)^2185*12500000000000^1673 ≤ 3817010838043^1673*5000000000^2185 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2016064673 5000000000 3817010838043 12500000000000 2185 1673 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2185/512 : ℝ)) 2185 1673 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(172182019/400000000 : ℝ), (2296880843/5000000000 : ℝ), (2016064673/5000000000 : ℝ)] ![(1662900067523/5000000000000 : ℝ), (36205911924299/100000000000000 : ℝ), (3817010838043/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(172182019/400000000 : ℝ)|^2185 ≤ (1662900067523/5000000000000 : ℝ)^1673
        have hw : |(172182019/400000000 : ℝ)|=(172182019/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2296880843/5000000000 : ℝ)|^2185 ≤ (36205911924299/100000000000000 : ℝ)^1673
        have hw : |(2296880843/5000000000 : ℝ)|=(2296880843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2016064673/5000000000 : ℝ)|^2185 ≤ (3817010838043/12500000000000 : ℝ)^1673
        have hw : |(2016064673/5000000000 : ℝ)|=(2016064673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1410_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157414197/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9487/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7493/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1283/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15859/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9487/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (7493/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9487/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (7493/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9487/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (7493/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9487/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (7493/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9487/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (7493/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9487/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (7493/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (7493/100000 : ℝ) ^ (4369/1024 : ℝ) ≤ (1579808296943357/100000000000000000000 : ℝ) := by
    have hpowers : (7493/100000 : ℝ)^4369 ≤ (1579808296943357/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7493 : ℕ)^4369*100000000000000000000^1024 ≤ 1579808296943357^1024*100000^4369 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7493 100000 1579808296943357 100000000000000000000 4369 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7493/100000 : ℝ)) (X := (1579808296943357/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4369 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (9487/50000 : ℝ) ^ (4369/1024 : ℝ) ≤ (83213084179430669/100000000000000000000 : ℝ) := by
    have hpowers : (9487/50000 : ℝ)^4369 ≤ (83213084179430669/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9487 : ℕ)^4369*100000000000000000000^1024 ≤ 83213084179430669^1024*50000^4369 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9487 50000 83213084179430669 100000000000000000000 4369 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9487/50000 : ℝ)) (X := (83213084179430669/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4369 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001579808296943357/50000000000000000000 : ℝ) ≤ (2500018513437051/2500000000000000 : ℝ) ^ (4369/1024 : ℝ) := by
    have hpowers : (50001579808296943357/50000000000000000000 : ℝ)^1024 ≤ (2500018513437051/2500000000000000 : ℝ)^4369 := by
      have hnat : (50001579808296943357 : ℕ)^1024*2500000000000000^4369 ≤ 2500018513437051^4369*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001579808296943357 50000000000000000000 2500018513437051 2500000000000000 1024 4369 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500018513437051/2500000000000000 : ℝ)) (X := (50001579808296943357/50000000000000000000 : ℝ)) (by norm_num) 4369 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50042396446238187013/50000000000000000000 : ℝ) ≤ (10001986718973049/10000000000000000 : ℝ) ^ (4369/1024 : ℝ) := by
    have hpowers : (50042396446238187013/50000000000000000000 : ℝ)^1024 ≤ (10001986718973049/10000000000000000 : ℝ)^4369 := by
      have hnat : (50042396446238187013 : ℕ)^1024*10000000000000000^4369 ≤ 10001986718973049^4369*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50042396446238187013 50000000000000000000 10001986718973049 10000000000000000 1024 4369 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001986718973049/10000000000000000 : ℝ)) (X := (50042396446238187013/50000000000000000000 : ℝ)) (by norm_num) 4369 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50083213084179430669/50000000000000000000 : ℝ) ≤ (5001949692098947/5000000000000000 : ℝ) ^ (4369/1024 : ℝ) := by
    have hpowers : (50083213084179430669/50000000000000000000 : ℝ)^1024 ≤ (5001949692098947/5000000000000000 : ℝ)^4369 := by
      have hnat : (50083213084179430669 : ℕ)^1024*5000000000000000^4369 ≤ 5001949692098947^4369*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50083213084179430669 50000000000000000000 5001949692098947 5000000000000000 1024 4369 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001949692098947/5000000000000000 : ℝ)) (X := (50083213084179430669/50000000000000000000 : ℝ)) (by norm_num) 4369 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1579808296943357/100000000000000000000 : ℝ) ≤ ((57391093505011801477/57405000000000000000 : ℝ)+2*(382533044969/229620000000000 : ℝ)*(7493/100000 : ℝ))^(4369/1024 : ℝ) := by
    rw [show (57391093505011801477/57405000000000000000 : ℝ)+2*(382533044969/229620000000000 : ℝ)*(7493/100000 : ℝ)=(2500018513437051/2500000000000000 : ℝ) by norm_num, show 1+2*(1579808296943357/100000000000000000000 : ℝ)=(50001579808296943357/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(83213084179430669/100000000000000000000 : ℝ)+(1579808296943357/100000000000000000000 : ℝ) ≤ ((57391093505011801477/57405000000000000000 : ℝ)+(382533044969/229620000000000 : ℝ)*((9487/50000 : ℝ)+(7493/100000 : ℝ)))^(4369/1024 : ℝ) := by
    rw [show (57391093505011801477/57405000000000000000 : ℝ)+(382533044969/229620000000000 : ℝ)*((9487/50000 : ℝ)+(7493/100000 : ℝ))=(10001986718973049/10000000000000000 : ℝ) by norm_num, show 1+(83213084179430669/100000000000000000000 : ℝ)+(1579808296943357/100000000000000000000 : ℝ)=(50042396446238187013/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(83213084179430669/100000000000000000000 : ℝ) ≤ ((57391093505011801477/57405000000000000000 : ℝ)+2*(382533044969/229620000000000 : ℝ)*(9487/50000 : ℝ))^(4369/1024 : ℝ) := by
    rw [show (57391093505011801477/57405000000000000000 : ℝ)+2*(382533044969/229620000000000 : ℝ)*(9487/50000 : ℝ)=(5001949692098947/5000000000000000 : ℝ) by norm_num, show 1+2*(83213084179430669/100000000000000000000 : ℝ)=(50083213084179430669/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (57391093505011801477/57405000000000000000 : ℝ)*(X 1 0+X 2 0)+(382533044969/229620000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4369/1024 : ℝ)) (lo := (7493/100000 : ℝ)) (hi := (9487/50000 : ℝ)) (c := (57391093505011801477/57405000000000000000 : ℝ)) (alpha := (382533044969/229620000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (57391093505011801477/57405000000000000000 : ℝ)*(X 0 1+X 2 1)+(382533044969/229620000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4369/1024 : ℝ)) (lo := (7493/100000 : ℝ)) (hi := (9487/50000 : ℝ)) (c := (57391093505011801477/57405000000000000000 : ℝ)) (alpha := (382533044969/229620000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (57391093505011801477/57405000000000000000 : ℝ)*(X 0 2+X 1 2)+(382533044969/229620000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4369/1024 : ℝ)) (lo := (7493/100000 : ℝ)) (hi := (9487/50000 : ℝ)) (c := (57391093505011801477/57405000000000000000 : ℝ)) (alpha := (382533044969/229620000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-989626031/5000000000 : ℝ)*X 0 0+(5462519447/10000000000 : ℝ)*X 0 1+(1299497067/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2680678581/5000000000 : ℝ)*X 1 0+(-2115468827/10000000000 : ℝ)*X 1 1+(1299497061/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5361356909/10000000000 : ℝ)*X 2 0+(5197988529/10000000000 : ℝ)*X 2 1+(-2115468787/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((860888841/2000000000 : ℝ)*X 0 0+(1007196959/2500000000 : ℝ)*X 0 1+(459707587/1000000000 : ℝ)*X 0 2+(860888841/2000000000 : ℝ)*X 1 0+(1007196959/2500000000 : ℝ)*X 1 1+(459707587/1000000000 : ℝ)*X 1 2+(860888841/2000000000 : ℝ)*X 2 0+(1007196959/2500000000 : ℝ)*X 2 1+(459707587/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-197930099/1000000000 : ℝ)*X 0 0+(2599765589/5000000000 : ℝ)*X 0 1+(27304819/50000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((66158691/125000000 : ℝ)*X 1 0+(-1852493893/10000000000 : ℝ)*X 1 1+(2730481763/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1058539343/2000000000 : ℝ)*X 2 0+(5460963503/10000000000 : ℝ)*X 2 1+(-370498389/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((172182019/400000000 : ℝ)*X 0 0+(2296880843/5000000000 : ℝ)*X 0 1+(2016064673/5000000000 : ℝ)*X 0 2+(172182019/400000000 : ℝ)*X 1 0+(2296880843/5000000000 : ℝ)*X 1 1+(2016064673/5000000000 : ℝ)*X 1 2+(172182019/400000000 : ℝ)*X 2 0+(2296880843/5000000000 : ℝ)*X 2 1+(2016064673/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1410_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (25014702119878653660513771/5375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (23077047/4000000000000 : ℝ)*(base19) + (31211503/12500000000000 : ℝ)*(base23) + (19950181/25000000000000 : ℝ)*(lower2) + (147083249/100000000000000 : ℝ)*(upper3) + (26720797/100000000000000 : ℝ)*(upper5) + (1384990292164353/50000000000000 : ℝ)*(major0) + (1384990292164353/50000000000000 : ℝ)*(major1) + (1384990292164353/50000000000000 : ℝ)*(major2) + (1890139973590407/50000000000000 : ℝ)*(sp0) + (1890141983529259/50000000000000 : ℝ)*(sp1) + (378028429429267/10000000000000 : ℝ)*(sp2) + (1759673156092679/100000000000000 : ℝ)*(sp3) + (4596803879/100000000000000 : ℝ)*(sp4) + (1656725047/50000000000000 : ℝ)*(sp7) + (879838234771387/50000000000000 : ℝ)*(f.failure) + (1890142271992347/50000000000000 : ℝ)*(f.sum) + (24318654963929/3827000000000000000000000000 : ℝ)*base65 + (8280236269178133127/956750000000000000000000000000000 : ℝ)*base67 + (8003731541011633127/956750000000000000000000000000000 : ℝ)*base69 + (390401878465383127/956750000000000000000000000000000 : ℝ)*base71 + (3997544614101/956750000000000000000000000 : ℝ)*base73 + (1620017743258366873/956750000000000000000000000000000 : ℝ)*base76 + (2284622300145883127/956750000000000000000000000000000 : ℝ)*base77 + (2738321593814366873/956750000000000000000000000000000 : ℝ)*base80 + (2368172047681/382700000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (63181239/5000000000000000000000 : ℝ)*base89 + (63181239/5000000000000000000000 : ℝ)*base91 + (63181239/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (543879272815304314889611479/478375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (126882237/50000000000000 : ℝ)*(base19) + (657346151/50000000000000 : ℝ)*(base23) + (6848597/3125000000000 : ℝ)*(lower2) + (2075451/20000000000000 : ℝ)*(upper3) + (44318827/100000000000000 : ℝ)*(lower4) + (1401404366576391/50000000000000 : ℝ)*(major0) + (1401404366576391/50000000000000 : ℝ)*(major1) + (1401404366576391/50000000000000 : ℝ)*(major2) + (27301604857/100000000000000 : ℝ)*(sp2) + (166752549/12500000000000 : ℝ)*(sp3) + (1912543164282543/50000000000000 : ℝ)*(sp4) + (956271518700153/25000000000000 : ℝ)*(sp5) + (1912528856133963/50000000000000 : ℝ)*(sp6) + (1780529765822389/100000000000000 : ℝ)*(sp7) + (1780531099842781/100000000000000 : ℝ)*(f.failure) + (1912543164282543/50000000000000 : ℝ)*(f.sum) + (10971691502279/3827000000000000000000000000 : ℝ)*base66 + (2498353543822793169/956750000000000000000000000000000 : ℝ)*base67 + (1791636226042793169/956750000000000000000000000000000 : ℝ)*base69 + (1043008951931043169/956750000000000000000000000000000 : ℝ)*base71 + (44408596441/956750000000000000000000000 : ℝ)*base74 + (2495238679636793169/956750000000000000000000000000000 : ℝ)*base75 + (3022085799565793169/956750000000000000000000000000000 : ℝ)*base77 + (9615675324917543169/956750000000000000000000000000000 : ℝ)*base79 + (351115204751/3827000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (2638143/10000000000000000000000 : ℝ)*base90 + (2638143/10000000000000000000000 : ℝ)*base92 + (2638143/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1410_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157414197/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9487/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7493/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1283/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15859/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1410_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1410_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157414197/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1283/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15859/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1410_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1410_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1410_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4369/1024 : ℝ) ≤ p) (hpb : p ≤ (2185/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157414197/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1283/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15859/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1410_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
