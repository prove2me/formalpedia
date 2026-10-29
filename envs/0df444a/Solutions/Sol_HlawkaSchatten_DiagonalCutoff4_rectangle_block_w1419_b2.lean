-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1419_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:51:23.634814+00:00
-- url     : https://prove2.me/submissions/d779d900-ba5e-4250-8805-efac1d2660d9

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
theorem support_rectangle_w1419_s6_0 (p : ℝ) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1979272469/10000000000 : ℝ)*x 0 + (2704370041/5000000000 : ℝ)*x 1 + (5246673433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1979272469/10000000000 : ℝ)^4379 ≤ (482889493503/4000000000000 : ℝ)^3355 := by
    have hnat : (1979272469 : ℕ)^4379*4000000000000^3355 ≤ 482889493503^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1979272469 10000000000 482889493503 4000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2704370041/5000000000 : ℝ)^4379 ≤ (44836607952533/100000000000000 : ℝ)^3355 := by
    have hnat : (2704370041 : ℕ)^4379*100000000000000^3355 ≤ 44836607952533^3355*5000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704370041 5000000000 44836607952533 100000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246673433/10000000000 : ℝ)^4379 ≤ (43091154691057/100000000000000 : ℝ)^3355 := by
    have hnat : (5246673433 : ℕ)^4379*100000000000000^3355 ≤ 43091154691057^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246673433 10000000000 43091154691057 100000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4379/1024 : ℝ)) 4379 3355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1979272469/10000000000 : ℝ), (2704370041/5000000000 : ℝ), (5246673433/10000000000 : ℝ)] ![(482889493503/4000000000000 : ℝ), (44836607952533/100000000000000 : ℝ), (43091154691057/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1979272469/10000000000 : ℝ)|^4379 ≤ (482889493503/4000000000000 : ℝ)^3355
        have hw : |(-1979272469/10000000000 : ℝ)|=(1979272469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2704370041/5000000000 : ℝ)|^4379 ≤ (44836607952533/100000000000000 : ℝ)^3355
        have hw : |(2704370041/5000000000 : ℝ)|=(2704370041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246673433/10000000000 : ℝ)|^4379 ≤ (43091154691057/100000000000000 : ℝ)^3355
        have hw : |(5246673433/10000000000 : ℝ)|=(5246673433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1419_s6_1 (p : ℝ) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673768477/5000000000 : ℝ)*x 0 + (-1030895089/5000000000 : ℝ)*x 1 + (655834179/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673768477/5000000000 : ℝ)^4379 ≤ (4417554915637/10000000000000 : ℝ)^3355 := by
    have hnat : (2673768477 : ℕ)^4379*10000000000000^3355 ≤ 4417554915637^3355*5000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673768477 5000000000 4417554915637 10000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1030895089/5000000000 : ℝ)^4379 ≤ (3183324037917/25000000000000 : ℝ)^3355 := by
    have hnat : (1030895089 : ℕ)^4379*25000000000000^3355 ≤ 3183324037917^3355*5000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030895089 5000000000 3183324037917 25000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655834179/1250000000 : ℝ)^4379 ≤ (43091154680337/100000000000000 : ℝ)^3355 := by
    have hnat : (655834179 : ℕ)^4379*100000000000000^3355 ≤ 43091154680337^3355*1250000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655834179 1250000000 43091154680337 100000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4379/1024 : ℝ)) 4379 3355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673768477/5000000000 : ℝ), (-1030895089/5000000000 : ℝ), (655834179/1250000000 : ℝ)] ![(4417554915637/10000000000000 : ℝ), (3183324037917/25000000000000 : ℝ), (43091154680337/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673768477/5000000000 : ℝ)|^4379 ≤ (4417554915637/10000000000000 : ℝ)^3355
        have hw : |(2673768477/5000000000 : ℝ)|=(2673768477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1030895089/5000000000 : ℝ)|^4379 ≤ (3183324037917/25000000000000 : ℝ)^3355
        have hw : |(-1030895089/5000000000 : ℝ)|=(1030895089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(655834179/1250000000 : ℝ)|^4379 ≤ (43091154680337/100000000000000 : ℝ)^3355
        have hw : |(655834179/1250000000 : ℝ)|=(655834179/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1419_s6_2 (p : ℝ) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673768477/5000000000 : ℝ)*x 0 + (5246673433/10000000000 : ℝ)*x 1 + (-2061790177/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673768477/5000000000 : ℝ)^4379 ≤ (4417554915637/10000000000000 : ℝ)^3355 := by
    have hnat : (2673768477 : ℕ)^4379*10000000000000^3355 ≤ 4417554915637^3355*5000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673768477 5000000000 4417554915637 10000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246673433/10000000000 : ℝ)^4379 ≤ (43091154691057/100000000000000 : ℝ)^3355 := by
    have hnat : (5246673433 : ℕ)^4379*100000000000000^3355 ≤ 43091154691057^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246673433 10000000000 43091154691057 100000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2061790177/10000000000 : ℝ)^4379 ≤ (12733296143607/100000000000000 : ℝ)^3355 := by
    have hnat : (2061790177 : ℕ)^4379*100000000000000^3355 ≤ 12733296143607^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2061790177 10000000000 12733296143607 100000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4379/1024 : ℝ)) 4379 3355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673768477/5000000000 : ℝ), (5246673433/10000000000 : ℝ), (-2061790177/10000000000 : ℝ)] ![(4417554915637/10000000000000 : ℝ), (43091154691057/100000000000000 : ℝ), (12733296143607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673768477/5000000000 : ℝ)|^4379 ≤ (4417554915637/10000000000000 : ℝ)^3355
        have hw : |(2673768477/5000000000 : ℝ)|=(2673768477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246673433/10000000000 : ℝ)|^4379 ≤ (43091154691057/100000000000000 : ℝ)^3355
        have hw : |(5246673433/10000000000 : ℝ)|=(5246673433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2061790177/10000000000 : ℝ)|^4379 ≤ (12733296143607/100000000000000 : ℝ)^3355
        have hw : |(-2061790177/10000000000 : ℝ)|=(2061790177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1419_s6_3 (p : ℝ) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4306879797/10000000000 : ℝ)*x 0 + (2067709573/5000000000 : ℝ)*x 1 + (4484739359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4306879797/10000000000 : ℝ)^4379 ≤ (16652265962273/50000000000000 : ℝ)^3355 := by
    have hnat : (4306879797 : ℕ)^4379*50000000000000^3355 ≤ 16652265962273^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4306879797 10000000000 16652265962273 50000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2067709573/5000000000 : ℝ)^4379 ≤ (15792290634891/50000000000000 : ℝ)^3355 := by
    have hnat : (2067709573 : ℕ)^4379*50000000000000^3355 ≤ 15792290634891^3355*5000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2067709573 5000000000 15792290634891 50000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4484739359/10000000000 : ℝ)^4379 ≤ (35110886794967/100000000000000 : ℝ)^3355 := by
    have hnat : (4484739359 : ℕ)^4379*100000000000000^3355 ≤ 35110886794967^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4484739359 10000000000 35110886794967 100000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4379/1024 : ℝ)) 4379 3355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4306879797/10000000000 : ℝ), (2067709573/5000000000 : ℝ), (4484739359/10000000000 : ℝ)] ![(16652265962273/50000000000000 : ℝ), (15792290634891/50000000000000 : ℝ), (35110886794967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4306879797/10000000000 : ℝ)|^4379 ≤ (16652265962273/50000000000000 : ℝ)^3355
        have hw : |(4306879797/10000000000 : ℝ)|=(4306879797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2067709573/5000000000 : ℝ)|^4379 ≤ (15792290634891/50000000000000 : ℝ)^3355
        have hw : |(2067709573/5000000000 : ℝ)|=(2067709573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4484739359/10000000000 : ℝ)|^4379 ≤ (35110886794967/100000000000000 : ℝ)^3355
        have hw : |(4484739359/10000000000 : ℝ)|=(4484739359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1419_s6_4 (p : ℝ) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-494820919/2500000000 : ℝ)*x 0 + (5247257597/10000000000 : ℝ)*x 1 + (1352038263/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (494820919/2500000000 : ℝ)^4379 ≤ (12072326555959/100000000000000 : ℝ)^3355 := by
    have hnat : (494820919 : ℕ)^4379*100000000000000^3355 ≤ 12072326555959^3355*2500000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      494820919 2500000000 12072326555959 100000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247257597/10000000000 : ℝ)^4379 ≤ (43097416916343/100000000000000 : ℝ)^3355 := by
    have hnat : (5247257597 : ℕ)^4379*100000000000000^3355 ≤ 43097416916343^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247257597 10000000000 43097416916343 100000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1352038263/2500000000 : ℝ)^4379 ≤ (22415128256551/50000000000000 : ℝ)^3355 := by
    have hnat : (1352038263 : ℕ)^4379*50000000000000^3355 ≤ 22415128256551^3355*2500000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352038263 2500000000 22415128256551 50000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4379/1024 : ℝ)) 4379 3355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-494820919/2500000000 : ℝ), (5247257597/10000000000 : ℝ), (1352038263/2500000000 : ℝ)] ![(12072326555959/100000000000000 : ℝ), (43097416916343/100000000000000 : ℝ), (22415128256551/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-494820919/2500000000 : ℝ)|^4379 ≤ (12072326555959/100000000000000 : ℝ)^3355
        have hw : |(-494820919/2500000000 : ℝ)|=(494820919/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247257597/10000000000 : ℝ)|^4379 ≤ (43097416916343/100000000000000 : ℝ)^3355
        have hw : |(5247257597/10000000000 : ℝ)|=(5247257597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1352038263/2500000000 : ℝ)|^4379 ≤ (22415128256551/50000000000000 : ℝ)^3355
        have hw : |(1352038263/2500000000 : ℝ)|=(1352038263/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1419_s6_5 (p : ℝ) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305445717/10000000000 : ℝ)*x 0 + (-237538801/1250000000 : ℝ)*x 1 + (2704076517/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305445717/10000000000 : ℝ)^4379 ≤ (43722255825931/100000000000000 : ℝ)^3355 := by
    have hnat : (5305445717 : ℕ)^4379*100000000000000^3355 ≤ 43722255825931^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305445717 10000000000 43722255825931 100000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (237538801/1250000000 : ℝ)^4379 ≤ (2289497569393/20000000000000 : ℝ)^3355 := by
    have hnat : (237538801 : ℕ)^4379*20000000000000^3355 ≤ 2289497569393^3355*1250000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      237538801 1250000000 2289497569393 20000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2704076517/5000000000 : ℝ)^4379 ≤ (2801891019897/6250000000000 : ℝ)^3355 := by
    have hnat : (2704076517 : ℕ)^4379*6250000000000^3355 ≤ 2801891019897^3355*5000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704076517 5000000000 2801891019897 6250000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4379/1024 : ℝ)) 4379 3355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305445717/10000000000 : ℝ), (-237538801/1250000000 : ℝ), (2704076517/5000000000 : ℝ)] ![(43722255825931/100000000000000 : ℝ), (2289497569393/20000000000000 : ℝ), (2801891019897/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305445717/10000000000 : ℝ)|^4379 ≤ (43722255825931/100000000000000 : ℝ)^3355
        have hw : |(5305445717/10000000000 : ℝ)|=(5305445717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-237538801/1250000000 : ℝ)|^4379 ≤ (2289497569393/20000000000000 : ℝ)^3355
        have hw : |(-237538801/1250000000 : ℝ)|=(237538801/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2704076517/5000000000 : ℝ)|^4379 ≤ (2801891019897/6250000000000 : ℝ)^3355
        have hw : |(2704076517/5000000000 : ℝ)|=(2704076517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1419_s6_6 (p : ℝ) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326361497/2500000000 : ℝ)*x 0 + (5408152619/10000000000 : ℝ)*x 1 + (-118769413/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326361497/2500000000 : ℝ)^4379 ≤ (4372225874089/10000000000000 : ℝ)^3355 := by
    have hnat : (1326361497 : ℕ)^4379*10000000000000^3355 ≤ 4372225874089^3355*2500000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326361497 2500000000 4372225874089 10000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5408152619/10000000000 : ℝ)^4379 ≤ (22415125914143/50000000000000 : ℝ)^3355 := by
    have hnat : (5408152619 : ℕ)^4379*50000000000000^3355 ≤ 22415125914143^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408152619 10000000000 22415125914143 50000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (118769413/625000000 : ℝ)^4379 ≤ (11447489419491/100000000000000 : ℝ)^3355 := by
    have hnat : (118769413 : ℕ)^4379*100000000000000^3355 ≤ 11447489419491^3355*625000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      118769413 625000000 11447489419491 100000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4379/1024 : ℝ)) 4379 3355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326361497/2500000000 : ℝ), (5408152619/10000000000 : ℝ), (-118769413/625000000 : ℝ)] ![(4372225874089/10000000000000 : ℝ), (22415125914143/50000000000000 : ℝ), (11447489419491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326361497/2500000000 : ℝ)|^4379 ≤ (4372225874089/10000000000000 : ℝ)^3355
        have hw : |(1326361497/2500000000 : ℝ)|=(1326361497/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5408152619/10000000000 : ℝ)|^4379 ≤ (22415125914143/50000000000000 : ℝ)^3355
        have hw : |(5408152619/10000000000 : ℝ)|=(5408152619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-118769413/625000000 : ℝ)|^4379 ≤ (11447489419491/100000000000000 : ℝ)^3355
        have hw : |(-118769413/625000000 : ℝ)|=(118769413/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1419_s6_7 (p : ℝ) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4306903881/10000000000 : ℝ)*x 0 + (4483480897/10000000000 : ℝ)*x 1 + (827336929/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4306903881/10000000000 : ℝ)^4379 ≤ (16652387503047/50000000000000 : ℝ)^3355 := by
    have hnat : (4306903881 : ℕ)^4379*50000000000000^3355 ≤ 16652387503047^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4306903881 10000000000 16652387503047 50000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4483480897/10000000000 : ℝ)^4379 ≤ (7019605551167/20000000000000 : ℝ)^3355 := by
    have hnat : (4483480897 : ℕ)^4379*20000000000000^3355 ≤ 7019605551167^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4483480897 10000000000 7019605551167 20000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (827336929/2000000000 : ℝ)^4379 ≤ (3949649652971/12500000000000 : ℝ)^3355 := by
    have hnat : (827336929 : ℕ)^4379*12500000000000^3355 ≤ 3949649652971^3355*2000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      827336929 2000000000 3949649652971 12500000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4379/1024 : ℝ)) 4379 3355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4306903881/10000000000 : ℝ), (4483480897/10000000000 : ℝ), (827336929/2000000000 : ℝ)] ![(16652387503047/50000000000000 : ℝ), (7019605551167/20000000000000 : ℝ), (3949649652971/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4306903881/10000000000 : ℝ)|^4379 ≤ (16652387503047/50000000000000 : ℝ)^3355
        have hw : |(4306903881/10000000000 : ℝ)|=(4306903881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4483480897/10000000000 : ℝ)|^4379 ≤ (7019605551167/20000000000000 : ℝ)^3355
        have hw : |(4483480897/10000000000 : ℝ)|=(4483480897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(827336929/2000000000 : ℝ)|^4379 ≤ (3949649652971/12500000000000 : ℝ)^3355
        have hw : |(827336929/2000000000 : ℝ)|=(827336929/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1419_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78885271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3689/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2263/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (11319/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (461/3125 : ℝ)*pair X 0 0 := by
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
  have lower0 : (2263/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3689/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2263/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3689/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2263/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3689/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2263/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3689/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2263/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3689/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2263/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2263/20000 : ℝ) ^ (2189/512 : ℝ) ≤ (8995049766818231/100000000000000000000 : ℝ) := by
    have hpowers : (2263/20000 : ℝ)^2189 ≤ (8995049766818231/100000000000000000000 : ℝ)^512 := by
      have hnat : (2263 : ℕ)^2189*100000000000000000000^512 ≤ 8995049766818231^512*20000^2189 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2263 20000 8995049766818231 100000000000000000000 2189 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2263/20000 : ℝ)) (X := (8995049766818231/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2189 512 (by norm_num) hpowers
    exact h
  have hpowhi : (3689/25000 : ℝ) ^ (2189/512 : ℝ) ≤ (13995433233123253/50000000000000000000 : ℝ) := by
    have hpowers : (3689/25000 : ℝ)^2189 ≤ (13995433233123253/50000000000000000000 : ℝ)^512 := by
      have hnat : (3689 : ℕ)^2189*50000000000000000000^512 ≤ 13995433233123253^512*25000^2189 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3689 25000 13995433233123253 50000000000000000000 2189 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3689/25000 : ℝ)) (X := (13995433233123253/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2189 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008995049766818231/50000000000000000000 : ℝ) ≤ (2500105188399847/2500000000000000 : ℝ) ^ (2189/512 : ℝ) := by
    have hpowers : (50008995049766818231/50000000000000000000 : ℝ)^512 ≤ (2500105188399847/2500000000000000 : ℝ)^2189 := by
      have hnat : (50008995049766818231 : ℕ)^512*2500000000000000^2189 ≤ 2500105188399847^2189*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008995049766818231 50000000000000000000 2500105188399847 2500000000000000 512 2189 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500105188399847/2500000000000000 : ℝ)) (X := (50008995049766818231/50000000000000000000 : ℝ)) (by norm_num) 2189 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100036985916233064737/100000000000000000000 : ℝ) ≤ (10000864966049469/10000000000000000 : ℝ) ^ (2189/512 : ℝ) := by
    have hpowers : (100036985916233064737/100000000000000000000 : ℝ)^512 ≤ (10000864966049469/10000000000000000 : ℝ)^2189 := by
      have hnat : (100036985916233064737 : ℕ)^512*10000000000000000^2189 ≤ 10000864966049469^2189*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100036985916233064737 100000000000000000000 10000864966049469 10000000000000000 512 2189 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000864966049469/10000000000000000 : ℝ)) (X := (100036985916233064737/100000000000000000000 : ℝ)) (by norm_num) 2189 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25013995433233123253/25000000000000000000 : ℝ) ≤ (200026183569991/200000000000000 : ℝ) ^ (2189/512 : ℝ) := by
    have hpowers : (25013995433233123253/25000000000000000000 : ℝ)^512 ≤ (200026183569991/200000000000000 : ℝ)^2189 := by
      have hnat : (25013995433233123253 : ℕ)^512*200000000000000^2189 ≤ 200026183569991^2189*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013995433233123253 25000000000000000000 200026183569991 200000000000000 512 2189 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200026183569991/200000000000000 : ℝ)) (X := (25013995433233123253/25000000000000000000 : ℝ)) (by norm_num) 2189 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8995049766818231/100000000000000000000 : ℝ) ≤ ((554861214280486469/555000000000000000 : ℝ)+2*(444212450081/344100000000000 : ℝ)*(2263/20000 : ℝ))^(2189/512 : ℝ) := by
    rw [show (554861214280486469/555000000000000000 : ℝ)+2*(444212450081/344100000000000 : ℝ)*(2263/20000 : ℝ)=(2500105188399847/2500000000000000 : ℝ) by norm_num, show 1+2*(8995049766818231/100000000000000000000 : ℝ)=(50008995049766818231/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13995433233123253/50000000000000000000 : ℝ)+(8995049766818231/100000000000000000000 : ℝ) ≤ ((554861214280486469/555000000000000000 : ℝ)+(444212450081/344100000000000 : ℝ)*((3689/25000 : ℝ)+(2263/20000 : ℝ)))^(2189/512 : ℝ) := by
    rw [show (554861214280486469/555000000000000000 : ℝ)+(444212450081/344100000000000 : ℝ)*((3689/25000 : ℝ)+(2263/20000 : ℝ))=(10000864966049469/10000000000000000 : ℝ) by norm_num, show 1+(13995433233123253/50000000000000000000 : ℝ)+(8995049766818231/100000000000000000000 : ℝ)=(100036985916233064737/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13995433233123253/50000000000000000000 : ℝ) ≤ ((554861214280486469/555000000000000000 : ℝ)+2*(444212450081/344100000000000 : ℝ)*(3689/25000 : ℝ))^(2189/512 : ℝ) := by
    rw [show (554861214280486469/555000000000000000 : ℝ)+2*(444212450081/344100000000000 : ℝ)*(3689/25000 : ℝ)=(200026183569991/200000000000000 : ℝ) by norm_num, show 1+2*(13995433233123253/50000000000000000000 : ℝ)=(25013995433233123253/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (554861214280486469/555000000000000000 : ℝ)*(X 1 0+X 2 0)+(444212450081/344100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2189/512 : ℝ)) (lo := (2263/20000 : ℝ)) (hi := (3689/25000 : ℝ)) (c := (554861214280486469/555000000000000000 : ℝ)) (alpha := (444212450081/344100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (554861214280486469/555000000000000000 : ℝ)*(X 0 1+X 2 1)+(444212450081/344100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2189/512 : ℝ)) (lo := (2263/20000 : ℝ)) (hi := (3689/25000 : ℝ)) (c := (554861214280486469/555000000000000000 : ℝ)) (alpha := (444212450081/344100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (554861214280486469/555000000000000000 : ℝ)*(X 0 2+X 1 2)+(444212450081/344100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2189/512 : ℝ)) (lo := (2263/20000 : ℝ)) (hi := (3689/25000 : ℝ)) (c := (554861214280486469/555000000000000000 : ℝ)) (alpha := (444212450081/344100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1979272469/10000000000 : ℝ)*X 0 0+(2704370041/5000000000 : ℝ)*X 0 1+(5246673433/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1419_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673768477/5000000000 : ℝ)*X 1 0+(-1030895089/5000000000 : ℝ)*X 1 1+(655834179/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1419_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673768477/5000000000 : ℝ)*X 2 0+(5246673433/10000000000 : ℝ)*X 2 1+(-2061790177/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1419_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4306879797/10000000000 : ℝ)*X 0 0+(2067709573/5000000000 : ℝ)*X 0 1+(4484739359/10000000000 : ℝ)*X 0 2+(4306879797/10000000000 : ℝ)*X 1 0+(2067709573/5000000000 : ℝ)*X 1 1+(4484739359/10000000000 : ℝ)*X 1 2+(4306879797/10000000000 : ℝ)*X 2 0+(2067709573/5000000000 : ℝ)*X 2 1+(4484739359/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1419_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-494820919/2500000000 : ℝ)*X 0 0+(5247257597/10000000000 : ℝ)*X 0 1+(1352038263/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1419_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305445717/10000000000 : ℝ)*X 1 0+(-237538801/1250000000 : ℝ)*X 1 1+(2704076517/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1419_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326361497/2500000000 : ℝ)*X 2 0+(5408152619/10000000000 : ℝ)*X 2 1+(-118769413/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1419_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4306903881/10000000000 : ℝ)*X 0 0+(4483480897/10000000000 : ℝ)*X 0 1+(827336929/2000000000 : ℝ)*X 0 2+(4306903881/10000000000 : ℝ)*X 1 0+(4483480897/10000000000 : ℝ)*X 1 1+(827336929/2000000000 : ℝ)*X 1 2+(4306903881/10000000000 : ℝ)*X 2 0+(4483480897/10000000000 : ℝ)*X 2 1+(827336929/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1419_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (84038810378778350293485433/9250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (830041331/50000000000000 : ℝ)*(base19) + (386773751/25000000000000 : ℝ)*(base23) + (7552571/12500000000000 : ℝ)*(lower2) + (113059341/50000000000000 : ℝ)*(upper3) + (145254637/100000000000000 : ℝ)*(upper5) + (4516554227235643/100000000000000 : ℝ)*(major0) + (4516554227235643/100000000000000 : ℝ)*(major1) + (4516554227235643/100000000000000 : ℝ)*(major2) + (6170337247843013/100000000000000 : ℝ)*(sp0) + (617037041294677/10000000000000 : ℝ)*(sp1) + (1542592631483607/25000000000000 : ℝ)*(sp2) + (1431359306139551/50000000000000 : ℝ)*(sp3) + (1741259321/5000000000000 : ℝ)*(sp4) + (8733160093/50000000000000 : ℝ)*(sp7) + (357842009824911/12500000000000 : ℝ)*(f.failure) + (771296509128679/12500000000000 : ℝ)*(f.sum) + (5774148275221/2150625000000000000000000000 : ℝ)*base65 + (5025824636166466141/573500000000000000000000000000000 : ℝ)*base68 + (5375713268165966141/573500000000000000000000000000000 : ℝ)*base70 + (1963804567633533859/573500000000000000000000000000000 : ℝ)*base71 + (7603296499087/17205000000000000000000000000 : ℝ)*base74 + (166884839265533859/573500000000000000000000000000000 : ℝ)*base75 + (3970530542331533859/573500000000000000000000000000000 : ℝ)*base77 + (1199706248260533859/573500000000000000000000000000000 : ℝ)*base79 + (18195677902477/17205000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1964119/625000000000000000000 : ℝ)*base90 + (1964119/625000000000000000000 : ℝ)*base92 + (1964119/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5756598015621864483646797/775000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1171503887/100000000000000 : ℝ)*(base19) + (1505076057/100000000000000 : ℝ)*(base23) + (21662311/5000000000000 : ℝ)*(lower1) + (15748687/100000000000000 : ℝ)*(upper3) + (56271/195312500000 : ℝ)*(lower4) + (454935956416051/10000000000000 : ℝ)*(major0) + (454935956416051/10000000000000 : ℝ)*(major1) + (454935956416051/10000000000000 : ℝ)*(major2) + (4815122523/100000000000000 : ℝ)*(sp1) + (1590733941/100000000000000 : ℝ)*(sp3) + (1243037946718377/20000000000000 : ℝ)*(sp4) + (1553795936741369/25000000000000 : ℝ)*(sp5) + (6215188228515829/100000000000000 : ℝ)*(sp6) + (1441763778199783/50000000000000 : ℝ)*(sp7) + (1441764573566753/50000000000000 : ℝ)*(f.failure) + (1243037946718377/20000000000000 : ℝ)*(f.sum) + (86671362833/93000000000000000000000000 : ℝ)*base66 + (6504162549515599/1550000000000000000000000000000 : ℝ)*base67 + (31532535938284401/1550000000000000000000000000000 : ℝ)*base70 + (12093297657684401/1550000000000000000000000000000 : ℝ)*base72 + (34581714293/23250000000000000000000000 : ℝ)*base74 + (63751425093284401/1550000000000000000000000000000 : ℝ)*base76 + (52379755025584401/1550000000000000000000000000000 : ℝ)*base78 + (12044628550215599/1550000000000000000000000000000 : ℝ)*base79 + (2914425191/3720000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (3004937/2500000000000000000000 : ℝ)*base90 + (3004937/2500000000000000000000 : ℝ)*base92 + (3004937/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1419_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78885271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3689/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2263/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11319/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (461/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1419_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1419_s7_0 (p : ℝ) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-197927497/1000000000 : ℝ)*x 0 + (540871053/1000000000 : ℝ)*x 1 + (1311675351/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (197927497/1000000000 : ℝ)^4379 ≤ (6036128623951/50000000000000 : ℝ)^3355 := by
    have hnat : (197927497 : ℕ)^4379*50000000000000^3355 ≤ 6036128623951^3355*1000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197927497 1000000000 6036128623951 50000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (540871053/1000000000 : ℝ)^4379 ≤ (44836288206199/100000000000000 : ℝ)^3355 := by
    have hnat : (540871053 : ℕ)^4379*100000000000000^3355 ≤ 44836288206199^3355*1000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540871053 1000000000 44836288206199 100000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311675351/2500000000 : ℝ)^4379 ≤ (21545727267357/50000000000000 : ℝ)^3355 := by
    have hnat : (1311675351 : ℕ)^4379*50000000000000^3355 ≤ 21545727267357^3355*2500000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311675351 2500000000 21545727267357 50000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4379/1024 : ℝ)) 4379 3355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-197927497/1000000000 : ℝ), (540871053/1000000000 : ℝ), (1311675351/2500000000 : ℝ)] ![(6036128623951/50000000000000 : ℝ), (44836288206199/100000000000000 : ℝ), (21545727267357/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-197927497/1000000000 : ℝ)|^4379 ≤ (6036128623951/50000000000000 : ℝ)^3355
        have hw : |(-197927497/1000000000 : ℝ)|=(197927497/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(540871053/1000000000 : ℝ)|^4379 ≤ (44836288206199/100000000000000 : ℝ)^3355
        have hw : |(540871053/1000000000 : ℝ)|=(540871053/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311675351/2500000000 : ℝ)|^4379 ≤ (21545727267357/50000000000000 : ℝ)^3355
        have hw : |(1311675351/2500000000 : ℝ)|=(1311675351/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1419_s7_1 (p : ℝ) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069505881/2000000000 : ℝ)*x 0 + (-515440911/2500000000 : ℝ)*x 1 + (5246700977/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069505881/2000000000 : ℝ)^4379 ≤ (138048336753/312500000000 : ℝ)^3355 := by
    have hnat : (1069505881 : ℕ)^4379*312500000000^3355 ≤ 138048336753^3355*2000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069505881 2000000000 138048336753 312500000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (515440911/2500000000 : ℝ)^4379 ≤ (6366541133251/50000000000000 : ℝ)^3355 := by
    have hnat : (515440911 : ℕ)^4379*50000000000000^3355 ≤ 6366541133251^3355*2500000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515440911 2500000000 6366541133251 50000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246700977/10000000000 : ℝ)^4379 ≤ (43091449957353/100000000000000 : ℝ)^3355 := by
    have hnat : (5246700977 : ℕ)^4379*100000000000000^3355 ≤ 43091449957353^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246700977 10000000000 43091449957353 100000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4379/1024 : ℝ)) 4379 3355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069505881/2000000000 : ℝ), (-515440911/2500000000 : ℝ), (5246700977/10000000000 : ℝ)] ![(138048336753/312500000000 : ℝ), (6366541133251/50000000000000 : ℝ), (43091449957353/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069505881/2000000000 : ℝ)|^4379 ≤ (138048336753/312500000000 : ℝ)^3355
        have hw : |(1069505881/2000000000 : ℝ)|=(1069505881/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-515440911/2500000000 : ℝ)|^4379 ≤ (6366541133251/50000000000000 : ℝ)^3355
        have hw : |(-515440911/2500000000 : ℝ)|=(515440911/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246700977/10000000000 : ℝ)|^4379 ≤ (43091449957353/100000000000000 : ℝ)^3355
        have hw : |(5246700977/10000000000 : ℝ)|=(5246700977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1419_s7_2 (p : ℝ) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347529449/10000000000 : ℝ)*x 0 + (5246701011/10000000000 : ℝ)*x 1 + (-103088177/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347529449/10000000000 : ℝ)^4379 ≤ (2208773411769/5000000000000 : ℝ)^3355 := by
    have hnat : (5347529449 : ℕ)^4379*5000000000000^3355 ≤ 2208773411769^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347529449 10000000000 2208773411769 5000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246701011/10000000000 : ℝ)^4379 ≤ (43091450321827/100000000000000 : ℝ)^3355 := by
    have hnat : (5246701011 : ℕ)^4379*100000000000000^3355 ≤ 43091450321827^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246701011 10000000000 43091450321827 100000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (103088177/500000000 : ℝ)^4379 ≤ (636654071409/5000000000000 : ℝ)^3355 := by
    have hnat : (103088177 : ℕ)^4379*5000000000000^3355 ≤ 636654071409^3355*500000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103088177 500000000 636654071409 5000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4379/1024 : ℝ)) 4379 3355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347529449/10000000000 : ℝ), (5246701011/10000000000 : ℝ), (-103088177/500000000 : ℝ)] ![(2208773411769/5000000000000 : ℝ), (43091450321827/100000000000000 : ℝ), (636654071409/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347529449/10000000000 : ℝ)|^4379 ≤ (2208773411769/5000000000000 : ℝ)^3355
        have hw : |(5347529449/10000000000 : ℝ)|=(5347529449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246701011/10000000000 : ℝ)|^4379 ≤ (43091450321827/100000000000000 : ℝ)^3355
        have hw : |(5246701011/10000000000 : ℝ)|=(5246701011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-103088177/500000000 : ℝ)|^4379 ≤ (636654071409/5000000000000 : ℝ)^3355
        have hw : |(-103088177/500000000 : ℝ)|=(103088177/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1419_s7_3 (p : ℝ) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2153440981/5000000000 : ℝ)*x 0 + (4135479547/10000000000 : ℝ)*x 1 + (560584787/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2153440981/5000000000 : ℝ)^4379 ≤ (3330455377603/10000000000000 : ℝ)^3355 := by
    have hnat : (2153440981 : ℕ)^4379*10000000000000^3355 ≤ 3330455377603^3355*5000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2153440981 5000000000 3330455377603 10000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4135479547/10000000000 : ℝ)^4379 ≤ (31585183389857/100000000000000 : ℝ)^3355 := by
    have hnat : (4135479547 : ℕ)^4379*100000000000000^3355 ≤ 31585183389857^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4135479547 10000000000 31585183389857 100000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (560584787/1250000000 : ℝ)^4379 ≤ (8777565706049/25000000000000 : ℝ)^3355 := by
    have hnat : (560584787 : ℕ)^4379*25000000000000^3355 ≤ 8777565706049^3355*1250000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560584787 1250000000 8777565706049 25000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4379/1024 : ℝ)) 4379 3355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2153440981/5000000000 : ℝ), (4135479547/10000000000 : ℝ), (560584787/1250000000 : ℝ)] ![(3330455377603/10000000000000 : ℝ), (31585183389857/100000000000000 : ℝ), (8777565706049/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2153440981/5000000000 : ℝ)|^4379 ≤ (3330455377603/10000000000000 : ℝ)^3355
        have hw : |(2153440981/5000000000 : ℝ)|=(2153440981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4135479547/10000000000 : ℝ)|^4379 ≤ (31585183389857/100000000000000 : ℝ)^3355
        have hw : |(4135479547/10000000000 : ℝ)|=(4135479547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(560584787/1250000000 : ℝ)|^4379 ≤ (8777565706049/25000000000000 : ℝ)^3355
        have hw : |(560584787/1250000000 : ℝ)|=(560584787/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1419_s7_4 (p : ℝ) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1979286661/10000000000 : ℝ)*x 0 + (5247284501/10000000000 : ℝ)*x 1 + (5408124199/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1979286661/10000000000 : ℝ)^4379 ≤ (482894012777/4000000000000 : ℝ)^3355 := by
    have hnat : (1979286661 : ℕ)^4379*4000000000000^3355 ≤ 482894012777^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1979286661 10000000000 482894012777 4000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247284501/10000000000 : ℝ)^4379 ≤ (538721316647/1250000000000 : ℝ)^3355 := by
    have hnat : (5247284501 : ℕ)^4379*1250000000000^3355 ≤ 538721316647^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247284501 10000000000 538721316647 1250000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5408124199/10000000000 : ℝ)^4379 ≤ (22414972170067/50000000000000 : ℝ)^3355 := by
    have hnat : (5408124199 : ℕ)^4379*50000000000000^3355 ≤ 22414972170067^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408124199 10000000000 22414972170067 50000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4379/1024 : ℝ)) 4379 3355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1979286661/10000000000 : ℝ), (5247284501/10000000000 : ℝ), (5408124199/10000000000 : ℝ)] ![(482894012777/4000000000000 : ℝ), (538721316647/1250000000000 : ℝ), (22414972170067/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1979286661/10000000000 : ℝ)|^4379 ≤ (482894012777/4000000000000 : ℝ)^3355
        have hw : |(-1979286661/10000000000 : ℝ)|=(1979286661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247284501/10000000000 : ℝ)|^4379 ≤ (538721316647/1250000000000 : ℝ)^3355
        have hw : |(5247284501/10000000000 : ℝ)|=(5247284501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5408124199/10000000000 : ℝ)|^4379 ≤ (22414972170067/50000000000000 : ℝ)^3355
        have hw : |(5408124199/10000000000 : ℝ)|=(5408124199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1419_s7_5 (p : ℝ) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652726449/5000000000 : ℝ)*x 0 + (-950170131/5000000000 : ℝ)*x 1 + (5408124199/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652726449/5000000000 : ℝ)^4379 ≤ (43722333066973/100000000000000 : ℝ)^3355 := by
    have hnat : (2652726449 : ℕ)^4379*100000000000000^3355 ≤ 43722333066973^3355*5000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652726449 5000000000 43722333066973 100000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (950170131/5000000000 : ℝ)^4379 ≤ (2289544515721/20000000000000 : ℝ)^3355 := by
    have hnat : (950170131 : ℕ)^4379*20000000000000^3355 ≤ 2289544515721^3355*5000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      950170131 5000000000 2289544515721 20000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5408124199/10000000000 : ℝ)^4379 ≤ (22414972170067/50000000000000 : ℝ)^3355 := by
    have hnat : (5408124199 : ℕ)^4379*50000000000000^3355 ≤ 22414972170067^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408124199 10000000000 22414972170067 50000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4379/1024 : ℝ)) 4379 3355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652726449/5000000000 : ℝ), (-950170131/5000000000 : ℝ), (5408124199/10000000000 : ℝ)] ![(43722333066973/100000000000000 : ℝ), (2289544515721/20000000000000 : ℝ), (22414972170067/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652726449/5000000000 : ℝ)|^4379 ≤ (43722333066973/100000000000000 : ℝ)^3355
        have hw : |(2652726449/5000000000 : ℝ)|=(2652726449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-950170131/5000000000 : ℝ)|^4379 ≤ (2289544515721/20000000000000 : ℝ)^3355
        have hw : |(-950170131/5000000000 : ℝ)|=(950170131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5408124199/10000000000 : ℝ)|^4379 ≤ (22414972170067/50000000000000 : ℝ)^3355
        have hw : |(5408124199/10000000000 : ℝ)|=(5408124199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1419_s7_6 (p : ℝ) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652726449/5000000000 : ℝ)*x 0 + (5408124199/10000000000 : ℝ)*x 1 + (-950170131/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652726449/5000000000 : ℝ)^4379 ≤ (43722333066973/100000000000000 : ℝ)^3355 := by
    have hnat : (2652726449 : ℕ)^4379*100000000000000^3355 ≤ 43722333066973^3355*5000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652726449 5000000000 43722333066973 100000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5408124199/10000000000 : ℝ)^4379 ≤ (22414972170067/50000000000000 : ℝ)^3355 := by
    have hnat : (5408124199 : ℕ)^4379*50000000000000^3355 ≤ 22414972170067^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408124199 10000000000 22414972170067 50000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (950170131/5000000000 : ℝ)^4379 ≤ (2289544515721/20000000000000 : ℝ)^3355 := by
    have hnat : (950170131 : ℕ)^4379*20000000000000^3355 ≤ 2289544515721^3355*5000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      950170131 5000000000 2289544515721 20000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4379/1024 : ℝ)) 4379 3355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652726449/5000000000 : ℝ), (5408124199/10000000000 : ℝ), (-950170131/5000000000 : ℝ)] ![(43722333066973/100000000000000 : ℝ), (22414972170067/50000000000000 : ℝ), (2289544515721/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652726449/5000000000 : ℝ)|^4379 ≤ (43722333066973/100000000000000 : ℝ)^3355
        have hw : |(2652726449/5000000000 : ℝ)|=(2652726449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5408124199/10000000000 : ℝ)|^4379 ≤ (22414972170067/50000000000000 : ℝ)^3355
        have hw : |(5408124199/10000000000 : ℝ)|=(5408124199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-950170131/5000000000 : ℝ)|^4379 ≤ (2289544515721/20000000000000 : ℝ)^3355
        have hw : |(-950170131/5000000000 : ℝ)|=(950170131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1419_s7_7 (p : ℝ) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (34455251/80000000 : ℝ)*x 0 + (4483420079/10000000000 : ℝ)*x 1 + (4136744451/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (34455251/80000000 : ℝ)^4379 ≤ (33304800178239/100000000000000 : ℝ)^3355 := by
    have hnat : (34455251 : ℕ)^4379*100000000000000^3355 ≤ 33304800178239^3355*80000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34455251 80000000 33304800178239 100000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4483420079/10000000000 : ℝ)^4379 ≤ (17548703170909/50000000000000 : ℝ)^3355 := by
    have hnat : (4483420079 : ℕ)^4379*50000000000000^3355 ≤ 17548703170909^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4483420079 10000000000 17548703170909 50000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4136744451/10000000000 : ℝ)^4379 ≤ (50556469549/160000000000 : ℝ)^3355 := by
    have hnat : (4136744451 : ℕ)^4379*160000000000^3355 ≤ 50556469549^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4136744451 10000000000 50556469549 160000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4379/1024 : ℝ)) 4379 3355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(34455251/80000000 : ℝ), (4483420079/10000000000 : ℝ), (4136744451/10000000000 : ℝ)] ![(33304800178239/100000000000000 : ℝ), (17548703170909/50000000000000 : ℝ), (50556469549/160000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(34455251/80000000 : ℝ)|^4379 ≤ (33304800178239/100000000000000 : ℝ)^3355
        have hw : |(34455251/80000000 : ℝ)|=(34455251/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4483420079/10000000000 : ℝ)|^4379 ≤ (17548703170909/50000000000000 : ℝ)^3355
        have hw : |(4483420079/10000000000 : ℝ)|=(4483420079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4136744451/10000000000 : ℝ)|^4379 ≤ (50556469549/160000000000 : ℝ)^3355
        have hw : |(4136744451/10000000000 : ℝ)|=(4136744451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1419_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78885271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (461/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11319/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (283/2500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14751/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (461/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11319/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (461/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11319/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (461/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11319/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (461/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11319/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (461/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11319/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (461/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11319/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11319/100000 : ℝ) ^ (2189/512 : ℝ) ≤ (4504326407433751/50000000000000000000 : ℝ) := by
    have hpowers : (11319/100000 : ℝ)^2189 ≤ (4504326407433751/50000000000000000000 : ℝ)^512 := by
      have hnat : (11319 : ℕ)^2189*50000000000000000000^512 ≤ 4504326407433751^512*100000^2189 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11319 100000 4504326407433751 50000000000000000000 2189 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11319/100000 : ℝ)) (X := (4504326407433751/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2189 512 (by norm_num) hpowers
    exact h
  have hpowhi : (461/3125 : ℝ) ^ (2189/512 : ℝ) ≤ (559168813348577/2000000000000000000 : ℝ) := by
    have hpowers : (461/3125 : ℝ)^2189 ≤ (559168813348577/2000000000000000000 : ℝ)^512 := by
      have hnat : (461 : ℕ)^2189*2000000000000000000^512 ≤ 559168813348577^512*3125^2189 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        461 3125 559168813348577 2000000000000000000 2189 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (461/3125 : ℝ)) (X := (559168813348577/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2189 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004504326407433751/25000000000000000000 : ℝ) ≤ (2500105347463349/2500000000000000 : ℝ) ^ (2189/512 : ℝ) := by
    have hpowers : (25004504326407433751/25000000000000000000 : ℝ)^512 ≤ (2500105347463349/2500000000000000 : ℝ)^2189 := by
      have hnat : (25004504326407433751 : ℕ)^512*2500000000000000^2189 ≤ 2500105347463349^2189*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004504326407433751 25000000000000000000 2500105347463349 2500000000000000 512 2189 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500105347463349/2500000000000000 : ℝ)) (X := (25004504326407433751/25000000000000000000 : ℝ)) (by norm_num) 2189 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (3126155221671321761/3125000000000000000 : ℝ) ≤ (2500216131479027/2500000000000000 : ℝ) ^ (2189/512 : ℝ) := by
    have hpowers : (3126155221671321761/3125000000000000000 : ℝ)^512 ≤ (2500216131479027/2500000000000000 : ℝ)^2189 := by
      have hnat : (3126155221671321761 : ℕ)^512*2500000000000000^2189 ≤ 2500216131479027^2189*3125000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126155221671321761 3125000000000000000 2500216131479027 2500000000000000 512 2189 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500216131479027/2500000000000000 : ℝ)) (X := (3126155221671321761/3125000000000000000 : ℝ)) (by norm_num) 2189 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (1000559168813348577/1000000000000000000 : ℝ) ≤ (500065383098941/500000000000000 : ℝ) ^ (2189/512 : ℝ) := by
    have hpowers : (1000559168813348577/1000000000000000000 : ℝ)^512 ≤ (500065383098941/500000000000000 : ℝ)^2189 := by
      have hnat : (1000559168813348577 : ℕ)^512*500000000000000^2189 ≤ 500065383098941^2189*1000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000559168813348577 1000000000000000000 500065383098941 500000000000000 512 2189 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500065383098941/500000000000000 : ℝ)) (X := (1000559168813348577/1000000000000000000 : ℝ)) (by norm_num) 2189 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4504326407433751/50000000000000000000 : ℝ) ≤ ((8580353729294758553/8582500000000000000 : ℝ)+2*(55392007839/42912500000000 : ℝ)*(11319/100000 : ℝ))^(2189/512 : ℝ) := by
    rw [show (8580353729294758553/8582500000000000000 : ℝ)+2*(55392007839/42912500000000 : ℝ)*(11319/100000 : ℝ)=(2500105347463349/2500000000000000 : ℝ) by norm_num, show 1+2*(4504326407433751/50000000000000000000 : ℝ)=(25004504326407433751/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(559168813348577/2000000000000000000 : ℝ)+(4504326407433751/50000000000000000000 : ℝ) ≤ ((8580353729294758553/8582500000000000000 : ℝ)+(55392007839/42912500000000 : ℝ)*((461/3125 : ℝ)+(11319/100000 : ℝ)))^(2189/512 : ℝ) := by
    rw [show (8580353729294758553/8582500000000000000 : ℝ)+(55392007839/42912500000000 : ℝ)*((461/3125 : ℝ)+(11319/100000 : ℝ))=(2500216131479027/2500000000000000 : ℝ) by norm_num, show 1+(559168813348577/2000000000000000000 : ℝ)+(4504326407433751/50000000000000000000 : ℝ)=(3126155221671321761/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(559168813348577/2000000000000000000 : ℝ) ≤ ((8580353729294758553/8582500000000000000 : ℝ)+2*(55392007839/42912500000000 : ℝ)*(461/3125 : ℝ))^(2189/512 : ℝ) := by
    rw [show (8580353729294758553/8582500000000000000 : ℝ)+2*(55392007839/42912500000000 : ℝ)*(461/3125 : ℝ)=(500065383098941/500000000000000 : ℝ) by norm_num, show 1+2*(559168813348577/2000000000000000000 : ℝ)=(1000559168813348577/1000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8580353729294758553/8582500000000000000 : ℝ)*(X 1 0+X 2 0)+(55392007839/42912500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2189/512 : ℝ)) (lo := (11319/100000 : ℝ)) (hi := (461/3125 : ℝ)) (c := (8580353729294758553/8582500000000000000 : ℝ)) (alpha := (55392007839/42912500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8580353729294758553/8582500000000000000 : ℝ)*(X 0 1+X 2 1)+(55392007839/42912500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2189/512 : ℝ)) (lo := (11319/100000 : ℝ)) (hi := (461/3125 : ℝ)) (c := (8580353729294758553/8582500000000000000 : ℝ)) (alpha := (55392007839/42912500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8580353729294758553/8582500000000000000 : ℝ)*(X 0 2+X 1 2)+(55392007839/42912500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2189/512 : ℝ)) (lo := (11319/100000 : ℝ)) (hi := (461/3125 : ℝ)) (c := (8580353729294758553/8582500000000000000 : ℝ)) (alpha := (55392007839/42912500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-197927497/1000000000 : ℝ)*X 0 0+(540871053/1000000000 : ℝ)*X 0 1+(1311675351/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1419_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069505881/2000000000 : ℝ)*X 1 0+(-515440911/2500000000 : ℝ)*X 1 1+(5246700977/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1419_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347529449/10000000000 : ℝ)*X 2 0+(5246701011/10000000000 : ℝ)*X 2 1+(-103088177/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1419_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2153440981/5000000000 : ℝ)*X 0 0+(4135479547/10000000000 : ℝ)*X 0 1+(560584787/1250000000 : ℝ)*X 0 2+(2153440981/5000000000 : ℝ)*X 1 0+(4135479547/10000000000 : ℝ)*X 1 1+(560584787/1250000000 : ℝ)*X 1 2+(2153440981/5000000000 : ℝ)*X 2 0+(4135479547/10000000000 : ℝ)*X 2 1+(560584787/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1419_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1979286661/10000000000 : ℝ)*X 0 0+(5247284501/10000000000 : ℝ)*X 0 1+(5408124199/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1419_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652726449/5000000000 : ℝ)*X 1 0+(-950170131/5000000000 : ℝ)*X 1 1+(5408124199/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1419_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652726449/5000000000 : ℝ)*X 2 0+(5408124199/10000000000 : ℝ)*X 2 1+(-950170131/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1419_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((34455251/80000000 : ℝ)*X 0 0+(4483420079/10000000000 : ℝ)*X 0 1+(4136744451/10000000000 : ℝ)*X 0 2+(34455251/80000000 : ℝ)*X 1 0+(4483420079/10000000000 : ℝ)*X 1 1+(4136744451/10000000000 : ℝ)*X 1 2+(34455251/80000000 : ℝ)*X 2 0+(4483420079/10000000000 : ℝ)*X 2 1+(4136744451/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1419_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2696884361177623506557374341/429125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (554488787/100000000000000 : ℝ)*(base19) + (463107317/100000000000000 : ℝ)*(base23) + (166049527/100000000000000 : ℝ)*(lower2) + (20143809/20000000000000 : ℝ)*(lower4) + (131802119/100000000000000 : ℝ)*(upper5) + (90362012424339/2000000000000 : ℝ)*(major0) + (90362012424339/2000000000000 : ℝ)*(major1) + (4518100621216951/100000000000000 : ℝ)*(major2) + (154312120013393/2500000000000 : ℝ)*(sp0) + (6172484246046933/100000000000000 : ℝ)*(sp1) + (6172481795642033/100000000000000 : ℝ)*(sp2) + (57274161639989/2000000000000 : ℝ)*(sp3) + (2541786369/100000000000000 : ℝ)*(sp6) + (8150411637/100000000000000 : ℝ)*(sp7) + (1431858116205543/50000000000000 : ℝ)*(f.failure) + (154312120013393/2500000000000 : ℝ)*(f.sum) + (90074449092881/17165000000000000000000000000 : ℝ)*base65 + (150581664451867533/17165000000000000000000000000000 : ℝ)*base68 + (1220747054808081903/858250000000000000000000000000000 : ℝ)*base69 + (284438309299422533/17165000000000000000000000000000 : ℝ)*base72 + (71666646919709/17165000000000000000000000000 : ℝ)*base74 + (1492981671004831903/858250000000000000000000000000000 : ℝ)*base75 + (65332544799411467/17165000000000000000000000000000 : ℝ)*base77 + (192124660468233533/17165000000000000000000000000000 : ℝ)*base80 + (24250756572557/3433000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (1257153/2500000000000000000000 : ℝ)*base89 + (1257153/2500000000000000000000 : ℝ)*base91 + (23742847/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (302339177068203928103161773/85825000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (298750649/50000000000000 : ℝ)*(base19) + (649147037/100000000000000 : ℝ)*(base23) + (20261389/10000000000000 : ℝ)*(lower1) + (17937821/25000000000000 : ℝ)*(upper3) + (23466967/100000000000000 : ℝ)*(lower4) + (72563847/100000000000000 : ℝ)*(upper5) + (910189237353749/20000000000000 : ℝ)*(major0) + (910189237353749/20000000000000 : ℝ)*(major1) + (910189237353749/20000000000000 : ℝ)*(major2) + (93482861/10000000000000 : ℝ)*(sp2) + (3108678728490537/50000000000000 : ℝ)*(sp4) + (194292401858743/3125000000000 : ℝ)*(sp5) + (6217355873005427/100000000000000 : ℝ)*(sp6) + (721133699782933/25000000000000 : ℝ)*(sp7) + (721133699782933/25000000000000 : ℝ)*(f.failure) + (3108678728490537/50000000000000 : ℝ)*(f.sum) + (10430251491/68660000000000000000000000 : ℝ)*base65 + (6399244518541734803/171650000000000000000000000000000 : ℝ)*base68 + (1918792955189134803/171650000000000000000000000000000 : ℝ)*base70 + (1378413606747634803/171650000000000000000000000000000 : ℝ)*base72 + (727359376457/171650000000000000000000000 : ℝ)*base74 + (3867413481850834803/171650000000000000000000000000000 : ℝ)*base76 + (1041640166812834803/171650000000000000000000000000000 : ℝ)*base78 + (1243774292776584803/171650000000000000000000000000000 : ℝ)*base80 + (9920835579613/1716500000000000000000000000 : ℝ)*base82 + (1620157/1250000000000000000000 : ℝ)*base90 + (1620157/1250000000000000000000 : ℝ)*base92 + (1620157/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1419_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78885271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (461/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11319/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (283/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14751/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1419_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1419_box_0 (p : ℝ) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1817891057/10000000000 : ℝ)*x 0 + (5386683041/10000000000 : ℝ)*x 1 + (2693341721/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1817891057/10000000000 : ℝ)^4379 ≤ (10803787772763/100000000000000 : ℝ)^3355 := by
    have hnat : (1817891057 : ℕ)^4379*100000000000000^3355 ≤ 10803787772763^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1817891057 10000000000 10803787772763 100000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5386683041/10000000000 : ℝ)^4379 ≤ (44598103940387/100000000000000 : ℝ)^3355 := by
    have hnat : (5386683041 : ℕ)^4379*100000000000000^3355 ≤ 44598103940387^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386683041 10000000000 44598103940387 100000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2693341721/5000000000 : ℝ)^4379 ≤ (44598108273717/100000000000000 : ℝ)^3355 := by
    have hnat : (2693341721 : ℕ)^4379*100000000000000^3355 ≤ 44598108273717^3355*5000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693341721 5000000000 44598108273717 100000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4379/1024 : ℝ)) 4379 3355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1817891057/10000000000 : ℝ), (5386683041/10000000000 : ℝ), (2693341721/5000000000 : ℝ)] ![(10803787772763/100000000000000 : ℝ), (44598103940387/100000000000000 : ℝ), (44598108273717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1817891057/10000000000 : ℝ)|^4379 ≤ (10803787772763/100000000000000 : ℝ)^3355
        have hw : |(-1817891057/10000000000 : ℝ)|=(1817891057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5386683041/10000000000 : ℝ)|^4379 ≤ (44598103940387/100000000000000 : ℝ)^3355
        have hw : |(5386683041/10000000000 : ℝ)|=(5386683041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2693341721/5000000000 : ℝ)|^4379 ≤ (44598108273717/100000000000000 : ℝ)^3355
        have hw : |(2693341721/5000000000 : ℝ)|=(2693341721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1419_box_1 (p : ℝ) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5285990107/10000000000 : ℝ)*x 0 + (-1956188169/10000000000 : ℝ)*x 1 + (5386683133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285990107/10000000000 : ℝ)^4379 ≤ (5439137820659/12500000000000 : ℝ)^3355 := by
    have hnat : (5285990107 : ℕ)^4379*12500000000000^3355 ≤ 5439137820659^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285990107 10000000000 5439137820659 12500000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1956188169/10000000000 : ℝ)^4379 ≤ (371524765123/3125000000000 : ℝ)^3355 := by
    have hnat : (1956188169 : ℕ)^4379*3125000000000^3355 ≤ 371524765123^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1956188169 10000000000 371524765123 3125000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5386683133/10000000000 : ℝ)^4379 ≤ (44598104934567/100000000000000 : ℝ)^3355 := by
    have hnat : (5386683133 : ℕ)^4379*100000000000000^3355 ≤ 44598104934567^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386683133 10000000000 44598104934567 100000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4379/1024 : ℝ)) 4379 3355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285990107/10000000000 : ℝ), (-1956188169/10000000000 : ℝ), (5386683133/10000000000 : ℝ)] ![(5439137820659/12500000000000 : ℝ), (371524765123/3125000000000 : ℝ), (44598104934567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285990107/10000000000 : ℝ)|^4379 ≤ (5439137820659/12500000000000 : ℝ)^3355
        have hw : |(5285990107/10000000000 : ℝ)|=(5285990107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1956188169/10000000000 : ℝ)|^4379 ≤ (371524765123/3125000000000 : ℝ)^3355
        have hw : |(-1956188169/10000000000 : ℝ)|=(1956188169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5386683133/10000000000 : ℝ)|^4379 ≤ (44598104934567/100000000000000 : ℝ)^3355
        have hw : |(5386683133/10000000000 : ℝ)|=(5386683133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1419_box_2 (p : ℝ) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1057198093/2000000000 : ℝ)*x 0 + (5386683097/10000000000 : ℝ)*x 1 + (-1956187733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057198093/2000000000 : ℝ)^4379 ≤ (43513106411713/100000000000000 : ℝ)^3355 := by
    have hnat : (1057198093 : ℕ)^4379*100000000000000^3355 ≤ 43513106411713^3355*2000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057198093 2000000000 43513106411713 100000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5386683097/10000000000 : ℝ)^4379 ≤ (2229905227277/5000000000000 : ℝ)^3355 := by
    have hnat : (5386683097 : ℕ)^4379*5000000000000^3355 ≤ 2229905227277^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386683097 10000000000 2229905227277 5000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1956187733/10000000000 : ℝ)^4379 ≤ (1188878902537/10000000000000 : ℝ)^3355 := by
    have hnat : (1956187733 : ℕ)^4379*10000000000000^3355 ≤ 1188878902537^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1956187733 10000000000 1188878902537 10000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4379/1024 : ℝ)) 4379 3355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057198093/2000000000 : ℝ), (5386683097/10000000000 : ℝ), (-1956187733/10000000000 : ℝ)] ![(43513106411713/100000000000000 : ℝ), (2229905227277/5000000000000 : ℝ), (1188878902537/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057198093/2000000000 : ℝ)|^4379 ≤ (43513106411713/100000000000000 : ℝ)^3355
        have hw : |(1057198093/2000000000 : ℝ)|=(1057198093/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5386683097/10000000000 : ℝ)|^4379 ≤ (2229905227277/5000000000000 : ℝ)^3355
        have hw : |(5386683097/10000000000 : ℝ)|=(5386683097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1956187733/10000000000 : ℝ)|^4379 ≤ (1188878902537/10000000000000 : ℝ)^3355
        have hw : |(-1956187733/10000000000 : ℝ)|=(1956187733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1419_box_3 (p : ℝ) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4453379043/10000000000 : ℝ)*x 0 + (1059340339/2500000000 : ℝ)*x 1 + (4237361397/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4453379043/10000000000 : ℝ)^4379 ≤ (34790774033347/100000000000000 : ℝ)^3355 := by
    have hnat : (4453379043 : ℕ)^4379*100000000000000^3355 ≤ 34790774033347^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4453379043 10000000000 34790774033347 100000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1059340339/2500000000 : ℝ)^4379 ≤ (6520922553479/20000000000000 : ℝ)^3355 := by
    have hnat : (1059340339 : ℕ)^4379*20000000000000^3355 ≤ 6520922553479^3355*2500000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059340339 2500000000 6520922553479 20000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4237361397/10000000000 : ℝ)^4379 ≤ (815115329479/2500000000000 : ℝ)^3355 := by
    have hnat : (4237361397 : ℕ)^4379*2500000000000^3355 ≤ 815115329479^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4237361397 10000000000 815115329479 2500000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4379/1024 : ℝ)) 4379 3355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4453379043/10000000000 : ℝ), (1059340339/2500000000 : ℝ), (4237361397/10000000000 : ℝ)] ![(34790774033347/100000000000000 : ℝ), (6520922553479/20000000000000 : ℝ), (815115329479/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4453379043/10000000000 : ℝ)|^4379 ≤ (34790774033347/100000000000000 : ℝ)^3355
        have hw : |(4453379043/10000000000 : ℝ)|=(4453379043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1059340339/2500000000 : ℝ)|^4379 ≤ (6520922553479/20000000000000 : ℝ)^3355
        have hw : |(1059340339/2500000000 : ℝ)|=(1059340339/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4237361397/10000000000 : ℝ)|^4379 ≤ (815115329479/2500000000000 : ℝ)^3355
        have hw : |(4237361397/10000000000 : ℝ)|=(4237361397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1419_box_4 (p : ℝ) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1071698193/5000000000 : ℝ)*x 0 + (658296921/1250000000 : ℝ)*x 1 + (526637549/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071698193/5000000000 : ℝ)^4379 ≤ (6697522996793/50000000000000 : ℝ)^3355 := by
    have hnat : (1071698193 : ℕ)^4379*50000000000000^3355 ≤ 6697522996793^3355*5000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071698193 5000000000 6697522996793 50000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658296921/1250000000 : ℝ)^4379 ≤ (10825619085121/25000000000000 : ℝ)^3355 := by
    have hnat : (658296921 : ℕ)^4379*25000000000000^3355 ≤ 10825619085121^3355*1250000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658296921 1250000000 10825619085121 25000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526637549/1000000000 : ℝ)^4379 ≤ (10825619412449/25000000000000 : ℝ)^3355 := by
    have hnat : (526637549 : ℕ)^4379*25000000000000^3355 ≤ 10825619412449^3355*1000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526637549 1000000000 10825619412449 25000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4379/1024 : ℝ)) 4379 3355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1071698193/5000000000 : ℝ), (658296921/1250000000 : ℝ), (526637549/1000000000 : ℝ)] ![(6697522996793/50000000000000 : ℝ), (10825619085121/25000000000000 : ℝ), (10825619412449/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1071698193/5000000000 : ℝ)|^4379 ≤ (6697522996793/50000000000000 : ℝ)^3355
        have hw : |(-1071698193/5000000000 : ℝ)|=(1071698193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658296921/1250000000 : ℝ)|^4379 ≤ (10825619085121/25000000000000 : ℝ)^3355
        have hw : |(658296921/1250000000 : ℝ)|=(658296921/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526637549/1000000000 : ℝ)|^4379 ≤ (10825619412449/25000000000000 : ℝ)^3355
        have hw : |(526637549/1000000000 : ℝ)|=(526637549/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1419_box_5 (p : ℝ) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2685110849/5000000000 : ℝ)*x 0 + (-2004969737/10000000000 : ℝ)*x 1 + (2633188013/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2685110849/5000000000 : ℝ)^4379 ≤ (44420300594171/100000000000000 : ℝ)^3355 := by
    have hnat : (2685110849 : ℕ)^4379*100000000000000^3355 ≤ 44420300594171^3355*5000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2685110849 5000000000 44420300594171 100000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2004969737/10000000000 : ℝ)^4379 ≤ (6138607991987/50000000000000 : ℝ)^3355 := by
    have hnat : (2004969737 : ℕ)^4379*50000000000000^3355 ≤ 6138607991987^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2004969737 10000000000 6138607991987 50000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633188013/5000000000 : ℝ)^4379 ≤ (43302483402183/100000000000000 : ℝ)^3355 := by
    have hnat : (2633188013 : ℕ)^4379*100000000000000^3355 ≤ 43302483402183^3355*5000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633188013 5000000000 43302483402183 100000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4379/1024 : ℝ)) 4379 3355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2685110849/5000000000 : ℝ), (-2004969737/10000000000 : ℝ), (2633188013/5000000000 : ℝ)] ![(44420300594171/100000000000000 : ℝ), (6138607991987/50000000000000 : ℝ), (43302483402183/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2685110849/5000000000 : ℝ)|^4379 ≤ (44420300594171/100000000000000 : ℝ)^3355
        have hw : |(2685110849/5000000000 : ℝ)|=(2685110849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2004969737/10000000000 : ℝ)|^4379 ≤ (6138607991987/50000000000000 : ℝ)^3355
        have hw : |(-2004969737/10000000000 : ℝ)|=(2004969737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633188013/5000000000 : ℝ)|^4379 ≤ (43302483402183/100000000000000 : ℝ)^3355
        have hw : |(2633188013/5000000000 : ℝ)|=(2633188013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1419_box_6 (p : ℝ) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (268511099/500000000 : ℝ)*x 0 + (5266375379/10000000000 : ℝ)*x 1 + (-1002485113/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268511099/500000000 : ℝ)^4379 ≤ (8884060727741/20000000000000 : ℝ)^3355 := by
    have hnat : (268511099 : ℕ)^4379*20000000000000^3355 ≤ 8884060727741^3355*500000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268511099 500000000 8884060727741 20000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266375379/10000000000 : ℝ)^4379 ≤ (43302476458537/100000000000000 : ℝ)^3355 := by
    have hnat : (5266375379 : ℕ)^4379*100000000000000^3355 ≤ 43302476458537^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266375379 10000000000 43302476458537 100000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1002485113/5000000000 : ℝ)^4379 ≤ (12277219892233/100000000000000 : ℝ)^3355 := by
    have hnat : (1002485113 : ℕ)^4379*100000000000000^3355 ≤ 12277219892233^3355*5000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1002485113 5000000000 12277219892233 100000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4379/1024 : ℝ)) 4379 3355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(268511099/500000000 : ℝ), (5266375379/10000000000 : ℝ), (-1002485113/5000000000 : ℝ)] ![(8884060727741/20000000000000 : ℝ), (43302476458537/100000000000000 : ℝ), (12277219892233/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(268511099/500000000 : ℝ)|^4379 ≤ (8884060727741/20000000000000 : ℝ)^3355
        have hw : |(268511099/500000000 : ℝ)|=(268511099/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266375379/10000000000 : ℝ)|^4379 ≤ (43302476458537/100000000000000 : ℝ)^3355
        have hw : |(5266375379/10000000000 : ℝ)|=(5266375379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1002485113/5000000000 : ℝ)|^4379 ≤ (12277219892233/100000000000000 : ℝ)^3355
        have hw : |(-1002485113/5000000000 : ℝ)|=(1002485113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1419_box_7 (p : ℝ) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2079674579/5000000000 : ℝ)*x 0 + (2192162681/5000000000 : ℝ)*x 1 + (548040613/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2079674579/5000000000 : ℝ)^4379 ≤ (31823342475067/100000000000000 : ℝ)^3355 := by
    have hnat : (2079674579 : ℕ)^4379*100000000000000^3355 ≤ 31823342475067^3355*5000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2079674579 5000000000 31823342475067 100000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2192162681/5000000000 : ℝ)^4379 ≤ (852208276969/2500000000000 : ℝ)^3355 := by
    have hnat : (2192162681 : ℕ)^4379*2500000000000^3355 ≤ 852208276969^3355*5000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2192162681 5000000000 852208276969 2500000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (548040613/1250000000 : ℝ)^4379 ≤ (34088326430923/100000000000000 : ℝ)^3355 := by
    have hnat : (548040613 : ℕ)^4379*100000000000000^3355 ≤ 34088326430923^3355*1250000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548040613 1250000000 34088326430923 100000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4379/1024 : ℝ)) 4379 3355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2079674579/5000000000 : ℝ), (2192162681/5000000000 : ℝ), (548040613/1250000000 : ℝ)] ![(31823342475067/100000000000000 : ℝ), (852208276969/2500000000000 : ℝ), (34088326430923/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2079674579/5000000000 : ℝ)|^4379 ≤ (31823342475067/100000000000000 : ℝ)^3355
        have hw : |(2079674579/5000000000 : ℝ)|=(2079674579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2192162681/5000000000 : ℝ)|^4379 ≤ (852208276969/2500000000000 : ℝ)^3355
        have hw : |(2192162681/5000000000 : ℝ)|=(2192162681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(548040613/1250000000 : ℝ)|^4379 ≤ (34088326430923/100000000000000 : ℝ)^3355
        have hw : |(548040613/1250000000 : ℝ)|=(548040613/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1419_box_8 (p : ℝ) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-414971467/2000000000 : ℝ)*x 0 + (2591601947/5000000000 : ℝ)*x 1 + (2700331543/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (414971467/2000000000 : ℝ)^4379 ≤ (641936488773/5000000000000 : ℝ)^3355 := by
    have hnat : (414971467 : ℕ)^4379*5000000000000^3355 ≤ 641936488773^3355*2000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      414971467 2000000000 641936488773 5000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2591601947/5000000000 : ℝ)^4379 ≤ (21206016890553/50000000000000 : ℝ)^3355 := by
    have hnat : (2591601947 : ℕ)^4379*50000000000000^3355 ≤ 21206016890553^3355*5000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591601947 5000000000 21206016890553 50000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2700331543/5000000000 : ℝ)^4379 ≤ (44749236429221/100000000000000 : ℝ)^3355 := by
    have hnat : (2700331543 : ℕ)^4379*100000000000000^3355 ≤ 44749236429221^3355*5000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700331543 5000000000 44749236429221 100000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4379/1024 : ℝ)) 4379 3355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-414971467/2000000000 : ℝ), (2591601947/5000000000 : ℝ), (2700331543/5000000000 : ℝ)] ![(641936488773/5000000000000 : ℝ), (21206016890553/50000000000000 : ℝ), (44749236429221/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-414971467/2000000000 : ℝ)|^4379 ≤ (641936488773/5000000000000 : ℝ)^3355
        have hw : |(-414971467/2000000000 : ℝ)|=(414971467/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2591601947/5000000000 : ℝ)|^4379 ≤ (21206016890553/50000000000000 : ℝ)^3355
        have hw : |(2591601947/5000000000 : ℝ)|=(2591601947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2700331543/5000000000 : ℝ)|^4379 ≤ (44749236429221/100000000000000 : ℝ)^3355
        have hw : |(2700331543/5000000000 : ℝ)|=(2700331543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1419_box_9 (p : ℝ) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2638099137/5000000000 : ℝ)*x 0 + (-1950392333/10000000000 : ℝ)*x 1 + (5400663019/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638099137/5000000000 : ℝ)^4379 ≤ (43407926412451/100000000000000 : ℝ)^3355 := by
    have hnat : (2638099137 : ℕ)^4379*100000000000000^3355 ≤ 43407926412451^3355*5000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638099137 5000000000 43407926412451 100000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1950392333/10000000000 : ℝ)^4379 ≤ (5921418937133/50000000000000 : ℝ)^3355 := by
    have hnat : (1950392333 : ℕ)^4379*50000000000000^3355 ≤ 5921418937133^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1950392333 10000000000 5921418937133 50000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5400663019/10000000000 : ℝ)^4379 ≤ (22374617852313/50000000000000 : ℝ)^3355 := by
    have hnat : (5400663019 : ℕ)^4379*50000000000000^3355 ≤ 22374617852313^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400663019 10000000000 22374617852313 50000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4379/1024 : ℝ)) 4379 3355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638099137/5000000000 : ℝ), (-1950392333/10000000000 : ℝ), (5400663019/10000000000 : ℝ)] ![(43407926412451/100000000000000 : ℝ), (5921418937133/50000000000000 : ℝ), (22374617852313/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638099137/5000000000 : ℝ)|^4379 ≤ (43407926412451/100000000000000 : ℝ)^3355
        have hw : |(2638099137/5000000000 : ℝ)|=(2638099137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1950392333/10000000000 : ℝ)|^4379 ≤ (5921418937133/50000000000000 : ℝ)^3355
        have hw : |(-1950392333/10000000000 : ℝ)|=(1950392333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5400663019/10000000000 : ℝ)|^4379 ≤ (22374617852313/50000000000000 : ℝ)^3355
        have hw : |(5400663019/10000000000 : ℝ)|=(5400663019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1419_box_10 (p : ℝ) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276198179/10000000000 : ℝ)*x 0 + (2700331539/5000000000 : ℝ)*x 1 + (-97519619/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276198179/10000000000 : ℝ)^4379 ≤ (1736317015693/4000000000000 : ℝ)^3355 := by
    have hnat : (5276198179 : ℕ)^4379*4000000000000^3355 ≤ 1736317015693^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276198179 10000000000 1736317015693 4000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2700331539/5000000000 : ℝ)^4379 ≤ (22374618171351/50000000000000 : ℝ)^3355 := by
    have hnat : (2700331539 : ℕ)^4379*50000000000000^3355 ≤ 22374618171351^3355*5000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700331539 5000000000 22374618171351 50000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (97519619/500000000 : ℝ)^4379 ≤ (2960709561689/25000000000000 : ℝ)^3355 := by
    have hnat : (97519619 : ℕ)^4379*25000000000000^3355 ≤ 2960709561689^3355*500000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      97519619 500000000 2960709561689 25000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4379/1024 : ℝ)) 4379 3355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276198179/10000000000 : ℝ), (2700331539/5000000000 : ℝ), (-97519619/500000000 : ℝ)] ![(1736317015693/4000000000000 : ℝ), (22374618171351/50000000000000 : ℝ), (2960709561689/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276198179/10000000000 : ℝ)|^4379 ≤ (1736317015693/4000000000000 : ℝ)^3355
        have hw : |(5276198179/10000000000 : ℝ)|=(5276198179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2700331539/5000000000 : ℝ)|^4379 ≤ (22374618171351/50000000000000 : ℝ)^3355
        have hw : |(2700331539/5000000000 : ℝ)|=(2700331539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-97519619/500000000 : ℝ)|^4379 ≤ (2960709561689/25000000000000 : ℝ)^3355
        have hw : |(-97519619/500000000 : ℝ)|=(97519619/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1419_box_11 (p : ℝ) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2243494133/5000000000 : ℝ)*x 0 + (2110134831/5000000000 : ℝ)*x 1 + (4220269629/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2243494133/5000000000 : ℝ)^4379 ≤ (4391733625281/12500000000000 : ℝ)^3355 := by
    have hnat : (2243494133 : ℕ)^4379*12500000000000^3355 ≤ 4391733625281^3355*5000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2243494133 5000000000 4391733625281 12500000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2110134831/5000000000 : ℝ)^4379 ≤ (32433065655943/100000000000000 : ℝ)^3355 := by
    have hnat : (2110134831 : ℕ)^4379*100000000000000^3355 ≤ 32433065655943^3355*5000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2110134831 5000000000 32433065655943 100000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4220269629/10000000000 : ℝ)^4379 ≤ (3243306532493/10000000000000 : ℝ)^3355 := by
    have hnat : (4220269629 : ℕ)^4379*10000000000000^3355 ≤ 3243306532493^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4220269629 10000000000 3243306532493 10000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4379/1024 : ℝ)) 4379 3355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2243494133/5000000000 : ℝ), (2110134831/5000000000 : ℝ), (4220269629/10000000000 : ℝ)] ![(4391733625281/12500000000000 : ℝ), (32433065655943/100000000000000 : ℝ), (3243306532493/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2243494133/5000000000 : ℝ)|^4379 ≤ (4391733625281/12500000000000 : ℝ)^3355
        have hw : |(2243494133/5000000000 : ℝ)|=(2243494133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2110134831/5000000000 : ℝ)|^4379 ≤ (32433065655943/100000000000000 : ℝ)^3355
        have hw : |(2110134831/5000000000 : ℝ)|=(2110134831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4220269629/10000000000 : ℝ)|^4379 ≤ (3243306532493/10000000000000 : ℝ)^3355
        have hw : |(4220269629/10000000000 : ℝ)|=(4220269629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1419_box_12 (p : ℝ) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-188662751/1000000000 : ℝ)*x 0 + (2733905831/5000000000 : ℝ)*x 1 + (5255254449/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (188662751/1000000000 : ℝ)^4379 ≤ (11340022640717/100000000000000 : ℝ)^3355 := by
    have hnat : (188662751 : ℕ)^4379*100000000000000^3355 ≤ 11340022640717^3355*1000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      188662751 1000000000 11340022640717 100000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2733905831/5000000000 : ℝ)^4379 ≤ (2842300809939/6250000000000 : ℝ)^3355 := by
    have hnat : (2733905831 : ℕ)^4379*6250000000000^3355 ≤ 2842300809939^3355*5000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2733905831 5000000000 2842300809939 6250000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5255254449/10000000000 : ℝ)^4379 ≤ (43183164382249/100000000000000 : ℝ)^3355 := by
    have hnat : (5255254449 : ℕ)^4379*100000000000000^3355 ≤ 43183164382249^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255254449 10000000000 43183164382249 100000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4379/1024 : ℝ)) 4379 3355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-188662751/1000000000 : ℝ), (2733905831/5000000000 : ℝ), (5255254449/10000000000 : ℝ)] ![(11340022640717/100000000000000 : ℝ), (2842300809939/6250000000000 : ℝ), (43183164382249/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-188662751/1000000000 : ℝ)|^4379 ≤ (11340022640717/100000000000000 : ℝ)^3355
        have hw : |(-188662751/1000000000 : ℝ)|=(188662751/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2733905831/5000000000 : ℝ)|^4379 ≤ (2842300809939/6250000000000 : ℝ)^3355
        have hw : |(2733905831/5000000000 : ℝ)|=(2733905831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5255254449/10000000000 : ℝ)|^4379 ≤ (43183164382249/100000000000000 : ℝ)^3355
        have hw : |(5255254449/10000000000 : ℝ)|=(5255254449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1419_box_13 (p : ℝ) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5378006623/10000000000 : ℝ)*x 0 + (-2009379159/10000000000 : ℝ)*x 1 + (656906797/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5378006623/10000000000 : ℝ)^4379 ≤ (44504366939391/100000000000000 : ℝ)^3355 := by
    have hnat : (5378006623 : ℕ)^4379*100000000000000^3355 ≤ 44504366939391^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378006623 10000000000 44504366939391 100000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2009379159/10000000000 : ℝ)^4379 ≤ (153905868123/1250000000000 : ℝ)^3355 := by
    have hnat : (2009379159 : ℕ)^4379*1250000000000^3355 ≤ 153905868123^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2009379159 10000000000 153905868123 1250000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (656906797/1250000000 : ℝ)^4379 ≤ (43183163599313/100000000000000 : ℝ)^3355 := by
    have hnat : (656906797 : ℕ)^4379*100000000000000^3355 ≤ 43183163599313^3355*1250000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656906797 1250000000 43183163599313 100000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4379/1024 : ℝ)) 4379 3355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5378006623/10000000000 : ℝ), (-2009379159/10000000000 : ℝ), (656906797/1250000000 : ℝ)] ![(44504366939391/100000000000000 : ℝ), (153905868123/1250000000000 : ℝ), (43183163599313/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5378006623/10000000000 : ℝ)|^4379 ≤ (44504366939391/100000000000000 : ℝ)^3355
        have hw : |(5378006623/10000000000 : ℝ)|=(5378006623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2009379159/10000000000 : ℝ)|^4379 ≤ (153905868123/1250000000000 : ℝ)^3355
        have hw : |(-2009379159/10000000000 : ℝ)|=(2009379159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(656906797/1250000000 : ℝ)|^4379 ≤ (43183163599313/100000000000000 : ℝ)^3355
        have hw : |(656906797/1250000000 : ℝ)|=(656906797/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1419_box_14 (p : ℝ) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1075601277/2000000000 : ℝ)*x 0 + (5255254553/10000000000 : ℝ)*x 1 + (-2009379243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075601277/2000000000 : ℝ)^4379 ≤ (8900872873751/20000000000000 : ℝ)^3355 := by
    have hnat : (1075601277 : ℕ)^4379*20000000000000^3355 ≤ 8900872873751^3355*2000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075601277 2000000000 8900872873751 20000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5255254553/10000000000 : ℝ)^4379 ≤ (674736960901/1562500000000 : ℝ)^3355 := by
    have hnat : (5255254553 : ℕ)^4379*1562500000000^3355 ≤ 674736960901^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255254553 10000000000 674736960901 1562500000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2009379243/10000000000 : ℝ)^4379 ≤ (12312470121647/100000000000000 : ℝ)^3355 := by
    have hnat : (2009379243 : ℕ)^4379*100000000000000^3355 ≤ 12312470121647^3355*10000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2009379243 10000000000 12312470121647 100000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4379/1024 : ℝ)) 4379 3355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075601277/2000000000 : ℝ), (5255254553/10000000000 : ℝ), (-2009379243/10000000000 : ℝ)] ![(8900872873751/20000000000000 : ℝ), (674736960901/1562500000000 : ℝ), (12312470121647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075601277/2000000000 : ℝ)|^4379 ≤ (8900872873751/20000000000000 : ℝ)^3355
        have hw : |(1075601277/2000000000 : ℝ)|=(1075601277/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5255254553/10000000000 : ℝ)|^4379 ≤ (674736960901/1562500000000 : ℝ)^3355
        have hw : |(5255254553/10000000000 : ℝ)|=(5255254553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2009379243/10000000000 : ℝ)|^4379 ≤ (12312470121647/100000000000000 : ℝ)^3355
        have hw : |(-2009379243/10000000000 : ℝ)|=(2009379243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1419_box_15 (p : ℝ) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2065860927/5000000000 : ℝ)*x 0 + (879579717/2000000000 : ℝ)*x 1 + (1099474483/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2065860927/5000000000 : ℝ)^4379 ≤ (15773864574331/50000000000000 : ℝ)^3355 := by
    have hnat : (2065860927 : ℕ)^4379*50000000000000^3355 ≤ 15773864574331^3355*5000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2065860927 5000000000 15773864574331 50000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (879579717/2000000000 : ℝ)^4379 ≤ (34226138738153/100000000000000 : ℝ)^3355 := by
    have hnat : (879579717 : ℕ)^4379*100000000000000^3355 ≤ 34226138738153^3355*2000000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      879579717 2000000000 34226138738153 100000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1099474483/2500000000 : ℝ)^4379 ≤ (34226132105179/100000000000000 : ℝ)^3355 := by
    have hnat : (1099474483 : ℕ)^4379*100000000000000^3355 ≤ 34226132105179^3355*2500000000^4379 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099474483 2500000000 34226132105179 100000000000000 4379 3355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4379/1024 : ℝ)) 4379 3355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2065860927/5000000000 : ℝ), (879579717/2000000000 : ℝ), (1099474483/2500000000 : ℝ)] ![(15773864574331/50000000000000 : ℝ), (34226138738153/100000000000000 : ℝ), (34226132105179/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2065860927/5000000000 : ℝ)|^4379 ≤ (15773864574331/50000000000000 : ℝ)^3355
        have hw : |(2065860927/5000000000 : ℝ)|=(2065860927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(879579717/2000000000 : ℝ)|^4379 ≤ (34226138738153/100000000000000 : ℝ)^3355
        have hw : |(879579717/2000000000 : ℝ)|=(879579717/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1099474483/2500000000 : ℝ)|^4379 ≤ (34226132105179/100000000000000 : ℝ)^3355
        have hw : |(1099474483/2500000000 : ℝ)|=(1099474483/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1419_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78885271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14751/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (283/2500 : ℝ)*pair X i i ≤ pair X i h) :
    -(62893/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59093/100000 : ℝ) ∧ (80393/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84647/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14751/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (283/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14751/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (283/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14751/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (283/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14751/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (283/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14751/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (283/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14751/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (283/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (283/2500 : ℝ) ^ (2189/512 : ℝ) ≤ (9012056038014269/100000000000000000000 : ℝ) := by
    have hpowers : (283/2500 : ℝ)^2189 ≤ (9012056038014269/100000000000000000000 : ℝ)^512 := by
      have hnat : (283 : ℕ)^2189*100000000000000000000^512 ≤ 9012056038014269^512*2500^2189 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        283 2500 9012056038014269 100000000000000000000 2189 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (283/2500 : ℝ)) (X := (9012056038014269/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2189 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14751/100000 : ℝ) ^ (2189/512 : ℝ) ≤ (27950338716113733/100000000000000000000 : ℝ) := by
    have hpowers : (14751/100000 : ℝ)^2189 ≤ (27950338716113733/100000000000000000000 : ℝ)^512 := by
      have hnat : (14751 : ℕ)^2189*100000000000000000000^512 ≤ 27950338716113733^512*100000^2189 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14751 100000 27950338716113733 100000000000000000000 2189 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14751/100000 : ℝ)) (X := (27950338716113733/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2189 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009012056038014269/50000000000000000000 : ℝ) ≤ (1250052693628999/1250000000000000 : ℝ) ^ (2189/512 : ℝ) := by
    have hpowers : (50009012056038014269/50000000000000000000 : ℝ)^512 ≤ (1250052693628999/1250000000000000 : ℝ)^2189 := by
      have hnat : (50009012056038014269 : ℕ)^512*1250000000000000^2189 ≤ 1250052693628999^2189*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009012056038014269 50000000000000000000 1250052693628999 1250000000000000 512 2189 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250052693628999/1250000000000000 : ℝ)) (X := (50009012056038014269/50000000000000000000 : ℝ)) (by norm_num) 2189 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50018481197377064001/50000000000000000000 : ℝ) ≤ (10000864416045493/10000000000000000 : ℝ) ^ (2189/512 : ℝ) := by
    have hpowers : (50018481197377064001/50000000000000000000 : ℝ)^512 ≤ (10000864416045493/10000000000000000 : ℝ)^2189 := by
      have hnat : (50018481197377064001 : ℕ)^512*10000000000000000^2189 ≤ 10000864416045493^2189*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018481197377064001 50000000000000000000 10000864416045493 10000000000000000 512 2189 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000864416045493/10000000000000000 : ℝ)) (X := (50018481197377064001/50000000000000000000 : ℝ)) (by norm_num) 2189 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50027950338716113733/50000000000000000000 : ℝ) ≤ (5000653641529497/5000000000000000 : ℝ) ^ (2189/512 : ℝ) := by
    have hpowers : (50027950338716113733/50000000000000000000 : ℝ)^512 ≤ (5000653641529497/5000000000000000 : ℝ)^2189 := by
      have hnat : (50027950338716113733 : ℕ)^512*5000000000000000^2189 ≤ 5000653641529497^2189*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027950338716113733 50000000000000000000 5000653641529497 5000000000000000 512 2189 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000653641529497/5000000000000000 : ℝ)) (X := (50027950338716113733/50000000000000000000 : ℝ)) (by norm_num) 2189 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9012056038014269/100000000000000000000 : ℝ) ≤ ((4287677478192887739/4288750000000000000 : ℝ)+2*(442867013501/343100000000000 : ℝ)*(283/2500 : ℝ))^(2189/512 : ℝ) := by
    rw [show (4287677478192887739/4288750000000000000 : ℝ)+2*(442867013501/343100000000000 : ℝ)*(283/2500 : ℝ)=(1250052693628999/1250000000000000 : ℝ) by norm_num, show 1+2*(9012056038014269/100000000000000000000 : ℝ)=(50009012056038014269/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27950338716113733/100000000000000000000 : ℝ)+(9012056038014269/100000000000000000000 : ℝ) ≤ ((4287677478192887739/4288750000000000000 : ℝ)+(442867013501/343100000000000 : ℝ)*((14751/100000 : ℝ)+(283/2500 : ℝ)))^(2189/512 : ℝ) := by
    rw [show (4287677478192887739/4288750000000000000 : ℝ)+(442867013501/343100000000000 : ℝ)*((14751/100000 : ℝ)+(283/2500 : ℝ))=(10000864416045493/10000000000000000 : ℝ) by norm_num, show 1+(27950338716113733/100000000000000000000 : ℝ)+(9012056038014269/100000000000000000000 : ℝ)=(50018481197377064001/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27950338716113733/100000000000000000000 : ℝ) ≤ ((4287677478192887739/4288750000000000000 : ℝ)+2*(442867013501/343100000000000 : ℝ)*(14751/100000 : ℝ))^(2189/512 : ℝ) := by
    rw [show (4287677478192887739/4288750000000000000 : ℝ)+2*(442867013501/343100000000000 : ℝ)*(14751/100000 : ℝ)=(5000653641529497/5000000000000000 : ℝ) by norm_num, show 1+2*(27950338716113733/100000000000000000000 : ℝ)=(50027950338716113733/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4287677478192887739/4288750000000000000 : ℝ)*(X 1 0+X 2 0)+(442867013501/343100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2189/512 : ℝ)) (lo := (283/2500 : ℝ)) (hi := (14751/100000 : ℝ)) (c := (4287677478192887739/4288750000000000000 : ℝ)) (alpha := (442867013501/343100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4287677478192887739/4288750000000000000 : ℝ)*(X 0 1+X 2 1)+(442867013501/343100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2189/512 : ℝ)) (lo := (283/2500 : ℝ)) (hi := (14751/100000 : ℝ)) (c := (4287677478192887739/4288750000000000000 : ℝ)) (alpha := (442867013501/343100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4287677478192887739/4288750000000000000 : ℝ)*(X 0 2+X 1 2)+(442867013501/343100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2189/512 : ℝ)) (lo := (283/2500 : ℝ)) (hi := (14751/100000 : ℝ)) (c := (4287677478192887739/4288750000000000000 : ℝ)) (alpha := (442867013501/343100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1817891057/10000000000 : ℝ)*X 0 0+(5386683041/10000000000 : ℝ)*X 0 1+(2693341721/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1419_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5285990107/10000000000 : ℝ)*X 1 0+(-1956188169/10000000000 : ℝ)*X 1 1+(5386683133/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1419_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1057198093/2000000000 : ℝ)*X 2 0+(5386683097/10000000000 : ℝ)*X 2 1+(-1956187733/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1419_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4453379043/10000000000 : ℝ)*X 0 0+(1059340339/2500000000 : ℝ)*X 0 1+(4237361397/10000000000 : ℝ)*X 0 2+(4453379043/10000000000 : ℝ)*X 1 0+(1059340339/2500000000 : ℝ)*X 1 1+(4237361397/10000000000 : ℝ)*X 1 2+(4453379043/10000000000 : ℝ)*X 2 0+(1059340339/2500000000 : ℝ)*X 2 1+(4237361397/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1419_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1071698193/5000000000 : ℝ)*X 0 0+(658296921/1250000000 : ℝ)*X 0 1+(526637549/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1419_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2685110849/5000000000 : ℝ)*X 1 0+(-2004969737/10000000000 : ℝ)*X 1 1+(2633188013/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1419_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((268511099/500000000 : ℝ)*X 2 0+(5266375379/10000000000 : ℝ)*X 2 1+(-1002485113/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1419_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2079674579/5000000000 : ℝ)*X 0 0+(2192162681/5000000000 : ℝ)*X 0 1+(548040613/1250000000 : ℝ)*X 0 2+(2079674579/5000000000 : ℝ)*X 1 0+(2192162681/5000000000 : ℝ)*X 1 1+(548040613/1250000000 : ℝ)*X 1 2+(2079674579/5000000000 : ℝ)*X 2 0+(2192162681/5000000000 : ℝ)*X 2 1+(548040613/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1419_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-414971467/2000000000 : ℝ)*X 0 0+(2591601947/5000000000 : ℝ)*X 0 1+(2700331543/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1419_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2638099137/5000000000 : ℝ)*X 1 0+(-1950392333/10000000000 : ℝ)*X 1 1+(5400663019/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1419_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5276198179/10000000000 : ℝ)*X 2 0+(2700331539/5000000000 : ℝ)*X 2 1+(-97519619/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1419_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2243494133/5000000000 : ℝ)*X 0 0+(2110134831/5000000000 : ℝ)*X 0 1+(4220269629/10000000000 : ℝ)*X 0 2+(2243494133/5000000000 : ℝ)*X 1 0+(2110134831/5000000000 : ℝ)*X 1 1+(4220269629/10000000000 : ℝ)*X 1 2+(2243494133/5000000000 : ℝ)*X 2 0+(2110134831/5000000000 : ℝ)*X 2 1+(4220269629/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1419_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-188662751/1000000000 : ℝ)*X 0 0+(2733905831/5000000000 : ℝ)*X 0 1+(5255254449/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1419_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5378006623/10000000000 : ℝ)*X 1 0+(-2009379159/10000000000 : ℝ)*X 1 1+(656906797/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1419_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1075601277/2000000000 : ℝ)*X 2 0+(5255254553/10000000000 : ℝ)*X 2 1+(-2009379243/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1419_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2065860927/5000000000 : ℝ)*X 0 0+(879579717/2000000000 : ℝ)*X 0 1+(1099474483/2500000000 : ℝ)*X 0 2+(2065860927/5000000000 : ℝ)*X 1 0+(879579717/2000000000 : ℝ)*X 1 1+(1099474483/2500000000 : ℝ)*X 1 2+(2065860927/5000000000 : ℝ)*X 2 0+(879579717/2000000000 : ℝ)*X 2 1+(1099474483/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1419_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62893/100000 : ℝ) ≤ (-14779353691131681497818089/23500000000000000000000000 : ℝ) := by norm_num
    linear_combination (42641329/50000000000000 : ℝ)*(lower0) + (50577349/100000000000000 : ℝ)*(upper1) + (23080779/20000000000000 : ℝ)*(lower4) + (2677001/12500000000000 : ℝ)*(lower5) + (15029672428713/500000000000 : ℝ)*(major0) + (15029672428713/500000000000 : ℝ)*(major1) + (15029672428713/500000000000 : ℝ)*(major2) + (2465607319/50000000000000 : ℝ)*(sp2) + (6724045719/100000000000000 : ℝ)*(sp3) + (1031893868273109/25000000000000 : ℝ)*(sp4) + (2063665535526261/50000000000000 : ℝ)*(sp5) + (2063785270938899/50000000000000 : ℝ)*(sp6) + (381050079320793/20000000000000 : ℝ)*(sp7) + (122201019957/50000000000000 : ℝ)*(sp13) + (476314280162421/25000000000000 : ℝ)*(f.failure) + (1031893868273109/25000000000000 : ℝ)*(f.sum) + (84459391037/47000000000000000000000000 : ℝ)*base66 + (323013499488509/29375000000000000000000000000 : ℝ)*base67 + (14075493364183/14687500000000000000000000000 : ℝ)*base70 + (22914961515529/7343750000000000000000000000 : ℝ)*base72 + (310799661651/23500000000000000000000000 : ℝ)*base73 + (39269395069567/14687500000000000000000000000 : ℝ)*base75 + (22787616289327/3671875000000000000000000000 : ℝ)*base78 + (21332458638509/29375000000000000000000000000 : ℝ)*base79 + (15277724593/47000000000000000000000000 : ℝ)*base81 + (4601091/1250000000000000000000 : ℝ)*base89 + (4601091/1250000000000000000000 : ℝ)*base91 + (4601091/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (59093/100000 : ℝ) ≤ (5068928119855973687138630877/8577500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1419989/4000000000000 : ℝ)*(lower1) + (84913543/100000000000000 : ℝ)*(lower3) + (37926527/20000000000000 : ℝ)*(upper4) + (9287511/20000000000000 : ℝ)*(upper5) + (3077199647816901/100000000000000 : ℝ)*(major0) + (3077199647816901/100000000000000 : ℝ)*(major1) + (3077199647816901/100000000000000 : ℝ)*(major2) + (4184273497879011/100000000000000 : ℝ)*(sp0) + (104605408961921/2500000000000 : ℝ)*(sp1) + (4184257041759991/100000000000000 : ℝ)*(sp2) + (1950425381569893/100000000000000 : ℝ)*(sp3) + (1461779/78125000000 : ℝ)*(sp7) + (14284850543/25000000000000 : ℝ)*(sp9) + (822805951/5000000000000 : ℝ)*(sp10) + (487606813161753/25000000000000 : ℝ)*(f.failure) + (4184273497879011/100000000000000 : ℝ)*(f.sum) + (15826420937059/17155000000000000000000000000 : ℝ)*base66 + (2544855115403764339/428875000000000000000000000000000 : ℝ)*base67 + (1055776983044235661/428875000000000000000000000000000 : ℝ)*base70 + (5978786232427764339/428875000000000000000000000000000 : ℝ)*base71 + (83729451385959/17155000000000000000000000000 : ℝ)*base74 + (2348741238457485661/428875000000000000000000000000000 : ℝ)*base76 + (1247276056921860661/428875000000000000000000000000000 : ℝ)*base78 + (3782346807564264339/428875000000000000000000000000000 : ℝ)*base79 + (346654527630289/17155000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (10259937/1250000000000000000000 : ℝ)*base90 + (10259937/1250000000000000000000 : ℝ)*base92 + (10259937/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (80393/100000 : ℝ) ≤ (86199299483986955585832399691539/107218750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12742187/50000000000000 : ℝ)*(upper2) + (982389/50000000000000 : ℝ)*(lower3) + (20715997/50000000000000 : ℝ)*(lower5) + (1692824287221061/50000000000000 : ℝ)*(major0) + (1692824287221061/50000000000000 : ℝ)*(major1) + (1692824287221061/50000000000000 : ℝ)*(major2) + (683127593/100000000000000 : ℝ)*(sp0) + (18588109211/100000000000000 : ℝ)*(sp2) + (11879047879/100000000000000 : ℝ)*(sp3) + (4598563952985771/100000000000000 : ℝ)*(sp8) + (4598566554199573/100000000000000 : ℝ)*(sp9) + (4598547966090361/100000000000000 : ℝ)*(sp10) + (1072960069061529/50000000000000 : ℝ)*(sp11) + (191808621/10000000000000 : ℝ)*(sp12) + (1072966008585469/50000000000000 : ℝ)*(f.failure) + (4598566554199573/100000000000000 : ℝ)*(f.sum) + (166948640900077/17155000000000000000000000000 : ℝ)*base65 + (67480032885421079/214437500000000000000000000000000 : ℝ)*base67 + (566199209396671079/214437500000000000000000000000000 : ℝ)*base69 + (1629888748554171079/214437500000000000000000000000000 : ℝ)*base71 + (121876066142917/17155000000000000000000000000 : ℝ)*base73 + (1108880868600733579/214437500000000000000000000000000 : ℝ)*base75 + (2987666527335921079/214437500000000000000000000000000 : ℝ)*base77 + (1833871623150546079/214437500000000000000000000000000 : ℝ)*base79 + (22296296947953/4288750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base88 + (1272901/2500000000000000000000 : ℝ)*base90 + (1272901/2500000000000000000000 : ℝ)*base92 + (1272901/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-84647/100000 : ℝ) ≤ (-22688736607875508528786850307117/26804687500000000000000000000000 : ℝ) := by norm_num
    linear_combination (31123677/20000000000000 : ℝ)*(lower0) + (1659339/12500000000000 : ℝ)*(lower2) + (46987183/100000000000000 : ℝ)*(upper3) + (43722559/50000000000000 : ℝ)*(lower4) + (53484503228303/1562500000000 : ℝ)*(major0) + (53484503228303/1562500000000 : ℝ)*(major1) + (53484503228303/1562500000000 : ℝ)*(major2) + (7597005337/100000000000000 : ℝ)*(sp0) + (20363163511/12500000000000 : ℝ)*(sp5) + (114358162897/100000000000000 : ℝ)*(sp6) + (2352305979826019/50000000000000 : ℝ)*(sp12) + (2352228325674643/50000000000000 : ℝ)*(sp13) + (4704505198494477/100000000000000 : ℝ)*(sp14) + (10848058716219/500000000000 : ℝ)*(sp15) + (10848058716219/500000000000 : ℝ)*(f.failure) + (2352309778328687/50000000000000 : ℝ)*(f.sum) + (196978057381687/17155000000000000000000000000 : ℝ)*base65 + (866437682952931539/53609375000000000000000000000000 : ℝ)*base68 + (39574587835078729/3350585937500000000000000000000 : ℝ)*base70 + (23446190919635793/26804687500000000000000000000000 : ℝ)*base71 + (51890121132271/8577500000000000000000000000 : ℝ)*base73 + (49316408244860583/6701171875000000000000000000000 : ℝ)*base76 + (2403759016833130961/53609375000000000000000000000000 : ℝ)*base77 + (37197635904860583/6701171875000000000000000000000 : ℝ)*base80 + (38518911689507/17155000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (89651/25000000000000000000 : ℝ)*base90 + (89651/25000000000000000000 : ℝ)*base92 + (89651/25000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1419_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78885271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14751/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (283/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62893/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59093/100000 : ℝ) else (80393/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84647/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1419_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1419_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78885271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3689/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2263/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62893/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59093/100000 : ℝ) else (80393/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84647/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1419_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1419_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1419_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2189/512 : ℝ) ≤ p) (hpb : p ≤ (4379/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78885271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3689/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2263/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62893/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59093/100000 : ℝ) else (80393/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84647/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1419_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
