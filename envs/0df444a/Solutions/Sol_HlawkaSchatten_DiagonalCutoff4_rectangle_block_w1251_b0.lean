-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1251_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:23:48.575682+00:00
-- url     : https://prove2.me/submissions/c721456e-1533-41bb-bc76-5813afef344d

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
theorem support_rectangle_w1251_s0_0 (p : ℝ) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1857786237/10000000000 : ℝ)*x 0 + (6029479119/10000000000 : ℝ)*x 1 + (4794101133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1857786237/10000000000 : ℝ)^2111 ≤ (10837474436591/100000000000000 : ℝ)^1599 := by
    have hnat : (1857786237 : ℕ)^2111*100000000000000^1599 ≤ 10837474436591^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1857786237 10000000000 10837474436591 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6029479119/10000000000 : ℝ)^2111 ≤ (6409665586197/12500000000000 : ℝ)^1599 := by
    have hnat : (6029479119 : ℕ)^2111*12500000000000^1599 ≤ 6409665586197^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6029479119 10000000000 6409665586197 12500000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4794101133/10000000000 : ℝ)^2111 ≤ (37885200857269/100000000000000 : ℝ)^1599 := by
    have hnat : (4794101133 : ℕ)^2111*100000000000000^1599 ≤ 37885200857269^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4794101133 10000000000 37885200857269 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2111/512 : ℝ)) 2111 1599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1857786237/10000000000 : ℝ), (6029479119/10000000000 : ℝ), (4794101133/10000000000 : ℝ)] ![(10837474436591/100000000000000 : ℝ), (6409665586197/12500000000000 : ℝ), (37885200857269/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1857786237/10000000000 : ℝ)|^2111 ≤ (10837474436591/100000000000000 : ℝ)^1599
        have hw : |(-1857786237/10000000000 : ℝ)|=(1857786237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6029479119/10000000000 : ℝ)|^2111 ≤ (6409665586197/12500000000000 : ℝ)^1599
        have hw : |(6029479119/10000000000 : ℝ)|=(6029479119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4794101133/10000000000 : ℝ)|^2111 ≤ (37885200857269/100000000000000 : ℝ)^1599
        have hw : |(4794101133/10000000000 : ℝ)|=(4794101133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1251_s0_1 (p : ℝ) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1377663119/2500000000 : ℝ)*x 0 + (-2563780391/10000000000 : ℝ)*x 1 + (4794101073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1377663119/2500000000 : ℝ)^2111 ≤ (45534041527169/100000000000000 : ℝ)^1599 := by
    have hnat : (1377663119 : ℕ)^2111*100000000000000^1599 ≤ 45534041527169^1599*2500000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1377663119 2500000000 45534041527169 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2563780391/10000000000 : ℝ)^2111 ≤ (8290379113041/50000000000000 : ℝ)^1599 := by
    have hnat : (2563780391 : ℕ)^2111*50000000000000^1599 ≤ 8290379113041^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2563780391 10000000000 8290379113041 50000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4794101073/10000000000 : ℝ)^2111 ≤ (37885200231299/100000000000000 : ℝ)^1599 := by
    have hnat : (4794101073 : ℕ)^2111*100000000000000^1599 ≤ 37885200231299^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4794101073 10000000000 37885200231299 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2111/512 : ℝ)) 2111 1599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1377663119/2500000000 : ℝ), (-2563780391/10000000000 : ℝ), (4794101073/10000000000 : ℝ)] ![(45534041527169/100000000000000 : ℝ), (8290379113041/50000000000000 : ℝ), (37885200231299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1377663119/2500000000 : ℝ)|^2111 ≤ (45534041527169/100000000000000 : ℝ)^1599
        have hw : |(1377663119/2500000000 : ℝ)|=(1377663119/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2563780391/10000000000 : ℝ)|^2111 ≤ (8290379113041/50000000000000 : ℝ)^1599
        have hw : |(-2563780391/10000000000 : ℝ)|=(2563780391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4794101073/10000000000 : ℝ)|^2111 ≤ (37885200231299/100000000000000 : ℝ)^1599
        have hw : |(4794101073/10000000000 : ℝ)|=(4794101073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1251_s0_2 (p : ℝ) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5510652397/10000000000 : ℝ)*x 0 + (958820233/2000000000 : ℝ)*x 1 + (-128189019/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5510652397/10000000000 : ℝ)^2111 ≤ (22767020332691/50000000000000 : ℝ)^1599 := by
    have hnat : (5510652397 : ℕ)^2111*50000000000000^1599 ≤ 22767020332691^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5510652397 10000000000 22767020332691 50000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (958820233/2000000000 : ℝ)^2111 ≤ (473565014889/1250000000000 : ℝ)^1599 := by
    have hnat : (958820233 : ℕ)^2111*1250000000000^1599 ≤ 473565014889^1599*2000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      958820233 2000000000 473565014889 1250000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (128189019/500000000 : ℝ)^2111 ≤ (16580758132163/100000000000000 : ℝ)^1599 := by
    have hnat : (128189019 : ℕ)^2111*100000000000000^1599 ≤ 16580758132163^1599*500000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128189019 500000000 16580758132163 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2111/512 : ℝ)) 2111 1599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5510652397/10000000000 : ℝ), (958820233/2000000000 : ℝ), (-128189019/500000000 : ℝ)] ![(22767020332691/50000000000000 : ℝ), (473565014889/1250000000000 : ℝ), (16580758132163/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5510652397/10000000000 : ℝ)|^2111 ≤ (22767020332691/50000000000000 : ℝ)^1599
        have hw : |(5510652397/10000000000 : ℝ)|=(5510652397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(958820233/2000000000 : ℝ)|^2111 ≤ (473565014889/1250000000000 : ℝ)^1599
        have hw : |(958820233/2000000000 : ℝ)|=(958820233/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-128189019/500000000 : ℝ)|^2111 ≤ (16580758132163/100000000000000 : ℝ)^1599
        have hw : |(-128189019/500000000 : ℝ)|=(128189019/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1251_s0_3 (p : ℝ) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4192315581/10000000000 : ℝ)*x 0 + (3116556707/10000000000 : ℝ)*x 1 + (5626963713/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4192315581/10000000000 : ℝ)^2111 ≤ (31736839844699/100000000000000 : ℝ)^1599 := by
    have hnat : (4192315581 : ℕ)^2111*100000000000000^1599 ≤ 31736839844699^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4192315581 10000000000 31736839844699 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3116556707/10000000000 : ℝ)^2111 ≤ (5364011799471/25000000000000 : ℝ)^1599 := by
    have hnat : (3116556707 : ℕ)^2111*25000000000000^1599 ≤ 5364011799471^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3116556707 10000000000 5364011799471 25000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5626963713/10000000000 : ℝ)^2111 ≤ (46807112943129/100000000000000 : ℝ)^1599 := by
    have hnat : (5626963713 : ℕ)^2111*100000000000000^1599 ≤ 46807112943129^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5626963713 10000000000 46807112943129 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2111/512 : ℝ)) 2111 1599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4192315581/10000000000 : ℝ), (3116556707/10000000000 : ℝ), (5626963713/10000000000 : ℝ)] ![(31736839844699/100000000000000 : ℝ), (5364011799471/25000000000000 : ℝ), (46807112943129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4192315581/10000000000 : ℝ)|^2111 ≤ (31736839844699/100000000000000 : ℝ)^1599
        have hw : |(4192315581/10000000000 : ℝ)|=(4192315581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3116556707/10000000000 : ℝ)|^2111 ≤ (5364011799471/25000000000000 : ℝ)^1599
        have hw : |(3116556707/10000000000 : ℝ)|=(3116556707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5626963713/10000000000 : ℝ)|^2111 ≤ (46807112943129/100000000000000 : ℝ)^1599
        have hw : |(5626963713/10000000000 : ℝ)|=(5626963713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1251_s0_4 (p : ℝ) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-58206819/312500000 : ℝ)*x 0 + (4825908877/10000000000 : ℝ)*x 1 + (1199309367/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (58206819/312500000 : ℝ)^2111 ≤ (5437351536681/50000000000000 : ℝ)^1599 := by
    have hnat : (58206819 : ℕ)^2111*50000000000000^1599 ≤ 5437351536681^1599*312500000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58206819 312500000 5437351536681 50000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4825908877/10000000000 : ℝ)^2111 ≤ (38217397640779/100000000000000 : ℝ)^1599 := by
    have hnat : (4825908877 : ℕ)^2111*100000000000000^1599 ≤ 38217397640779^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4825908877 10000000000 38217397640779 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1199309367/2000000000 : ℝ)^2111 ≤ (5090789926649/10000000000000 : ℝ)^1599 := by
    have hnat : (1199309367 : ℕ)^2111*10000000000000^1599 ≤ 5090789926649^1599*2000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1199309367 2000000000 5090789926649 10000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2111/512 : ℝ)) 2111 1599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-58206819/312500000 : ℝ), (4825908877/10000000000 : ℝ), (1199309367/2000000000 : ℝ)] ![(5437351536681/50000000000000 : ℝ), (38217397640779/100000000000000 : ℝ), (5090789926649/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-58206819/312500000 : ℝ)|^2111 ≤ (5437351536681/50000000000000 : ℝ)^1599
        have hw : |(-58206819/312500000 : ℝ)|=(58206819/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4825908877/10000000000 : ℝ)|^2111 ≤ (38217397640779/100000000000000 : ℝ)^1599
        have hw : |(4825908877/10000000000 : ℝ)|=(4825908877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1199309367/2000000000 : ℝ)|^2111 ≤ (5090789926649/10000000000000 : ℝ)^1599
        have hw : |(1199309367/2000000000 : ℝ)|=(1199309367/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1251_s0_5 (p : ℝ) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2587242919/5000000000 : ℝ)*x 0 + (-170166551/1250000000 : ℝ)*x 1 + (1199309837/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2587242919/5000000000 : ℝ)^2111 ≤ (41903224642247/100000000000000 : ℝ)^1599 := by
    have hnat : (2587242919 : ℕ)^2111*100000000000000^1599 ≤ 41903224642247^1599*5000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587242919 5000000000 41903224642247 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (170166551/1250000000 : ℝ)^2111 ≤ (3594424874657/50000000000000 : ℝ)^1599 := by
    have hnat : (170166551 : ℕ)^2111*50000000000000^1599 ≤ 3594424874657^1599*1250000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170166551 1250000000 3594424874657 50000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1199309837/2000000000 : ℝ)^2111 ≤ (1590872675157/3125000000000 : ℝ)^1599 := by
    have hnat : (1199309837 : ℕ)^2111*3125000000000^1599 ≤ 1590872675157^1599*2000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1199309837 2000000000 1590872675157 3125000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2111/512 : ℝ)) 2111 1599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2587242919/5000000000 : ℝ), (-170166551/1250000000 : ℝ), (1199309837/2000000000 : ℝ)] ![(41903224642247/100000000000000 : ℝ), (3594424874657/50000000000000 : ℝ), (1590872675157/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2587242919/5000000000 : ℝ)|^2111 ≤ (41903224642247/100000000000000 : ℝ)^1599
        have hw : |(2587242919/5000000000 : ℝ)|=(2587242919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-170166551/1250000000 : ℝ)|^2111 ≤ (3594424874657/50000000000000 : ℝ)^1599
        have hw : |(-170166551/1250000000 : ℝ)|=(170166551/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1199309837/2000000000 : ℝ)|^2111 ≤ (1590872675157/3125000000000 : ℝ)^1599
        have hw : |(1199309837/2000000000 : ℝ)|=(1199309837/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1251_s0_6 (p : ℝ) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5174486817/10000000000 : ℝ)*x 0 + (2998273633/5000000000 : ℝ)*x 1 + (-1361333989/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5174486817/10000000000 : ℝ)^2111 ≤ (41903235108777/100000000000000 : ℝ)^1599 := by
    have hnat : (5174486817 : ℕ)^2111*100000000000000^1599 ≤ 41903235108777^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174486817 10000000000 41903235108777 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2998273633/5000000000 : ℝ)^2111 ≤ (50907904097089/100000000000000 : ℝ)^1599 := by
    have hnat : (2998273633 : ℕ)^2111*100000000000000^1599 ≤ 50907904097089^1599*5000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2998273633 5000000000 50907904097089 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1361333989/10000000000 : ℝ)^2111 ≤ (7188860771479/100000000000000 : ℝ)^1599 := by
    have hnat : (1361333989 : ℕ)^2111*100000000000000^1599 ≤ 7188860771479^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1361333989 10000000000 7188860771479 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2111/512 : ℝ)) 2111 1599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5174486817/10000000000 : ℝ), (2998273633/5000000000 : ℝ), (-1361333989/10000000000 : ℝ)] ![(41903235108777/100000000000000 : ℝ), (50907904097089/100000000000000 : ℝ), (7188860771479/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5174486817/10000000000 : ℝ)|^2111 ≤ (41903235108777/100000000000000 : ℝ)^1599
        have hw : |(5174486817/10000000000 : ℝ)|=(5174486817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2998273633/5000000000 : ℝ)|^2111 ≤ (50907904097089/100000000000000 : ℝ)^1599
        have hw : |(2998273633/5000000000 : ℝ)|=(2998273633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1361333989/10000000000 : ℝ)|^2111 ≤ (7188860771479/100000000000000 : ℝ)^1599
        have hw : |(-1361333989/10000000000 : ℝ)|=(1361333989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1251_s0_7 (p : ℝ) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4202136289/10000000000 : ℝ)*x 0 + (2781166401/5000000000 : ℝ)*x 1 + (795868083/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4202136289/10000000000 : ℝ)^2111 ≤ (15917513541279/50000000000000 : ℝ)^1599 := by
    have hnat : (4202136289 : ℕ)^2111*50000000000000^1599 ≤ 15917513541279^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4202136289 10000000000 15917513541279 50000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2781166401/5000000000 : ℝ)^2111 ≤ (46098651309387/100000000000000 : ℝ)^1599 := by
    have hnat : (2781166401 : ℕ)^2111*100000000000000^1599 ≤ 46098651309387^1599*5000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2781166401 5000000000 46098651309387 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (795868083/2500000000 : ℝ)^2111 ≤ (86196568719/390625000000 : ℝ)^1599 := by
    have hnat : (795868083 : ℕ)^2111*390625000000^1599 ≤ 86196568719^1599*2500000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      795868083 2500000000 86196568719 390625000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2111/512 : ℝ)) 2111 1599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4202136289/10000000000 : ℝ), (2781166401/5000000000 : ℝ), (795868083/2500000000 : ℝ)] ![(15917513541279/50000000000000 : ℝ), (46098651309387/100000000000000 : ℝ), (86196568719/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4202136289/10000000000 : ℝ)|^2111 ≤ (15917513541279/50000000000000 : ℝ)^1599
        have hw : |(4202136289/10000000000 : ℝ)|=(4202136289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2781166401/5000000000 : ℝ)|^2111 ≤ (46098651309387/100000000000000 : ℝ)^1599
        have hw : |(2781166401/5000000000 : ℝ)|=(2781166401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(795868083/2500000000 : ℝ)|^2111 ≤ (86196568719/390625000000 : ℝ)^1599
        have hw : |(795868083/2500000000 : ℝ)|=(795868083/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1251_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75802409/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (427/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13701/50000 : ℝ)*pair X 0 0 := by
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
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
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
  have hpowlo : (0 : ℝ) ^ (8443/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8443 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8443*1^2048 ≤ 0^2048*1^8443 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8443 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8443 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8443/2048 : ℝ) ≤ (91522734787435371/4000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8443 ≤ (91522734787435371/4000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8443*4000000000000000000^2048 ≤ 91522734787435371^2048*5^8443 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 91522734787435371 4000000000000000000 8443 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (91522734787435371/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8443 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8443/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8443 := by
      have hnat : (1 : ℕ)^2048*1^8443 ≤ 1^8443*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8443 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8443 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (4091522734787435371/4000000000000000000 : ℝ) ≤ (10055026585788709/10000000000000000 : ℝ) ^ (8443/2048 : ℝ) := by
    have hpowers : (4091522734787435371/4000000000000000000 : ℝ)^2048 ≤ (10055026585788709/10000000000000000 : ℝ)^8443 := by
      have hnat : (4091522734787435371 : ℕ)^2048*10000000000000000^8443 ≤ 10055026585788709^8443*4000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4091522734787435371 4000000000000000000 10055026585788709 10000000000000000 2048 8443 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10055026585788709/10000000000000000 : ℝ)) (X := (4091522734787435371/4000000000000000000 : ℝ)) (by norm_num) 8443 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (2091522734787435371/2000000000000000000 : ℝ) ≤ (5055026585788709/5000000000000000 : ℝ) ^ (8443/2048 : ℝ) := by
    have hpowers : (2091522734787435371/2000000000000000000 : ℝ)^2048 ≤ (5055026585788709/5000000000000000 : ℝ)^8443 := by
      have hnat : (2091522734787435371 : ℕ)^2048*5000000000000000^8443 ≤ 5055026585788709^8443*2000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2091522734787435371 2000000000000000000 5055026585788709 5000000000000000 2048 8443 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5055026585788709/5000000000000000 : ℝ)) (X := (2091522734787435371/2000000000000000000 : ℝ)) (by norm_num) 8443 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(55026585788709/4000000000000000 : ℝ)*(0 : ℝ))^(8443/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(55026585788709/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(91522734787435371/4000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(55026585788709/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8443/2048 : ℝ) := by
    rw [show (1 : ℝ)+(55026585788709/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10055026585788709/10000000000000000 : ℝ) by norm_num, show 1+(91522734787435371/4000000000000000000 : ℝ)+(0 : ℝ)=(4091522734787435371/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(91522734787435371/4000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(55026585788709/4000000000000000 : ℝ)*(2/5 : ℝ))^(8443/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(55026585788709/4000000000000000 : ℝ)*(2/5 : ℝ)=(5055026585788709/5000000000000000 : ℝ) by norm_num, show 1+2*(91522734787435371/4000000000000000000 : ℝ)=(2091522734787435371/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(55026585788709/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8443/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (55026585788709/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(55026585788709/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8443/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (55026585788709/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(55026585788709/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8443/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (55026585788709/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1857786237/10000000000 : ℝ)*X 0 0+(6029479119/10000000000 : ℝ)*X 0 1+(4794101133/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1251_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1377663119/2500000000 : ℝ)*X 1 0+(-2563780391/10000000000 : ℝ)*X 1 1+(4794101073/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1251_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5510652397/10000000000 : ℝ)*X 2 0+(958820233/2000000000 : ℝ)*X 2 1+(-128189019/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1251_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4192315581/10000000000 : ℝ)*X 0 0+(3116556707/10000000000 : ℝ)*X 0 1+(5626963713/10000000000 : ℝ)*X 0 2+(4192315581/10000000000 : ℝ)*X 1 0+(3116556707/10000000000 : ℝ)*X 1 1+(5626963713/10000000000 : ℝ)*X 1 2+(4192315581/10000000000 : ℝ)*X 2 0+(3116556707/10000000000 : ℝ)*X 2 1+(5626963713/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1251_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-58206819/312500000 : ℝ)*X 0 0+(4825908877/10000000000 : ℝ)*X 0 1+(1199309367/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1251_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2587242919/5000000000 : ℝ)*X 1 0+(-170166551/1250000000 : ℝ)*X 1 1+(1199309837/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1251_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5174486817/10000000000 : ℝ)*X 2 0+(2998273633/5000000000 : ℝ)*X 2 1+(-1361333989/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1251_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4202136289/10000000000 : ℝ)*X 0 0+(2781166401/5000000000 : ℝ)*X 0 1+(795868083/2500000000 : ℝ)*X 0 2+(4202136289/10000000000 : ℝ)*X 1 0+(2781166401/5000000000 : ℝ)*X 1 1+(795868083/2500000000 : ℝ)*X 1 2+(4202136289/10000000000 : ℝ)*X 2 0+(2781166401/5000000000 : ℝ)*X 2 1+(795868083/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1251_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (181674957712756164950607/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (48282659/100000000000000 : ℝ)*(base1) + (892207533/100000000000000 : ℝ)*(base19) + (205498979/25000000000000 : ℝ)*(base23) + (29303559/50000000000000 : ℝ)*(base24) + (49122079/25000000000000 : ℝ)*(upper3) + (301954552067759/50000000000000 : ℝ)*(major0) + (301954552067759/50000000000000 : ℝ)*(major1) + (301954552067759/50000000000000 : ℝ)*(major2) + (161894374117337/20000000000000 : ℝ)*(sp0) + (404736462938919/50000000000000 : ℝ)*(sp1) + (809472937482337/100000000000000 : ℝ)*(sp2) + (199171345388349/50000000000000 : ℝ)*(sp3) + (997890673/50000000000000 : ℝ)*(sp4) + (765004831/50000000000000 : ℝ)*(sp7) + (19917213453451/5000000000000 : ℝ)*(f.failure) + (809473818085371/100000000000000 : ℝ)*(f.sum) + (91864470833131/100000000000000000000000000000 : ℝ)*base65 + (1097162751733131/200000000000000000000000000000 : ℝ)*base67 + (590542730533131/200000000000000000000000000000 : ℝ)*base69 + (1403943276333131/200000000000000000000000000000 : ℝ)*base71 + (59307350066869/100000000000000000000000000000 : ℝ)*base74 + (1994309498733131/200000000000000000000000000000 : ℝ)*base75 + (1586746296133131/200000000000000000000000000000 : ℝ)*base77 + (641306022133131/200000000000000000000000000000 : ℝ)*base79 + (651268514666869/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (163459/250000000000000000000 : ℝ)*base89 + (163459/250000000000000000000 : ℝ)*base91 + (163459/250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2133323657511517159413/2000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (68346983/50000000000000 : ℝ)*(base1) + (220246001/100000000000000 : ℝ)*(base19) + (161569189/50000000000000 : ℝ)*(base23) + (43983891/100000000000000 : ℝ)*(upper3) + (12746058800327/2000000000000 : ℝ)*(major0) + (12746058800327/2000000000000 : ℝ)*(major1) + (12746058800327/2000000000000 : ℝ)*(major2) + (1355289127/100000000000000 : ℝ)*(sp1) + (451333241/100000000000000 : ℝ)*(sp2) + (379020207/50000000000000 : ℝ)*(sp3) + (85423481591163/10000000000000 : ℝ)*(sp4) + (106779137960317/12500000000000 : ℝ)*(sp5) + (170846780949209/20000000000000 : ℝ)*(sp6) + (84074054105051/20000000000000 : ℝ)*(sp7) + (105092791314909/25000000000000 : ℝ)*(f.failure) + (1668427107847/195312500000 : ℝ)*(f.sum) + (4546001351843/4000000000000000000000000000 : ℝ)*base65 + (57789956363843/8000000000000000000000000000 : ℝ)*base67 + (47132178971843/8000000000000000000000000000 : ℝ)*base69 + (32225859315843/8000000000000000000000000000 : ℝ)*base71 + (11999098655843/4000000000000000000000000000 : ℝ)*base73 + (69457975923843/8000000000000000000000000000 : ℝ)*base75 + (45270148739843/8000000000000000000000000000 : ℝ)*base77 + (49903162563843/8000000000000000000000000000 : ℝ)*base79 + (5480415079843/4000000000000000000000000000 : ℝ)*base81 + (4815781/1250000000000000000000 : ℝ)*base89 + (4815781/1250000000000000000000 : ℝ)*base91 + (4815781/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1251_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75802409/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (427/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13701/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1251_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1251_s1_0 (p : ℝ) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-205454693/1000000000 : ℝ)*x 0 + (1134668147/2000000000 : ℝ)*x 1 + (25121451/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (205454693/1000000000 : ℝ)^2111 ≤ (3094479948233/25000000000000 : ℝ)^1599 := by
    have hnat : (205454693 : ℕ)^2111*25000000000000^1599 ≤ 3094479948233^1599*1000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205454693 1000000000 3094479948233 25000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1134668147/2000000000 : ℝ)^2111 ≤ (47317091588079/100000000000000 : ℝ)^1599 := by
    have hnat : (1134668147 : ℕ)^2111*100000000000000^1599 ≤ 47317091588079^1599*2000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1134668147 2000000000 47317091588079 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (25121451/50000000 : ℝ)^2111 ≤ (40304988607417/100000000000000 : ℝ)^1599 := by
    have hnat : (25121451 : ℕ)^2111*100000000000000^1599 ≤ 40304988607417^1599*50000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25121451 50000000 40304988607417 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2111/512 : ℝ)) 2111 1599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-205454693/1000000000 : ℝ), (1134668147/2000000000 : ℝ), (25121451/50000000 : ℝ)] ![(3094479948233/25000000000000 : ℝ), (47317091588079/100000000000000 : ℝ), (40304988607417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-205454693/1000000000 : ℝ)|^2111 ≤ (3094479948233/25000000000000 : ℝ)^1599
        have hw : |(-205454693/1000000000 : ℝ)|=(205454693/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1134668147/2000000000 : ℝ)|^2111 ≤ (47317091588079/100000000000000 : ℝ)^1599
        have hw : |(1134668147/2000000000 : ℝ)|=(1134668147/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(25121451/50000000 : ℝ)|^2111 ≤ (40304988607417/100000000000000 : ℝ)^1599
        have hw : |(25121451/50000000 : ℝ)|=(25121451/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1251_s1_1 (p : ℝ) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1082633337/2000000000 : ℝ)*x 0 + (-2402929481/10000000000 : ℝ)*x 1 + (5024290389/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1082633337/2000000000 : ℝ)^2111 ≤ (22236811248757/50000000000000 : ℝ)^1599 := by
    have hnat : (1082633337 : ℕ)^2111*50000000000000^1599 ≤ 22236811248757^1599*2000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082633337 2000000000 22236811248757 50000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2402929481/10000000000 : ℝ)^2111 ≤ (3805346721597/25000000000000 : ℝ)^1599 := by
    have hnat : (2402929481 : ℕ)^2111*25000000000000^1599 ≤ 3805346721597^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2402929481 10000000000 3805346721597 25000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5024290389/10000000000 : ℝ)^2111 ≤ (1259530956533/3125000000000 : ℝ)^1599 := by
    have hnat : (5024290389 : ℕ)^2111*3125000000000^1599 ≤ 1259530956533^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5024290389 10000000000 1259530956533 3125000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2111/512 : ℝ)) 2111 1599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1082633337/2000000000 : ℝ), (-2402929481/10000000000 : ℝ), (5024290389/10000000000 : ℝ)] ![(22236811248757/50000000000000 : ℝ), (3805346721597/25000000000000 : ℝ), (1259530956533/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1082633337/2000000000 : ℝ)|^2111 ≤ (22236811248757/50000000000000 : ℝ)^1599
        have hw : |(1082633337/2000000000 : ℝ)|=(1082633337/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2402929481/10000000000 : ℝ)|^2111 ≤ (3805346721597/25000000000000 : ℝ)^1599
        have hw : |(-2402929481/10000000000 : ℝ)|=(2402929481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5024290389/10000000000 : ℝ)|^2111 ≤ (1259530956533/3125000000000 : ℝ)^1599
        have hw : |(5024290389/10000000000 : ℝ)|=(5024290389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1251_s1_2 (p : ℝ) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5413166857/10000000000 : ℝ)*x 0 + (5024290271/10000000000 : ℝ)*x 1 + (-1201464703/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5413166857/10000000000 : ℝ)^2111 ≤ (44473624363117/100000000000000 : ℝ)^1599 := by
    have hnat : (5413166857 : ℕ)^2111*100000000000000^1599 ≤ 44473624363117^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413166857 10000000000 44473624363117 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5024290271/10000000000 : ℝ)^2111 ≤ (10076247339839/25000000000000 : ℝ)^1599 := by
    have hnat : (5024290271 : ℕ)^2111*25000000000000^1599 ≤ 10076247339839^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5024290271 10000000000 10076247339839 25000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1201464703/5000000000 : ℝ)^2111 ≤ (1902673282397/12500000000000 : ℝ)^1599 := by
    have hnat : (1201464703 : ℕ)^2111*12500000000000^1599 ≤ 1902673282397^1599*5000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1201464703 5000000000 1902673282397 12500000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2111/512 : ℝ)) 2111 1599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5413166857/10000000000 : ℝ), (5024290271/10000000000 : ℝ), (-1201464703/5000000000 : ℝ)] ![(44473624363117/100000000000000 : ℝ), (10076247339839/25000000000000 : ℝ), (1902673282397/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5413166857/10000000000 : ℝ)|^2111 ≤ (44473624363117/100000000000000 : ℝ)^1599
        have hw : |(5413166857/10000000000 : ℝ)|=(5413166857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5024290271/10000000000 : ℝ)|^2111 ≤ (10076247339839/25000000000000 : ℝ)^1599
        have hw : |(5024290271/10000000000 : ℝ)|=(5024290271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1201464703/5000000000 : ℝ)|^2111 ≤ (1902673282397/12500000000000 : ℝ)^1599
        have hw : |(-1201464703/5000000000 : ℝ)|=(1201464703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1251_s1_3 (p : ℝ) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ)) (x : Fin 3 → ℝ) :
    (861615241/2000000000 : ℝ)*x 0 + (924272413/2500000000 : ℝ)*x 1 + (1003204667/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (861615241/2000000000 : ℝ)^2111 ≤ (32898861455697/100000000000000 : ℝ)^1599 := by
    have hnat : (861615241 : ℕ)^2111*100000000000000^1599 ≤ 32898861455697^1599*2000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      861615241 2000000000 32898861455697 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (924272413/2500000000 : ℝ)^2111 ≤ (26883678574141/100000000000000 : ℝ)^1599 := by
    have hnat : (924272413 : ℕ)^2111*100000000000000^1599 ≤ 26883678574141^1599*2500000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      924272413 2500000000 26883678574141 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1003204667/2000000000 : ℝ)^2111 ≤ (40217459955469/100000000000000 : ℝ)^1599 := by
    have hnat : (1003204667 : ℕ)^2111*100000000000000^1599 ≤ 40217459955469^1599*2000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1003204667 2000000000 40217459955469 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2111/512 : ℝ)) 2111 1599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(861615241/2000000000 : ℝ), (924272413/2500000000 : ℝ), (1003204667/2000000000 : ℝ)] ![(32898861455697/100000000000000 : ℝ), (26883678574141/100000000000000 : ℝ), (40217459955469/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(861615241/2000000000 : ℝ)|^2111 ≤ (32898861455697/100000000000000 : ℝ)^1599
        have hw : |(861615241/2000000000 : ℝ)|=(861615241/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(924272413/2500000000 : ℝ)|^2111 ≤ (26883678574141/100000000000000 : ℝ)^1599
        have hw : |(924272413/2500000000 : ℝ)|=(924272413/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1003204667/2000000000 : ℝ)|^2111 ≤ (40217459955469/100000000000000 : ℝ)^1599
        have hw : |(1003204667/2000000000 : ℝ)|=(1003204667/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1251_s1_4 (p : ℝ) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-256901559/1250000000 : ℝ)*x 0 + (2516392867/5000000000 : ℝ)*x 1 + (70808553/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (256901559/1250000000 : ℝ)^2111 ≤ (12383213615201/100000000000000 : ℝ)^1599 := by
    have hnat : (256901559 : ℕ)^2111*100000000000000^1599 ≤ 12383213615201^1599*1250000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256901559 1250000000 12383213615201 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2516392867/5000000000 : ℝ)^2111 ≤ (20197493219577/50000000000000 : ℝ)^1599 := by
    have hnat : (2516392867 : ℕ)^2111*50000000000000^1599 ≤ 20197493219577^1599*5000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2516392867 5000000000 20197493219577 50000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (70808553/125000000 : ℝ)^2111 ≤ (5902724991191/12500000000000 : ℝ)^1599 := by
    have hnat : (70808553 : ℕ)^2111*12500000000000^1599 ≤ 5902724991191^1599*125000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70808553 125000000 5902724991191 12500000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2111/512 : ℝ)) 2111 1599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-256901559/1250000000 : ℝ), (2516392867/5000000000 : ℝ), (70808553/125000000 : ℝ)] ![(12383213615201/100000000000000 : ℝ), (20197493219577/50000000000000 : ℝ), (5902724991191/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-256901559/1250000000 : ℝ)|^2111 ≤ (12383213615201/100000000000000 : ℝ)^1599
        have hw : |(-256901559/1250000000 : ℝ)|=(256901559/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2516392867/5000000000 : ℝ)|^2111 ≤ (20197493219577/50000000000000 : ℝ)^1599
        have hw : |(2516392867/5000000000 : ℝ)|=(2516392867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(70808553/125000000 : ℝ)|^2111 ≤ (5902724991191/12500000000000 : ℝ)^1599
        have hw : |(70808553/125000000 : ℝ)|=(70808553/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1251_s1_5 (p : ℝ) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ)) (x : Fin 3 → ℝ) :
    (262294071/500000000 : ℝ)*x 0 + (-1762535373/10000000000 : ℝ)*x 1 + (5664684519/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (262294071/500000000 : ℝ)^2111 ≤ (42668198639337/100000000000000 : ℝ)^1599 := by
    have hnat : (262294071 : ℕ)^2111*100000000000000^1599 ≤ 42668198639337^1599*500000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262294071 500000000 42668198639337 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1762535373/10000000000 : ℝ)^2111 ≤ (10109998343157/100000000000000 : ℝ)^1599 := by
    have hnat : (1762535373 : ℕ)^2111*100000000000000^1599 ≤ 10109998343157^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1762535373 10000000000 10109998343157 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5664684519/10000000000 : ℝ)^2111 ≤ (1180545075001/2500000000000 : ℝ)^1599 := by
    have hnat : (5664684519 : ℕ)^2111*2500000000000^1599 ≤ 1180545075001^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5664684519 10000000000 1180545075001 2500000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2111/512 : ℝ)) 2111 1599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(262294071/500000000 : ℝ), (-1762535373/10000000000 : ℝ), (5664684519/10000000000 : ℝ)] ![(42668198639337/100000000000000 : ℝ), (10109998343157/100000000000000 : ℝ), (1180545075001/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(262294071/500000000 : ℝ)|^2111 ≤ (42668198639337/100000000000000 : ℝ)^1599
        have hw : |(262294071/500000000 : ℝ)|=(262294071/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1762535373/10000000000 : ℝ)|^2111 ≤ (10109998343157/100000000000000 : ℝ)^1599
        have hw : |(-1762535373/10000000000 : ℝ)|=(1762535373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5664684519/10000000000 : ℝ)|^2111 ≤ (1180545075001/2500000000000 : ℝ)^1599
        have hw : |(5664684519/10000000000 : ℝ)|=(5664684519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1251_s1_6 (p : ℝ) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1049176269/2000000000 : ℝ)*x 0 + (5664684311/10000000000 : ℝ)*x 1 + (-1762535781/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1049176269/2000000000 : ℝ)^2111 ≤ (21334098916991/50000000000000 : ℝ)^1599 := by
    have hnat : (1049176269 : ℕ)^2111*50000000000000^1599 ≤ 21334098916991^1599*2000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049176269 2000000000 21334098916991 50000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5664684311/10000000000 : ℝ)^2111 ≤ (47221800710913/100000000000000 : ℝ)^1599 := by
    have hnat : (5664684311 : ℕ)^2111*100000000000000^1599 ≤ 47221800710913^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5664684311 10000000000 47221800710913 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1762535781/10000000000 : ℝ)^2111 ≤ (2022000286567/20000000000000 : ℝ)^1599 := by
    have hnat : (1762535781 : ℕ)^2111*20000000000000^1599 ≤ 2022000286567^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1762535781 10000000000 2022000286567 20000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2111/512 : ℝ)) 2111 1599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1049176269/2000000000 : ℝ), (5664684311/10000000000 : ℝ), (-1762535781/10000000000 : ℝ)] ![(21334098916991/50000000000000 : ℝ), (47221800710913/100000000000000 : ℝ), (2022000286567/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1049176269/2000000000 : ℝ)|^2111 ≤ (21334098916991/50000000000000 : ℝ)^1599
        have hw : |(1049176269/2000000000 : ℝ)|=(1049176269/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5664684311/10000000000 : ℝ)|^2111 ≤ (47221800710913/100000000000000 : ℝ)^1599
        have hw : |(5664684311/10000000000 : ℝ)|=(5664684311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1762535781/10000000000 : ℝ)|^2111 ≤ (2022000286567/20000000000000 : ℝ)^1599
        have hw : |(-1762535781/10000000000 : ℝ)|=(1762535781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1251_s1_7 (p : ℝ) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ)) (x : Fin 3 → ℝ) :
    (861885701/2000000000 : ℝ)*x 0 + (4998759731/10000000000 : ℝ)*x 1 + (185734037/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (861885701/2000000000 : ℝ)^2111 ≤ (3291249573331/10000000000000 : ℝ)^1599 := by
    have hnat : (861885701 : ℕ)^2111*10000000000000^1599 ≤ 3291249573331^1599*2000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      861885701 2000000000 3291249573331 10000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4998759731/10000000000 : ℝ)^2111 ≤ (40034823794733/100000000000000 : ℝ)^1599 := by
    have hnat : (4998759731 : ℕ)^2111*100000000000000^1599 ≤ 40034823794733^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4998759731 10000000000 40034823794733 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (185734037/500000000 : ℝ)^2111 ≤ (2705268045347/10000000000000 : ℝ)^1599 := by
    have hnat : (185734037 : ℕ)^2111*10000000000000^1599 ≤ 2705268045347^1599*500000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      185734037 500000000 2705268045347 10000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2111/512 : ℝ)) 2111 1599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(861885701/2000000000 : ℝ), (4998759731/10000000000 : ℝ), (185734037/500000000 : ℝ)] ![(3291249573331/10000000000000 : ℝ), (40034823794733/100000000000000 : ℝ), (2705268045347/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(861885701/2000000000 : ℝ)|^2111 ≤ (3291249573331/10000000000000 : ℝ)^1599
        have hw : |(861885701/2000000000 : ℝ)|=(861885701/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4998759731/10000000000 : ℝ)|^2111 ≤ (40034823794733/100000000000000 : ℝ)^1599
        have hw : |(4998759731/10000000000 : ℝ)|=(4998759731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(185734037/500000000 : ℝ)|^2111 ≤ (2705268045347/10000000000000 : ℝ)^1599
        have hw : |(185734037/500000000 : ℝ)|=(185734037/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1251_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75802409/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13701/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (427/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (3119/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (19961/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13701/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (427/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13701/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (427/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13701/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (427/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13701/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (427/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13701/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (427/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13701/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (427/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (427/50000 : ℝ) ^ (8443/2048 : ℝ) ≤ (148348743629/50000000000000000000 : ℝ) := by
    have hpowers : (427/50000 : ℝ)^8443 ≤ (148348743629/50000000000000000000 : ℝ)^2048 := by
      have hnat : (427 : ℕ)^8443*50000000000000000000^2048 ≤ 148348743629^2048*50000^8443 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        427 50000 148348743629 50000000000000000000 8443 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (427/50000 : ℝ)) (X := (148348743629/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8443 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (13701/50000 : ℝ) ^ (8443/2048 : ℝ) ≤ (48108789850927193/10000000000000000000 : ℝ) := by
    have hpowers : (13701/50000 : ℝ)^8443 ≤ (48108789850927193/10000000000000000000 : ℝ)^2048 := by
      have hnat : (13701 : ℕ)^8443*10000000000000000000^2048 ≤ 48108789850927193^2048*50000^8443 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13701 50000 48108789850927193 10000000000000000000 8443 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13701/50000 : ℝ)) (X := (48108789850927193/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8443 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000000148348743629/25000000000000000000 : ℝ) ≤ (2500000003598463/2500000000000000 : ℝ) ^ (8443/2048 : ℝ) := by
    have hpowers : (25000000148348743629/25000000000000000000 : ℝ)^2048 ≤ (2500000003598463/2500000000000000 : ℝ)^8443 := by
      have hnat : (25000000148348743629 : ℕ)^2048*2500000000000000^8443 ≤ 2500000003598463^8443*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000148348743629 25000000000000000000 2500000003598463 2500000000000000 2048 8443 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000003598463/2500000000000000 : ℝ)) (X := (25000000148348743629/25000000000000000000 : ℝ)) (by norm_num) 8443 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25120272048801689797/25000000000000000000 : ℝ) ≤ (100116484489839/100000000000000 : ℝ) ^ (8443/2048 : ℝ) := by
    have hpowers : (25120272048801689797/25000000000000000000 : ℝ)^2048 ≤ (100116484489839/100000000000000 : ℝ)^8443 := by
      have hnat : (25120272048801689797 : ℕ)^2048*100000000000000^8443 ≤ 100116484489839^8443*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25120272048801689797 25000000000000000000 100116484489839 100000000000000 2048 8443 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (100116484489839/100000000000000 : ℝ)) (X := (25120272048801689797/25000000000000000000 : ℝ)) (by norm_num) 8443 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (5048108789850927193/5000000000000000000 : ℝ) ≤ (2505824220893487/2500000000000000 : ℝ) ^ (8443/2048 : ℝ) := by
    have hpowers : (5048108789850927193/5000000000000000000 : ℝ)^2048 ≤ (2505824220893487/2500000000000000 : ℝ)^8443 := by
      have hnat : (5048108789850927193 : ℕ)^2048*2500000000000000^8443 ≤ 2505824220893487^8443*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5048108789850927193 5000000000000000000 2505824220893487 2500000000000000 2048 8443 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2505824220893487/2500000000000000 : ℝ)) (X := (5048108789850927193/5000000000000000000 : ℝ)) (by norm_num) 8443 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(148348743629/50000000000000000000 : ℝ) ≤ ((16591256553490511307/16592500000000000000 : ℝ)+2*(364013580939/82962500000000 : ℝ)*(427/50000 : ℝ))^(8443/2048 : ℝ) := by
    rw [show (16591256553490511307/16592500000000000000 : ℝ)+2*(364013580939/82962500000000 : ℝ)*(427/50000 : ℝ)=(2500000003598463/2500000000000000 : ℝ) by norm_num, show 1+2*(148348743629/50000000000000000000 : ℝ)=(25000000148348743629/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(48108789850927193/10000000000000000000 : ℝ)+(148348743629/50000000000000000000 : ℝ) ≤ ((16591256553490511307/16592500000000000000 : ℝ)+(364013580939/82962500000000 : ℝ)*((13701/50000 : ℝ)+(427/50000 : ℝ)))^(8443/2048 : ℝ) := by
    rw [show (16591256553490511307/16592500000000000000 : ℝ)+(364013580939/82962500000000 : ℝ)*((13701/50000 : ℝ)+(427/50000 : ℝ))=(100116484489839/100000000000000 : ℝ) by norm_num, show 1+(48108789850927193/10000000000000000000 : ℝ)+(148348743629/50000000000000000000 : ℝ)=(25120272048801689797/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(48108789850927193/10000000000000000000 : ℝ) ≤ ((16591256553490511307/16592500000000000000 : ℝ)+2*(364013580939/82962500000000 : ℝ)*(13701/50000 : ℝ))^(8443/2048 : ℝ) := by
    rw [show (16591256553490511307/16592500000000000000 : ℝ)+2*(364013580939/82962500000000 : ℝ)*(13701/50000 : ℝ)=(2505824220893487/2500000000000000 : ℝ) by norm_num, show 1+2*(48108789850927193/10000000000000000000 : ℝ)=(5048108789850927193/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (16591256553490511307/16592500000000000000 : ℝ)*(X 1 0+X 2 0)+(364013580939/82962500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8443/2048 : ℝ)) (lo := (427/50000 : ℝ)) (hi := (13701/50000 : ℝ)) (c := (16591256553490511307/16592500000000000000 : ℝ)) (alpha := (364013580939/82962500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (16591256553490511307/16592500000000000000 : ℝ)*(X 0 1+X 2 1)+(364013580939/82962500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8443/2048 : ℝ)) (lo := (427/50000 : ℝ)) (hi := (13701/50000 : ℝ)) (c := (16591256553490511307/16592500000000000000 : ℝ)) (alpha := (364013580939/82962500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (16591256553490511307/16592500000000000000 : ℝ)*(X 0 2+X 1 2)+(364013580939/82962500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8443/2048 : ℝ)) (lo := (427/50000 : ℝ)) (hi := (13701/50000 : ℝ)) (c := (16591256553490511307/16592500000000000000 : ℝ)) (alpha := (364013580939/82962500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-205454693/1000000000 : ℝ)*X 0 0+(1134668147/2000000000 : ℝ)*X 0 1+(25121451/50000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1251_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1082633337/2000000000 : ℝ)*X 1 0+(-2402929481/10000000000 : ℝ)*X 1 1+(5024290389/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1251_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5413166857/10000000000 : ℝ)*X 2 0+(5024290271/10000000000 : ℝ)*X 2 1+(-1201464703/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1251_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((861615241/2000000000 : ℝ)*X 0 0+(924272413/2500000000 : ℝ)*X 0 1+(1003204667/2000000000 : ℝ)*X 0 2+(861615241/2000000000 : ℝ)*X 1 0+(924272413/2500000000 : ℝ)*X 1 1+(1003204667/2000000000 : ℝ)*X 1 2+(861615241/2000000000 : ℝ)*X 2 0+(924272413/2500000000 : ℝ)*X 2 1+(1003204667/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1251_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-256901559/1250000000 : ℝ)*X 0 0+(2516392867/5000000000 : ℝ)*X 0 1+(70808553/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1251_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((262294071/500000000 : ℝ)*X 1 0+(-1762535373/10000000000 : ℝ)*X 1 1+(5664684519/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1251_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1049176269/2000000000 : ℝ)*X 2 0+(5664684311/10000000000 : ℝ)*X 2 1+(-1762535781/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1251_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((861885701/2000000000 : ℝ)*X 0 0+(4998759731/10000000000 : ℝ)*X 0 1+(185734037/500000000 : ℝ)*X 0 2+(861885701/2000000000 : ℝ)*X 1 0+(4998759731/10000000000 : ℝ)*X 1 1+(185734037/500000000 : ℝ)*X 1 2+(861885701/2000000000 : ℝ)*X 2 0+(4998759731/10000000000 : ℝ)*X 2 1+(185734037/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1251_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5936822776055111548876795431/829625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6907481/10000000000000 : ℝ)*(base1) + (1572633273/100000000000000 : ℝ)*(base19) + (810794483/50000000000000 : ℝ)*(base23) + (33393509/20000000000000 : ℝ)*(upper3) + (103799419/50000000000000 : ℝ)*(upper5) + (1149464041674563/100000000000000 : ℝ)*(major0) + (1149464041674563/100000000000000 : ℝ)*(major1) + (1149464041674563/100000000000000 : ℝ)*(major2) + (48147525696507/3125000000000 : ℝ)*(sp0) + (770364352543307/50000000000000 : ℝ)*(sp1) + (1540728656130921/100000000000000 : ℝ)*(sp2) + (379096435271043/50000000000000 : ℝ)*(sp3) + (9524506473/100000000000000 : ℝ)*(sp4) + (2313738973/50000000000000 : ℝ)*(sp7) + (379098783547421/50000000000000 : ℝ)*(f.failure) + (96295642357493/6250000000000 : ℝ)*(f.sum) + (4545021883777/4148125000000000000000000000 : ℝ)*base65 + (7015325415662183841/1659250000000000000000000000000000 : ℝ)*base67 + (700087590474683841/1659250000000000000000000000000000 : ℝ)*base69 + (12854854142009683841/1659250000000000000000000000000000 : ℝ)*base71 + (213659329823/4148125000000000000000000000 : ℝ)*base74 + (11762203594209183841/1659250000000000000000000000000000 : ℝ)*base75 + (8763424541419933841/1659250000000000000000000000000000 : ℝ)*base77 + (18551246490698933841/1659250000000000000000000000000000 : ℝ)*base79 + (9572728507671/8296250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (2537189/2500000000000000000000 : ℝ)*base89 + (2537189/2500000000000000000000 : ℝ)*base91 + (2537189/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8736941557879386522197493651/829625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (21851093/25000000000000 : ℝ)*(base1) + (2107741901/100000000000000 : ℝ)*(base19) + (257218933/12500000000000 : ℝ)*(base23) + (259445281/100000000000000 : ℝ)*(upper3) + (29321853/12500000000000 : ℝ)*(upper5) + (1180650457283377/100000000000000 : ℝ)*(major0) + (1180650457283377/100000000000000 : ℝ)*(major1) + (1180650457283377/100000000000000 : ℝ)*(major2) + (10133886733/100000000000000 : ℝ)*(sp1) + (2318933311/25000000000000 : ℝ)*(sp2) + (1582532223345227/100000000000000 : ℝ)*(sp4) + (1582519894312221/100000000000000 : ℝ)*(sp5) + (1582520802456147/100000000000000 : ℝ)*(sp6) + (389384170090867/50000000000000 : ℝ)*(sp7) + (389384213793053/50000000000000 : ℝ)*(f.failure) + (316506427188171/20000000000000 : ℝ)*(f.sum) + (8956164403643/16592500000000000000000000000 : ℝ)*base66 + (8083571028518756261/1659250000000000000000000000000000 : ℝ)*base68 + (4405976920047756261/1659250000000000000000000000000000 : ℝ)*base70 + (607830810881506261/1659250000000000000000000000000000 : ℝ)*base72 + (12723957554339/8296250000000000000000000000 : ℝ)*base74 + (9071113195990756261/1659250000000000000000000000000000 : ℝ)*base76 + (10662633435638006261/1659250000000000000000000000000000 : ℝ)*base78 + (8405942103281506261/1659250000000000000000000000000000 : ℝ)*base80 + (44758281627559/33185000000000000000000000000 : ℝ)*base81 + (19864677/2500000000000000000000 : ℝ)*base89 + (19864677/2500000000000000000000 : ℝ)*base91 + (19864677/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1251_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75802409/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13701/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (427/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3119/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (19961/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1251_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1251_s2_0 (p : ℝ) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1051067879/5000000000 : ℝ)*x 0 + (5491269331/10000000000 : ℝ)*x 1 + (5176004257/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051067879/5000000000 : ℝ)^2111 ≤ (1275782528533/10000000000000 : ℝ)^1599 := by
    have hnat : (1051067879 : ℕ)^2111*10000000000000^1599 ≤ 1275782528533^1599*5000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051067879 5000000000 1275782528533 10000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5491269331/10000000000 : ℝ)^2111 ≤ (45322715806263/100000000000000 : ℝ)^1599 := by
    have hnat : (5491269331 : ℕ)^2111*100000000000000^1599 ≤ 45322715806263^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5491269331 10000000000 45322715806263 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5176004257/10000000000 : ℝ)^2111 ≤ (4191945888527/10000000000000 : ℝ)^1599 := by
    have hnat : (5176004257 : ℕ)^2111*10000000000000^1599 ≤ 4191945888527^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176004257 10000000000 4191945888527 10000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2111/512 : ℝ)) 2111 1599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1051067879/5000000000 : ℝ), (5491269331/10000000000 : ℝ), (5176004257/10000000000 : ℝ)] ![(1275782528533/10000000000000 : ℝ), (45322715806263/100000000000000 : ℝ), (4191945888527/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1051067879/5000000000 : ℝ)|^2111 ≤ (1275782528533/10000000000000 : ℝ)^1599
        have hw : |(-1051067879/5000000000 : ℝ)|=(1051067879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5491269331/10000000000 : ℝ)|^2111 ≤ (45322715806263/100000000000000 : ℝ)^1599
        have hw : |(5491269331/10000000000 : ℝ)|=(5491269331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5176004257/10000000000 : ℝ)|^2111 ≤ (4191945888527/10000000000000 : ℝ)^1599
        have hw : |(5176004257/10000000000 : ℝ)|=(5176004257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1251_s2_1 (p : ℝ) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ)) (x : Fin 3 → ℝ) :
    (335582699/625000000 : ℝ)*x 0 + (-2265390103/10000000000 : ℝ)*x 1 + (5176004347/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (335582699/625000000 : ℝ)^2111 ≤ (43998690380233/100000000000000 : ℝ)^1599 := by
    have hnat : (335582699 : ℕ)^2111*100000000000000^1599 ≤ 43998690380233^1599*625000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335582699 625000000 43998690380233 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2265390103/10000000000 : ℝ)^2111 ≤ (7040924878619/50000000000000 : ℝ)^1599 := by
    have hnat : (2265390103 : ℕ)^2111*50000000000000^1599 ≤ 7040924878619^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2265390103 10000000000 7040924878619 50000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5176004347/10000000000 : ℝ)^2111 ≤ (20959729923777/50000000000000 : ℝ)^1599 := by
    have hnat : (5176004347 : ℕ)^2111*50000000000000^1599 ≤ 20959729923777^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176004347 10000000000 20959729923777 50000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2111/512 : ℝ)) 2111 1599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(335582699/625000000 : ℝ), (-2265390103/10000000000 : ℝ), (5176004347/10000000000 : ℝ)] ![(43998690380233/100000000000000 : ℝ), (7040924878619/50000000000000 : ℝ), (20959729923777/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(335582699/625000000 : ℝ)|^2111 ≤ (43998690380233/100000000000000 : ℝ)^1599
        have hw : |(335582699/625000000 : ℝ)|=(335582699/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2265390103/10000000000 : ℝ)|^2111 ≤ (7040924878619/50000000000000 : ℝ)^1599
        have hw : |(-2265390103/10000000000 : ℝ)|=(2265390103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5176004347/10000000000 : ℝ)|^2111 ≤ (20959729923777/50000000000000 : ℝ)^1599
        have hw : |(5176004347/10000000000 : ℝ)|=(5176004347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1251_s2_2 (p : ℝ) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ)) (x : Fin 3 → ℝ) :
    (536932307/1000000000 : ℝ)*x 0 + (5176004421/10000000000 : ℝ)*x 1 + (-2265390157/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536932307/1000000000 : ℝ)^2111 ≤ (8799737829389/20000000000000 : ℝ)^1599 := by
    have hnat : (536932307 : ℕ)^2111*20000000000000^1599 ≤ 8799737829389^1599*1000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536932307 1000000000 8799737829389 20000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5176004421/10000000000 : ℝ)^2111 ≤ (20959730319383/50000000000000 : ℝ)^1599 := by
    have hnat : (5176004421 : ℕ)^2111*50000000000000^1599 ≤ 20959730319383^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176004421 10000000000 20959730319383 50000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2265390157/10000000000 : ℝ)^2111 ≤ (14081850200387/100000000000000 : ℝ)^1599 := by
    have hnat : (2265390157 : ℕ)^2111*100000000000000^1599 ≤ 14081850200387^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2265390157 10000000000 14081850200387 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2111/512 : ℝ)) 2111 1599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(536932307/1000000000 : ℝ), (5176004421/10000000000 : ℝ), (-2265390157/10000000000 : ℝ)] ![(8799737829389/20000000000000 : ℝ), (20959730319383/50000000000000 : ℝ), (14081850200387/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(536932307/1000000000 : ℝ)|^2111 ≤ (8799737829389/20000000000000 : ℝ)^1599
        have hw : |(536932307/1000000000 : ℝ)|=(536932307/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5176004421/10000000000 : ℝ)|^2111 ≤ (20959730319383/50000000000000 : ℝ)^1599
        have hw : |(5176004421/10000000000 : ℝ)|=(5176004421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2265390157/10000000000 : ℝ)|^2111 ≤ (14081850200387/100000000000000 : ℝ)^1599
        have hw : |(-2265390157/10000000000 : ℝ)|=(2265390157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1251_s2_3 (p : ℝ) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2170483549/5000000000 : ℝ)*x 0 + (2016033473/5000000000 : ℝ)*x 1 + (292044729/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2170483549/5000000000 : ℝ)^2111 ≤ (16615432428489/50000000000000 : ℝ)^1599 := by
    have hnat : (2170483549 : ℕ)^2111*50000000000000^1599 ≤ 16615432428489^1599*5000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2170483549 5000000000 16615432428489 50000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2016033473/5000000000 : ℝ)^2111 ≤ (30145165007311/100000000000000 : ℝ)^1599 := by
    have hnat : (2016033473 : ℕ)^2111*100000000000000^1599 ≤ 30145165007311^1599*5000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2016033473 5000000000 30145165007311 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (292044729/625000000 : ℝ)^2111 ≤ (36623970119347/100000000000000 : ℝ)^1599 := by
    have hnat : (292044729 : ℕ)^2111*100000000000000^1599 ≤ 36623970119347^1599*625000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      292044729 625000000 36623970119347 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2111/512 : ℝ)) 2111 1599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2170483549/5000000000 : ℝ), (2016033473/5000000000 : ℝ), (292044729/625000000 : ℝ)] ![(16615432428489/50000000000000 : ℝ), (30145165007311/100000000000000 : ℝ), (36623970119347/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2170483549/5000000000 : ℝ)|^2111 ≤ (16615432428489/50000000000000 : ℝ)^1599
        have hw : |(2170483549/5000000000 : ℝ)|=(2170483549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2016033473/5000000000 : ℝ)|^2111 ≤ (30145165007311/100000000000000 : ℝ)^1599
        have hw : |(2016033473/5000000000 : ℝ)|=(2016033473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(292044729/625000000 : ℝ)|^2111 ≤ (36623970119347/100000000000000 : ℝ)^1599
        have hw : |(292044729/625000000 : ℝ)|=(292044729/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1251_s2_4 (p : ℝ) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-420442467/2000000000 : ℝ)*x 0 + (161813077/312500000 : ℝ)*x 1 + (5489236347/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (420442467/2000000000 : ℝ)^2111 ≤ (12758438844627/100000000000000 : ℝ)^1599 := by
    have hnat : (420442467 : ℕ)^2111*100000000000000^1599 ≤ 12758438844627^1599*2000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420442467 2000000000 12758438844627 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (161813077/312500000 : ℝ)^2111 ≤ (4194099622049/10000000000000 : ℝ)^1599 := by
    have hnat : (161813077 : ℕ)^2111*10000000000000^1599 ≤ 4194099622049^1599*312500000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161813077 312500000 4194099622049 10000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5489236347/10000000000 : ℝ)^2111 ≤ (11325141229249/25000000000000 : ℝ)^1599 := by
    have hnat : (5489236347 : ℕ)^2111*25000000000000^1599 ≤ 11325141229249^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5489236347 10000000000 11325141229249 25000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2111/512 : ℝ)) 2111 1599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-420442467/2000000000 : ℝ), (161813077/312500000 : ℝ), (5489236347/10000000000 : ℝ)] ![(12758438844627/100000000000000 : ℝ), (4194099622049/10000000000000 : ℝ), (11325141229249/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-420442467/2000000000 : ℝ)|^2111 ≤ (12758438844627/100000000000000 : ℝ)^1599
        have hw : |(-420442467/2000000000 : ℝ)|=(420442467/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(161813077/312500000 : ℝ)|^2111 ≤ (4194099622049/10000000000000 : ℝ)^1599
        have hw : |(161813077/312500000 : ℝ)|=(161813077/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5489236347/10000000000 : ℝ)|^2111 ≤ (11325141229249/25000000000000 : ℝ)^1599
        have hw : |(5489236347/10000000000 : ℝ)|=(5489236347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1251_s2_5 (p : ℝ) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1057753591/2000000000 : ℝ)*x 0 + (-1952157857/10000000000 : ℝ)*x 1 + (686154549/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057753591/2000000000 : ℝ)^2111 ≤ (43129318236161/100000000000000 : ℝ)^1599 := by
    have hnat : (1057753591 : ℕ)^2111*100000000000000^1599 ≤ 43129318236161^1599*2000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057753591 2000000000 43129318236161 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1952157857/10000000000 : ℝ)^2111 ≤ (11570116338579/100000000000000 : ℝ)^1599 := by
    have hnat : (1952157857 : ℕ)^2111*100000000000000^1599 ≤ 11570116338579^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1952157857 10000000000 11570116338579 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (686154549/1250000000 : ℝ)^2111 ≤ (11325141351819/25000000000000 : ℝ)^1599 := by
    have hnat : (686154549 : ℕ)^2111*25000000000000^1599 ≤ 11325141351819^1599*1250000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      686154549 1250000000 11325141351819 25000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2111/512 : ℝ)) 2111 1599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057753591/2000000000 : ℝ), (-1952157857/10000000000 : ℝ), (686154549/1250000000 : ℝ)] ![(43129318236161/100000000000000 : ℝ), (11570116338579/100000000000000 : ℝ), (11325141351819/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057753591/2000000000 : ℝ)|^2111 ≤ (43129318236161/100000000000000 : ℝ)^1599
        have hw : |(1057753591/2000000000 : ℝ)|=(1057753591/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1952157857/10000000000 : ℝ)|^2111 ≤ (11570116338579/100000000000000 : ℝ)^1599
        have hw : |(-1952157857/10000000000 : ℝ)|=(1952157857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(686154549/1250000000 : ℝ)|^2111 ≤ (11325141351819/25000000000000 : ℝ)^1599
        have hw : |(686154549/1250000000 : ℝ)|=(686154549/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1251_s2_6 (p : ℝ) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1057753621/2000000000 : ℝ)*x 0 + (5489236489/10000000000 : ℝ)*x 1 + (-1952157517/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057753621/2000000000 : ℝ)^2111 ≤ (21564659925537/50000000000000 : ℝ)^1599 := by
    have hnat : (1057753621 : ℕ)^2111*50000000000000^1599 ≤ 21564659925537^1599*2000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057753621 2000000000 21564659925537 50000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5489236489/10000000000 : ℝ)^2111 ≤ (45300566464101/100000000000000 : ℝ)^1599 := by
    have hnat : (5489236489 : ℕ)^2111*100000000000000^1599 ≤ 45300566464101^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5489236489 10000000000 45300566464101 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1952157517/10000000000 : ℝ)^2111 ≤ (2892528419553/25000000000000 : ℝ)^1599 := by
    have hnat : (1952157517 : ℕ)^2111*25000000000000^1599 ≤ 2892528419553^1599*10000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1952157517 10000000000 2892528419553 25000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2111/512 : ℝ)) 2111 1599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057753621/2000000000 : ℝ), (5489236489/10000000000 : ℝ), (-1952157517/10000000000 : ℝ)] ![(21564659925537/50000000000000 : ℝ), (45300566464101/100000000000000 : ℝ), (2892528419553/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057753621/2000000000 : ℝ)|^2111 ≤ (21564659925537/50000000000000 : ℝ)^1599
        have hw : |(1057753621/2000000000 : ℝ)|=(1057753621/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5489236489/10000000000 : ℝ)|^2111 ≤ (45300566464101/100000000000000 : ℝ)^1599
        have hw : |(5489236489/10000000000 : ℝ)|=(5489236489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1952157517/10000000000 : ℝ)|^2111 ≤ (2892528419553/25000000000000 : ℝ)^1599
        have hw : |(-1952157517/10000000000 : ℝ)|=(1952157517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1251_s2_7 (p : ℝ) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1085280553/2500000000 : ℝ)*x 0 + (1167155743/2500000000 : ℝ)*x 1 + (2018098707/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1085280553/2500000000 : ℝ)^2111 ≤ (33232432504433/100000000000000 : ℝ)^1599 := by
    have hnat : (1085280553 : ℕ)^2111*100000000000000^1599 ≤ 33232432504433^1599*2500000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085280553 2500000000 33232432504433 100000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1167155743/2500000000 : ℝ)^2111 ≤ (9145406722371/25000000000000 : ℝ)^1599 := by
    have hnat : (1167155743 : ℕ)^2111*25000000000000^1599 ≤ 9145406722371^1599*2500000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1167155743 2500000000 9145406722371 25000000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2018098707/5000000000 : ℝ)^2111 ≤ (1886621286827/6250000000000 : ℝ)^1599 := by
    have hnat : (2018098707 : ℕ)^2111*6250000000000^1599 ≤ 1886621286827^1599*5000000000^2111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2018098707 5000000000 1886621286827 6250000000000 2111 1599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2111/512 : ℝ)) 2111 1599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1085280553/2500000000 : ℝ), (1167155743/2500000000 : ℝ), (2018098707/5000000000 : ℝ)] ![(33232432504433/100000000000000 : ℝ), (9145406722371/25000000000000 : ℝ), (1886621286827/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1085280553/2500000000 : ℝ)|^2111 ≤ (33232432504433/100000000000000 : ℝ)^1599
        have hw : |(1085280553/2500000000 : ℝ)|=(1085280553/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1167155743/2500000000 : ℝ)|^2111 ≤ (9145406722371/25000000000000 : ℝ)^1599
        have hw : |(1167155743/2500000000 : ℝ)|=(1167155743/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2018098707/5000000000 : ℝ)|^2111 ≤ (1886621286827/6250000000000 : ℝ)^1599
        have hw : |(2018098707/5000000000 : ℝ)|=(2018098707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1251_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75802409/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19961/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3119/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (298/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (81/500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (19961/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3119/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (19961/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3119/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (19961/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3119/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (19961/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3119/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (19961/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3119/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (19961/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3119/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3119/50000 : ℝ) ^ (8443/2048 : ℝ) ≤ (107771502281731/10000000000000000000 : ℝ) := by
    have hpowers : (3119/50000 : ℝ)^8443 ≤ (107771502281731/10000000000000000000 : ℝ)^2048 := by
      have hnat : (3119 : ℕ)^8443*10000000000000000000^2048 ≤ 107771502281731^2048*50000^8443 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3119 50000 107771502281731 10000000000000000000 8443 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3119/50000 : ℝ)) (X := (107771502281731/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8443 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (19961/100000 : ℝ) ^ (8443/2048 : ℝ) ≤ (32576206807220827/25000000000000000000 : ℝ) := by
    have hpowers : (19961/100000 : ℝ)^8443 ≤ (32576206807220827/25000000000000000000 : ℝ)^2048 := by
      have hnat : (19961 : ℕ)^8443*25000000000000000000^2048 ≤ 32576206807220827^2048*100000^8443 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19961 100000 32576206807220827 25000000000000000000 8443 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19961/100000 : ℝ)) (X := (32576206807220827/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8443 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000107771502281731/5000000000000000000 : ℝ) ≤ (10000052283367287/10000000000000000 : ℝ) ^ (8443/2048 : ℝ) := by
    have hpowers : (5000107771502281731/5000000000000000000 : ℝ)^2048 ≤ (10000052283367287/10000000000000000 : ℝ)^8443 := by
      have hnat : (5000107771502281731 : ℕ)^2048*10000000000000000^8443 ≤ 10000052283367287^8443*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000107771502281731 5000000000000000000 10000052283367287 10000000000000000 2048 8443 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000052283367287/10000000000000000 : ℝ)) (X := (5000107771502281731/5000000000000000000 : ℝ)) (by norm_num) 8443 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50065691271125850309/50000000000000000000 : ℝ) ≤ (5001592666519319/5000000000000000 : ℝ) ^ (8443/2048 : ℝ) := by
    have hpowers : (50065691271125850309/50000000000000000000 : ℝ)^2048 ≤ (5001592666519319/5000000000000000 : ℝ)^8443 := by
      have hnat : (50065691271125850309 : ℕ)^2048*5000000000000000^8443 ≤ 5001592666519319^8443*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50065691271125850309 50000000000000000000 5001592666519319 5000000000000000 2048 8443 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001592666519319/5000000000000000 : ℝ)) (X := (50065691271125850309/50000000000000000000 : ℝ)) (by norm_num) 8443 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12532576206807220827/12500000000000000000 : ℝ) ≤ (10006318382709989/10000000000000000 : ℝ) ^ (8443/2048 : ℝ) := by
    have hpowers : (12532576206807220827/12500000000000000000 : ℝ)^2048 ≤ (10006318382709989/10000000000000000 : ℝ)^8443 := by
      have hnat : (12532576206807220827 : ℕ)^2048*10000000000000000^8443 ≤ 10006318382709989^8443*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12532576206807220827 12500000000000000000 10006318382709989 10000000000000000 2048 8443 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006318382709989/10000000000000000 : ℝ)) (X := (12532576206807220827/12500000000000000000 : ℝ)) (by norm_num) 8443 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(107771502281731/10000000000000000000 : ℝ) ≤ ((5487665182277980177/5489200000000000000 : ℝ)+2*(3133049671351/1372300000000000 : ℝ)*(3119/50000 : ℝ))^(8443/2048 : ℝ) := by
    rw [show (5487665182277980177/5489200000000000000 : ℝ)+2*(3133049671351/1372300000000000 : ℝ)*(3119/50000 : ℝ)=(10000052283367287/10000000000000000 : ℝ) by norm_num, show 1+2*(107771502281731/10000000000000000000 : ℝ)=(5000107771502281731/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32576206807220827/25000000000000000000 : ℝ)+(107771502281731/10000000000000000000 : ℝ) ≤ ((5487665182277980177/5489200000000000000 : ℝ)+(3133049671351/1372300000000000 : ℝ)*((19961/100000 : ℝ)+(3119/50000 : ℝ)))^(8443/2048 : ℝ) := by
    rw [show (5487665182277980177/5489200000000000000 : ℝ)+(3133049671351/1372300000000000 : ℝ)*((19961/100000 : ℝ)+(3119/50000 : ℝ))=(5001592666519319/5000000000000000 : ℝ) by norm_num, show 1+(32576206807220827/25000000000000000000 : ℝ)+(107771502281731/10000000000000000000 : ℝ)=(50065691271125850309/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32576206807220827/25000000000000000000 : ℝ) ≤ ((5487665182277980177/5489200000000000000 : ℝ)+2*(3133049671351/1372300000000000 : ℝ)*(19961/100000 : ℝ))^(8443/2048 : ℝ) := by
    rw [show (5487665182277980177/5489200000000000000 : ℝ)+2*(3133049671351/1372300000000000 : ℝ)*(19961/100000 : ℝ)=(10006318382709989/10000000000000000 : ℝ) by norm_num, show 1+2*(32576206807220827/25000000000000000000 : ℝ)=(12532576206807220827/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5487665182277980177/5489200000000000000 : ℝ)*(X 1 0+X 2 0)+(3133049671351/1372300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8443/2048 : ℝ)) (lo := (3119/50000 : ℝ)) (hi := (19961/100000 : ℝ)) (c := (5487665182277980177/5489200000000000000 : ℝ)) (alpha := (3133049671351/1372300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5487665182277980177/5489200000000000000 : ℝ)*(X 0 1+X 2 1)+(3133049671351/1372300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8443/2048 : ℝ)) (lo := (3119/50000 : ℝ)) (hi := (19961/100000 : ℝ)) (c := (5487665182277980177/5489200000000000000 : ℝ)) (alpha := (3133049671351/1372300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5487665182277980177/5489200000000000000 : ℝ)*(X 0 2+X 1 2)+(3133049671351/1372300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8443/2048 : ℝ)) (lo := (3119/50000 : ℝ)) (hi := (19961/100000 : ℝ)) (c := (5487665182277980177/5489200000000000000 : ℝ)) (alpha := (3133049671351/1372300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1051067879/5000000000 : ℝ)*X 0 0+(5491269331/10000000000 : ℝ)*X 0 1+(5176004257/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1251_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((335582699/625000000 : ℝ)*X 1 0+(-2265390103/10000000000 : ℝ)*X 1 1+(5176004347/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1251_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((536932307/1000000000 : ℝ)*X 2 0+(5176004421/10000000000 : ℝ)*X 2 1+(-2265390157/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1251_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2170483549/5000000000 : ℝ)*X 0 0+(2016033473/5000000000 : ℝ)*X 0 1+(292044729/625000000 : ℝ)*X 0 2+(2170483549/5000000000 : ℝ)*X 1 0+(2016033473/5000000000 : ℝ)*X 1 1+(292044729/625000000 : ℝ)*X 1 2+(2170483549/5000000000 : ℝ)*X 2 0+(2016033473/5000000000 : ℝ)*X 2 1+(292044729/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1251_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-420442467/2000000000 : ℝ)*X 0 0+(161813077/312500000 : ℝ)*X 0 1+(5489236347/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1251_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1057753591/2000000000 : ℝ)*X 1 0+(-1952157857/10000000000 : ℝ)*X 1 1+(686154549/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1251_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1057753621/2000000000 : ℝ)*X 2 0+(5489236489/10000000000 : ℝ)*X 2 1+(-1952157517/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1251_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1085280553/2500000000 : ℝ)*X 0 0+(1167155743/2500000000 : ℝ)*X 0 1+(2018098707/5000000000 : ℝ)*X 0 2+(1085280553/2500000000 : ℝ)*X 1 0+(1167155743/2500000000 : ℝ)*X 1 1+(2018098707/5000000000 : ℝ)*X 1 2+(1085280553/2500000000 : ℝ)*X 2 0+(1167155743/2500000000 : ℝ)*X 2 1+(2018098707/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1251_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (102428270410515513395217/34307500000000000000000000000 : ℝ) := by norm_num
    linear_combination (233095713/50000000000000 : ℝ)*(base19) + (373059137/100000000000000 : ℝ)*(base23) + (346139/2500000000000 : ℝ)*(lower2) + (96083133/100000000000000 : ℝ)*(upper3) + (706159/3125000000000 : ℝ)*(upper5) + (1183217148275621/50000000000000 : ℝ)*(major0) + (1183217148275621/50000000000000 : ℝ)*(major1) + (1183217148275621/50000000000000 : ℝ)*(major2) + (3171940586559479/100000000000000 : ℝ)*(sp0) + (634389028791347/20000000000000 : ℝ)*(sp1) + (12390411082379/390625000000 : ℝ)*(sp2) + (1560920058176243/100000000000000 : ℝ)*(sp3) + (2511794341/50000000000000 : ℝ)*(sp4) + (706314567/25000000000000 : ℝ)*(sp7) + (156092288343451/10000000000000 : ℝ)*(f.failure) + (3171945610148161/100000000000000 : ℝ)*(f.sum) + (146072219817257/17153750000000000000000000000 : ℝ)*base66 + (841511165141588917/274460000000000000000000000000000 : ℝ)*base67 + (819291792004188917/274460000000000000000000000000000 : ℝ)*base69 + (1283766139373951083/274460000000000000000000000000000 : ℝ)*base72 + (88265498234507/68615000000000000000000000000 : ℝ)*base73 + (618878687040291083/274460000000000000000000000000000 : ℝ)*base76 + (1689566074076351083/274460000000000000000000000000000 : ℝ)*base78 + (123218576254368917/274460000000000000000000000000000 : ℝ)*base79 + (34223032305151/34307500000000000000000000000 : ℝ)*base81 + (4826541/500000000000000000000 : ℝ)*base90 + (4826541/500000000000000000000 : ℝ)*base92 + (4826541/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (98972862905344095467024541/13723000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (46049539/2500000000000 : ℝ)*(base19) + (1046621661/50000000000000 : ℝ)*(base23) + (1767671/5000000000000 : ℝ)*(upper2) + (25062141/10000000000000 : ℝ)*(upper3) + (563041/400000000000 : ℝ)*(upper5) + (239719808578289/10000000000000 : ℝ)*(major0) + (239719808578289/10000000000000 : ℝ)*(major1) + (239719808578289/10000000000000 : ℝ)*(major2) + (2373289439/12500000000000 : ℝ)*(sp1) + (25110818617/100000000000000 : ℝ)*(sp2) + (160659047783391/5000000000000 : ℝ)*(sp4) + (803290031842687/25000000000000 : ℝ)*(sp5) + (1606576875802941/50000000000000 : ℝ)*(sp6) + (1581214975491669/100000000000000 : ℝ)*(sp7) + (1581214975491669/100000000000000 : ℝ)*(f.failure) + (160659047783391/5000000000000 : ℝ)*(f.sum) + (14596174462167/6861500000000000000000000000 : ℝ)*base65 + (466750581413117153/54892000000000000000000000000000 : ℝ)*base67 + (256077898188981153/54892000000000000000000000000000 : ℝ)*base69 + (163284900544941153/54892000000000000000000000000000 : ℝ)*base71 + (590262303473/1372300000000000000000000000 : ℝ)*base74 + (496442372429701153/54892000000000000000000000000000 : ℝ)*base75 + (144161776428157153/54892000000000000000000000000000 : ℝ)*base77 + (23539579409782847/54892000000000000000000000000000 : ℝ)*base80 + (35500397764591/13723000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (30369379/5000000000000000000000 : ℝ)*base90 + (30369379/5000000000000000000000 : ℝ)*base92 + (30369379/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1251_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75802409/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19961/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3119/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (298/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (81/500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1251_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1251_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75802409/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (298/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (81/500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1251_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1251_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1251_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8443/2048 : ℝ) ≤ p) (hpb : p ≤ (2111/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75802409/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (298/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (81/500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1251_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
