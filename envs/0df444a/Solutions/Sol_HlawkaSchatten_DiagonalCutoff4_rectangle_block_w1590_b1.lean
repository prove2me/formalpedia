-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1590_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:36:57.885488+00:00
-- url     : https://prove2.me/submissions/13d58ea2-1a23-4f2a-af2d-2ccf8aeea467

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
theorem support_rectangle_w1590_s3_0 (p : ℝ) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-351149211/2000000000 : ℝ)*x 0 + (2733332309/5000000000 : ℝ)*x 1 + (1294447139/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (351149211/2000000000 : ℝ)^4679 ≤ (539208778179/5000000000000 : ℝ)^3655 := by
    have hnat : (351149211 : ℕ)^4679*5000000000000^3655 ≤ 539208778179^3655*2000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      351149211 2000000000 539208778179 5000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2733332309/5000000000 : ℝ)^4679 ≤ (23078716926809/50000000000000 : ℝ)^3655 := by
    have hnat : (2733332309 : ℕ)^4679*50000000000000^3655 ≤ 23078716926809^3655*5000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2733332309 5000000000 23078716926809 50000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1294447139/2500000000 : ℝ)^4679 ≤ (43058390566031/100000000000000 : ℝ)^3655 := by
    have hnat : (1294447139 : ℕ)^4679*100000000000000^3655 ≤ 43058390566031^3655*2500000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294447139 2500000000 43058390566031 100000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4679/1024 : ℝ)) 4679 3655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-351149211/2000000000 : ℝ), (2733332309/5000000000 : ℝ), (1294447139/2500000000 : ℝ)] ![(539208778179/5000000000000 : ℝ), (23078716926809/50000000000000 : ℝ), (43058390566031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-351149211/2000000000 : ℝ)|^4679 ≤ (539208778179/5000000000000 : ℝ)^3655
        have hw : |(-351149211/2000000000 : ℝ)|=(351149211/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2733332309/5000000000 : ℝ)|^4679 ≤ (23078716926809/50000000000000 : ℝ)^3655
        have hw : |(2733332309/5000000000 : ℝ)|=(2733332309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1294447139/2500000000 : ℝ)|^4679 ≤ (43058390566031/100000000000000 : ℝ)^3655
        have hw : |(1294447139/2500000000 : ℝ)|=(1294447139/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1590_s3_1 (p : ℝ) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5356604749/10000000000 : ℝ)*x 0 + (-476218073/2500000000 : ℝ)*x 1 + (2588894287/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5356604749/10000000000 : ℝ)^4679 ≤ (56213962349/125000000000 : ℝ)^3655 := by
    have hnat : (5356604749 : ℕ)^4679*125000000000^3655 ≤ 56213962349^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5356604749 10000000000 56213962349 125000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (476218073/2500000000 : ℝ)^4679 ≤ (11970439347883/100000000000000 : ℝ)^3655 := by
    have hnat : (476218073 : ℕ)^4679*100000000000000^3655 ≤ 11970439347883^3655*2500000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      476218073 2500000000 11970439347883 100000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2588894287/5000000000 : ℝ)^4679 ≤ (5382298844707/12500000000000 : ℝ)^3655 := by
    have hnat : (2588894287 : ℕ)^4679*12500000000000^3655 ≤ 5382298844707^3655*5000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588894287 5000000000 5382298844707 12500000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4679/1024 : ℝ)) 4679 3655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5356604749/10000000000 : ℝ), (-476218073/2500000000 : ℝ), (2588894287/5000000000 : ℝ)] ![(56213962349/125000000000 : ℝ), (11970439347883/100000000000000 : ℝ), (5382298844707/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5356604749/10000000000 : ℝ)|^4679 ≤ (56213962349/125000000000 : ℝ)^3655
        have hw : |(5356604749/10000000000 : ℝ)|=(5356604749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-476218073/2500000000 : ℝ)|^4679 ≤ (11970439347883/100000000000000 : ℝ)^3655
        have hw : |(-476218073/2500000000 : ℝ)|=(476218073/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2588894287/5000000000 : ℝ)|^4679 ≤ (5382298844707/12500000000000 : ℝ)^3655
        have hw : |(2588894287/5000000000 : ℝ)|=(2588894287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1590_s3_2 (p : ℝ) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5356604753/10000000000 : ℝ)*x 0 + (1294447137/2500000000 : ℝ)*x 1 + (-1904872321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5356604753/10000000000 : ℝ)^4679 ≤ (4497116992219/10000000000000 : ℝ)^3655 := by
    have hnat : (5356604753 : ℕ)^4679*10000000000000^3655 ≤ 4497116992219^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5356604753 10000000000 4497116992219 10000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1294447137/2500000000 : ℝ)^4679 ≤ (8611678096173/20000000000000 : ℝ)^3655 := by
    have hnat : (1294447137 : ℕ)^4679*20000000000000^3655 ≤ 8611678096173^3655*2500000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294447137 2500000000 8611678096173 20000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1904872321/10000000000 : ℝ)^4679 ≤ (11970439581179/100000000000000 : ℝ)^3655 := by
    have hnat : (1904872321 : ℕ)^4679*100000000000000^3655 ≤ 11970439581179^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1904872321 10000000000 11970439581179 100000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4679/1024 : ℝ)) 4679 3655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5356604753/10000000000 : ℝ), (1294447137/2500000000 : ℝ), (-1904872321/10000000000 : ℝ)] ![(4497116992219/10000000000000 : ℝ), (8611678096173/20000000000000 : ℝ), (11970439581179/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5356604753/10000000000 : ℝ)|^4679 ≤ (4497116992219/10000000000000 : ℝ)^3655
        have hw : |(5356604753/10000000000 : ℝ)|=(5356604753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1294447137/2500000000 : ℝ)|^4679 ≤ (8611678096173/20000000000000 : ℝ)^3655
        have hw : |(1294447137/2500000000 : ℝ)|=(1294447137/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1904872321/10000000000 : ℝ)|^4679 ≤ (11970439581179/100000000000000 : ℝ)^3655
        have hw : |(-1904872321/10000000000 : ℝ)|=(1904872321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1590_s3_3 (p : ℝ) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4229213859/10000000000 : ℝ)*x 0 + (3894826921/10000000000 : ℝ)*x 1 + (1146509083/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4229213859/10000000000 : ℝ)^4679 ≤ (33231580359541/100000000000000 : ℝ)^3655 := by
    have hnat : (4229213859 : ℕ)^4679*100000000000000^3655 ≤ 33231580359541^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4229213859 10000000000 33231580359541 100000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3894826921/10000000000 : ℝ)^4679 ≤ (29905951451121/100000000000000 : ℝ)^3655 := by
    have hnat : (3894826921 : ℕ)^4679*100000000000000^3655 ≤ 29905951451121^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3894826921 10000000000 29905951451121 100000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1146509083/2500000000 : ℝ)^4679 ≤ (36862468168051/100000000000000 : ℝ)^3655 := by
    have hnat : (1146509083 : ℕ)^4679*100000000000000^3655 ≤ 36862468168051^3655*2500000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1146509083 2500000000 36862468168051 100000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4679/1024 : ℝ)) 4679 3655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4229213859/10000000000 : ℝ), (3894826921/10000000000 : ℝ), (1146509083/2500000000 : ℝ)] ![(33231580359541/100000000000000 : ℝ), (29905951451121/100000000000000 : ℝ), (36862468168051/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4229213859/10000000000 : ℝ)|^4679 ≤ (33231580359541/100000000000000 : ℝ)^3655
        have hw : |(4229213859/10000000000 : ℝ)|=(4229213859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3894826921/10000000000 : ℝ)|^4679 ≤ (29905951451121/100000000000000 : ℝ)^3655
        have hw : |(3894826921/10000000000 : ℝ)|=(3894826921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1146509083/2500000000 : ℝ)|^4679 ≤ (36862468168051/100000000000000 : ℝ)^3655
        have hw : |(1146509083/2500000000 : ℝ)|=(1146509083/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1590_s3_4 (p : ℝ) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-219477653/1250000000 : ℝ)*x 0 + (2589965161/5000000000 : ℝ)*x 1 + (2732250129/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (219477653/1250000000 : ℝ)^4679 ≤ (134809582807/1250000000000 : ℝ)^3655 := by
    have hnat : (219477653 : ℕ)^4679*1250000000000^3655 ≤ 134809582807^3655*1250000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219477653 1250000000 134809582807 1250000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2589965161/5000000000 : ℝ)^4679 ≤ (4308119274379/10000000000000 : ℝ)^3655 := by
    have hnat : (2589965161 : ℕ)^4679*10000000000000^3655 ≤ 4308119274379^3655*5000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2589965161 5000000000 4308119274379 10000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2732250129/5000000000 : ℝ)^4679 ≤ (9226808123559/20000000000000 : ℝ)^3655 := by
    have hnat : (2732250129 : ℕ)^4679*20000000000000^3655 ≤ 9226808123559^3655*5000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2732250129 5000000000 9226808123559 20000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4679/1024 : ℝ)) 4679 3655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-219477653/1250000000 : ℝ), (2589965161/5000000000 : ℝ), (2732250129/5000000000 : ℝ)] ![(134809582807/1250000000000 : ℝ), (4308119274379/10000000000000 : ℝ), (9226808123559/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-219477653/1250000000 : ℝ)|^4679 ≤ (134809582807/1250000000000 : ℝ)^3655
        have hw : |(-219477653/1250000000 : ℝ)|=(219477653/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2589965161/5000000000 : ℝ)|^4679 ≤ (4308119274379/10000000000000 : ℝ)^3655
        have hw : |(2589965161/5000000000 : ℝ)|=(2589965161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2732250129/5000000000 : ℝ)|^4679 ≤ (9226808123559/20000000000000 : ℝ)^3655
        have hw : |(2732250129/5000000000 : ℝ)|=(2732250129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1590_s3_5 (p : ℝ) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2640093861/5000000000 : ℝ)*x 0 + (-404540149/2500000000 : ℝ)*x 1 + (136612503/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2640093861/5000000000 : ℝ)^4679 ≤ (4415151953467/10000000000000 : ℝ)^3655 := by
    have hnat : (2640093861 : ℕ)^4679*10000000000000^3655 ≤ 4415151953467^3655*5000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640093861 5000000000 4415151953467 10000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (404540149/2500000000 : ℝ)^4679 ≤ (2428610330957/25000000000000 : ℝ)^3655 := by
    have hnat : (404540149 : ℕ)^4679*25000000000000^3655 ≤ 2428610330957^3655*2500000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      404540149 2500000000 2428610330957 25000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (136612503/250000000 : ℝ)^4679 ≤ (46134039126321/100000000000000 : ℝ)^3655 := by
    have hnat : (136612503 : ℕ)^4679*100000000000000^3655 ≤ 46134039126321^3655*250000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136612503 250000000 46134039126321 100000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4679/1024 : ℝ)) 4679 3655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2640093861/5000000000 : ℝ), (-404540149/2500000000 : ℝ), (136612503/250000000 : ℝ)] ![(4415151953467/10000000000000 : ℝ), (2428610330957/25000000000000 : ℝ), (46134039126321/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2640093861/5000000000 : ℝ)|^4679 ≤ (4415151953467/10000000000000 : ℝ)^3655
        have hw : |(2640093861/5000000000 : ℝ)|=(2640093861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-404540149/2500000000 : ℝ)|^4679 ≤ (2428610330957/25000000000000 : ℝ)^3655
        have hw : |(-404540149/2500000000 : ℝ)|=(404540149/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(136612503/250000000 : ℝ)|^4679 ≤ (46134039126321/100000000000000 : ℝ)^3655
        have hw : |(136612503/250000000 : ℝ)|=(136612503/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1590_s3_6 (p : ℝ) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1320046891/2500000000 : ℝ)*x 0 + (2732250149/5000000000 : ℝ)*x 1 + (-809080283/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1320046891/2500000000 : ℝ)^4679 ≤ (2759469865211/6250000000000 : ℝ)^3655 := by
    have hnat : (1320046891 : ℕ)^4679*6250000000000^3655 ≤ 2759469865211^3655*2500000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320046891 2500000000 2759469865211 6250000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2732250149/5000000000 : ℝ)^4679 ≤ (46134041050107/100000000000000 : ℝ)^3655 := by
    have hnat : (2732250149 : ℕ)^4679*100000000000000^3655 ≤ 46134041050107^3655*5000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2732250149 5000000000 46134041050107 100000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (809080283/5000000000 : ℝ)^4679 ≤ (2428610273317/25000000000000 : ℝ)^3655 := by
    have hnat : (809080283 : ℕ)^4679*25000000000000^3655 ≤ 2428610273317^3655*5000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      809080283 5000000000 2428610273317 25000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4679/1024 : ℝ)) 4679 3655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1320046891/2500000000 : ℝ), (2732250149/5000000000 : ℝ), (-809080283/5000000000 : ℝ)] ![(2759469865211/6250000000000 : ℝ), (46134041050107/100000000000000 : ℝ), (2428610273317/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1320046891/2500000000 : ℝ)|^4679 ≤ (2759469865211/6250000000000 : ℝ)^3655
        have hw : |(1320046891/2500000000 : ℝ)|=(1320046891/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2732250149/5000000000 : ℝ)|^4679 ≤ (46134041050107/100000000000000 : ℝ)^3655
        have hw : |(2732250149/5000000000 : ℝ)|=(2732250149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-809080283/5000000000 : ℝ)|^4679 ≤ (2428610273317/25000000000000 : ℝ)^3655
        have hw : |(-809080283/5000000000 : ℝ)|=(809080283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1590_s3_7 (p : ℝ) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4229393743/10000000000 : ℝ)*x 0 + (4580911617/10000000000 : ℝ)*x 1 + (1950002877/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4229393743/10000000000 : ℝ)^4679 ≤ (16616694916331/50000000000000 : ℝ)^3655 := by
    have hnat : (4229393743 : ℕ)^4679*50000000000000^3655 ≤ 16616694916331^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4229393743 10000000000 16616694916331 50000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4580911617/10000000000 : ℝ)^4679 ≤ (36809743446469/100000000000000 : ℝ)^3655 := by
    have hnat : (4580911617 : ℕ)^4679*100000000000000^3655 ≤ 36809743446469^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4580911617 10000000000 36809743446469 100000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1950002877/5000000000 : ℝ)^4679 ≤ (5991373340469/20000000000000 : ℝ)^3655 := by
    have hnat : (1950002877 : ℕ)^4679*20000000000000^3655 ≤ 5991373340469^3655*5000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1950002877 5000000000 5991373340469 20000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4679/1024 : ℝ)) 4679 3655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4229393743/10000000000 : ℝ), (4580911617/10000000000 : ℝ), (1950002877/5000000000 : ℝ)] ![(16616694916331/50000000000000 : ℝ), (36809743446469/100000000000000 : ℝ), (5991373340469/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4229393743/10000000000 : ℝ)|^4679 ≤ (16616694916331/50000000000000 : ℝ)^3655
        have hw : |(4229393743/10000000000 : ℝ)|=(4229393743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4580911617/10000000000 : ℝ)|^4679 ≤ (36809743446469/100000000000000 : ℝ)^3655
        have hw : |(4580911617/10000000000 : ℝ)|=(4580911617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1950002877/5000000000 : ℝ)|^4679 ≤ (5991373340469/20000000000000 : ℝ)^3655
        have hw : |(1950002877/5000000000 : ℝ)|=(1950002877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1590_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84818851/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8293/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2021/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (10277/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3279/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8293/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2021/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8293/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2021/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8293/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2021/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8293/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2021/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8293/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2021/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8293/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2021/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2021/20000 : ℝ) ^ (4675/1024 : ℝ) ≤ (2852860610171939/100000000000000000000 : ℝ) := by
    have hpowers : (2021/20000 : ℝ)^4675 ≤ (2852860610171939/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2021 : ℕ)^4675*100000000000000000000^1024 ≤ 2852860610171939^1024*20000^4675 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2021 20000 2852860610171939 100000000000000000000 4675 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2021/20000 : ℝ)) (X := (2852860610171939/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4675 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8293/50000 : ℝ) ^ (4675/1024 : ℝ) ≤ (27402198967809983/100000000000000000000 : ℝ) := by
    have hpowers : (8293/50000 : ℝ)^4675 ≤ (27402198967809983/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8293 : ℕ)^4675*100000000000000000000^1024 ≤ 27402198967809983^1024*50000^4675 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8293 50000 27402198967809983 100000000000000000000 4675 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8293/50000 : ℝ)) (X := (27402198967809983/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4675 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002852860610171939/50000000000000000000 : ℝ) ≤ (2500031243467171/2500000000000000 : ℝ) ^ (4675/1024 : ℝ) := by
    have hpowers : (50002852860610171939/50000000000000000000 : ℝ)^1024 ≤ (2500031243467171/2500000000000000 : ℝ)^4675 := by
      have hnat : (50002852860610171939 : ℕ)^1024*2500000000000000^4675 ≤ 2500031243467171^4675*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002852860610171939 50000000000000000000 2500031243467171 2500000000000000 1024 4675 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500031243467171/2500000000000000 : ℝ)) (X := (50002852860610171939/50000000000000000000 : ℝ)) (by norm_num) 4675 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50015127529788990961/50000000000000000000 : ℝ) ≤ (2500165655195389/2500000000000000 : ℝ) ^ (4675/1024 : ℝ) := by
    have hpowers : (50015127529788990961/50000000000000000000 : ℝ)^1024 ≤ (2500165655195389/2500000000000000 : ℝ)^4675 := by
      have hnat : (50015127529788990961 : ℕ)^1024*2500000000000000^4675 ≤ 2500165655195389^4675*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015127529788990961 50000000000000000000 2500165655195389 2500000000000000 1024 4675 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500165655195389/2500000000000000 : ℝ)) (X := (50015127529788990961/50000000000000000000 : ℝ)) (by norm_num) 4675 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50027402198967809983/50000000000000000000 : ℝ) ≤ (2500300066923607/2500000000000000 : ℝ) ^ (4675/1024 : ℝ) := by
    have hpowers : (50027402198967809983/50000000000000000000 : ℝ)^1024 ≤ (2500300066923607/2500000000000000 : ℝ)^4675 := by
      have hnat : (50027402198967809983 : ℕ)^1024*2500000000000000^4675 ≤ 2500300066923607^4675*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027402198967809983 50000000000000000000 2500300066923607 2500000000000000 1024 4675 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500300066923607/2500000000000000 : ℝ)) (X := (50027402198967809983/50000000000000000000 : ℝ)) (by norm_num) 4675 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2852860610171939/100000000000000000000 : ℝ) ≤ ((16199986027883449471/16202500000000000000 : ℝ)+2*(67205864109/81012500000000 : ℝ)*(2021/20000 : ℝ))^(4675/1024 : ℝ) := by
    rw [show (16199986027883449471/16202500000000000000 : ℝ)+2*(67205864109/81012500000000 : ℝ)*(2021/20000 : ℝ)=(2500031243467171/2500000000000000 : ℝ) by norm_num, show 1+2*(2852860610171939/100000000000000000000 : ℝ)=(50002852860610171939/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27402198967809983/100000000000000000000 : ℝ)+(2852860610171939/100000000000000000000 : ℝ) ≤ ((16199986027883449471/16202500000000000000 : ℝ)+(67205864109/81012500000000 : ℝ)*((8293/50000 : ℝ)+(2021/20000 : ℝ)))^(4675/1024 : ℝ) := by
    rw [show (16199986027883449471/16202500000000000000 : ℝ)+(67205864109/81012500000000 : ℝ)*((8293/50000 : ℝ)+(2021/20000 : ℝ))=(2500165655195389/2500000000000000 : ℝ) by norm_num, show 1+(27402198967809983/100000000000000000000 : ℝ)+(2852860610171939/100000000000000000000 : ℝ)=(50015127529788990961/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27402198967809983/100000000000000000000 : ℝ) ≤ ((16199986027883449471/16202500000000000000 : ℝ)+2*(67205864109/81012500000000 : ℝ)*(8293/50000 : ℝ))^(4675/1024 : ℝ) := by
    rw [show (16199986027883449471/16202500000000000000 : ℝ)+2*(67205864109/81012500000000 : ℝ)*(8293/50000 : ℝ)=(2500300066923607/2500000000000000 : ℝ) by norm_num, show 1+2*(27402198967809983/100000000000000000000 : ℝ)=(50027402198967809983/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (16199986027883449471/16202500000000000000 : ℝ)*(X 1 0+X 2 0)+(67205864109/81012500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4675/1024 : ℝ)) (lo := (2021/20000 : ℝ)) (hi := (8293/50000 : ℝ)) (c := (16199986027883449471/16202500000000000000 : ℝ)) (alpha := (67205864109/81012500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (16199986027883449471/16202500000000000000 : ℝ)*(X 0 1+X 2 1)+(67205864109/81012500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4675/1024 : ℝ)) (lo := (2021/20000 : ℝ)) (hi := (8293/50000 : ℝ)) (c := (16199986027883449471/16202500000000000000 : ℝ)) (alpha := (67205864109/81012500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (16199986027883449471/16202500000000000000 : ℝ)*(X 0 2+X 1 2)+(67205864109/81012500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4675/1024 : ℝ)) (lo := (2021/20000 : ℝ)) (hi := (8293/50000 : ℝ)) (c := (16199986027883449471/16202500000000000000 : ℝ)) (alpha := (67205864109/81012500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-351149211/2000000000 : ℝ)*X 0 0+(2733332309/5000000000 : ℝ)*X 0 1+(1294447139/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1590_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5356604749/10000000000 : ℝ)*X 1 0+(-476218073/2500000000 : ℝ)*X 1 1+(2588894287/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1590_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5356604753/10000000000 : ℝ)*X 2 0+(1294447137/2500000000 : ℝ)*X 2 1+(-1904872321/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1590_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4229213859/10000000000 : ℝ)*X 0 0+(3894826921/10000000000 : ℝ)*X 0 1+(1146509083/2500000000 : ℝ)*X 0 2+(4229213859/10000000000 : ℝ)*X 1 0+(3894826921/10000000000 : ℝ)*X 1 1+(1146509083/2500000000 : ℝ)*X 1 2+(4229213859/10000000000 : ℝ)*X 2 0+(3894826921/10000000000 : ℝ)*X 2 1+(1146509083/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1590_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-219477653/1250000000 : ℝ)*X 0 0+(2589965161/5000000000 : ℝ)*X 0 1+(2732250129/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1590_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2640093861/5000000000 : ℝ)*X 1 0+(-404540149/2500000000 : ℝ)*X 1 1+(136612503/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1590_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1320046891/2500000000 : ℝ)*X 2 0+(2732250149/5000000000 : ℝ)*X 2 1+(-809080283/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1590_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4229393743/10000000000 : ℝ)*X 0 0+(4580911617/10000000000 : ℝ)*X 0 1+(1950002877/5000000000 : ℝ)*X 0 2+(4229393743/10000000000 : ℝ)*X 1 0+(4580911617/10000000000 : ℝ)*X 1 1+(1950002877/5000000000 : ℝ)*X 1 2+(4229393743/10000000000 : ℝ)*X 2 0+(4580911617/10000000000 : ℝ)*X 2 1+(1950002877/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1590_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (247222413185119997492916969/32405000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1300244199/100000000000000 : ℝ)*(base19) + (122293321/10000000000000 : ℝ)*(base23) + (4279713/10000000000000 : ℝ)*(lower2) + (40556781/20000000000000 : ℝ)*(upper3) + (122794251/100000000000000 : ℝ)*(upper5) + (2454238047909837/100000000000000 : ℝ)*(major0) + (2454238047909837/100000000000000 : ℝ)*(major1) + (1227119023954919/50000000000000 : ℝ)*(major2) + (865427029958433/25000000000000 : ℝ)*(sp0) + (1730860916506863/50000000000000 : ℝ)*(sp1) + (1730860955162357/50000000000000 : ℝ)*(sp2) + (361686420729297/25000000000000 : ℝ)*(sp3) + (234584753/1562500000000 : ℝ)*(sp4) + (878167469/12500000000000 : ℝ)*(sp7) + (72337635412847/5000000000000 : ℝ)*(f.failure) + (865430783314481/25000000000000 : ℝ)*(f.sum) + (340977351671/64810000000000000000000000 : ℝ)*base66 + (16190599409848746227/1620250000000000000000000000000000 : ℝ)*base67 + (12382395367927697849/810125000000000000000000000000000 : ℝ)*base69 + (3799240911468753773/1620250000000000000000000000000000 : ℝ)*base72 + (398659363283/162025000000000000000000000 : ℝ)*base73 + (11047184449893197849/810125000000000000000000000000000 : ℝ)*base75 + (7347630914332446227/1620250000000000000000000000000000 : ℝ)*base77 + (14307177367618946227/1620250000000000000000000000000000 : ℝ)*base79 + (19191144019357/16202500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (678797/250000000000000000000 : ℝ)*base89 + (678797/250000000000000000000 : ℝ)*base91 + (1821203/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (300293277706455135293170809/25316406250000000000000000000000 : ℝ) := by norm_num
    linear_combination (499615039/25000000000000 : ℝ)*(base19) + (1026758419/50000000000000 : ℝ)*(base23) + (30987477/12500000000000 : ℝ)*(upper3) + (35458583/50000000000000 : ℝ)*(lower4) + (244524983/100000000000000 : ℝ)*(upper5) + (622838129679447/25000000000000 : ℝ)*(major0) + (622838129679447/25000000000000 : ℝ)*(major1) + (622838129679447/25000000000000 : ℝ)*(major2) + (4255200481/20000000000000 : ℝ)*(sp1) + (11532811377/50000000000000 : ℝ)*(sp2) + (3514073265093427/100000000000000 : ℝ)*(sp4) + (702809998126173/20000000000000 : ℝ)*(sp5) + (702809629190767/20000000000000 : ℝ)*(sp6) + (734315688477609/50000000000000 : ℝ)*(sp7) + (734315688477609/50000000000000 : ℝ)*(f.failure) + (3514073265093427/100000000000000 : ℝ)*(f.sum) + (109413513463447/16202500000000000000000000000 : ℝ)*base66 + (5073609218166177463/405062500000000000000000000000000 : ℝ)*base68 + (5392623294027302463/405062500000000000000000000000000 : ℝ)*base70 + (4295281968314239963/405062500000000000000000000000000 : ℝ)*base72 + (69876227727897/16202500000000000000000000000 : ℝ)*base74 + (2936223181346197537/405062500000000000000000000000000 : ℝ)*base75 + (4579148483050927463/405062500000000000000000000000000 : ℝ)*base78 + (1152997342664177463/405062500000000000000000000000000 : ℝ)*base80 + (2555151402011/506328125000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (34607259/2500000000000000000000 : ℝ)*base89 + (34607259/2500000000000000000000 : ℝ)*base91 + (34607259/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1590_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84818851/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8293/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2021/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10277/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3279/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1590_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1590_s4_0 (p : ℝ) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-35118609/200000000 : ℝ)*x 0 + (5465746461/10000000000 : ℝ)*x 1 + (5178584549/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (35118609/200000000 : ℝ)^4679 ≤ (10785625491597/100000000000000 : ℝ)^3655 := by
    have hnat : (35118609 : ℕ)^4679*100000000000000^3655 ≤ 10785625491597^3655*200000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35118609 200000000 10785625491597 100000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5465746461/10000000000 : ℝ)^4679 ≤ (922950194849/2000000000000 : ℝ)^3655 := by
    have hnat : (5465746461 : ℕ)^4679*2000000000000^3655 ≤ 922950194849^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5465746461 10000000000 922950194849 2000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5178584549/10000000000 : ℝ)^4679 ≤ (4306686474723/10000000000000 : ℝ)^3655 := by
    have hnat : (5178584549 : ℕ)^4679*10000000000000^3655 ≤ 4306686474723^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178584549 10000000000 4306686474723 10000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4679/1024 : ℝ)) 4679 3655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-35118609/200000000 : ℝ), (5465746461/10000000000 : ℝ), (5178584549/10000000000 : ℝ)] ![(10785625491597/100000000000000 : ℝ), (922950194849/2000000000000 : ℝ), (4306686474723/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-35118609/200000000 : ℝ)|^4679 ≤ (10785625491597/100000000000000 : ℝ)^3655
        have hw : |(-35118609/200000000 : ℝ)|=(35118609/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5465746461/10000000000 : ℝ)|^4679 ≤ (922950194849/2000000000000 : ℝ)^3655
        have hw : |(5465746461/10000000000 : ℝ)|=(5465746461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5178584549/10000000000 : ℝ)|^4679 ≤ (4306686474723/10000000000000 : ℝ)^3655
        have hw : |(5178584549/10000000000 : ℝ)|=(5178584549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1590_s4_1 (p : ℝ) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1071272249/2000000000 : ℝ)*x 0 + (-476036051/2500000000 : ℝ)*x 1 + (5178584549/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071272249/2000000000 : ℝ)^4679 ≤ (2810534551237/6250000000000 : ℝ)^3655 := by
    have hnat : (1071272249 : ℕ)^4679*6250000000000^3655 ≤ 2810534551237^3655*2000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071272249 2000000000 2810534551237 6250000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (476036051/2500000000 : ℝ)^4679 ≤ (11964582411499/100000000000000 : ℝ)^3655 := by
    have hnat : (476036051 : ℕ)^4679*100000000000000^3655 ≤ 11964582411499^3655*2500000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      476036051 2500000000 11964582411499 100000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5178584549/10000000000 : ℝ)^4679 ≤ (4306686474723/10000000000000 : ℝ)^3655 := by
    have hnat : (5178584549 : ℕ)^4679*10000000000000^3655 ≤ 4306686474723^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178584549 10000000000 4306686474723 10000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4679/1024 : ℝ)) 4679 3655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071272249/2000000000 : ℝ), (-476036051/2500000000 : ℝ), (5178584549/10000000000 : ℝ)] ![(2810534551237/6250000000000 : ℝ), (11964582411499/100000000000000 : ℝ), (4306686474723/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071272249/2000000000 : ℝ)|^4679 ≤ (2810534551237/6250000000000 : ℝ)^3655
        have hw : |(1071272249/2000000000 : ℝ)|=(1071272249/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-476036051/2500000000 : ℝ)|^4679 ≤ (11964582411499/100000000000000 : ℝ)^3655
        have hw : |(-476036051/2500000000 : ℝ)|=(476036051/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5178584549/10000000000 : ℝ)|^4679 ≤ (4306686474723/10000000000000 : ℝ)^3655
        have hw : |(5178584549/10000000000 : ℝ)|=(5178584549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1590_s4_2 (p : ℝ) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1071272249/2000000000 : ℝ)*x 0 + (5178584549/10000000000 : ℝ)*x 1 + (-476036051/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071272249/2000000000 : ℝ)^4679 ≤ (2810534551237/6250000000000 : ℝ)^3655 := by
    have hnat : (1071272249 : ℕ)^4679*6250000000000^3655 ≤ 2810534551237^3655*2000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071272249 2000000000 2810534551237 6250000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5178584549/10000000000 : ℝ)^4679 ≤ (4306686474723/10000000000000 : ℝ)^3655 := by
    have hnat : (5178584549 : ℕ)^4679*10000000000000^3655 ≤ 4306686474723^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178584549 10000000000 4306686474723 10000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (476036051/2500000000 : ℝ)^4679 ≤ (11964582411499/100000000000000 : ℝ)^3655 := by
    have hnat : (476036051 : ℕ)^4679*100000000000000^3655 ≤ 11964582411499^3655*2500000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      476036051 2500000000 11964582411499 100000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4679/1024 : ℝ)) 4679 3655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071272249/2000000000 : ℝ), (5178584549/10000000000 : ℝ), (-476036051/2500000000 : ℝ)] ![(2810534551237/6250000000000 : ℝ), (4306686474723/10000000000000 : ℝ), (11964582411499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071272249/2000000000 : ℝ)|^4679 ≤ (2810534551237/6250000000000 : ℝ)^3655
        have hw : |(1071272249/2000000000 : ℝ)|=(1071272249/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5178584549/10000000000 : ℝ)|^4679 ≤ (4306686474723/10000000000000 : ℝ)^3655
        have hw : |(5178584549/10000000000 : ℝ)|=(5178584549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-476036051/2500000000 : ℝ)|^4679 ≤ (11964582411499/100000000000000 : ℝ)^3655
        have hw : |(-476036051/2500000000 : ℝ)|=(476036051/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1590_s4_3 (p : ℝ) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2114666733/5000000000 : ℝ)*x 0 + (3896864699/10000000000 : ℝ)*x 1 + (1145993131/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2114666733/5000000000 : ℝ)^4679 ≤ (33232783497227/100000000000000 : ℝ)^3655 := by
    have hnat : (2114666733 : ℕ)^4679*100000000000000^3655 ≤ 33232783497227^3655*5000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114666733 5000000000 33232783497227 100000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3896864699/10000000000 : ℝ)^4679 ≤ (7481495857097/25000000000000 : ℝ)^3655 := by
    have hnat : (3896864699 : ℕ)^4679*25000000000000^3655 ≤ 7481495857097^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3896864699 10000000000 7481495857097 25000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1145993131/2500000000 : ℝ)^4679 ≤ (3684123305911/10000000000000 : ℝ)^3655 := by
    have hnat : (1145993131 : ℕ)^4679*10000000000000^3655 ≤ 3684123305911^3655*2500000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1145993131 2500000000 3684123305911 10000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4679/1024 : ℝ)) 4679 3655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2114666733/5000000000 : ℝ), (3896864699/10000000000 : ℝ), (1145993131/2500000000 : ℝ)] ![(33232783497227/100000000000000 : ℝ), (7481495857097/25000000000000 : ℝ), (3684123305911/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2114666733/5000000000 : ℝ)|^4679 ≤ (33232783497227/100000000000000 : ℝ)^3655
        have hw : |(2114666733/5000000000 : ℝ)|=(2114666733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3896864699/10000000000 : ℝ)|^4679 ≤ (7481495857097/25000000000000 : ℝ)^3655
        have hw : |(3896864699/10000000000 : ℝ)|=(3896864699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1145993131/2500000000 : ℝ)|^4679 ≤ (3684123305911/10000000000000 : ℝ)^3655
        have hw : |(1145993131/2500000000 : ℝ)|=(1145993131/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1590_s4_4 (p : ℝ) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-175600431/1000000000 : ℝ)*x 0 + (5180701069/10000000000 : ℝ)*x 1 + (1365901933/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (175600431/1000000000 : ℝ)^4679 ≤ (2696551569203/25000000000000 : ℝ)^3655 := by
    have hnat : (175600431 : ℕ)^4679*25000000000000^3655 ≤ 2696551569203^3655*1000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      175600431 1000000000 2696551569203 25000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5180701069/10000000000 : ℝ)^4679 ≤ (43089399099909/100000000000000 : ℝ)^3655 := by
    have hnat : (5180701069 : ℕ)^4679*100000000000000^3655 ≤ 43089399099909^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180701069 10000000000 43089399099909 100000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1365901933/2500000000 : ℝ)^4679 ≤ (46124394609169/100000000000000 : ℝ)^3655 := by
    have hnat : (1365901933 : ℕ)^4679*100000000000000^3655 ≤ 46124394609169^3655*2500000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1365901933 2500000000 46124394609169 100000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4679/1024 : ℝ)) 4679 3655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-175600431/1000000000 : ℝ), (5180701069/10000000000 : ℝ), (1365901933/2500000000 : ℝ)] ![(2696551569203/25000000000000 : ℝ), (43089399099909/100000000000000 : ℝ), (46124394609169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-175600431/1000000000 : ℝ)|^4679 ≤ (2696551569203/25000000000000 : ℝ)^3655
        have hw : |(-175600431/1000000000 : ℝ)|=(175600431/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5180701069/10000000000 : ℝ)|^4679 ≤ (43089399099909/100000000000000 : ℝ)^3655
        have hw : |(5180701069/10000000000 : ℝ)|=(5180701069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1365901933/2500000000 : ℝ)|^4679 ≤ (46124394609169/100000000000000 : ℝ)^3655
        have hw : |(1365901933/2500000000 : ℝ)|=(1365901933/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1590_s4_5 (p : ℝ) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (20626559/39062500 : ℝ)*x 0 + (-1619121021/10000000000 : ℝ)*x 1 + (5463607733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20626559/39062500 : ℝ)^4679 ≤ (22076891131447/50000000000000 : ℝ)^3655 := by
    have hnat : (20626559 : ℕ)^4679*50000000000000^3655 ≤ 22076891131447^3655*39062500^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20626559 39062500 22076891131447 50000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1619121021/10000000000 : ℝ)^4679 ≤ (388872924379/4000000000000 : ℝ)^3655 := by
    have hnat : (1619121021 : ℕ)^4679*4000000000000^3655 ≤ 388872924379^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1619121021 10000000000 388872924379 4000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5463607733/10000000000 : ℝ)^4679 ≤ (5765549327497/12500000000000 : ℝ)^3655 := by
    have hnat : (5463607733 : ℕ)^4679*12500000000000^3655 ≤ 5765549327497^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5463607733 10000000000 5765549327497 12500000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4679/1024 : ℝ)) 4679 3655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(20626559/39062500 : ℝ), (-1619121021/10000000000 : ℝ), (5463607733/10000000000 : ℝ)] ![(22076891131447/50000000000000 : ℝ), (388872924379/4000000000000 : ℝ), (5765549327497/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(20626559/39062500 : ℝ)|^4679 ≤ (22076891131447/50000000000000 : ℝ)^3655
        have hw : |(20626559/39062500 : ℝ)|=(20626559/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1619121021/10000000000 : ℝ)|^4679 ≤ (388872924379/4000000000000 : ℝ)^3655
        have hw : |(-1619121021/10000000000 : ℝ)|=(1619121021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5463607733/10000000000 : ℝ)|^4679 ≤ (5765549327497/12500000000000 : ℝ)^3655
        have hw : |(5463607733/10000000000 : ℝ)|=(5463607733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1590_s4_6 (p : ℝ) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (20626559/39062500 : ℝ)*x 0 + (1365901933/2500000000 : ℝ)*x 1 + (-1619121021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20626559/39062500 : ℝ)^4679 ≤ (22076891131447/50000000000000 : ℝ)^3655 := by
    have hnat : (20626559 : ℕ)^4679*50000000000000^3655 ≤ 22076891131447^3655*39062500^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20626559 39062500 22076891131447 50000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1365901933/2500000000 : ℝ)^4679 ≤ (46124394609169/100000000000000 : ℝ)^3655 := by
    have hnat : (1365901933 : ℕ)^4679*100000000000000^3655 ≤ 46124394609169^3655*2500000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1365901933 2500000000 46124394609169 100000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1619121021/10000000000 : ℝ)^4679 ≤ (388872924379/4000000000000 : ℝ)^3655 := by
    have hnat : (1619121021 : ℕ)^4679*4000000000000^3655 ≤ 388872924379^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1619121021 10000000000 388872924379 4000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4679/1024 : ℝ)) 4679 3655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(20626559/39062500 : ℝ), (1365901933/2500000000 : ℝ), (-1619121021/10000000000 : ℝ)] ![(22076891131447/50000000000000 : ℝ), (46124394609169/100000000000000 : ℝ), (388872924379/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(20626559/39062500 : ℝ)|^4679 ≤ (22076891131447/50000000000000 : ℝ)^3655
        have hw : |(20626559/39062500 : ℝ)|=(20626559/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1365901933/2500000000 : ℝ)|^4679 ≤ (46124394609169/100000000000000 : ℝ)^3655
        have hw : |(1365901933/2500000000 : ℝ)|=(1365901933/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1619121021/10000000000 : ℝ)|^4679 ≤ (388872924379/4000000000000 : ℝ)^3655
        have hw : |(-1619121021/10000000000 : ℝ)|=(1619121021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1590_s4_7 (p : ℝ) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4229510193/10000000000 : ℝ)*x 0 + (2289454107/5000000000 : ℝ)*x 1 + (3901982151/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4229510193/10000000000 : ℝ)^4679 ≤ (33234561227633/100000000000000 : ℝ)^3655 := by
    have hnat : (4229510193 : ℕ)^4679*100000000000000^3655 ≤ 33234561227633^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4229510193 10000000000 33234561227633 100000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2289454107/5000000000 : ℝ)^4679 ≤ (9197284070329/25000000000000 : ℝ)^3655 := by
    have hnat : (2289454107 : ℕ)^4679*25000000000000^3655 ≤ 9197284070329^3655*5000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2289454107 5000000000 9197284070329 25000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3901982151/10000000000 : ℝ)^4679 ≤ (1498815123759/5000000000000 : ℝ)^3655 := by
    have hnat : (3901982151 : ℕ)^4679*5000000000000^3655 ≤ 1498815123759^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3901982151 10000000000 1498815123759 5000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4679/1024 : ℝ)) 4679 3655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4229510193/10000000000 : ℝ), (2289454107/5000000000 : ℝ), (3901982151/10000000000 : ℝ)] ![(33234561227633/100000000000000 : ℝ), (9197284070329/25000000000000 : ℝ), (1498815123759/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4229510193/10000000000 : ℝ)|^4679 ≤ (33234561227633/100000000000000 : ℝ)^3655
        have hw : |(4229510193/10000000000 : ℝ)|=(4229510193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2289454107/5000000000 : ℝ)|^4679 ≤ (9197284070329/25000000000000 : ℝ)^3655
        have hw : |(2289454107/5000000000 : ℝ)|=(2289454107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3901982151/10000000000 : ℝ)|^4679 ≤ (1498815123759/5000000000000 : ℝ)^3655
        have hw : |(3901982151/10000000000 : ℝ)|=(3901982151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1590_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84818851/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3279/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10277/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5147/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (131/800 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3279/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10277/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3279/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10277/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3279/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10277/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3279/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10277/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3279/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10277/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3279/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10277/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10277/100000 : ℝ) ^ (4675/1024 : ℝ) ≤ (770345123215009/25000000000000000000 : ℝ) := by
    have hpowers : (10277/100000 : ℝ)^4675 ≤ (770345123215009/25000000000000000000 : ℝ)^1024 := by
      have hnat : (10277 : ℕ)^4675*25000000000000000000^1024 ≤ 770345123215009^1024*100000^4675 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10277 100000 770345123215009 25000000000000000000 4675 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10277/100000 : ℝ)) (X := (770345123215009/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4675 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3279/20000 : ℝ) ^ (4675/1024 : ℝ) ≤ (6497708391306199/25000000000000000000 : ℝ) := by
    have hpowers : (3279/20000 : ℝ)^4675 ≤ (6497708391306199/25000000000000000000 : ℝ)^1024 := by
      have hnat : (3279 : ℕ)^4675*25000000000000000000^1024 ≤ 6497708391306199^1024*20000^4675 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3279 20000 6497708391306199 25000000000000000000 4675 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3279/20000 : ℝ)) (X := (6497708391306199/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4675 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500770345123215009/12500000000000000000 : ℝ) ≤ (2500033746071617/2500000000000000 : ℝ) ^ (4675/1024 : ℝ) := by
    have hpowers : (12500770345123215009/12500000000000000000 : ℝ)^1024 ≤ (2500033746071617/2500000000000000 : ℝ)^4675 := by
      have hnat : (12500770345123215009 : ℕ)^1024*2500000000000000^4675 ≤ 2500033746071617^4675*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500770345123215009 12500000000000000000 2500033746071617 2500000000000000 1024 4675 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500033746071617/2500000000000000 : ℝ)) (X := (12500770345123215009/12500000000000000000 : ℝ)) (by norm_num) 4675 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (3125908506689315151/3125000000000000000 : ℝ) ≤ (1000063671803739/1000000000000000 : ℝ) ^ (4675/1024 : ℝ) := by
    have hpowers : (3125908506689315151/3125000000000000000 : ℝ)^1024 ≤ (1000063671803739/1000000000000000 : ℝ)^4675 := by
      have hnat : (3125908506689315151 : ℕ)^1024*1000000000000000^4675 ≤ 1000063671803739^4675*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125908506689315151 3125000000000000000 1000063671803739 1000000000000000 1024 4675 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000063671803739/1000000000000000 : ℝ)) (X := (3125908506689315151/3125000000000000000 : ℝ)) (by norm_num) 4675 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12506497708391306199/12500000000000000000 : ℝ) ≤ (1250142306473539/1250000000000000 : ℝ) ^ (4675/1024 : ℝ) := by
    have hpowers : (12506497708391306199/12500000000000000000 : ℝ)^1024 ≤ (1250142306473539/1250000000000000 : ℝ)^4675 := by
      have hnat : (12506497708391306199 : ℕ)^1024*1250000000000000^4675 ≤ 1250142306473539^4675*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506497708391306199 12500000000000000000 1250142306473539 1250000000000000 1024 4675 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250142306473539/1250000000000000 : ℝ)) (X := (12506497708391306199/12500000000000000000 : ℝ)) (by norm_num) 4675 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(770345123215009/25000000000000000000 : ℝ) ≤ ((15292628299587040109/15295000000000000000 : ℝ)+2*(250866875461/305900000000000 : ℝ)*(10277/100000 : ℝ))^(4675/1024 : ℝ) := by
    rw [show (15292628299587040109/15295000000000000000 : ℝ)+2*(250866875461/305900000000000 : ℝ)*(10277/100000 : ℝ)=(2500033746071617/2500000000000000 : ℝ) by norm_num, show 1+2*(770345123215009/25000000000000000000 : ℝ)=(12500770345123215009/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6497708391306199/25000000000000000000 : ℝ)+(770345123215009/25000000000000000000 : ℝ) ≤ ((15292628299587040109/15295000000000000000 : ℝ)+(250866875461/305900000000000 : ℝ)*((3279/20000 : ℝ)+(10277/100000 : ℝ)))^(4675/1024 : ℝ) := by
    rw [show (15292628299587040109/15295000000000000000 : ℝ)+(250866875461/305900000000000 : ℝ)*((3279/20000 : ℝ)+(10277/100000 : ℝ))=(1000063671803739/1000000000000000 : ℝ) by norm_num, show 1+(6497708391306199/25000000000000000000 : ℝ)+(770345123215009/25000000000000000000 : ℝ)=(3125908506689315151/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6497708391306199/25000000000000000000 : ℝ) ≤ ((15292628299587040109/15295000000000000000 : ℝ)+2*(250866875461/305900000000000 : ℝ)*(3279/20000 : ℝ))^(4675/1024 : ℝ) := by
    rw [show (15292628299587040109/15295000000000000000 : ℝ)+2*(250866875461/305900000000000 : ℝ)*(3279/20000 : ℝ)=(1250142306473539/1250000000000000 : ℝ) by norm_num, show 1+2*(6497708391306199/25000000000000000000 : ℝ)=(12506497708391306199/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (15292628299587040109/15295000000000000000 : ℝ)*(X 1 0+X 2 0)+(250866875461/305900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4675/1024 : ℝ)) (lo := (10277/100000 : ℝ)) (hi := (3279/20000 : ℝ)) (c := (15292628299587040109/15295000000000000000 : ℝ)) (alpha := (250866875461/305900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (15292628299587040109/15295000000000000000 : ℝ)*(X 0 1+X 2 1)+(250866875461/305900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4675/1024 : ℝ)) (lo := (10277/100000 : ℝ)) (hi := (3279/20000 : ℝ)) (c := (15292628299587040109/15295000000000000000 : ℝ)) (alpha := (250866875461/305900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (15292628299587040109/15295000000000000000 : ℝ)*(X 0 2+X 1 2)+(250866875461/305900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4675/1024 : ℝ)) (lo := (10277/100000 : ℝ)) (hi := (3279/20000 : ℝ)) (c := (15292628299587040109/15295000000000000000 : ℝ)) (alpha := (250866875461/305900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-35118609/200000000 : ℝ)*X 0 0+(5465746461/10000000000 : ℝ)*X 0 1+(5178584549/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1590_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1071272249/2000000000 : ℝ)*X 1 0+(-476036051/2500000000 : ℝ)*X 1 1+(5178584549/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1590_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1071272249/2000000000 : ℝ)*X 2 0+(5178584549/10000000000 : ℝ)*X 2 1+(-476036051/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1590_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2114666733/5000000000 : ℝ)*X 0 0+(3896864699/10000000000 : ℝ)*X 0 1+(1145993131/2500000000 : ℝ)*X 0 2+(2114666733/5000000000 : ℝ)*X 1 0+(3896864699/10000000000 : ℝ)*X 1 1+(1145993131/2500000000 : ℝ)*X 1 2+(2114666733/5000000000 : ℝ)*X 2 0+(3896864699/10000000000 : ℝ)*X 2 1+(1145993131/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1590_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-175600431/1000000000 : ℝ)*X 0 0+(5180701069/10000000000 : ℝ)*X 0 1+(1365901933/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1590_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((20626559/39062500 : ℝ)*X 1 0+(-1619121021/10000000000 : ℝ)*X 1 1+(5463607733/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1590_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((20626559/39062500 : ℝ)*X 2 0+(1365901933/2500000000 : ℝ)*X 2 1+(-1619121021/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1590_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4229510193/10000000000 : ℝ)*X 0 0+(2289454107/5000000000 : ℝ)*X 0 1+(3901982151/10000000000 : ℝ)*X 0 2+(4229510193/10000000000 : ℝ)*X 1 0+(2289454107/5000000000 : ℝ)*X 1 1+(3901982151/10000000000 : ℝ)*X 1 2+(4229510193/10000000000 : ℝ)*X 2 0+(2289454107/5000000000 : ℝ)*X 2 1+(3901982151/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1590_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (30801452857501460244110121/3414062500000000000000000000000 : ℝ) := by norm_num
    linear_combination (304734471/20000000000000 : ℝ)*(base19) + (356124781/25000000000000 : ℝ)*(base23) + (13280191/25000000000000 : ℝ)*(lower2) + (225060937/100000000000000 : ℝ)*(upper3) + (75905669/50000000000000 : ℝ)*(upper5) + (77152869289943/3125000000000 : ℝ)*(major0) + (77152869289943/3125000000000 : ℝ)*(major1) + (77152869289943/3125000000000 : ℝ)*(major2) + (1741187236818387/50000000000000 : ℝ)*(sp0) + (43529885349713/1250000000000 : ℝ)*(sp1) + (348239092715027/10000000000000 : ℝ)*(sp2) + (1455382862184493/100000000000000 : ℝ)*(sp3) + (17878012621/100000000000000 : ℝ)*(sp4) + (405999563/5000000000000 : ℝ)*(sp7) + (181923872771969/12500000000000 : ℝ)*(f.failure) + (696478470329879/20000000000000 : ℝ)*(f.sum) + (21999673064431/3823750000000000000000000000 : ℝ)*base66 + (103102566636432463/47796875000000000000000000000000 : ℝ)*base68 + (436203298833619963/47796875000000000000000000000000 : ℝ)*base70 + (93471650353067537/47796875000000000000000000000000 : ℝ)*base71 + (28696229661529/15295000000000000000000000000 : ℝ)*base74 + (517790865853276213/47796875000000000000000000000000 : ℝ)*base76 + (179614425578963713/47796875000000000000000000000000 : ℝ)*base78 + (29635592617908897/11949218750000000000000000000000 : ℝ)*base80 + (13932737677113/1911875000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (4412381/625000000000000000000 : ℝ)*base90 + (4412381/625000000000000000000 : ℝ)*base92 + (4412381/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1918456961280578741667/805000000000000000000000000 : ℝ) := by norm_num
    linear_combination (187344519/50000000000000 : ℝ)*(base19) + (81152253/20000000000000 : ℝ)*(base23) + (11998303/10000000000000 : ℝ)*(lower1) + (50344089/100000000000000 : ℝ)*(upper3) + (1398923/10000000000000 : ℝ)*(lower4) + (24686899/50000000000000 : ℝ)*(upper5) + (313249671057861/12500000000000 : ℝ)*(major0) + (313249671057861/12500000000000 : ℝ)*(major1) + (313249671057861/12500000000000 : ℝ)*(major2) + (159167897/50000000000000 : ℝ)*(sp2) + (1767365132327743/50000000000000 : ℝ)*(sp4) + (220920618122903/6250000000000 : ℝ)*(sp5) + (3534729540558427/100000000000000 : ℝ)*(sp6) + (59090575713243/4000000000000 : ℝ)*(sp7) + (59090575713243/4000000000000 : ℝ)*(f.failure) + (1767365132327743/50000000000000 : ℝ)*(f.sum) + (5453505043997/805000000000000000000000000 : ℝ)*base65 + (55367912057405429/10062500000000000000000000000000 : ℝ)*base68 + (46619529205717929/10062500000000000000000000000000 : ℝ)*base70 + (34927474019907071/10062500000000000000000000000000 : ℝ)*base71 + (580645131631/402500000000000000000000000 : ℝ)*base73 + (5931629184782071/10062500000000000000000000000000 : ℝ)*base75 + (54217122586717929/10062500000000000000000000000000 : ℝ)*base78 + (1786182961594571/10062500000000000000000000000000 : ℝ)*base79 + (736628476281/402500000000000000000000000 : ℝ)*base81 + (743793/200000000000000000000 : ℝ)*base89 + (743793/200000000000000000000 : ℝ)*base91 + (743793/200000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1590_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84818851/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3279/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10277/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5147/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (131/800 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1590_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1590_s5_0 (p : ℝ) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-109746901/625000000 : ℝ)*x 0 + (5465654843/10000000000 : ℝ)*x 1 + (1035732563/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (109746901/625000000 : ℝ)^4679 ≤ (10785782490077/100000000000000 : ℝ)^3655 := by
    have hnat : (109746901 : ℕ)^4679*100000000000000^3655 ≤ 10785782490077^3655*625000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109746901 625000000 10785782490077 100000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5465654843/10000000000 : ℝ)^4679 ≤ (23073259746923/50000000000000 : ℝ)^3655 := by
    have hnat : (5465654843 : ℕ)^4679*50000000000000^3655 ≤ 23073259746923^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5465654843 10000000000 23073259746923 50000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1035732563/2000000000 : ℝ)^4679 ≤ (21533848995339/50000000000000 : ℝ)^3655 := by
    have hnat : (1035732563 : ℕ)^4679*50000000000000^3655 ≤ 21533848995339^3655*2000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035732563 2000000000 21533848995339 50000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4679/1024 : ℝ)) 4679 3655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-109746901/625000000 : ℝ), (5465654843/10000000000 : ℝ), (1035732563/2000000000 : ℝ)] ![(10785782490077/100000000000000 : ℝ), (23073259746923/50000000000000 : ℝ), (21533848995339/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-109746901/625000000 : ℝ)|^4679 ≤ (10785782490077/100000000000000 : ℝ)^3655
        have hw : |(-109746901/625000000 : ℝ)|=(109746901/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5465654843/10000000000 : ℝ)|^4679 ≤ (23073259746923/50000000000000 : ℝ)^3655
        have hw : |(5465654843/10000000000 : ℝ)|=(5465654843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1035732563/2000000000 : ℝ)|^4679 ≤ (21533848995339/50000000000000 : ℝ)^3655
        have hw : |(1035732563/2000000000 : ℝ)|=(1035732563/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1590_s5_1 (p : ℝ) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5356336409/10000000000 : ℝ)*x 0 + (-1904073563/10000000000 : ℝ)*x 1 + (2589331497/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5356336409/10000000000 : ℝ)^4679 ≤ (22484142948369/50000000000000 : ℝ)^3655 := by
    have hnat : (5356336409 : ℕ)^4679*50000000000000^3655 ≤ 22484142948369^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5356336409 10000000000 22484142948369 50000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1904073563/10000000000 : ℝ)^4679 ≤ (2392802837923/20000000000000 : ℝ)^3655 := by
    have hnat : (1904073563 : ℕ)^4679*20000000000000^3655 ≤ 2392802837923^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1904073563 10000000000 2392802837923 20000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2589331497/5000000000 : ℝ)^4679 ≤ (4306769989637/10000000000000 : ℝ)^3655 := by
    have hnat : (2589331497 : ℕ)^4679*10000000000000^3655 ≤ 4306769989637^3655*5000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2589331497 5000000000 4306769989637 10000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4679/1024 : ℝ)) 4679 3655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5356336409/10000000000 : ℝ), (-1904073563/10000000000 : ℝ), (2589331497/5000000000 : ℝ)] ![(22484142948369/50000000000000 : ℝ), (2392802837923/20000000000000 : ℝ), (4306769989637/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5356336409/10000000000 : ℝ)|^4679 ≤ (22484142948369/50000000000000 : ℝ)^3655
        have hw : |(5356336409/10000000000 : ℝ)|=(5356336409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1904073563/10000000000 : ℝ)|^4679 ≤ (2392802837923/20000000000000 : ℝ)^3655
        have hw : |(-1904073563/10000000000 : ℝ)|=(1904073563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2589331497/5000000000 : ℝ)|^4679 ≤ (4306769989637/10000000000000 : ℝ)^3655
        have hw : |(2589331497/5000000000 : ℝ)|=(2589331497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1590_s5_2 (p : ℝ) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2678168347/5000000000 : ℝ)*x 0 + (1294665693/2500000000 : ℝ)*x 1 + (-476018369/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2678168347/5000000000 : ℝ)^4679 ≤ (5621036119969/12500000000000 : ℝ)^3655 := by
    have hnat : (2678168347 : ℕ)^4679*12500000000000^3655 ≤ 5621036119969^3655*5000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2678168347 5000000000 5621036119969 12500000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1294665693/2500000000 : ℝ)^4679 ≤ (21533848766443/50000000000000 : ℝ)^3655 := by
    have hnat : (1294665693 : ℕ)^4679*50000000000000^3655 ≤ 21533848766443^3655*2500000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294665693 2500000000 21533848766443 50000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (476018369/2500000000 : ℝ)^4679 ≤ (747750843113/6250000000000 : ℝ)^3655 := by
    have hnat : (476018369 : ℕ)^4679*6250000000000^3655 ≤ 747750843113^3655*2500000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      476018369 2500000000 747750843113 6250000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4679/1024 : ℝ)) 4679 3655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2678168347/5000000000 : ℝ), (1294665693/2500000000 : ℝ), (-476018369/2500000000 : ℝ)] ![(5621036119969/12500000000000 : ℝ), (21533848766443/50000000000000 : ℝ), (747750843113/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2678168347/5000000000 : ℝ)|^4679 ≤ (5621036119969/12500000000000 : ℝ)^3655
        have hw : |(2678168347/5000000000 : ℝ)|=(2678168347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1294665693/2500000000 : ℝ)|^4679 ≤ (21533848766443/50000000000000 : ℝ)^3655
        have hw : |(1294665693/2500000000 : ℝ)|=(1294665693/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-476018369/2500000000 : ℝ)|^4679 ≤ (747750843113/6250000000000 : ℝ)^3655
        have hw : |(-476018369/2500000000 : ℝ)|=(476018369/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1590_s5_3 (p : ℝ) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (422934523/1000000000 : ℝ)*x 0 + (779413383/2000000000 : ℝ)*x 1 + (4583767799/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (422934523/1000000000 : ℝ)^4679 ≤ (33232901832887/100000000000000 : ℝ)^3655 := by
    have hnat : (422934523 : ℕ)^4679*100000000000000^3655 ≤ 33232901832887^3655*1000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422934523 1000000000 33232901832887 100000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (779413383/2000000000 : ℝ)^4679 ≤ (29927971433241/100000000000000 : ℝ)^3655 := by
    have hnat : (779413383 : ℕ)^4679*100000000000000^3655 ≤ 29927971433241^3655*2000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      779413383 2000000000 29927971433241 100000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4583767799/10000000000 : ℝ)^4679 ≤ (1841956336561/5000000000000 : ℝ)^3655 := by
    have hnat : (4583767799 : ℕ)^4679*5000000000000^3655 ≤ 1841956336561^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4583767799 10000000000 1841956336561 5000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4679/1024 : ℝ)) 4679 3655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(422934523/1000000000 : ℝ), (779413383/2000000000 : ℝ), (4583767799/10000000000 : ℝ)] ![(33232901832887/100000000000000 : ℝ), (29927971433241/100000000000000 : ℝ), (1841956336561/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(422934523/1000000000 : ℝ)|^4679 ≤ (33232901832887/100000000000000 : ℝ)^3655
        have hw : |(422934523/1000000000 : ℝ)|=(422934523/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(779413383/2000000000 : ℝ)|^4679 ≤ (29927971433241/100000000000000 : ℝ)^3655
        have hw : |(779413383/2000000000 : ℝ)|=(779413383/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4583767799/10000000000 : ℝ)|^4679 ≤ (1841956336561/5000000000000 : ℝ)^3655
        have hw : |(4583767799/10000000000 : ℝ)|=(4583767799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1590_s5_4 (p : ℝ) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1756024113/10000000000 : ℝ)*x 0 + (5180777001/10000000000 : ℝ)*x 1 + (5463518513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1756024113/10000000000 : ℝ)^4679 ≤ (10786361995409/100000000000000 : ℝ)^3655 := by
    have hnat : (1756024113 : ℕ)^4679*100000000000000^3655 ≤ 10786361995409^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1756024113 10000000000 10786361995409 100000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5180777001/10000000000 : ℝ)^4679 ≤ (10772551896847/25000000000000 : ℝ)^3655 := by
    have hnat : (5180777001 : ℕ)^4679*25000000000000^3655 ≤ 10772551896847^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180777001 10000000000 10772551896847 25000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5463518513/10000000000 : ℝ)^4679 ≤ (46123430395709/100000000000000 : ℝ)^3655 := by
    have hnat : (5463518513 : ℕ)^4679*100000000000000^3655 ≤ 46123430395709^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5463518513 10000000000 46123430395709 100000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4679/1024 : ℝ)) 4679 3655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1756024113/10000000000 : ℝ), (5180777001/10000000000 : ℝ), (5463518513/10000000000 : ℝ)] ![(10786361995409/100000000000000 : ℝ), (10772551896847/25000000000000 : ℝ), (46123430395709/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1756024113/10000000000 : ℝ)|^4679 ≤ (10786361995409/100000000000000 : ℝ)^3655
        have hw : |(-1756024113/10000000000 : ℝ)|=(1756024113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5180777001/10000000000 : ℝ)|^4679 ≤ (10772551896847/25000000000000 : ℝ)^3655
        have hw : |(5180777001/10000000000 : ℝ)|=(5180777001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5463518513/10000000000 : ℝ)|^4679 ≤ (46123430395709/100000000000000 : ℝ)^3655
        have hw : |(5463518513/10000000000 : ℝ)|=(5463518513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1590_s5_5 (p : ℝ) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5280419577/10000000000 : ℝ)*x 0 + (-1619217973/10000000000 : ℝ)*x 1 + (5463518497/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5280419577/10000000000 : ℝ)^4679 ≤ (2759625088529/6250000000000 : ℝ)^3655 := by
    have hnat : (5280419577 : ℕ)^4679*6250000000000^3655 ≤ 2759625088529^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280419577 10000000000 2759625088529 6250000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1619217973/10000000000 : ℝ)^4679 ≤ (4861284173301/50000000000000 : ℝ)^3655 := by
    have hnat : (1619217973 : ℕ)^4679*50000000000000^3655 ≤ 4861284173301^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1619217973 10000000000 4861284173301 50000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5463518497/10000000000 : ℝ)^4679 ≤ (46123430222793/100000000000000 : ℝ)^3655 := by
    have hnat : (5463518497 : ℕ)^4679*100000000000000^3655 ≤ 46123430222793^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5463518497 10000000000 46123430222793 100000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4679/1024 : ℝ)) 4679 3655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5280419577/10000000000 : ℝ), (-1619217973/10000000000 : ℝ), (5463518497/10000000000 : ℝ)] ![(2759625088529/6250000000000 : ℝ), (4861284173301/50000000000000 : ℝ), (46123430222793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5280419577/10000000000 : ℝ)|^4679 ≤ (2759625088529/6250000000000 : ℝ)^3655
        have hw : |(5280419577/10000000000 : ℝ)|=(5280419577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1619217973/10000000000 : ℝ)|^4679 ≤ (4861284173301/50000000000000 : ℝ)^3655
        have hw : |(-1619217973/10000000000 : ℝ)|=(1619217973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5463518497/10000000000 : ℝ)|^4679 ≤ (46123430222793/100000000000000 : ℝ)^3655
        have hw : |(5463518497/10000000000 : ℝ)|=(5463518497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1590_s5_6 (p : ℝ) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2640209689/5000000000 : ℝ)*x 0 + (682939833/1250000000 : ℝ)*x 1 + (-50600563/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2640209689/5000000000 : ℝ)^4679 ≤ (5519249910783/12500000000000 : ℝ)^3655 := by
    have hnat : (2640209689 : ℕ)^4679*12500000000000^3655 ≤ 5519249910783^3655*5000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640209689 5000000000 5519249910783 12500000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (682939833/1250000000 : ℝ)^4679 ≤ (23061716013801/50000000000000 : ℝ)^3655 := by
    have hnat : (682939833 : ℕ)^4679*50000000000000^3655 ≤ 23061716013801^3655*1250000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      682939833 1250000000 23061716013801 50000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (50600563/312500000 : ℝ)^4679 ≤ (9722568677131/100000000000000 : ℝ)^3655 := by
    have hnat : (50600563 : ℕ)^4679*100000000000000^3655 ≤ 9722568677131^3655*312500000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50600563 312500000 9722568677131 100000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4679/1024 : ℝ)) 4679 3655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2640209689/5000000000 : ℝ), (682939833/1250000000 : ℝ), (-50600563/312500000 : ℝ)] ![(5519249910783/12500000000000 : ℝ), (23061716013801/50000000000000 : ℝ), (9722568677131/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2640209689/5000000000 : ℝ)|^4679 ≤ (5519249910783/12500000000000 : ℝ)^3655
        have hw : |(2640209689/5000000000 : ℝ)|=(2640209689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(682939833/1250000000 : ℝ)|^4679 ≤ (23061716013801/50000000000000 : ℝ)^3655
        have hw : |(682939833/1250000000 : ℝ)|=(682939833/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-50600563/312500000 : ℝ)|^4679 ≤ (9722568677131/100000000000000 : ℝ)^3655
        have hw : |(-50600563/312500000 : ℝ)|=(50600563/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1590_s5_7 (p : ℝ) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4229521849/10000000000 : ℝ)*x 0 + (4578709601/10000000000 : ℝ)*x 1 + (487772243/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4229521849/10000000000 : ℝ)^4679 ≤ (33234678478279/100000000000000 : ℝ)^3655 := by
    have hnat : (4229521849 : ℕ)^4679*100000000000000^3655 ≤ 33234678478279^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4229521849 10000000000 33234678478279 100000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4578709601/10000000000 : ℝ)^4679 ≤ (2299193341847/6250000000000 : ℝ)^3655 := by
    have hnat : (4578709601 : ℕ)^4679*6250000000000^3655 ≤ 2299193341847^3655*10000000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4578709601 10000000000 2299193341847 6250000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (487772243/1250000000 : ℝ)^4679 ≤ (29978228042299/100000000000000 : ℝ)^3655 := by
    have hnat : (487772243 : ℕ)^4679*100000000000000^3655 ≤ 29978228042299^3655*1250000000^4679 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      487772243 1250000000 29978228042299 100000000000000 4679 3655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4679/1024 : ℝ)) 4679 3655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4229521849/10000000000 : ℝ), (4578709601/10000000000 : ℝ), (487772243/1250000000 : ℝ)] ![(33234678478279/100000000000000 : ℝ), (2299193341847/6250000000000 : ℝ), (29978228042299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4229521849/10000000000 : ℝ)|^4679 ≤ (33234678478279/100000000000000 : ℝ)^3655
        have hw : |(4229521849/10000000000 : ℝ)|=(4229521849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4578709601/10000000000 : ℝ)|^4679 ≤ (2299193341847/6250000000000 : ℝ)^3655
        have hw : |(4578709601/10000000000 : ℝ)|=(4578709601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(487772243/1250000000 : ℝ)|^4679 ≤ (29978228042299/100000000000000 : ℝ)^3655
        have hw : |(487772243/1250000000 : ℝ)|=(487772243/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1590_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84818851/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (131/800 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5147/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1287/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8187/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (131/800 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5147/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (131/800 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5147/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (131/800 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5147/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (131/800 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5147/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (131/800 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5147/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (131/800 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5147/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5147/50000 : ℝ) ^ (4675/1024 : ℝ) ≤ (1552359959647781/50000000000000000000 : ℝ) := by
    have hpowers : (5147/50000 : ℝ)^4675 ≤ (1552359959647781/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5147 : ℕ)^4675*50000000000000000000^1024 ≤ 1552359959647781^1024*50000^4675 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5147 50000 1552359959647781 50000000000000000000 4675 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5147/50000 : ℝ)) (X := (1552359959647781/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4675 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (131/800 : ℝ) ^ (4675/1024 : ℝ) ≤ (25846397404030043/100000000000000000000 : ℝ) := by
    have hpowers : (131/800 : ℝ)^4675 ≤ (25846397404030043/100000000000000000000 : ℝ)^1024 := by
      have hnat : (131 : ℕ)^4675*100000000000000000000^1024 ≤ 25846397404030043^1024*800^4675 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        131 800 25846397404030043 100000000000000000000 4675 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (131/800 : ℝ)) (X := (25846397404030043/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4675 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25001552359959647781/25000000000000000000 : ℝ) ≤ (10000136006678687/10000000000000000 : ℝ) ^ (4675/1024 : ℝ) := by
    have hpowers : (25001552359959647781/25000000000000000000 : ℝ)^1024 ≤ (10000136006678687/10000000000000000 : ℝ)^4675 := by
      have hnat : (25001552359959647781 : ℕ)^1024*10000000000000000^4675 ≤ 10000136006678687^4675*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001552359959647781 25000000000000000000 10000136006678687 10000000000000000 1024 4675 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000136006678687/10000000000000000 : ℝ)) (X := (25001552359959647781/25000000000000000000 : ℝ)) (by norm_num) 4675 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20005790223464665121/20000000000000000000 : ℝ) ≤ (10000634066166411/10000000000000000 : ℝ) ^ (4675/1024 : ℝ) := by
    have hpowers : (20005790223464665121/20000000000000000000 : ℝ)^1024 ≤ (10000634066166411/10000000000000000 : ℝ)^4675 := by
      have hnat : (20005790223464665121 : ℕ)^1024*10000000000000000^4675 ≤ 10000634066166411^4675*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20005790223464665121 20000000000000000000 10000634066166411 10000000000000000 1024 4675 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000634066166411/10000000000000000 : ℝ)) (X := (20005790223464665121/20000000000000000000 : ℝ)) (by norm_num) 4675 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50025846397404030043/50000000000000000000 : ℝ) ≤ (2000226425130827/2000000000000000 : ℝ) ^ (4675/1024 : ℝ) := by
    have hpowers : (50025846397404030043/50000000000000000000 : ℝ)^1024 ≤ (2000226425130827/2000000000000000 : ℝ)^4675 := by
      have hnat : (50025846397404030043 : ℕ)^1024*2000000000000000^4675 ≤ 2000226425130827^4675*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025846397404030043 50000000000000000000 2000226425130827 2000000000000000 1024 4675 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000226425130827/2000000000000000 : ℝ)) (X := (50025846397404030043/50000000000000000000 : ℝ)) (by norm_num) 4675 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1552359959647781/50000000000000000000 : ℝ) ≤ ((12160114601575966787/12162000000000000000 : ℝ)+2*(124514871931/152025000000000 : ℝ)*(5147/50000 : ℝ))^(4675/1024 : ℝ) := by
    rw [show (12160114601575966787/12162000000000000000 : ℝ)+2*(124514871931/152025000000000 : ℝ)*(5147/50000 : ℝ)=(10000136006678687/10000000000000000 : ℝ) by norm_num, show 1+2*(1552359959647781/50000000000000000000 : ℝ)=(25001552359959647781/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(25846397404030043/100000000000000000000 : ℝ)+(1552359959647781/50000000000000000000 : ℝ) ≤ ((12160114601575966787/12162000000000000000 : ℝ)+(124514871931/152025000000000 : ℝ)*((131/800 : ℝ)+(5147/50000 : ℝ)))^(4675/1024 : ℝ) := by
    rw [show (12160114601575966787/12162000000000000000 : ℝ)+(124514871931/152025000000000 : ℝ)*((131/800 : ℝ)+(5147/50000 : ℝ))=(10000634066166411/10000000000000000 : ℝ) by norm_num, show 1+(25846397404030043/100000000000000000000 : ℝ)+(1552359959647781/50000000000000000000 : ℝ)=(20005790223464665121/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(25846397404030043/100000000000000000000 : ℝ) ≤ ((12160114601575966787/12162000000000000000 : ℝ)+2*(124514871931/152025000000000 : ℝ)*(131/800 : ℝ))^(4675/1024 : ℝ) := by
    rw [show (12160114601575966787/12162000000000000000 : ℝ)+2*(124514871931/152025000000000 : ℝ)*(131/800 : ℝ)=(2000226425130827/2000000000000000 : ℝ) by norm_num, show 1+2*(25846397404030043/100000000000000000000 : ℝ)=(50025846397404030043/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (12160114601575966787/12162000000000000000 : ℝ)*(X 1 0+X 2 0)+(124514871931/152025000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4675/1024 : ℝ)) (lo := (5147/50000 : ℝ)) (hi := (131/800 : ℝ)) (c := (12160114601575966787/12162000000000000000 : ℝ)) (alpha := (124514871931/152025000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (12160114601575966787/12162000000000000000 : ℝ)*(X 0 1+X 2 1)+(124514871931/152025000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4675/1024 : ℝ)) (lo := (5147/50000 : ℝ)) (hi := (131/800 : ℝ)) (c := (12160114601575966787/12162000000000000000 : ℝ)) (alpha := (124514871931/152025000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (12160114601575966787/12162000000000000000 : ℝ)*(X 0 2+X 1 2)+(124514871931/152025000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4675/1024 : ℝ)) (lo := (5147/50000 : ℝ)) (hi := (131/800 : ℝ)) (c := (12160114601575966787/12162000000000000000 : ℝ)) (alpha := (124514871931/152025000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-109746901/625000000 : ℝ)*X 0 0+(5465654843/10000000000 : ℝ)*X 0 1+(1035732563/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1590_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5356336409/10000000000 : ℝ)*X 1 0+(-1904073563/10000000000 : ℝ)*X 1 1+(2589331497/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1590_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2678168347/5000000000 : ℝ)*X 2 0+(1294665693/2500000000 : ℝ)*X 2 1+(-476018369/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1590_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((422934523/1000000000 : ℝ)*X 0 0+(779413383/2000000000 : ℝ)*X 0 1+(4583767799/10000000000 : ℝ)*X 0 2+(422934523/1000000000 : ℝ)*X 1 0+(779413383/2000000000 : ℝ)*X 1 1+(4583767799/10000000000 : ℝ)*X 1 2+(422934523/1000000000 : ℝ)*X 2 0+(779413383/2000000000 : ℝ)*X 2 1+(4583767799/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1590_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1756024113/10000000000 : ℝ)*X 0 0+(5180777001/10000000000 : ℝ)*X 0 1+(5463518513/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1590_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5280419577/10000000000 : ℝ)*X 1 0+(-1619217973/10000000000 : ℝ)*X 1 1+(5463518497/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1590_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2640209689/5000000000 : ℝ)*X 2 0+(682939833/1250000000 : ℝ)*X 2 1+(-50600563/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1590_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4229521849/10000000000 : ℝ)*X 0 0+(4578709601/10000000000 : ℝ)*X 0 1+(487772243/1250000000 : ℝ)*X 0 2+(4229521849/10000000000 : ℝ)*X 1 0+(4578709601/10000000000 : ℝ)*X 1 1+(487772243/1250000000 : ℝ)*X 1 2+(4229521849/10000000000 : ℝ)*X 2 0+(4578709601/10000000000 : ℝ)*X 2 1+(487772243/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1590_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (547284548572622804048537361/101350000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (977435463/100000000000000 : ℝ)*(base19) + (1138853781/100000000000000 : ℝ)*(base23) + (43965057/50000000000000 : ℝ)*(upper3) + (12845591/100000000000000 : ℝ)*(upper4) + (164012517/100000000000000 : ℝ)*(upper5) + (1235173766117001/50000000000000 : ℝ)*(major0) + (1235173766117001/50000000000000 : ℝ)*(major1) + (1235173766117001/50000000000000 : ℝ)*(major2) + (3484430124179057/100000000000000 : ℝ)*(sp0) + (1742222396561657/50000000000000 : ℝ)*(sp1) + (871111157926249/25000000000000 : ℝ)*(sp2) + (291248736610667/20000000000000 : ℝ)*(sp3) + (391159493/2500000000000 : ℝ)*(sp4) + (5430857677/100000000000000 : ℝ)*(sp7) + (364062278477753/25000000000000 : ℝ)*(f.failure) + (435555721319847/12500000000000 : ℝ)*(f.sum) + (16465832352431/10135000000000000000000000000 : ℝ)*base65 + (1778705663618258071/202700000000000000000000000000000 : ℝ)*base68 + (1290613467884758071/202700000000000000000000000000000 : ℝ)*base70 + (1220318867523458071/202700000000000000000000000000000 : ℝ)*base72 + (10855929370029/2533750000000000000000000000 : ℝ)*base73 + (2376076082897458071/202700000000000000000000000000000 : ℝ)*base76 + (460798683378058071/202700000000000000000000000000000 : ℝ)*base78 + (1189166120398958071/202700000000000000000000000000000 : ℝ)*base80 + (16487633690121/10135000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (13521803/1250000000000000000000 : ℝ)*base89 + (13521803/1250000000000000000000 : ℝ)*base91 + (13521803/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1232517075015747428467015583/101350000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1973054503/100000000000000 : ℝ)*(base19) + (125173023/6250000000000 : ℝ)*(base23) + (2806639/500000000000 : ℝ)*(lower1) + (328085883/100000000000000 : ℝ)*(upper3) + (67500769/100000000000000 : ℝ)*(lower4) + (227438183/100000000000000 : ℝ)*(upper5) + (1253723923433509/50000000000000 : ℝ)*(major0) + (1253723923433509/50000000000000 : ℝ)*(major1) + (1253723923433509/50000000000000 : ℝ)*(major2) + (489247997/20000000000000 : ℝ)*(sp2) + (3536775850704347/100000000000000 : ℝ)*(sp4) + (884193469412461/25000000000000 : ℝ)*(sp5) + (1768385700847997/50000000000000 : ℝ)*(sp6) + (369529859415777/25000000000000 : ℝ)*(sp7) + (369529859415777/25000000000000 : ℝ)*(f.failure) + (3536775850704347/100000000000000 : ℝ)*(f.sum) + (63312030572773/30405000000000000000000000000 : ℝ)*base66 + (2279701024691685583/608100000000000000000000000000000 : ℝ)*base67 + (436341523956885583/608100000000000000000000000000000 : ℝ)*base69 + (6438579677650814417/608100000000000000000000000000000 : ℝ)*base72 + (8138596357519/3800625000000000000000000000 : ℝ)*base73 + (7869750166744814417/608100000000000000000000000000000 : ℝ)*base76 + (2643722709256214417/608100000000000000000000000000000 : ℝ)*base78 + (1114741810129214417/608100000000000000000000000000000 : ℝ)*base80 + (1580400137723/7601250000000000000000000000 : ℝ)*base81 + (11412227/1250000000000000000000 : ℝ)*base89 + (11412227/1250000000000000000000 : ℝ)*base91 + (11412227/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1590_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84818851/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (131/800 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5147/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1287/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8187/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1590_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1590_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84818851/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8293/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2021/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1287/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8187/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1590_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1590_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1590_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4675/1024 : ℝ) ≤ p) (hpb : p ≤ (4679/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84818851/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8293/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2021/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1287/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8187/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1590_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
