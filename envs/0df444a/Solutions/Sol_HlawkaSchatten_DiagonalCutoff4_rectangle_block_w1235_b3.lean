-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1235_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:16:34.411603+00:00
-- url     : https://prove2.me/submissions/1b43b6b3-3929-4f8d-8010-a2d445287726

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
theorem support_rectangle_w1235_box_0 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-499821261/2500000000 : ℝ)*x 0 + (5374946191/10000000000 : ℝ)*x 1 + (5374945727/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (499821261/2500000000 : ℝ)^2107 ≤ (11924860569467/100000000000000 : ℝ)^1595 := by
    have hnat : (499821261 : ℕ)^2107*100000000000000^1595 ≤ 11924860569467^1595*2500000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      499821261 2500000000 11924860569467 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5374946191/10000000000 : ℝ)^2107 ≤ (4403757222091/10000000000000 : ℝ)^1595 := by
    have hnat : (5374946191 : ℕ)^2107*10000000000000^1595 ≤ 4403757222091^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374946191 10000000000 4403757222091 10000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5374945727/10000000000 : ℝ)^2107 ≤ (1761502687959/4000000000000 : ℝ)^1595 := by
    have hnat : (5374945727 : ℕ)^2107*4000000000000^1595 ≤ 1761502687959^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374945727 10000000000 1761502687959 4000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-499821261/2500000000 : ℝ), (5374946191/10000000000 : ℝ), (5374945727/10000000000 : ℝ)] ![(11924860569467/100000000000000 : ℝ), (4403757222091/10000000000000 : ℝ), (1761502687959/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-499821261/2500000000 : ℝ)|^2107 ≤ (11924860569467/100000000000000 : ℝ)^1595
        have hw : |(-499821261/2500000000 : ℝ)|=(499821261/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5374946191/10000000000 : ℝ)|^2107 ≤ (4403757222091/10000000000000 : ℝ)^1595
        have hw : |(5374946191/10000000000 : ℝ)|=(5374946191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5374945727/10000000000 : ℝ)|^2107 ≤ (1761502687959/4000000000000 : ℝ)^1595
        have hw : |(5374945727/10000000000 : ℝ)|=(5374945727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_box_1 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (662093367/1250000000 : ℝ)*x 0 + (-2105553687/10000000000 : ℝ)*x 1 + (537494633/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (662093367/1250000000 : ℝ)^2107 ≤ (2159659699197/5000000000000 : ℝ)^1595 := by
    have hnat : (662093367 : ℕ)^2107*5000000000000^1595 ≤ 2159659699197^1595*1250000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      662093367 1250000000 2159659699197 5000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2105553687/10000000000 : ℝ)^2107 ≤ (12769232273357/100000000000000 : ℝ)^1595 := by
    have hnat : (2105553687 : ℕ)^2107*100000000000000^1595 ≤ 12769232273357^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2105553687 10000000000 12769232273357 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (537494633/1000000000 : ℝ)^2107 ≤ (22018786862663/50000000000000 : ℝ)^1595 := by
    have hnat : (537494633 : ℕ)^2107*50000000000000^1595 ≤ 22018786862663^1595*1000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537494633 1000000000 22018786862663 50000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(662093367/1250000000 : ℝ), (-2105553687/10000000000 : ℝ), (537494633/1000000000 : ℝ)] ![(2159659699197/5000000000000 : ℝ), (12769232273357/100000000000000 : ℝ), (22018786862663/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(662093367/1250000000 : ℝ)|^2107 ≤ (2159659699197/5000000000000 : ℝ)^1595
        have hw : |(662093367/1250000000 : ℝ)|=(662093367/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2105553687/10000000000 : ℝ)|^2107 ≤ (12769232273357/100000000000000 : ℝ)^1595
        have hw : |(-2105553687/10000000000 : ℝ)|=(2105553687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(537494633/1000000000 : ℝ)|^2107 ≤ (22018786862663/50000000000000 : ℝ)^1595
        have hw : |(537494633/1000000000 : ℝ)|=(537494633/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_box_2 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (20690421/39062500 : ℝ)*x 0 + (5374946017/10000000000 : ℝ)*x 1 + (-2105552981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20690421/39062500 : ℝ)^2107 ≤ (43193203032703/100000000000000 : ℝ)^1595 := by
    have hnat : (20690421 : ℕ)^2107*100000000000000^1595 ≤ 43193203032703^1595*39062500^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20690421 39062500 43193203032703 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5374946017/10000000000 : ℝ)^2107 ≤ (11009392584421/25000000000000 : ℝ)^1595 := by
    have hnat : (5374946017 : ℕ)^2107*25000000000000^1595 ≤ 11009392584421^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374946017 10000000000 11009392584421 25000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2105552981/10000000000 : ℝ)^2107 ≤ (3192306654347/25000000000000 : ℝ)^1595 := by
    have hnat : (2105552981 : ℕ)^2107*25000000000000^1595 ≤ 3192306654347^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2105552981 10000000000 3192306654347 25000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(20690421/39062500 : ℝ), (5374946017/10000000000 : ℝ), (-2105552981/10000000000 : ℝ)] ![(43193203032703/100000000000000 : ℝ), (11009392584421/25000000000000 : ℝ), (3192306654347/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(20690421/39062500 : ℝ)|^2107 ≤ (43193203032703/100000000000000 : ℝ)^1595
        have hw : |(20690421/39062500 : ℝ)|=(20690421/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5374946017/10000000000 : ℝ)|^2107 ≤ (11009392584421/25000000000000 : ℝ)^1595
        have hw : |(5374946017/10000000000 : ℝ)|=(5374946017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2105552981/10000000000 : ℝ)|^2107 ≤ (3192306654347/25000000000000 : ℝ)^1595
        have hw : |(-2105552981/10000000000 : ℝ)|=(2105552981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_box_3 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1114582121/2500000000 : ℝ)*x 0 + (4300485957/10000000000 : ℝ)*x 1 + (860097289/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1114582121/2500000000 : ℝ)^2107 ≤ (8599935715421/25000000000000 : ℝ)^1595 := by
    have hnat : (1114582121 : ℕ)^2107*25000000000000^1595 ≤ 8599935715421^1595*2500000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1114582121 2500000000 8599935715421 25000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4300485957/10000000000 : ℝ)^2107 ≤ (32800126099667/100000000000000 : ℝ)^1595 := by
    have hnat : (4300485957 : ℕ)^2107*100000000000000^1595 ≤ 32800126099667^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4300485957 10000000000 32800126099667 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (860097289/2000000000 : ℝ)^2107 ≤ (32800131016457/100000000000000 : ℝ)^1595 := by
    have hnat : (860097289 : ℕ)^2107*100000000000000^1595 ≤ 32800131016457^1595*2000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      860097289 2000000000 32800131016457 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1114582121/2500000000 : ℝ), (4300485957/10000000000 : ℝ), (860097289/2000000000 : ℝ)] ![(8599935715421/25000000000000 : ℝ), (32800126099667/100000000000000 : ℝ), (32800131016457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1114582121/2500000000 : ℝ)|^2107 ≤ (8599935715421/25000000000000 : ℝ)^1595
        have hw : |(1114582121/2500000000 : ℝ)|=(1114582121/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4300485957/10000000000 : ℝ)|^2107 ≤ (32800126099667/100000000000000 : ℝ)^1595
        have hw : |(4300485957/10000000000 : ℝ)|=(4300485957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(860097289/2000000000 : ℝ)|^2107 ≤ (32800131016457/100000000000000 : ℝ)^1595
        have hw : |(860097289/2000000000 : ℝ)|=(860097289/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_box_4 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2248480457/10000000000 : ℝ)*x 0 + (2641107757/5000000000 : ℝ)*x 1 + (5282215557/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2248480457/10000000000 : ℝ)^2107 ≤ (3481637094153/25000000000000 : ℝ)^1595 := by
    have hnat : (2248480457 : ℕ)^2107*25000000000000^1595 ≤ 3481637094153^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248480457 10000000000 3481637094153 25000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2641107757/5000000000 : ℝ)^2107 ≤ (43036725575459/100000000000000 : ℝ)^1595 := by
    have hnat : (2641107757 : ℕ)^2107*100000000000000^1595 ≤ 43036725575459^1595*5000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2641107757 5000000000 43036725575459 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5282215557/10000000000 : ℝ)^2107 ≤ (43036726038261/100000000000000 : ℝ)^1595 := by
    have hnat : (5282215557 : ℕ)^2107*100000000000000^1595 ≤ 43036726038261^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282215557 10000000000 43036726038261 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2248480457/10000000000 : ℝ), (2641107757/5000000000 : ℝ), (5282215557/10000000000 : ℝ)] ![(3481637094153/25000000000000 : ℝ), (43036725575459/100000000000000 : ℝ), (43036726038261/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2248480457/10000000000 : ℝ)|^2107 ≤ (3481637094153/25000000000000 : ℝ)^1595
        have hw : |(-2248480457/10000000000 : ℝ)|=(2248480457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2641107757/5000000000 : ℝ)|^2107 ≤ (43036725575459/100000000000000 : ℝ)^1595
        have hw : |(2641107757/5000000000 : ℝ)|=(2641107757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5282215557/10000000000 : ℝ)|^2107 ≤ (43036726038261/100000000000000 : ℝ)^1595
        have hw : |(5282215557/10000000000 : ℝ)|=(5282215557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_box_5 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5362125813/10000000000 : ℝ)*x 0 + (-2142295887/10000000000 : ℝ)*x 1 + (5282215509/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362125813/10000000000 : ℝ)^2107 ≤ (43898868681533/100000000000000 : ℝ)^1595 := by
    have hnat : (5362125813 : ℕ)^2107*100000000000000^1595 ≤ 43898868681533^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362125813 10000000000 43898868681533 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2142295887/10000000000 : ℝ)^2107 ≤ (13064405781713/100000000000000 : ℝ)^1595 := by
    have hnat : (2142295887 : ℕ)^2107*100000000000000^1595 ≤ 13064405781713^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2142295887 10000000000 13064405781713 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5282215509/10000000000 : ℝ)^2107 ≤ (8607345104329/20000000000000 : ℝ)^1595 := by
    have hnat : (5282215509 : ℕ)^2107*20000000000000^1595 ≤ 8607345104329^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282215509 10000000000 8607345104329 20000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362125813/10000000000 : ℝ), (-2142295887/10000000000 : ℝ), (5282215509/10000000000 : ℝ)] ![(43898868681533/100000000000000 : ℝ), (13064405781713/100000000000000 : ℝ), (8607345104329/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362125813/10000000000 : ℝ)|^2107 ≤ (43898868681533/100000000000000 : ℝ)^1595
        have hw : |(5362125813/10000000000 : ℝ)|=(5362125813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2142295887/10000000000 : ℝ)|^2107 ≤ (13064405781713/100000000000000 : ℝ)^1595
        have hw : |(-2142295887/10000000000 : ℝ)|=(2142295887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5282215509/10000000000 : ℝ)|^2107 ≤ (8607345104329/20000000000000 : ℝ)^1595
        have hw : |(5282215509/10000000000 : ℝ)|=(5282215509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_box_6 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1072425153/2000000000 : ℝ)*x 0 + (5282215571/10000000000 : ℝ)*x 1 + (-535573967/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072425153/2000000000 : ℝ)^2107 ≤ (43898868162421/100000000000000 : ℝ)^1595 := by
    have hnat : (1072425153 : ℕ)^2107*100000000000000^1595 ≤ 43898868162421^1595*2000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072425153 2000000000 43898868162421 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5282215571/10000000000 : ℝ)^2107 ≤ (43036726188941/100000000000000 : ℝ)^1595 := by
    have hnat : (5282215571 : ℕ)^2107*100000000000000^1595 ≤ 43036726188941^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282215571 10000000000 43036726188941 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (535573967/2500000000 : ℝ)^2107 ≤ (261288112573/2000000000000 : ℝ)^1595 := by
    have hnat : (535573967 : ℕ)^2107*2000000000000^1595 ≤ 261288112573^1595*2500000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535573967 2500000000 261288112573 2000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1072425153/2000000000 : ℝ), (5282215571/10000000000 : ℝ), (-535573967/2500000000 : ℝ)] ![(43898868162421/100000000000000 : ℝ), (43036726188941/100000000000000 : ℝ), (261288112573/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1072425153/2000000000 : ℝ)|^2107 ≤ (43898868162421/100000000000000 : ℝ)^1595
        have hw : |(1072425153/2000000000 : ℝ)|=(1072425153/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5282215571/10000000000 : ℝ)|^2107 ≤ (43036726188941/100000000000000 : ℝ)^1595
        have hw : |(5282215571/10000000000 : ℝ)|=(5282215571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-535573967/2500000000 : ℝ)|^2107 ≤ (261288112573/2000000000000 : ℝ)^1595
        have hw : |(-535573967/2500000000 : ℝ)|=(535573967/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_box_7 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4244745217/10000000000 : ℝ)*x 0 + (2203628803/5000000000 : ℝ)*x 1 + (220362889/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4244745217/10000000000 : ℝ)^2107 ≤ (32239688240271/100000000000000 : ℝ)^1595 := by
    have hnat : (4244745217 : ℕ)^2107*100000000000000^1595 ≤ 32239688240271^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4244745217 10000000000 32239688240271 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2203628803/5000000000 : ℝ)^2107 ≤ (33880154990639/100000000000000 : ℝ)^1595 := by
    have hnat : (2203628803 : ℕ)^2107*100000000000000^1595 ≤ 33880154990639^1595*5000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2203628803 5000000000 33880154990639 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (220362889/500000000 : ℝ)^2107 ≤ (33880156757613/100000000000000 : ℝ)^1595 := by
    have hnat : (220362889 : ℕ)^2107*100000000000000^1595 ≤ 33880156757613^1595*500000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220362889 500000000 33880156757613 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4244745217/10000000000 : ℝ), (2203628803/5000000000 : ℝ), (220362889/500000000 : ℝ)] ![(32239688240271/100000000000000 : ℝ), (33880154990639/100000000000000 : ℝ), (33880156757613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4244745217/10000000000 : ℝ)|^2107 ≤ (32239688240271/100000000000000 : ℝ)^1595
        have hw : |(4244745217/10000000000 : ℝ)|=(4244745217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2203628803/5000000000 : ℝ)|^2107 ≤ (33880154990639/100000000000000 : ℝ)^1595
        have hw : |(2203628803/5000000000 : ℝ)|=(2203628803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(220362889/500000000 : ℝ)|^2107 ≤ (33880156757613/100000000000000 : ℝ)^1595
        have hw : |(220362889/500000000 : ℝ)|=(220362889/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_box_8 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2196269113/10000000000 : ℝ)*x 0 + (1043795257/2000000000 : ℝ)*x 1 + (1346139681/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2196269113/10000000000 : ℝ)^2107 ≤ (13500956970281/100000000000000 : ℝ)^1595 := by
    have hnat : (2196269113 : ℕ)^2107*100000000000000^1595 ≤ 13500956970281^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2196269113 10000000000 13500956970281 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043795257/2000000000 : ℝ)^2107 ≤ (42357403192379/100000000000000 : ℝ)^1595 := by
    have hnat : (1043795257 : ℕ)^2107*100000000000000^1595 ≤ 42357403192379^1595*2000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043795257 2000000000 42357403192379 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1346139681/2500000000 : ℝ)^2107 ≤ (44141639819063/100000000000000 : ℝ)^1595 := by
    have hnat : (1346139681 : ℕ)^2107*100000000000000^1595 ≤ 44141639819063^1595*2500000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346139681 2500000000 44141639819063 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2196269113/10000000000 : ℝ), (1043795257/2000000000 : ℝ), (1346139681/2500000000 : ℝ)] ![(13500956970281/100000000000000 : ℝ), (42357403192379/100000000000000 : ℝ), (44141639819063/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2196269113/10000000000 : ℝ)|^2107 ≤ (13500956970281/100000000000000 : ℝ)^1595
        have hw : |(-2196269113/10000000000 : ℝ)|=(2196269113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043795257/2000000000 : ℝ)|^2107 ≤ (42357403192379/100000000000000 : ℝ)^1595
        have hw : |(1043795257/2000000000 : ℝ)|=(1043795257/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1346139681/2500000000 : ℝ)|^2107 ≤ (44141639819063/100000000000000 : ℝ)^1595
        have hw : |(1346139681/2500000000 : ℝ)|=(1346139681/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_box_9 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (661245871/1250000000 : ℝ)*x 0 + (-2101677351/10000000000 : ℝ)*x 1 + (1346139687/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661245871/1250000000 : ℝ)^2107 ≤ (43120172890999/100000000000000 : ℝ)^1595 := by
    have hnat : (661245871 : ℕ)^2107*100000000000000^1595 ≤ 43120172890999^1595*1250000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661245871 1250000000 43120172890999 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2101677351/10000000000 : ℝ)^2107 ≤ (12738187011271/100000000000000 : ℝ)^1595 := by
    have hnat : (2101677351 : ℕ)^2107*100000000000000^1595 ≤ 12738187011271^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2101677351 10000000000 12738187011271 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1346139687/2500000000 : ℝ)^2107 ≤ (44141640078967/100000000000000 : ℝ)^1595 := by
    have hnat : (1346139687 : ℕ)^2107*100000000000000^1595 ≤ 44141640078967^1595*2500000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346139687 2500000000 44141640078967 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661245871/1250000000 : ℝ), (-2101677351/10000000000 : ℝ), (1346139687/2500000000 : ℝ)] ![(43120172890999/100000000000000 : ℝ), (12738187011271/100000000000000 : ℝ), (44141640078967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661245871/1250000000 : ℝ)|^2107 ≤ (43120172890999/100000000000000 : ℝ)^1595
        have hw : |(661245871/1250000000 : ℝ)|=(661245871/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2101677351/10000000000 : ℝ)|^2107 ≤ (12738187011271/100000000000000 : ℝ)^1595
        have hw : |(-2101677351/10000000000 : ℝ)|=(2101677351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1346139687/2500000000 : ℝ)|^2107 ≤ (44141640078967/100000000000000 : ℝ)^1595
        have hw : |(1346139687/2500000000 : ℝ)|=(1346139687/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_box_10 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2644983489/5000000000 : ℝ)*x 0 + (5384558723/10000000000 : ℝ)*x 1 + (-525419343/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644983489/5000000000 : ℝ)^2107 ≤ (21560086499339/50000000000000 : ℝ)^1595 := by
    have hnat : (2644983489 : ℕ)^2107*50000000000000^1595 ≤ 21560086499339^1595*5000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644983489 5000000000 21560086499339 50000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5384558723/10000000000 : ℝ)^2107 ≤ (22070819904117/50000000000000 : ℝ)^1595 := by
    have hnat : (5384558723 : ℕ)^2107*50000000000000^1595 ≤ 22070819904117^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384558723 10000000000 22070819904117 50000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (525419343/2500000000 : ℝ)^2107 ≤ (12738187179409/100000000000000 : ℝ)^1595 := by
    have hnat : (525419343 : ℕ)^2107*100000000000000^1595 ≤ 12738187179409^1595*2500000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525419343 2500000000 12738187179409 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644983489/5000000000 : ℝ), (5384558723/10000000000 : ℝ), (-525419343/2500000000 : ℝ)] ![(21560086499339/50000000000000 : ℝ), (22070819904117/50000000000000 : ℝ), (12738187179409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644983489/5000000000 : ℝ)|^2107 ≤ (21560086499339/50000000000000 : ℝ)^1595
        have hw : |(2644983489/5000000000 : ℝ)|=(2644983489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5384558723/10000000000 : ℝ)|^2107 ≤ (22070819904117/50000000000000 : ℝ)^1595
        have hw : |(5384558723/10000000000 : ℝ)|=(5384558723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-525419343/2500000000 : ℝ)|^2107 ≤ (12738187179409/100000000000000 : ℝ)^1595
        have hw : |(-525419343/2500000000 : ℝ)|=(525419343/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_box_11 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4480195519/10000000000 : ℝ)*x 0 + (536176523/1250000000 : ℝ)*x 1 + (4289412141/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4480195519/10000000000 : ℝ)^2107 ≤ (17311400546451/50000000000000 : ℝ)^1595 := by
    have hnat : (4480195519 : ℕ)^2107*50000000000000^1595 ≤ 17311400546451^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4480195519 10000000000 17311400546451 50000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (536176523/1250000000 : ℝ)^2107 ≤ (32688599666717/100000000000000 : ℝ)^1595 := by
    have hnat : (536176523 : ℕ)^2107*100000000000000^1595 ≤ 32688599666717^1595*1250000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536176523 1250000000 32688599666717 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4289412141/10000000000 : ℝ)^2107 ≤ (32688599233833/100000000000000 : ℝ)^1595 := by
    have hnat : (4289412141 : ℕ)^2107*100000000000000^1595 ≤ 32688599233833^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4289412141 10000000000 32688599233833 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4480195519/10000000000 : ℝ), (536176523/1250000000 : ℝ), (4289412141/10000000000 : ℝ)] ![(17311400546451/50000000000000 : ℝ), (32688599666717/100000000000000 : ℝ), (32688599233833/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4480195519/10000000000 : ℝ)|^2107 ≤ (17311400546451/50000000000000 : ℝ)^1595
        have hw : |(4480195519/10000000000 : ℝ)|=(4480195519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(536176523/1250000000 : ℝ)|^2107 ≤ (32688599666717/100000000000000 : ℝ)^1595
        have hw : |(536176523/1250000000 : ℝ)|=(536176523/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4289412141/10000000000 : ℝ)|^2107 ≤ (32688599233833/100000000000000 : ℝ)^1595
        have hw : |(4289412141/10000000000 : ℝ)|=(4289412141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_box_12 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-410351921/2000000000 : ℝ)*x 0 + (5436972213/10000000000 : ℝ)*x 1 + (5274139089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (410351921/2000000000 : ℝ)^2107 ≤ (2468009988511/20000000000000 : ℝ)^1595 := by
    have hnat : (410351921 : ℕ)^2107*20000000000000^1595 ≤ 2468009988511^1595*2000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410351921 2000000000 2468009988511 20000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5436972213/10000000000 : ℝ)^2107 ≤ (44710128416301/100000000000000 : ℝ)^1595 := by
    have hnat : (5436972213 : ℕ)^2107*100000000000000^1595 ≤ 44710128416301^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436972213 10000000000 44710128416301 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5274139089/10000000000 : ℝ)^2107 ≤ (10737455407731/25000000000000 : ℝ)^1595 := by
    have hnat : (5274139089 : ℕ)^2107*25000000000000^1595 ≤ 10737455407731^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274139089 10000000000 10737455407731 25000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-410351921/2000000000 : ℝ), (5436972213/10000000000 : ℝ), (5274139089/10000000000 : ℝ)] ![(2468009988511/20000000000000 : ℝ), (44710128416301/100000000000000 : ℝ), (10737455407731/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-410351921/2000000000 : ℝ)|^2107 ≤ (2468009988511/20000000000000 : ℝ)^1595
        have hw : |(-410351921/2000000000 : ℝ)|=(410351921/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5436972213/10000000000 : ℝ)|^2107 ≤ (44710128416301/100000000000000 : ℝ)^1595
        have hw : |(5436972213/10000000000 : ℝ)|=(5436972213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5274139089/10000000000 : ℝ)|^2107 ≤ (10737455407731/25000000000000 : ℝ)^1595
        have hw : |(5274139089/10000000000 : ℝ)|=(5274139089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_box_13 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (335488647/625000000 : ℝ)*x 0 + (-2145439711/10000000000 : ℝ)*x 1 + (5274138829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (335488647/625000000 : ℝ)^2107 ≤ (1758417723141/4000000000000 : ℝ)^1595 := by
    have hnat : (335488647 : ℕ)^2107*4000000000000^1595 ≤ 1758417723141^1595*625000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335488647 625000000 1758417723141 4000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2145439711/10000000000 : ℝ)^2107 ≤ (2617947615223/20000000000000 : ℝ)^1595 := by
    have hnat : (2145439711 : ℕ)^2107*20000000000000^1595 ≤ 2617947615223^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2145439711 10000000000 2617947615223 20000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5274138829/10000000000 : ℝ)^2107 ≤ (42949818833959/100000000000000 : ℝ)^1595 := by
    have hnat : (5274138829 : ℕ)^2107*100000000000000^1595 ≤ 42949818833959^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274138829 10000000000 42949818833959 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(335488647/625000000 : ℝ), (-2145439711/10000000000 : ℝ), (5274138829/10000000000 : ℝ)] ![(1758417723141/4000000000000 : ℝ), (2617947615223/20000000000000 : ℝ), (42949818833959/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(335488647/625000000 : ℝ)|^2107 ≤ (1758417723141/4000000000000 : ℝ)^1595
        have hw : |(335488647/625000000 : ℝ)|=(335488647/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2145439711/10000000000 : ℝ)|^2107 ≤ (2617947615223/20000000000000 : ℝ)^1595
        have hw : |(-2145439711/10000000000 : ℝ)|=(2145439711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5274138829/10000000000 : ℝ)|^2107 ≤ (42949818833959/100000000000000 : ℝ)^1595
        have hw : |(5274138829/10000000000 : ℝ)|=(5274138829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_box_14 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5367818239/10000000000 : ℝ)*x 0 + (1318534747/2500000000 : ℝ)*x 1 + (-2145439651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5367818239/10000000000 : ℝ)^2107 ≤ (43960441856031/100000000000000 : ℝ)^1595 := by
    have hnat : (5367818239 : ℕ)^2107*100000000000000^1595 ≤ 43960441856031^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5367818239 10000000000 43960441856031 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1318534747/2500000000 : ℝ)^2107 ≤ (42949820544411/100000000000000 : ℝ)^1595 := by
    have hnat : (1318534747 : ℕ)^2107*100000000000000^1595 ≤ 42949820544411^1595*2500000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318534747 2500000000 42949820544411 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2145439651/10000000000 : ℝ)^2107 ≤ (6544868796267/50000000000000 : ℝ)^1595 := by
    have hnat : (2145439651 : ℕ)^2107*50000000000000^1595 ≤ 6544868796267^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2145439651 10000000000 6544868796267 50000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5367818239/10000000000 : ℝ), (1318534747/2500000000 : ℝ), (-2145439651/10000000000 : ℝ)] ![(43960441856031/100000000000000 : ℝ), (42949820544411/100000000000000 : ℝ), (6544868796267/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5367818239/10000000000 : ℝ)|^2107 ≤ (43960441856031/100000000000000 : ℝ)^1595
        have hw : |(5367818239/10000000000 : ℝ)|=(5367818239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1318534747/2500000000 : ℝ)|^2107 ≤ (42949820544411/100000000000000 : ℝ)^1595
        have hw : |(1318534747/2500000000 : ℝ)|=(1318534747/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2145439651/10000000000 : ℝ)|^2107 ≤ (6544868796267/50000000000000 : ℝ)^1595
        have hw : |(-2145439651/10000000000 : ℝ)|=(2145439651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_box_15 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4225910867/10000000000 : ℝ)*x 0 + (4416551931/10000000000 : ℝ)*x 1 + (883310493/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4225910867/10000000000 : ℝ)^2107 ≤ (32050852592881/100000000000000 : ℝ)^1595 := by
    have hnat : (4225910867 : ℕ)^2107*100000000000000^1595 ≤ 32050852592881^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4225910867 10000000000 32050852592881 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4416551931/10000000000 : ℝ)^2107 ≤ (6794914196459/20000000000000 : ℝ)^1595 := by
    have hnat : (4416551931 : ℕ)^2107*20000000000000^1595 ≤ 6794914196459^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4416551931 10000000000 6794914196459 20000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (883310493/2000000000 : ℝ)^2107 ≤ (4246822051093/12500000000000 : ℝ)^1595 := by
    have hnat : (883310493 : ℕ)^2107*12500000000000^1595 ≤ 4246822051093^1595*2000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      883310493 2000000000 4246822051093 12500000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4225910867/10000000000 : ℝ), (4416551931/10000000000 : ℝ), (883310493/2000000000 : ℝ)] ![(32050852592881/100000000000000 : ℝ), (6794914196459/20000000000000 : ℝ), (4246822051093/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4225910867/10000000000 : ℝ)|^2107 ≤ (32050852592881/100000000000000 : ℝ)^1595
        have hw : |(4225910867/10000000000 : ℝ)|=(4225910867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4416551931/10000000000 : ℝ)|^2107 ≤ (6794914196459/20000000000000 : ℝ)^1595
        have hw : |(4416551931/10000000000 : ℝ)|=(4416551931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(883310493/2000000000 : ℝ)|^2107 ≤ (4246822051093/12500000000000 : ℝ)^1595
        have hw : |(883310493/2000000000 : ℝ)|=(883310493/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1235_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37822863/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (141/1000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11471/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(12449/20000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(14843/25000 : ℝ) ∧ (10011/12500 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (8333/10000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (141/1000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11471/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (141/1000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11471/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (141/1000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11471/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (141/1000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11471/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (141/1000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11471/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (141/1000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11471/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11471/100000 : ℝ) ^ (8427/2048 : ℝ) ≤ (1688138413540313/12500000000000000000 : ℝ) := by
    have hpowers : (11471/100000 : ℝ)^8427 ≤ (1688138413540313/12500000000000000000 : ℝ)^2048 := by
      have hnat : (11471 : ℕ)^8427*12500000000000000000^2048 ≤ 1688138413540313^2048*100000^8427 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11471 100000 1688138413540313 12500000000000000000 8427 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11471/100000 : ℝ)) (X := (1688138413540313/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8427 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (141/1000 : ℝ) ^ (8427/2048 : ℝ) ≤ (31568407001193231/100000000000000000000 : ℝ) := by
    have hpowers : (141/1000 : ℝ)^8427 ≤ (31568407001193231/100000000000000000000 : ℝ)^2048 := by
      have hnat : (141 : ℕ)^8427*100000000000000000000^2048 ≤ 31568407001193231^2048*1000^8427 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        141 1000 31568407001193231 100000000000000000000 8427 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (141/1000 : ℝ)) (X := (31568407001193231/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8427 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251688138413540313/6250000000000000000 : ℝ) ≤ (10000656357723863/10000000000000000 : ℝ) ^ (8427/2048 : ℝ) := by
    have hpowers : (6251688138413540313/6250000000000000000 : ℝ)^2048 ≤ (10000656357723863/10000000000000000 : ℝ)^8427 := by
      have hnat : (6251688138413540313 : ℕ)^2048*10000000000000000^8427 ≤ 10000656357723863^8427*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251688138413540313 6250000000000000000 10000656357723863 10000000000000000 2048 8427 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000656357723863/10000000000000000 : ℝ)) (X := (6251688138413540313/6250000000000000000 : ℝ)) (by norm_num) 8427 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009014702861903147/20000000000000000000 : ℝ) ≤ (5000547613703397/5000000000000000 : ℝ) ^ (8427/2048 : ℝ) := by
    have hpowers : (20009014702861903147/20000000000000000000 : ℝ)^2048 ≤ (5000547613703397/5000000000000000 : ℝ)^8427 := by
      have hnat : (20009014702861903147 : ℕ)^2048*5000000000000000^8427 ≤ 5000547613703397^8427*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009014702861903147 20000000000000000000 5000547613703397 5000000000000000 2048 8427 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000547613703397/5000000000000000 : ℝ)) (X := (20009014702861903147/20000000000000000000 : ℝ)) (by norm_num) 8427 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031568407001193231/50000000000000000000 : ℝ) ≤ (400061363883589/400000000000000 : ℝ) ^ (8427/2048 : ℝ) := by
    have hpowers : (50031568407001193231/50000000000000000000 : ℝ)^2048 ≤ (400061363883589/400000000000000 : ℝ)^8427 := by
      have hnat : (50031568407001193231 : ℕ)^2048*400000000000000^8427 ≤ 400061363883589^8427*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031568407001193231 50000000000000000000 400061363883589 400000000000000 2048 8427 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400061363883589/400000000000000 : ℝ)) (X := (50031568407001193231/50000000000000000000 : ℝ)) (by norm_num) 8427 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1688138413540313/12500000000000000000 : ℝ) ≤ ((1051266280647609313/1051600000000000000 : ℝ)+2*(438869682931/262900000000000 : ℝ)*(11471/100000 : ℝ))^(8427/2048 : ℝ) := by
    rw [show (1051266280647609313/1051600000000000000 : ℝ)+2*(438869682931/262900000000000 : ℝ)*(11471/100000 : ℝ)=(10000656357723863/10000000000000000 : ℝ) by norm_num, show 1+2*(1688138413540313/12500000000000000000 : ℝ)=(6251688138413540313/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31568407001193231/100000000000000000000 : ℝ)+(1688138413540313/12500000000000000000 : ℝ) ≤ ((1051266280647609313/1051600000000000000 : ℝ)+(438869682931/262900000000000 : ℝ)*((141/1000 : ℝ)+(11471/100000 : ℝ)))^(8427/2048 : ℝ) := by
    rw [show (1051266280647609313/1051600000000000000 : ℝ)+(438869682931/262900000000000 : ℝ)*((141/1000 : ℝ)+(11471/100000 : ℝ))=(5000547613703397/5000000000000000 : ℝ) by norm_num, show 1+(31568407001193231/100000000000000000000 : ℝ)+(1688138413540313/12500000000000000000 : ℝ)=(20009014702861903147/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31568407001193231/100000000000000000000 : ℝ) ≤ ((1051266280647609313/1051600000000000000 : ℝ)+2*(438869682931/262900000000000 : ℝ)*(141/1000 : ℝ))^(8427/2048 : ℝ) := by
    rw [show (1051266280647609313/1051600000000000000 : ℝ)+2*(438869682931/262900000000000 : ℝ)*(141/1000 : ℝ)=(400061363883589/400000000000000 : ℝ) by norm_num, show 1+2*(31568407001193231/100000000000000000000 : ℝ)=(50031568407001193231/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1051266280647609313/1051600000000000000 : ℝ)*(X 1 0+X 2 0)+(438869682931/262900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8427/2048 : ℝ)) (lo := (11471/100000 : ℝ)) (hi := (141/1000 : ℝ)) (c := (1051266280647609313/1051600000000000000 : ℝ)) (alpha := (438869682931/262900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1051266280647609313/1051600000000000000 : ℝ)*(X 0 1+X 2 1)+(438869682931/262900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8427/2048 : ℝ)) (lo := (11471/100000 : ℝ)) (hi := (141/1000 : ℝ)) (c := (1051266280647609313/1051600000000000000 : ℝ)) (alpha := (438869682931/262900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1051266280647609313/1051600000000000000 : ℝ)*(X 0 2+X 1 2)+(438869682931/262900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8427/2048 : ℝ)) (lo := (11471/100000 : ℝ)) (hi := (141/1000 : ℝ)) (c := (1051266280647609313/1051600000000000000 : ℝ)) (alpha := (438869682931/262900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-499821261/2500000000 : ℝ)*X 0 0+(5374946191/10000000000 : ℝ)*X 0 1+(5374945727/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((662093367/1250000000 : ℝ)*X 1 0+(-2105553687/10000000000 : ℝ)*X 1 1+(537494633/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((20690421/39062500 : ℝ)*X 2 0+(5374946017/10000000000 : ℝ)*X 2 1+(-2105552981/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1114582121/2500000000 : ℝ)*X 0 0+(4300485957/10000000000 : ℝ)*X 0 1+(860097289/2000000000 : ℝ)*X 0 2+(1114582121/2500000000 : ℝ)*X 1 0+(4300485957/10000000000 : ℝ)*X 1 1+(860097289/2000000000 : ℝ)*X 1 2+(1114582121/2500000000 : ℝ)*X 2 0+(4300485957/10000000000 : ℝ)*X 2 1+(860097289/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2248480457/10000000000 : ℝ)*X 0 0+(2641107757/5000000000 : ℝ)*X 0 1+(5282215557/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5362125813/10000000000 : ℝ)*X 1 0+(-2142295887/10000000000 : ℝ)*X 1 1+(5282215509/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1072425153/2000000000 : ℝ)*X 2 0+(5282215571/10000000000 : ℝ)*X 2 1+(-535573967/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4244745217/10000000000 : ℝ)*X 0 0+(2203628803/5000000000 : ℝ)*X 0 1+(220362889/500000000 : ℝ)*X 0 2+(4244745217/10000000000 : ℝ)*X 1 0+(2203628803/5000000000 : ℝ)*X 1 1+(220362889/500000000 : ℝ)*X 1 2+(4244745217/10000000000 : ℝ)*X 2 0+(2203628803/5000000000 : ℝ)*X 2 1+(220362889/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2196269113/10000000000 : ℝ)*X 0 0+(1043795257/2000000000 : ℝ)*X 0 1+(1346139681/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((661245871/1250000000 : ℝ)*X 1 0+(-2101677351/10000000000 : ℝ)*X 1 1+(1346139687/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2644983489/5000000000 : ℝ)*X 2 0+(5384558723/10000000000 : ℝ)*X 2 1+(-525419343/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4480195519/10000000000 : ℝ)*X 0 0+(536176523/1250000000 : ℝ)*X 0 1+(4289412141/10000000000 : ℝ)*X 0 2+(4480195519/10000000000 : ℝ)*X 1 0+(536176523/1250000000 : ℝ)*X 1 1+(4289412141/10000000000 : ℝ)*X 1 2+(4480195519/10000000000 : ℝ)*X 2 0+(536176523/1250000000 : ℝ)*X 2 1+(4289412141/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-410351921/2000000000 : ℝ)*X 0 0+(5436972213/10000000000 : ℝ)*X 0 1+(5274139089/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((335488647/625000000 : ℝ)*X 1 0+(-2145439711/10000000000 : ℝ)*X 1 1+(5274138829/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5367818239/10000000000 : ℝ)*X 2 0+(1318534747/2500000000 : ℝ)*X 2 1+(-2145439651/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4225910867/10000000000 : ℝ)*X 0 0+(4416551931/10000000000 : ℝ)*X 0 1+(883310493/2000000000 : ℝ)*X 0 2+(4225910867/10000000000 : ℝ)*X 1 0+(4416551931/10000000000 : ℝ)*X 1 1+(883310493/2000000000 : ℝ)*X 1 2+(4225910867/10000000000 : ℝ)*X 2 0+(4416551931/10000000000 : ℝ)*X 2 1+(883310493/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-12449/20000 : ℝ) ≤ (-8181812546723395896815570742387/13145000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (20502591/25000000000000 : ℝ)*(upper0) + (42899603/50000000000000 : ℝ)*(upper1) + (1073921/3125000000000 : ℝ)*(upper2) + (60005889/100000000000000 : ℝ)*(upper3) + (124798467/100000000000000 : ℝ)*(upper5) + (999394558512211/25000000000000 : ℝ)*(major0) + (999394558512211/25000000000000 : ℝ)*(major1) + (999394558512211/25000000000000 : ℝ)*(major2) + (1311173017/100000000000000 : ℝ)*(sp2) + (6875359239/100000000000000 : ℝ)*(sp3) + (2686800642254563/50000000000000 : ℝ)*(sp4) + (2686800642254563/50000000000000 : ℝ)*(sp5) + (5373599973336109/100000000000000 : ℝ)*(sp6) + (2642295899320221/100000000000000 : ℝ)*(sp7) + (132115138733973/5000000000000 : ℝ)*(f.failure) + (2686800642254563/50000000000000 : ℝ)*(f.sum) + (48463502741369/13145000000000000000000000000 : ℝ)*base65 + (457806991471815043/26290000000000000000000000000000 : ℝ)*base67 + (8412348117711655043/26290000000000000000000000000000 : ℝ)*base69 + (264240881342995043/26290000000000000000000000000000 : ℝ)*base71 + (107884859582149/13145000000000000000000000000 : ℝ)*base73 + (305995873993575043/26290000000000000000000000000000 : ℝ)*base75 + (178508162378685043/26290000000000000000000000000000 : ℝ)*base77 + (3037734188836255043/26290000000000000000000000000000 : ℝ)*base79 + (1182106767932953/6572500000000000000000000000 : ℝ)*base82 + (775301/125000000000000000000 : ℝ)*base90 + (775301/125000000000000000000 : ℝ)*base92 + (775301/125000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (14843/25000 : ℝ) ≤ (15609486363514786562608707095601/26290000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (107279017/25000000000000 : ℝ)*(lower1) + (1166561/1562500000000 : ℝ)*(lower2) + (132492969/25000000000000 : ℝ)*(upper4) + (4063270158931141/100000000000000 : ℝ)*(major0) + (4063270158931141/100000000000000 : ℝ)*(major1) + (4063270158931141/100000000000000 : ℝ)*(major2) + (5421013048131753/100000000000000 : ℝ)*(sp0) + (5420906697208599/100000000000000 : ℝ)*(sp1) + (2710507413984161/50000000000000 : ℝ)*(sp2) + (1342849181567727/50000000000000 : ℝ)*(sp3) + (10525982811/100000000000000 : ℝ)*(sp6) + (12594565911/50000000000000 : ℝ)*(sp7) + (12305819381/100000000000000 : ℝ)*(sp8) + (59328371267/50000000000000 : ℝ)*(sp9) + (671430888066819/25000000000000 : ℝ)*(f.failure) + (2710512676975567/50000000000000 : ℝ)*(f.sum) + (13353743535073/6572500000000000000000000000 : ℝ)*base65 + (47327004961520133/105160000000000000000000000000000 : ℝ)*base67 + (494577170155000133/105160000000000000000000000000000 : ℝ)*base69 + (2186413205354640133/105160000000000000000000000000000 : ℝ)*base71 + (1113232954483/1643125000000000000000000000 : ℝ)*base74 + (138557520452319867/105160000000000000000000000000000 : ℝ)*base76 + (1858791672465880133/105160000000000000000000000000000 : ℝ)*base77 + (626470345943000133/105160000000000000000000000000000 : ℝ)*base79 + (65334032112929/13145000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (1367203/625000000000000000000 : ℝ)*base90 + (1367203/625000000000000000000 : ℝ)*base92 + (1367203/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (10011/12500 : ℝ) ≤ (3828335404370026280664037496271/4780000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1764959/50000000000000 : ℝ)*(upper0) + (5395489/50000000000000 : ℝ)*(upper1) + (2229267/25000000000000 : ℝ)*(upper2) + (2714873/20000000000000 : ℝ)*(upper3) + (6696261/100000000000000 : ℝ)*(upper4) + (4530153259408279/100000000000000 : ℝ)*(major0) + (4530153259408279/100000000000000 : ℝ)*(major1) + (4530153259408279/100000000000000 : ℝ)*(major2) + (12183096967/100000000000000 : ℝ)*(sp1) + (1622604789/100000000000000 : ℝ)*(sp3) + (1509821900165557/25000000000000 : ℝ)*(sp8) + (6039275417565261/100000000000000 : ℝ)*(sp9) + (1509821900165557/25000000000000 : ℝ)*(sp10) + (1497160197968731/50000000000000 : ℝ)*(sp11) + (11977288074169/400000000000 : ℝ)*(f.failure) + (1509821900165557/25000000000000 : ℝ)*(f.sum) + (141668376123301/13145000000000000000000000000 : ℝ)*base66 + (2242135902202061673/105160000000000000000000000000000 : ℝ)*base68 + (1222545352266658327/105160000000000000000000000000000 : ℝ)*base69 + (5106172325083541673/105160000000000000000000000000000 : ℝ)*base72 + (2569927046803/410781250000000000000000000 : ℝ)*base74 + (21976689825901673/105160000000000000000000000000000 : ℝ)*base76 + (1368585111960618327/105160000000000000000000000000000 : ℝ)*base77 + (2465785128220301673/105160000000000000000000000000000 : ℝ)*base80 + (57922035574873/6572500000000000000000000000 : ℝ)*base82 + (25847/10000000000000000000 : ℝ)*base89 + (25847/10000000000000000000 : ℝ)*base91 + (25847/10000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-8333/10000 : ℝ) ≤ (-796614646429160843371968986379/956000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (17143887/50000000000000 : ℝ)*(upper3) + (50450639/50000000000000 : ℝ)*(lower4) + (31209449/12500000000000 : ℝ)*(upper5) + (913128147527571/20000000000000 : ℝ)*(major0) + (913128147527571/20000000000000 : ℝ)*(major1) + (913128147527571/20000000000000 : ℝ)*(major2) + (3365475369/12500000000000 : ℝ)*(sp4) + (133536275011/50000000000000 : ℝ)*(sp5) + (32242029507/10000000000000 : ℝ)*(sp6) + (57339024303/25000000000000 : ℝ)*(sp7) + (6141252129886631/100000000000000 : ℝ)*(sp12) + (6141011981139561/100000000000000 : ℝ)*(sp13) + (383809789587157/6250000000000 : ℝ)*(sp14) + (377193628681359/12500000000000 : ℝ)*(sp15) + (754444596387021/25000000000000 : ℝ)*(f.failure) + (6141279053689583/100000000000000 : ℝ)*(f.sum) + (691624516107/131450000000000000000000000 : ℝ)*base65 + (41465149810152723/21032000000000000000000000000000 : ℝ)*base67 + (87533407129143277/21032000000000000000000000000000 : ℝ)*base70 + (215690192283920723/21032000000000000000000000000000 : ℝ)*base71 + (293288710111/52580000000000000000000000 : ℝ)*base73 + (11234818232151277/21032000000000000000000000000000 : ℝ)*base76 + (181268346994000723/21032000000000000000000000000000 : ℝ)*base77 + (142999504428112723/21032000000000000000000000000000 : ℝ)*base79 + (1387510053529/2629000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (3488877/625000000000000000000 : ℝ)*base90 + (3488877/625000000000000000000 : ℝ)*base92 + (3488877/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1235_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37822863/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (141/1000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11471/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12449/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(14843/25000 : ℝ) else (10011/12500 : ℝ) ≤ X j i ∧ X j i ≤ (8333/10000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1235_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1235_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37822863/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (141/1000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11471/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12449/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(14843/25000 : ℝ) else (10011/12500 : ℝ) ≤ X j i ∧ X j i ≤ (8333/10000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1235_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37822863/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (141/1000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11471/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12449/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(14843/25000 : ℝ) else (10011/12500 : ℝ) ≤ X j i ∧ X j i ≤ (8333/10000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1235_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
