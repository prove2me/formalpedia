-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1482_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:13:24.285883+00:00
-- url     : https://prove2.me/submissions/dafb6a07-161c-4de3-9628-2dbc64f9ce5e

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
theorem support_rectangle_w1482_s3_0 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-956276171/5000000000 : ℝ)*x 0 + (680221231/1250000000 : ℝ)*x 1 + (5211835233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (956276171/5000000000 : ℝ)^4461 ≤ (2920931336861/25000000000000 : ℝ)^3437 := by
    have hnat : (956276171 : ℕ)^4461*25000000000000^3437 ≤ 2920931336861^3437*5000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      956276171 5000000000 2920931336861 25000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (680221231/1250000000 : ℝ)^4461 ≤ (22697505047621/50000000000000 : ℝ)^3437 := by
    have hnat : (680221231 : ℕ)^4461*50000000000000^3437 ≤ 22697505047621^3437*1250000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      680221231 1250000000 22697505047621 50000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5211835233/10000000000 : ℝ)^4461 ≤ (21460632271711/50000000000000 : ℝ)^3437 := by
    have hnat : (5211835233 : ℕ)^4461*50000000000000^3437 ≤ 21460632271711^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5211835233 10000000000 21460632271711 50000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-956276171/5000000000 : ℝ), (680221231/1250000000 : ℝ), (5211835233/10000000000 : ℝ)] ![(2920931336861/25000000000000 : ℝ), (22697505047621/50000000000000 : ℝ), (21460632271711/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-956276171/5000000000 : ℝ)|^4461 ≤ (2920931336861/25000000000000 : ℝ)^3437
        have hw : |(-956276171/5000000000 : ℝ)|=(956276171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(680221231/1250000000 : ℝ)|^4461 ≤ (22697505047621/50000000000000 : ℝ)^3437
        have hw : |(680221231/1250000000 : ℝ)|=(680221231/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5211835233/10000000000 : ℝ)|^4461 ≤ (21460632271711/50000000000000 : ℝ)^3437
        have hw : |(5211835233/10000000000 : ℝ)|=(5211835233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_s3_1 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677201009/5000000000 : ℝ)*x 0 + (-1015250217/5000000000 : ℝ)*x 1 + (5211835377/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677201009/5000000000 : ℝ)^4461 ≤ (44451322353341/100000000000000 : ℝ)^3437 := by
    have hnat : (2677201009 : ℕ)^4461*100000000000000^3437 ≤ 44451322353341^3437*5000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677201009 5000000000 44451322353341 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1015250217/5000000000 : ℝ)^4461 ≤ (2525482309489/20000000000000 : ℝ)^3437 := by
    have hnat : (1015250217 : ℕ)^4461*20000000000000^3437 ≤ 2525482309489^3437*5000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1015250217 5000000000 2525482309489 20000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5211835377/10000000000 : ℝ)^4461 ≤ (42921266082629/100000000000000 : ℝ)^3437 := by
    have hnat : (5211835377 : ℕ)^4461*100000000000000^3437 ≤ 42921266082629^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5211835377 10000000000 42921266082629 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677201009/5000000000 : ℝ), (-1015250217/5000000000 : ℝ), (5211835377/10000000000 : ℝ)] ![(44451322353341/100000000000000 : ℝ), (2525482309489/20000000000000 : ℝ), (42921266082629/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677201009/5000000000 : ℝ)|^4461 ≤ (44451322353341/100000000000000 : ℝ)^3437
        have hw : |(2677201009/5000000000 : ℝ)|=(2677201009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1015250217/5000000000 : ℝ)|^4461 ≤ (2525482309489/20000000000000 : ℝ)^3437
        have hw : |(-1015250217/5000000000 : ℝ)|=(1015250217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5211835377/10000000000 : ℝ)|^4461 ≤ (42921266082629/100000000000000 : ℝ)^3437
        have hw : |(5211835377/10000000000 : ℝ)|=(5211835377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_s3_2 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677201001/5000000000 : ℝ)*x 0 + (651479401/1250000000 : ℝ)*x 1 + (-2030500679/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677201001/5000000000 : ℝ)^4461 ≤ (22225661090469/50000000000000 : ℝ)^3437 := by
    have hnat : (2677201001 : ℕ)^4461*50000000000000^3437 ≤ 22225661090469^3437*5000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677201001 5000000000 22225661090469 50000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (651479401/1250000000 : ℝ)^4461 ≤ (42921264276199/100000000000000 : ℝ)^3437 := by
    have hnat : (651479401 : ℕ)^4461*100000000000000^3437 ≤ 42921264276199^3437*1250000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      651479401 1250000000 42921264276199 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2030500679/10000000000 : ℝ)^4461 ≤ (6313706762503/50000000000000 : ℝ)^3437 := by
    have hnat : (2030500679 : ℕ)^4461*50000000000000^3437 ≤ 6313706762503^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2030500679 10000000000 6313706762503 50000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677201001/5000000000 : ℝ), (651479401/1250000000 : ℝ), (-2030500679/10000000000 : ℝ)] ![(22225661090469/50000000000000 : ℝ), (42921264276199/100000000000000 : ℝ), (6313706762503/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677201001/5000000000 : ℝ)|^4461 ≤ (22225661090469/50000000000000 : ℝ)^3437
        have hw : |(2677201001/5000000000 : ℝ)|=(2677201001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(651479401/1250000000 : ℝ)|^4461 ≤ (42921264276199/100000000000000 : ℝ)^3437
        have hw : |(651479401/1250000000 : ℝ)|=(651479401/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2030500679/10000000000 : ℝ)|^4461 ≤ (6313706762503/50000000000000 : ℝ)^3437
        have hw : |(-2030500679/10000000000 : ℝ)|=(2030500679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_s3_3 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4283509313/10000000000 : ℝ)*x 0 + (2017465067/5000000000 : ℝ)*x 1 + (2272661387/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4283509313/10000000000 : ℝ)^4461 ≤ (3327363449731/10000000000000 : ℝ)^3437 := by
    have hnat : (4283509313 : ℕ)^4461*10000000000000^3437 ≤ 3327363449731^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4283509313 10000000000 3327363449731 10000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2017465067/5000000000 : ℝ)^4461 ≤ (30789389037723/100000000000000 : ℝ)^3437 := by
    have hnat : (2017465067 : ℕ)^4461*100000000000000^3437 ≤ 30789389037723^3437*5000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2017465067 5000000000 30789389037723 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2272661387/5000000000 : ℝ)^4461 ≤ (35936976445133/100000000000000 : ℝ)^3437 := by
    have hnat : (2272661387 : ℕ)^4461*100000000000000^3437 ≤ 35936976445133^3437*5000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2272661387 5000000000 35936976445133 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4283509313/10000000000 : ℝ), (2017465067/5000000000 : ℝ), (2272661387/5000000000 : ℝ)] ![(3327363449731/10000000000000 : ℝ), (30789389037723/100000000000000 : ℝ), (35936976445133/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4283509313/10000000000 : ℝ)|^4461 ≤ (3327363449731/10000000000000 : ℝ)^3437
        have hw : |(4283509313/10000000000 : ℝ)|=(4283509313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2017465067/5000000000 : ℝ)|^4461 ≤ (30789389037723/100000000000000 : ℝ)^3437
        have hw : |(2017465067/5000000000 : ℝ)|=(2017465067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2272661387/5000000000 : ℝ)|^4461 ≤ (35936976445133/100000000000000 : ℝ)^3437
        have hw : |(2272661387/5000000000 : ℝ)|=(2272661387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_s3_4 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1912586263/10000000000 : ℝ)*x 0 + (651632269/1250000000 : ℝ)*x 1 + (5440537633/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1912586263/10000000000 : ℝ)^4461 ≤ (5841997154589/50000000000000 : ℝ)^3437 := by
    have hnat : (1912586263 : ℕ)^4461*50000000000000^3437 ≤ 5841997154589^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1912586263 10000000000 5841997154589 50000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (651632269/1250000000 : ℝ)^4461 ≤ (42934336704601/100000000000000 : ℝ)^3437 := by
    have hnat : (651632269 : ℕ)^4461*100000000000000^3437 ≤ 42934336704601^3437*1250000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      651632269 1250000000 42934336704601 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5440537633/10000000000 : ℝ)^4461 ≤ (9076333793891/20000000000000 : ℝ)^3437 := by
    have hnat : (5440537633 : ℕ)^4461*20000000000000^3437 ≤ 9076333793891^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5440537633 10000000000 9076333793891 20000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1912586263/10000000000 : ℝ), (651632269/1250000000 : ℝ), (5440537633/10000000000 : ℝ)] ![(5841997154589/50000000000000 : ℝ), (42934336704601/100000000000000 : ℝ), (9076333793891/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1912586263/10000000000 : ℝ)|^4461 ≤ (5841997154589/50000000000000 : ℝ)^3437
        have hw : |(-1912586263/10000000000 : ℝ)|=(1912586263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(651632269/1250000000 : ℝ)|^4461 ≤ (42934336704601/100000000000000 : ℝ)^3437
        have hw : |(651632269/1250000000 : ℝ)|=(651632269/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5440537633/10000000000 : ℝ)|^4461 ≤ (9076333793891/20000000000000 : ℝ)^3437
        have hw : |(5440537633/10000000000 : ℝ)|=(5440537633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_s3_5 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (132358199/250000000 : ℝ)*x 0 + (-1801798527/10000000000 : ℝ)*x 1 + (2720268859/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132358199/250000000 : ℝ)^4461 ≤ (10951273879707/25000000000000 : ℝ)^3437 := by
    have hnat : (132358199 : ℕ)^4461*25000000000000^3437 ≤ 10951273879707^3437*250000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132358199 250000000 10951273879707 25000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1801798527/10000000000 : ℝ)^4461 ≤ (1055979939/9765625000 : ℝ)^3437 := by
    have hnat : (1801798527 : ℕ)^4461*9765625000^3437 ≤ 1055979939^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1801798527 10000000000 1055979939 9765625000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2720268859/5000000000 : ℝ)^4461 ≤ (22690834944857/50000000000000 : ℝ)^3437 := by
    have hnat : (2720268859 : ℕ)^4461*50000000000000^3437 ≤ 22690834944857^3437*5000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2720268859 5000000000 22690834944857 50000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132358199/250000000 : ℝ), (-1801798527/10000000000 : ℝ), (2720268859/5000000000 : ℝ)] ![(10951273879707/25000000000000 : ℝ), (1055979939/9765625000 : ℝ), (22690834944857/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132358199/250000000 : ℝ)|^4461 ≤ (10951273879707/25000000000000 : ℝ)^3437
        have hw : |(132358199/250000000 : ℝ)|=(132358199/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1801798527/10000000000 : ℝ)|^4461 ≤ (1055979939/9765625000 : ℝ)^3437
        have hw : |(-1801798527/10000000000 : ℝ)|=(1801798527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2720268859/5000000000 : ℝ)|^4461 ≤ (22690834944857/50000000000000 : ℝ)^3437
        have hw : |(2720268859/5000000000 : ℝ)|=(2720268859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_s3_6 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323582113/2500000000 : ℝ)*x 0 + (1360134327/2500000000 : ℝ)*x 1 + (-1801798419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323582113/2500000000 : ℝ)^4461 ≤ (2737818800153/6250000000000 : ℝ)^3437 := by
    have hnat : (1323582113 : ℕ)^4461*6250000000000^3437 ≤ 2737818800153^3437*2500000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323582113 2500000000 2737818800153 6250000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1360134327/2500000000 : ℝ)^4461 ≤ (709088522669/1562500000000 : ℝ)^3437 := by
    have hnat : (1360134327 : ℕ)^4461*1562500000000^3437 ≤ 709088522669^3437*2500000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1360134327 2500000000 709088522669 1562500000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1801798419/10000000000 : ℝ)^4461 ≤ (2703308433527/25000000000000 : ℝ)^3437 := by
    have hnat : (1801798419 : ℕ)^4461*25000000000000^3437 ≤ 2703308433527^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1801798419 10000000000 2703308433527 25000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323582113/2500000000 : ℝ), (1360134327/2500000000 : ℝ), (-1801798419/10000000000 : ℝ)] ![(2737818800153/6250000000000 : ℝ), (709088522669/1562500000000 : ℝ), (2703308433527/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323582113/2500000000 : ℝ)|^4461 ≤ (2737818800153/6250000000000 : ℝ)^3437
        have hw : |(1323582113/2500000000 : ℝ)|=(1323582113/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1360134327/2500000000 : ℝ)|^4461 ≤ (709088522669/1562500000000 : ℝ)^3437
        have hw : |(1360134327/2500000000 : ℝ)|=(1360134327/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1801798419/10000000000 : ℝ)|^4461 ≤ (2703308433527/25000000000000 : ℝ)^3437
        have hw : |(-1801798419/10000000000 : ℝ)|=(1801798419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_s3_7 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4283584713/10000000000 : ℝ)*x 0 + (2271304177/5000000000 : ℝ)*x 1 + (4037665329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4283584713/10000000000 : ℝ)^4461 ≤ (8318598673381/25000000000000 : ℝ)^3437 := by
    have hnat : (4283584713 : ℕ)^4461*25000000000000^3437 ≤ 8318598673381^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4283584713 10000000000 8318598673381 25000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2271304177/5000000000 : ℝ)^4461 ≤ (35909123706677/100000000000000 : ℝ)^3437 := by
    have hnat : (2271304177 : ℕ)^4461*100000000000000^3437 ≤ 35909123706677^3437*5000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2271304177 5000000000 35909123706677 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4037665329/10000000000 : ℝ)^4461 ≤ (30816481587727/100000000000000 : ℝ)^3437 := by
    have hnat : (4037665329 : ℕ)^4461*100000000000000^3437 ≤ 30816481587727^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4037665329 10000000000 30816481587727 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4283584713/10000000000 : ℝ), (2271304177/5000000000 : ℝ), (4037665329/10000000000 : ℝ)] ![(8318598673381/25000000000000 : ℝ), (35909123706677/100000000000000 : ℝ), (30816481587727/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4283584713/10000000000 : ℝ)|^4461 ≤ (8318598673381/25000000000000 : ℝ)^3437
        have hw : |(4283584713/10000000000 : ℝ)|=(4283584713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2271304177/5000000000 : ℝ)|^4461 ≤ (35909123706677/100000000000000 : ℝ)^3437
        have hw : |(2271304177/5000000000 : ℝ)|=(2271304177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4037665329/10000000000 : ℝ)|^4461 ≤ (30816481587727/100000000000000 : ℝ)^3437
        have hw : |(4037665329/10000000000 : ℝ)|=(4037665329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1482_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5030833/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8061/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5101/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5353/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3893/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8061/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5101/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8061/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5101/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8061/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5101/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8061/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5101/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8061/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5101/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8061/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5101/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5101/50000 : ℝ) ^ (4459/1024 : ℝ) ≤ (150722465193721/3125000000000000000 : ℝ) := by
    have hpowers : (5101/50000 : ℝ)^4459 ≤ (150722465193721/3125000000000000000 : ℝ)^1024 := by
      have hnat : (5101 : ℕ)^4459*3125000000000000000^1024 ≤ 150722465193721^1024*50000^4459 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5101 50000 150722465193721 3125000000000000000 4459 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5101/50000 : ℝ)) (X := (150722465193721/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4459 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8061/50000 : ℝ) ^ (4459/1024 : ℝ) ≤ (4422031972547897/12500000000000000000 : ℝ) := by
    have hpowers : (8061/50000 : ℝ)^4459 ≤ (4422031972547897/12500000000000000000 : ℝ)^1024 := by
      have hnat : (8061 : ℕ)^4459*12500000000000000000^1024 ≤ 4422031972547897^1024*50000^4459 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8061 50000 4422031972547897 12500000000000000000 4459 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8061/50000 : ℝ)) (X := (4422031972547897/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4459 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562650722465193721/1562500000000000000 : ℝ) ≤ (2500055378899373/2500000000000000 : ℝ) ^ (4459/1024 : ℝ) := by
    have hpowers : (1562650722465193721/1562500000000000000 : ℝ)^1024 ≤ (2500055378899373/2500000000000000 : ℝ)^4459 := by
      have hnat : (1562650722465193721 : ℕ)^1024*2500000000000000^4459 ≤ 2500055378899373^4459*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562650722465193721 1562500000000000000 2500055378899373 2500000000000000 1024 4459 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500055378899373/2500000000000000 : ℝ)) (X := (1562650722465193721/1562500000000000000 : ℝ)) (by norm_num) 4459 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12505024921833322781/12500000000000000000 : ℝ) ≤ (10000923027301617/10000000000000000 : ℝ) ^ (4459/1024 : ℝ) := by
    have hpowers : (12505024921833322781/12500000000000000000 : ℝ)^1024 ≤ (10000923027301617/10000000000000000 : ℝ)^4459 := by
      have hnat : (12505024921833322781 : ℕ)^1024*10000000000000000^4459 ≤ 10000923027301617^4459*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505024921833322781 12500000000000000000 10000923027301617 10000000000000000 1024 4459 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000923027301617/10000000000000000 : ℝ)) (X := (12505024921833322781/12500000000000000000 : ℝ)) (by norm_num) 4459 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254422031972547897/6250000000000000000 : ℝ) ≤ (5000812269502871/5000000000000000 : ℝ) ^ (4459/1024 : ℝ) := by
    have hpowers : (6254422031972547897/6250000000000000000 : ℝ)^1024 ≤ (5000812269502871/5000000000000000 : ℝ)^4459 := by
      have hnat : (6254422031972547897 : ℕ)^1024*5000000000000000^4459 ≤ 5000812269502871^4459*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254422031972547897 6250000000000000000 5000812269502871 5000000000000000 1024 4459 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000812269502871/5000000000000000 : ℝ)) (X := (6254422031972547897/6250000000000000000 : ℝ)) (by norm_num) 4459 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(150722465193721/3125000000000000000 : ℝ) ≤ ((2959349886376309307/2960000000000000000 : ℝ)+2*(5612093633/4736000000000 : ℝ)*(5101/50000 : ℝ))^(4459/1024 : ℝ) := by
    rw [show (2959349886376309307/2960000000000000000 : ℝ)+2*(5612093633/4736000000000 : ℝ)*(5101/50000 : ℝ)=(2500055378899373/2500000000000000 : ℝ) by norm_num, show 1+2*(150722465193721/3125000000000000000 : ℝ)=(1562650722465193721/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4422031972547897/12500000000000000000 : ℝ)+(150722465193721/3125000000000000000 : ℝ) ≤ ((2959349886376309307/2960000000000000000 : ℝ)+(5612093633/4736000000000 : ℝ)*((8061/50000 : ℝ)+(5101/50000 : ℝ)))^(4459/1024 : ℝ) := by
    rw [show (2959349886376309307/2960000000000000000 : ℝ)+(5612093633/4736000000000 : ℝ)*((8061/50000 : ℝ)+(5101/50000 : ℝ))=(10000923027301617/10000000000000000 : ℝ) by norm_num, show 1+(4422031972547897/12500000000000000000 : ℝ)+(150722465193721/3125000000000000000 : ℝ)=(12505024921833322781/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4422031972547897/12500000000000000000 : ℝ) ≤ ((2959349886376309307/2960000000000000000 : ℝ)+2*(5612093633/4736000000000 : ℝ)*(8061/50000 : ℝ))^(4459/1024 : ℝ) := by
    rw [show (2959349886376309307/2960000000000000000 : ℝ)+2*(5612093633/4736000000000 : ℝ)*(8061/50000 : ℝ)=(5000812269502871/5000000000000000 : ℝ) by norm_num, show 1+2*(4422031972547897/12500000000000000000 : ℝ)=(6254422031972547897/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2959349886376309307/2960000000000000000 : ℝ)*(X 1 0+X 2 0)+(5612093633/4736000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4459/1024 : ℝ)) (lo := (5101/50000 : ℝ)) (hi := (8061/50000 : ℝ)) (c := (2959349886376309307/2960000000000000000 : ℝ)) (alpha := (5612093633/4736000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2959349886376309307/2960000000000000000 : ℝ)*(X 0 1+X 2 1)+(5612093633/4736000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4459/1024 : ℝ)) (lo := (5101/50000 : ℝ)) (hi := (8061/50000 : ℝ)) (c := (2959349886376309307/2960000000000000000 : ℝ)) (alpha := (5612093633/4736000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2959349886376309307/2960000000000000000 : ℝ)*(X 0 2+X 1 2)+(5612093633/4736000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4459/1024 : ℝ)) (lo := (5101/50000 : ℝ)) (hi := (8061/50000 : ℝ)) (c := (2959349886376309307/2960000000000000000 : ℝ)) (alpha := (5612093633/4736000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-956276171/5000000000 : ℝ)*X 0 0+(680221231/1250000000 : ℝ)*X 0 1+(5211835233/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2677201009/5000000000 : ℝ)*X 1 0+(-1015250217/5000000000 : ℝ)*X 1 1+(5211835377/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2677201001/5000000000 : ℝ)*X 2 0+(651479401/1250000000 : ℝ)*X 2 1+(-2030500679/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4283509313/10000000000 : ℝ)*X 0 0+(2017465067/5000000000 : ℝ)*X 0 1+(2272661387/5000000000 : ℝ)*X 0 2+(4283509313/10000000000 : ℝ)*X 1 0+(2017465067/5000000000 : ℝ)*X 1 1+(2272661387/5000000000 : ℝ)*X 1 2+(4283509313/10000000000 : ℝ)*X 2 0+(2017465067/5000000000 : ℝ)*X 2 1+(2272661387/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1912586263/10000000000 : ℝ)*X 0 0+(651632269/1250000000 : ℝ)*X 0 1+(5440537633/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((132358199/250000000 : ℝ)*X 1 0+(-1801798527/10000000000 : ℝ)*X 1 1+(2720268859/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1323582113/2500000000 : ℝ)*X 2 0+(1360134327/2500000000 : ℝ)*X 2 1+(-1801798419/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4283584713/10000000000 : ℝ)*X 0 0+(2271304177/5000000000 : ℝ)*X 0 1+(4037665329/10000000000 : ℝ)*X 0 2+(4283584713/10000000000 : ℝ)*X 1 0+(2271304177/5000000000 : ℝ)*X 1 1+(4037665329/10000000000 : ℝ)*X 1 2+(4283584713/10000000000 : ℝ)*X 2 0+(2271304177/5000000000 : ℝ)*X 2 1+(4037665329/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (424525895939206676831694933/74000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (638095911/50000000000000 : ℝ)*(base19) + (123881707/10000000000000 : ℝ)*(base23) + (39458513/100000000000000 : ℝ)*(lower2) + (48691157/20000000000000 : ℝ)*(upper3) + (1650321/6250000000000 : ℝ)*(lower4) + (1577099819422773/50000000000000 : ℝ)*(major0) + (1577099819422773/50000000000000 : ℝ)*(major1) + (1577099819422773/50000000000000 : ℝ)*(major2) + (1087271918505141/25000000000000 : ℝ)*(sp0) + (1087276302435833/25000000000000 : ℝ)*(sp1) + (869821049423617/20000000000000 : ℝ)*(sp2) + (979641466368237/50000000000000 : ℝ)*(sp3) + (18811914591/100000000000000 : ℝ)*(sp4) + (1208473947/12500000000000 : ℝ)*(sp7) + (39185852010561/2000000000000 : ℝ)*(f.failure) + (2174553242967577/50000000000000 : ℝ)*(f.sum) + (6871379769977/592000000000000000000000000 : ℝ)*base65 + (555521559511226689/148000000000000000000000000000000 : ℝ)*base68 + (1027253558419226689/148000000000000000000000000000000 : ℝ)*base70 + (809716206192773311/148000000000000000000000000000000 : ℝ)*base71 + (570055258999/592000000000000000000000000 : ℝ)*base74 + (652579962471226689/148000000000000000000000000000000 : ℝ)*base76 + (967845001480773311/148000000000000000000000000000000 : ℝ)*base77 + (1219906372759226689/148000000000000000000000000000000 : ℝ)*base80 + (138060499227/118400000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (2313/6250000000000000000 : ℝ)*base89 + (2313/6250000000000000000 : ℝ)*base91 + (2313/6250000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (541319623123450030486320381/74000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (184546601/20000000000000 : ℝ)*(base19) + (776080781/50000000000000 : ℝ)*(base23) + (7405079/10000000000000 : ℝ)*(upper3) + (48457569/50000000000000 : ℝ)*(lower4) + (19940473/10000000000000 : ℝ)*(upper5) + (1594106487223261/50000000000000 : ℝ)*(major0) + (1594106487223261/50000000000000 : ℝ)*(major1) + (1594106487223261/50000000000000 : ℝ)*(major2) + (16791777703/100000000000000 : ℝ)*(sp1) + (10064049233/50000000000000 : ℝ)*(sp2) + (2198002528994247/50000000000000 : ℝ)*(sp4) + (549498417934723/12500000000000 : ℝ)*(sp5) + (2197991688864233/50000000000000 : ℝ)*(sp6) + (990210323533437/50000000000000 : ℝ)*(sp7) + (990210323533437/50000000000000 : ℝ)*(f.failure) + (2198002528994247/50000000000000 : ℝ)*(f.sum) + (406979288803/118400000000000000000000000 : ℝ)*base66 + (1062468651672684873/148000000000000000000000000000000 : ℝ)*base68 + (249036640744684873/148000000000000000000000000000000 : ℝ)*base70 + (592796800471315127/148000000000000000000000000000000 : ℝ)*base71 + (3141331944527/592000000000000000000000000 : ℝ)*base74 + (2492772695587315127/148000000000000000000000000000000 : ℝ)*base75 + (777238943488684873/148000000000000000000000000000000 : ℝ)*base78 + (971788662136684873/148000000000000000000000000000000 : ℝ)*base80 + (2148401322289/592000000000000000000000000 : ℝ)*base81 + (1/50000000000000 : ℝ)*base86 + (838021/156250000000000000000 : ℝ)*base89 + (838021/156250000000000000000 : ℝ)*base91 + (838021/156250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1482_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5030833/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8061/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5101/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5353/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3893/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1482_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1482_s4_0 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-239146177/1250000000 : ℝ)*x 0 + (1087555943/2000000000 : ℝ)*x 1 + (1043083689/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (239146177/1250000000 : ℝ)^4461 ≤ (5844309194029/50000000000000 : ℝ)^3437 := by
    have hnat : (239146177 : ℕ)^4461*50000000000000^3437 ≤ 5844309194029^3437*1250000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      239146177 1250000000 5844309194029 50000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1087555943/2000000000 : ℝ)^4461 ≤ (45351812401429/100000000000000 : ℝ)^3437 := by
    have hnat : (1087555943 : ℕ)^4461*100000000000000^3437 ≤ 45351812401429^3437*2000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087555943 2000000000 45351812401429 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043083689/2000000000 : ℝ)^4461 ≤ (42959569193197/100000000000000 : ℝ)^3437 := by
    have hnat : (1043083689 : ℕ)^4461*100000000000000^3437 ≤ 42959569193197^3437*2000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043083689 2000000000 42959569193197 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-239146177/1250000000 : ℝ), (1087555943/2000000000 : ℝ), (1043083689/2000000000 : ℝ)] ![(5844309194029/50000000000000 : ℝ), (45351812401429/100000000000000 : ℝ), (42959569193197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-239146177/1250000000 : ℝ)|^4461 ≤ (5844309194029/50000000000000 : ℝ)^3437
        have hw : |(-239146177/1250000000 : ℝ)|=(239146177/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1087555943/2000000000 : ℝ)|^4461 ≤ (45351812401429/100000000000000 : ℝ)^3437
        have hw : |(1087555943/2000000000 : ℝ)|=(1087555943/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043083689/2000000000 : ℝ)|^4461 ≤ (42959569193197/100000000000000 : ℝ)^3437
        have hw : |(1043083689/2000000000 : ℝ)|=(1043083689/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_s4_1 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676682819/5000000000 : ℝ)*x 0 + (-6334809/31250000 : ℝ)*x 1 + (1303854389/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676682819/5000000000 : ℝ)^4461 ≤ (444401554463/1000000000000 : ℝ)^3437 := by
    have hnat : (2676682819 : ℕ)^4461*1000000000000^3437 ≤ 444401554463^3437*5000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676682819 5000000000 444401554463 1000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6334809/31250000 : ℝ)^4461 ≤ (12600284853257/100000000000000 : ℝ)^3437 := by
    have hnat : (6334809 : ℕ)^4461*100000000000000^3437 ≤ 12600284853257^3437*31250000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6334809 31250000 12600284853257 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1303854389/2500000000 : ℝ)^4461 ≤ (21479779844393/50000000000000 : ℝ)^3437 := by
    have hnat : (1303854389 : ℕ)^4461*50000000000000^3437 ≤ 21479779844393^3437*2500000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303854389 2500000000 21479779844393 50000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676682819/5000000000 : ℝ), (-6334809/31250000 : ℝ), (1303854389/2500000000 : ℝ)] ![(444401554463/1000000000000 : ℝ), (12600284853257/100000000000000 : ℝ), (21479779844393/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676682819/5000000000 : ℝ)|^4461 ≤ (444401554463/1000000000000 : ℝ)^3437
        have hw : |(2676682819/5000000000 : ℝ)|=(2676682819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6334809/31250000 : ℝ)|^4461 ≤ (12600284853257/100000000000000 : ℝ)^3437
        have hw : |(-6334809/31250000 : ℝ)|=(6334809/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1303854389/2500000000 : ℝ)|^4461 ≤ (21479779844393/50000000000000 : ℝ)^3437
        have hw : |(1303854389/2500000000 : ℝ)|=(1303854389/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_s4_2 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (214134609/400000000 : ℝ)*x 0 + (1043083667/2000000000 : ℝ)*x 1 + (-1013569199/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214134609/400000000 : ℝ)^4461 ≤ (11110037749097/25000000000000 : ℝ)^3437 := by
    have hnat : (214134609 : ℕ)^4461*25000000000000^3437 ≤ 11110037749097^3437*400000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214134609 400000000 11110037749097 25000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043083667/2000000000 : ℝ)^4461 ≤ (42959568017173/100000000000000 : ℝ)^3437 := by
    have hnat : (1043083667 : ℕ)^4461*100000000000000^3437 ≤ 42959568017173^3437*2000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043083667 2000000000 42959568017173 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1013569199/5000000000 : ℝ)^4461 ≤ (12600280964627/100000000000000 : ℝ)^3437 := by
    have hnat : (1013569199 : ℕ)^4461*100000000000000^3437 ≤ 12600280964627^3437*5000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1013569199 5000000000 12600280964627 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214134609/400000000 : ℝ), (1043083667/2000000000 : ℝ), (-1013569199/5000000000 : ℝ)] ![(11110037749097/25000000000000 : ℝ), (42959568017173/100000000000000 : ℝ), (12600280964627/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214134609/400000000 : ℝ)|^4461 ≤ (11110037749097/25000000000000 : ℝ)^3437
        have hw : |(214134609/400000000 : ℝ)|=(214134609/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043083667/2000000000 : ℝ)|^4461 ≤ (42959568017173/100000000000000 : ℝ)^3437
        have hw : |(1043083667/2000000000 : ℝ)|=(1043083667/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1013569199/5000000000 : ℝ)|^4461 ≤ (12600280964627/100000000000000 : ℝ)^3437
        have hw : |(-1013569199/5000000000 : ℝ)|=(1013569199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_s4_3 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4283891679/10000000000 : ℝ)*x 0 + (4043289791/10000000000 : ℝ)*x 1 + (4536874073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4283891679/10000000000 : ℝ)^4461 ≤ (33277489620497/100000000000000 : ℝ)^3437 := by
    have hnat : (4283891679 : ℕ)^4461*100000000000000^3437 ≤ 33277489620497^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4283891679 10000000000 33277489620497 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4043289791/10000000000 : ℝ)^4461 ≤ (30872209977427/100000000000000 : ℝ)^3437 := by
    have hnat : (4043289791 : ℕ)^4461*100000000000000^3437 ≤ 30872209977427^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4043289791 10000000000 30872209977427 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4536874073/10000000000 : ℝ)^4461 ≤ (448128754931/1250000000000 : ℝ)^3437 := by
    have hnat : (4536874073 : ℕ)^4461*1250000000000^3437 ≤ 448128754931^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4536874073 10000000000 448128754931 1250000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4283891679/10000000000 : ℝ), (4043289791/10000000000 : ℝ), (4536874073/10000000000 : ℝ)] ![(33277489620497/100000000000000 : ℝ), (30872209977427/100000000000000 : ℝ), (448128754931/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4283891679/10000000000 : ℝ)|^4461 ≤ (33277489620497/100000000000000 : ℝ)^3437
        have hw : |(4283891679/10000000000 : ℝ)|=(4283891679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4043289791/10000000000 : ℝ)|^4461 ≤ (30872209977427/100000000000000 : ℝ)^3437
        have hw : |(4043289791/10000000000 : ℝ)|=(4043289791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4536874073/10000000000 : ℝ)|^4461 ≤ (448128754931/1250000000000 : ℝ)^3437
        have hw : |(4536874073/10000000000 : ℝ)|=(4536874073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_s4_4 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-119575023/625000000 : ℝ)*x 0 + (5216562003/10000000000 : ℝ)*x 1 + (5436627547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (119575023/625000000 : ℝ)^4461 ≤ (91319248687/781250000000 : ℝ)^3437 := by
    have hnat : (119575023 : ℕ)^4461*781250000000^3437 ≤ 91319248687^3437*625000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      119575023 625000000 91319248687 781250000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216562003/10000000000 : ℝ)^4461 ≤ (1074294887881/2500000000000 : ℝ)^3437 := by
    have hnat : (5216562003 : ℕ)^4461*2500000000000^3437 ≤ 1074294887881^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216562003 10000000000 1074294887881 2500000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5436627547/10000000000 : ℝ)^4461 ≤ (2833708789939/6250000000000 : ℝ)^3437 := by
    have hnat : (5436627547 : ℕ)^4461*6250000000000^3437 ≤ 2833708789939^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436627547 10000000000 2833708789939 6250000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-119575023/625000000 : ℝ), (5216562003/10000000000 : ℝ), (5436627547/10000000000 : ℝ)] ![(91319248687/781250000000 : ℝ), (1074294887881/2500000000000 : ℝ), (2833708789939/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-119575023/625000000 : ℝ)|^4461 ≤ (91319248687/781250000000 : ℝ)^3437
        have hw : |(-119575023/625000000 : ℝ)|=(119575023/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216562003/10000000000 : ℝ)|^4461 ≤ (1074294887881/2500000000000 : ℝ)^3437
        have hw : |(5216562003/10000000000 : ℝ)|=(5216562003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5436627547/10000000000 : ℝ)|^4461 ≤ (2833708789939/6250000000000 : ℝ)^3437
        have hw : |(5436627547/10000000000 : ℝ)|=(5436627547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_s4_5 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295272377/10000000000 : ℝ)*x 0 + (-902964631/5000000000 : ℝ)*x 1 + (5436627551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295272377/10000000000 : ℝ)^4461 ≤ (43815237944141/100000000000000 : ℝ)^3437 := by
    have hnat : (5295272377 : ℕ)^4461*100000000000000^3437 ≤ 43815237944141^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295272377 10000000000 43815237944141 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (902964631/5000000000 : ℝ)^4461 ≤ (10845421363123/100000000000000 : ℝ)^3437 := by
    have hnat : (902964631 : ℕ)^4461*100000000000000^3437 ≤ 10845421363123^3437*5000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      902964631 5000000000 10845421363123 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5436627551/10000000000 : ℝ)^4461 ≤ (45339340682321/100000000000000 : ℝ)^3437 := by
    have hnat : (5436627551 : ℕ)^4461*100000000000000^3437 ≤ 45339340682321^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436627551 10000000000 45339340682321 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295272377/10000000000 : ℝ), (-902964631/5000000000 : ℝ), (5436627551/10000000000 : ℝ)] ![(43815237944141/100000000000000 : ℝ), (10845421363123/100000000000000 : ℝ), (45339340682321/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295272377/10000000000 : ℝ)|^4461 ≤ (43815237944141/100000000000000 : ℝ)^3437
        have hw : |(5295272377/10000000000 : ℝ)|=(5295272377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-902964631/5000000000 : ℝ)|^4461 ≤ (10845421363123/100000000000000 : ℝ)^3437
        have hw : |(-902964631/5000000000 : ℝ)|=(902964631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5436627551/10000000000 : ℝ)|^4461 ≤ (45339340682321/100000000000000 : ℝ)^3437
        have hw : |(5436627551/10000000000 : ℝ)|=(5436627551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_s4_6 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295272401/10000000000 : ℝ)*x 0 + (5436627537/10000000000 : ℝ)*x 1 + (-56435289/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295272401/10000000000 : ℝ)^4461 ≤ (10953809550473/25000000000000 : ℝ)^3437 := by
    have hnat : (5295272401 : ℕ)^4461*25000000000000^3437 ≤ 10953809550473^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295272401 10000000000 10953809550473 25000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5436627537/10000000000 : ℝ)^4461 ≤ (45339340530781/100000000000000 : ℝ)^3437 := by
    have hnat : (5436627537 : ℕ)^4461*100000000000000^3437 ≤ 45339340530781^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436627537 10000000000 45339340530781 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (56435289/312500000 : ℝ)^4461 ≤ (5422710626999/50000000000000 : ℝ)^3437 := by
    have hnat : (56435289 : ℕ)^4461*50000000000000^3437 ≤ 5422710626999^3437*312500000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56435289 312500000 5422710626999 50000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295272401/10000000000 : ℝ), (5436627537/10000000000 : ℝ), (-56435289/312500000 : ℝ)] ![(10953809550473/25000000000000 : ℝ), (45339340530781/100000000000000 : ℝ), (5422710626999/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295272401/10000000000 : ℝ)|^4461 ≤ (10953809550473/25000000000000 : ℝ)^3437
        have hw : |(5295272401/10000000000 : ℝ)|=(5295272401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5436627537/10000000000 : ℝ)|^4461 ≤ (45339340530781/100000000000000 : ℝ)^3437
        have hw : |(5436627537/10000000000 : ℝ)|=(5436627537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-56435289/312500000 : ℝ)|^4461 ≤ (5422710626999/50000000000000 : ℝ)^3437
        have hw : |(-56435289/312500000 : ℝ)|=(56435289/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_s4_7 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4283960759/10000000000 : ℝ)*x 0 + (4534334287/10000000000 : ℝ)*x 1 + (252865469/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4283960759/10000000000 : ℝ)^4461 ≤ (6655637223143/20000000000000 : ℝ)^3437 := by
    have hnat : (4283960759 : ℕ)^4461*20000000000000^3437 ≤ 6655637223143^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4283960759 10000000000 6655637223143 20000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4534334287/10000000000 : ℝ)^4461 ≤ (35824253876887/100000000000000 : ℝ)^3437 := by
    have hnat : (4534334287 : ℕ)^4461*100000000000000^3437 ≤ 35824253876887^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4534334287 10000000000 35824253876887 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (252865469/625000000 : ℝ)^4461 ≤ (1235902399811/4000000000000 : ℝ)^3437 := by
    have hnat : (252865469 : ℕ)^4461*4000000000000^3437 ≤ 1235902399811^3437*625000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      252865469 625000000 1235902399811 4000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4283960759/10000000000 : ℝ), (4534334287/10000000000 : ℝ), (252865469/625000000 : ℝ)] ![(6655637223143/20000000000000 : ℝ), (35824253876887/100000000000000 : ℝ), (1235902399811/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4283960759/10000000000 : ℝ)|^4461 ≤ (6655637223143/20000000000000 : ℝ)^3437
        have hw : |(4283960759/10000000000 : ℝ)|=(4283960759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4534334287/10000000000 : ℝ)|^4461 ≤ (35824253876887/100000000000000 : ℝ)^3437
        have hw : |(4534334287/10000000000 : ℝ)|=(4534334287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(252865469/625000000 : ℝ)|^4461 ≤ (1235902399811/4000000000000 : ℝ)^3437
        have hw : |(252865469/625000000 : ℝ)|=(252865469/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1482_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5030833/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3893/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5353/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10783/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15489/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3893/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5353/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3893/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5353/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3893/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5353/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3893/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5353/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3893/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5353/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3893/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5353/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5353/50000 : ℝ) ^ (4459/1024 : ℝ) ≤ (5950033261064953/100000000000000000000 : ℝ) := by
    have hpowers : (5353/50000 : ℝ)^4459 ≤ (5950033261064953/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5353 : ℕ)^4459*100000000000000000000^1024 ≤ 5950033261064953^1024*50000^4459 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5353 50000 5950033261064953 100000000000000000000 4459 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5353/50000 : ℝ)) (X := (5950033261064953/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4459 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3893/25000 : ℝ) ^ (4459/1024 : ℝ) ≤ (30413750441334071/100000000000000000000 : ℝ) := by
    have hpowers : (3893/25000 : ℝ)^4459 ≤ (30413750441334071/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3893 : ℕ)^4459*100000000000000000000^1024 ≤ 30413750441334071^1024*25000^4459 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3893 25000 30413750441334071 100000000000000000000 4459 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3893/25000 : ℝ)) (X := (30413750441334071/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4459 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005950033261064953/50000000000000000000 : ℝ) ≤ (5000136635003511/5000000000000000 : ℝ) ^ (4459/1024 : ℝ) := by
    have hpowers : (50005950033261064953/50000000000000000000 : ℝ)^1024 ≤ (5000136635003511/5000000000000000 : ℝ)^4459 := by
      have hnat : (50005950033261064953 : ℕ)^1024*5000000000000000^4459 ≤ 5000136635003511^4459*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005950033261064953 50000000000000000000 5000136635003511 5000000000000000 1024 4459 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000136635003511/5000000000000000 : ℝ)) (X := (50005950033261064953/50000000000000000000 : ℝ)) (by norm_num) 4459 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6252272736481399939/6250000000000000000 : ℝ) ≤ (10000834969726693/10000000000000000 : ℝ) ^ (4459/1024 : ℝ) := by
    have hpowers : (6252272736481399939/6250000000000000000 : ℝ)^1024 ≤ (10000834969726693/10000000000000000 : ℝ)^4459 := by
      have hnat : (6252272736481399939 : ℕ)^1024*10000000000000000^4459 ≤ 10000834969726693^4459*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252272736481399939 6250000000000000000 10000834969726693 10000000000000000 1024 4459 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000834969726693/10000000000000000 : ℝ)) (X := (6252272736481399939/6250000000000000000 : ℝ)) (by norm_num) 4459 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50030413750441334071/50000000000000000000 : ℝ) ≤ (2500349167361591/2500000000000000 : ℝ) ^ (4459/1024 : ℝ) := by
    have hpowers : (50030413750441334071/50000000000000000000 : ℝ)^1024 ≤ (2500349167361591/2500000000000000 : ℝ)^4459 := by
      have hnat : (50030413750441334071 : ℕ)^1024*2500000000000000^4459 ≤ 2500349167361591^4459*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030413750441334071 50000000000000000000 2500349167361591 2500000000000000 1024 4459 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500349167361591/2500000000000000 : ℝ)) (X := (50030413750441334071/50000000000000000000 : ℝ)) (by norm_num) 4459 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5950033261064953/100000000000000000000 : ℝ) ≤ ((60811628271820717/60825000000000000 : ℝ)+2*(561699719671/486600000000000 : ℝ)*(5353/50000 : ℝ))^(4459/1024 : ℝ) := by
    rw [show (60811628271820717/60825000000000000 : ℝ)+2*(561699719671/486600000000000 : ℝ)*(5353/50000 : ℝ)=(5000136635003511/5000000000000000 : ℝ) by norm_num, show 1+2*(5950033261064953/100000000000000000000 : ℝ)=(50005950033261064953/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30413750441334071/100000000000000000000 : ℝ)+(5950033261064953/100000000000000000000 : ℝ) ≤ ((60811628271820717/60825000000000000 : ℝ)+(561699719671/486600000000000 : ℝ)*((3893/25000 : ℝ)+(5353/50000 : ℝ)))^(4459/1024 : ℝ) := by
    rw [show (60811628271820717/60825000000000000 : ℝ)+(561699719671/486600000000000 : ℝ)*((3893/25000 : ℝ)+(5353/50000 : ℝ))=(10000834969726693/10000000000000000 : ℝ) by norm_num, show 1+(30413750441334071/100000000000000000000 : ℝ)+(5950033261064953/100000000000000000000 : ℝ)=(6252272736481399939/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30413750441334071/100000000000000000000 : ℝ) ≤ ((60811628271820717/60825000000000000 : ℝ)+2*(561699719671/486600000000000 : ℝ)*(3893/25000 : ℝ))^(4459/1024 : ℝ) := by
    rw [show (60811628271820717/60825000000000000 : ℝ)+2*(561699719671/486600000000000 : ℝ)*(3893/25000 : ℝ)=(2500349167361591/2500000000000000 : ℝ) by norm_num, show 1+2*(30413750441334071/100000000000000000000 : ℝ)=(50030413750441334071/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (60811628271820717/60825000000000000 : ℝ)*(X 1 0+X 2 0)+(561699719671/486600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4459/1024 : ℝ)) (lo := (5353/50000 : ℝ)) (hi := (3893/25000 : ℝ)) (c := (60811628271820717/60825000000000000 : ℝ)) (alpha := (561699719671/486600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (60811628271820717/60825000000000000 : ℝ)*(X 0 1+X 2 1)+(561699719671/486600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4459/1024 : ℝ)) (lo := (5353/50000 : ℝ)) (hi := (3893/25000 : ℝ)) (c := (60811628271820717/60825000000000000 : ℝ)) (alpha := (561699719671/486600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (60811628271820717/60825000000000000 : ℝ)*(X 0 2+X 1 2)+(561699719671/486600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4459/1024 : ℝ)) (lo := (5353/50000 : ℝ)) (hi := (3893/25000 : ℝ)) (c := (60811628271820717/60825000000000000 : ℝ)) (alpha := (561699719671/486600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-239146177/1250000000 : ℝ)*X 0 0+(1087555943/2000000000 : ℝ)*X 0 1+(1043083689/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676682819/5000000000 : ℝ)*X 1 0+(-6334809/31250000 : ℝ)*X 1 1+(1303854389/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((214134609/400000000 : ℝ)*X 2 0+(1043083667/2000000000 : ℝ)*X 2 1+(-1013569199/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4283891679/10000000000 : ℝ)*X 0 0+(4043289791/10000000000 : ℝ)*X 0 1+(4536874073/10000000000 : ℝ)*X 0 2+(4283891679/10000000000 : ℝ)*X 1 0+(4043289791/10000000000 : ℝ)*X 1 1+(4536874073/10000000000 : ℝ)*X 1 2+(4283891679/10000000000 : ℝ)*X 2 0+(4043289791/10000000000 : ℝ)*X 2 1+(4536874073/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-119575023/625000000 : ℝ)*X 0 0+(5216562003/10000000000 : ℝ)*X 0 1+(5436627547/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5295272377/10000000000 : ℝ)*X 1 0+(-902964631/5000000000 : ℝ)*X 1 1+(5436627551/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5295272401/10000000000 : ℝ)*X 2 0+(5436627537/10000000000 : ℝ)*X 2 1+(-56435289/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4283960759/10000000000 : ℝ)*X 0 0+(4534334287/10000000000 : ℝ)*X 0 1+(252865469/625000000 : ℝ)*X 0 2+(4283960759/10000000000 : ℝ)*X 1 0+(4534334287/10000000000 : ℝ)*X 1 1+(252865469/625000000 : ℝ)*X 1 2+(4283960759/10000000000 : ℝ)*X 2 0+(4534334287/10000000000 : ℝ)*X 2 1+(252865469/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (385161422479757094122687/101375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (690639177/100000000000000 : ℝ)*(base19) + (304449111/100000000000000 : ℝ)*(base23) + (2626817/2500000000000 : ℝ)*(lower3) + (24812263/50000000000000 : ℝ)*(upper4) + (5096253888851/156250000000 : ℝ)*(major0) + (5096253888851/156250000000 : ℝ)*(major1) + (5096253888851/156250000000 : ℝ)*(major2) + (1124297583939029/25000000000000 : ℝ)*(sp0) + (140537226863193/3125000000000 : ℝ)*(sp1) + (2248598285935589/50000000000000 : ℝ)*(sp2) + (405200589746527/20000000000000 : ℝ)*(sp3) + (6540564173/100000000000000 : ℝ)*(sp4) + (4926058937/100000000000000 : ℝ)*(sp5) + (502603059/10000000000000 : ℝ)*(sp7) + (81040318990529/4000000000000 : ℝ)*(f.failure) + (4497196876320289/100000000000000 : ℝ)*(f.sum) + (51590665529/2433000000000000000000000000 : ℝ)*base65 + (264056839144349/50687500000000000000000000000 : ℝ)*base67 + (282979552806099/50687500000000000000000000000 : ℝ)*base69 + (92240436282681/12671875000000000000000000000 : ℝ)*base71 + (2974467463991/2433000000000000000000000000 : ℝ)*base73 + (179303721844651/50687500000000000000000000000 : ℝ)*base76 + (22853282881073/101375000000000000000000000000 : ℝ)*base77 + (198982610671427/101375000000000000000000000000 : ℝ)*base80 + (2862726843799/2433000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (19343/12500000000000000000 : ℝ)*base90 + (19343/12500000000000000000 : ℝ)*base92 + (19343/12500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (35770477952181299662847/4055000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1467249947/100000000000000 : ℝ)*(base19) + (202631961/12500000000000 : ℝ)*(base23) + (46157729/25000000000000 : ℝ)*(upper3) + (14587147/25000000000000 : ℝ)*(lower4) + (183301179/100000000000000 : ℝ)*(upper5) + (1647809561801293/50000000000000 : ℝ)*(major0) + (1647809561801293/50000000000000 : ℝ)*(major1) + (1647809561801293/50000000000000 : ℝ)*(major2) + (687620831/3125000000000 : ℝ)*(sp1) + (24102381763/100000000000000 : ℝ)*(sp2) + (4544099882535659/100000000000000 : ℝ)*(sp4) + (4544076411419119/100000000000000 : ℝ)*(sp5) + (142002317471819/3125000000000 : ℝ)*(sp6) + (2047138070625299/100000000000000 : ℝ)*(sp7) + (2047138070625299/100000000000000 : ℝ)*(f.failure) + (4544099882535659/100000000000000 : ℝ)*(f.sum) + (7108856740409/6082500000000000000000000000 : ℝ)*base65 + (600882398772913/253437500000000000000000000000 : ℝ)*base67 + (411287974190201/506875000000000000000000000000 : ℝ)*base69 + (232843320370053/63359375000000000000000000000 : ℝ)*base72 + (2296785315443/3041250000000000000000000000 : ℝ)*base74 + (800041712235201/506875000000000000000000000000 : ℝ)*base75 + (1559270406671981/126718750000000000000000000000 : ℝ)*base78 + (1575642228028337/253437500000000000000000000000 : ℝ)*base80 + (68013034306333/12165000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (3594067/312500000000000000000 : ℝ)*base89 + (3594067/312500000000000000000 : ℝ)*base91 + (3594067/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1482_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5030833/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3893/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5353/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10783/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1482_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1482_s5_0 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1913252003/10000000000 : ℝ)*x 0 + (1087447399/2000000000 : ℝ)*x 1 + (5215906687/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1913252003/10000000000 : ℝ)^4461 ≤ (467570931639/4000000000000 : ℝ)^3437 := by
    have hnat : (1913252003 : ℕ)^4461*4000000000000^3437 ≤ 467570931639^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1913252003 10000000000 467570931639 4000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1087447399/2000000000 : ℝ)^4461 ≤ (45345937574223/100000000000000 : ℝ)^3437 := by
    have hnat : (1087447399 : ℕ)^4461*100000000000000^3437 ≤ 45345937574223^3437*2000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087447399 2000000000 45345937574223 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215906687/10000000000 : ℝ)^4461 ≤ (8592957824551/20000000000000 : ℝ)^3437 := by
    have hnat : (5215906687 : ℕ)^4461*20000000000000^3437 ≤ 8592957824551^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215906687 10000000000 8592957824551 20000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1913252003/10000000000 : ℝ), (1087447399/2000000000 : ℝ), (5215906687/10000000000 : ℝ)] ![(467570931639/4000000000000 : ℝ), (45345937574223/100000000000000 : ℝ), (8592957824551/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1913252003/10000000000 : ℝ)|^4461 ≤ (467570931639/4000000000000 : ℝ)^3437
        have hw : |(-1913252003/10000000000 : ℝ)|=(1913252003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1087447399/2000000000 : ℝ)|^4461 ≤ (45345937574223/100000000000000 : ℝ)^3437
        have hw : |(1087447399/2000000000 : ℝ)|=(1087447399/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215906687/10000000000 : ℝ)|^4461 ≤ (8592957824551/20000000000000 : ℝ)^3437
        have hw : |(5215906687/10000000000 : ℝ)|=(5215906687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_s5_1 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338306051/2500000000 : ℝ)*x 0 + (-2026679571/10000000000 : ℝ)*x 1 + (5215906677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338306051/2500000000 : ℝ)^4461 ≤ (44438631556829/100000000000000 : ℝ)^3437 := by
    have hnat : (1338306051 : ℕ)^4461*100000000000000^3437 ≤ 44438631556829^3437*2500000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338306051 2500000000 44438631556829 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2026679571/10000000000 : ℝ)^4461 ≤ (6298289706367/50000000000000 : ℝ)^3437 := by
    have hnat : (2026679571 : ℕ)^4461*50000000000000^3437 ≤ 6298289706367^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2026679571 10000000000 6298289706367 50000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215906677/10000000000 : ℝ)^4461 ≤ (42964789015841/100000000000000 : ℝ)^3437 := by
    have hnat : (5215906677 : ℕ)^4461*100000000000000^3437 ≤ 42964789015841^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215906677 10000000000 42964789015841 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338306051/2500000000 : ℝ), (-2026679571/10000000000 : ℝ), (5215906677/10000000000 : ℝ)] ![(44438631556829/100000000000000 : ℝ), (6298289706367/50000000000000 : ℝ), (42964789015841/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338306051/2500000000 : ℝ)|^4461 ≤ (44438631556829/100000000000000 : ℝ)^3437
        have hw : |(1338306051/2500000000 : ℝ)|=(1338306051/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2026679571/10000000000 : ℝ)|^4461 ≤ (6298289706367/50000000000000 : ℝ)^3437
        have hw : |(-2026679571/10000000000 : ℝ)|=(2026679571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215906677/10000000000 : ℝ)|^4461 ≤ (42964789015841/100000000000000 : ℝ)^3437
        have hw : |(5215906677/10000000000 : ℝ)|=(5215906677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_s5_2 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353224207/10000000000 : ℝ)*x 0 + (5215906679/10000000000 : ℝ)*x 1 + (-506669891/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353224207/10000000000 : ℝ)^4461 ≤ (44438631589153/100000000000000 : ℝ)^3437 := by
    have hnat : (5353224207 : ℕ)^4461*100000000000000^3437 ≤ 44438631589153^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353224207 10000000000 44438631589153 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5215906679/10000000000 : ℝ)^4461 ≤ (42964789037223/100000000000000 : ℝ)^3437 := by
    have hnat : (5215906679 : ℕ)^4461*100000000000000^3437 ≤ 42964789037223^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215906679 10000000000 42964789037223 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (506669891/2500000000 : ℝ)^4461 ≤ (1574572419533/12500000000000 : ℝ)^3437 := by
    have hnat : (506669891 : ℕ)^4461*12500000000000^3437 ≤ 1574572419533^3437*2500000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      506669891 2500000000 1574572419533 12500000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353224207/10000000000 : ℝ), (5215906679/10000000000 : ℝ), (-506669891/2500000000 : ℝ)] ![(44438631589153/100000000000000 : ℝ), (42964789037223/100000000000000 : ℝ), (1574572419533/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353224207/10000000000 : ℝ)|^4461 ≤ (44438631589153/100000000000000 : ℝ)^3437
        have hw : |(5353224207/10000000000 : ℝ)|=(5353224207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5215906679/10000000000 : ℝ)|^4461 ≤ (42964789037223/100000000000000 : ℝ)^3437
        have hw : |(5215906679/10000000000 : ℝ)|=(5215906679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-506669891/2500000000 : ℝ)|^4461 ≤ (1574572419533/12500000000000 : ℝ)^3437
        have hw : |(-506669891/2500000000 : ℝ)|=(506669891/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_s5_3 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4283943719/10000000000 : ℝ)*x 0 + (4044428387/10000000000 : ℝ)*x 1 + (2267861319/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4283943719/10000000000 : ℝ)^4461 ≤ (33278014310561/100000000000000 : ℝ)^3437 := by
    have hnat : (4283943719 : ℕ)^4461*100000000000000^3437 ≤ 33278014310561^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4283943719 10000000000 33278014310561 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4044428387/10000000000 : ℝ)^4461 ≤ (30883494245941/100000000000000 : ℝ)^3437 := by
    have hnat : (4044428387 : ℕ)^4461*100000000000000^3437 ≤ 30883494245941^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4044428387 10000000000 30883494245941 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2267861319/5000000000 : ℝ)^4461 ≤ (17919245715617/50000000000000 : ℝ)^3437 := by
    have hnat : (2267861319 : ℕ)^4461*50000000000000^3437 ≤ 17919245715617^3437*5000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2267861319 5000000000 17919245715617 50000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4283943719/10000000000 : ℝ), (4044428387/10000000000 : ℝ), (2267861319/5000000000 : ℝ)] ![(33278014310561/100000000000000 : ℝ), (30883494245941/100000000000000 : ℝ), (17919245715617/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4283943719/10000000000 : ℝ)|^4461 ≤ (33278014310561/100000000000000 : ℝ)^3437
        have hw : |(4283943719/10000000000 : ℝ)|=(4283943719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4044428387/10000000000 : ℝ)|^4461 ≤ (30883494245941/100000000000000 : ℝ)^3437
        have hw : |(4044428387/10000000000 : ℝ)|=(4044428387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2267861319/5000000000 : ℝ)|^4461 ≤ (17919245715617/50000000000000 : ℝ)^3437
        have hw : |(2267861319/5000000000 : ℝ)|=(2267861319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_s5_4 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1913282333/10000000000 : ℝ)*x 0 + (5217040047/10000000000 : ℝ)*x 1 + (543609529/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1913282333/10000000000 : ℝ)^4461 ≤ (2337902761117/20000000000000 : ℝ)^3437 := by
    have hnat : (1913282333 : ℕ)^4461*20000000000000^3437 ≤ 2337902761117^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1913282333 10000000000 2337902761117 20000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5217040047/10000000000 : ℝ)^4461 ≤ (42976906747521/100000000000000 : ℝ)^3437 := by
    have hnat : (5217040047 : ℕ)^4461*100000000000000^3437 ≤ 42976906747521^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217040047 10000000000 42976906747521 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (543609529/1000000000 : ℝ)^4461 ≤ (11333394858411/25000000000000 : ℝ)^3437 := by
    have hnat : (543609529 : ℕ)^4461*25000000000000^3437 ≤ 11333394858411^3437*1000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543609529 1000000000 11333394858411 25000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1913282333/10000000000 : ℝ), (5217040047/10000000000 : ℝ), (543609529/1000000000 : ℝ)] ![(2337902761117/20000000000000 : ℝ), (42976906747521/100000000000000 : ℝ), (11333394858411/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1913282333/10000000000 : ℝ)|^4461 ≤ (2337902761117/20000000000000 : ℝ)^3437
        have hw : |(-1913282333/10000000000 : ℝ)|=(1913282333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5217040047/10000000000 : ℝ)|^4461 ≤ (42976906747521/100000000000000 : ℝ)^3437
        have hw : |(5217040047/10000000000 : ℝ)|=(5217040047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(543609529/1000000000 : ℝ)|^4461 ≤ (11333394858411/25000000000000 : ℝ)^3437
        have hw : |(543609529/1000000000 : ℝ)|=(543609529/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_s5_5 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295401137/10000000000 : ℝ)*x 0 + (-225811369/1250000000 : ℝ)*x 1 + (543609529/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295401137/10000000000 : ℝ)^4461 ≤ (43816620784679/100000000000000 : ℝ)^3437 := by
    have hnat : (5295401137 : ℕ)^4461*100000000000000^3437 ≤ 43816620784679^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295401137 10000000000 43816620784679 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (225811369/1250000000 : ℝ)^4461 ≤ (10849799760731/100000000000000 : ℝ)^3437 := by
    have hnat : (225811369 : ℕ)^4461*100000000000000^3437 ≤ 10849799760731^3437*1250000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225811369 1250000000 10849799760731 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (543609529/1000000000 : ℝ)^4461 ≤ (11333394858411/25000000000000 : ℝ)^3437 := by
    have hnat : (543609529 : ℕ)^4461*25000000000000^3437 ≤ 11333394858411^3437*1000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543609529 1000000000 11333394858411 25000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295401137/10000000000 : ℝ), (-225811369/1250000000 : ℝ), (543609529/1000000000 : ℝ)] ![(43816620784679/100000000000000 : ℝ), (10849799760731/100000000000000 : ℝ), (11333394858411/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295401137/10000000000 : ℝ)|^4461 ≤ (43816620784679/100000000000000 : ℝ)^3437
        have hw : |(5295401137/10000000000 : ℝ)|=(5295401137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-225811369/1250000000 : ℝ)|^4461 ≤ (10849799760731/100000000000000 : ℝ)^3437
        have hw : |(-225811369/1250000000 : ℝ)|=(225811369/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(543609529/1000000000 : ℝ)|^4461 ≤ (11333394858411/25000000000000 : ℝ)^3437
        have hw : |(543609529/1000000000 : ℝ)|=(543609529/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_s5_6 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295401121/10000000000 : ℝ)*x 0 + (5436095297/10000000000 : ℝ)*x 1 + (-451622741/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295401121/10000000000 : ℝ)^4461 ≤ (10954155153211/25000000000000 : ℝ)^3437 := by
    have hnat : (5295401121 : ℕ)^4461*25000000000000^3437 ≤ 10954155153211^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295401121 10000000000 10954155153211 25000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5436095297/10000000000 : ℝ)^4461 ≤ (11333394877353/25000000000000 : ℝ)^3437 := by
    have hnat : (5436095297 : ℕ)^4461*25000000000000^3437 ≤ 11333394877353^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436095297 10000000000 11333394877353 25000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (451622741/2500000000 : ℝ)^4461 ≤ (2712449963569/25000000000000 : ℝ)^3437 := by
    have hnat : (451622741 : ℕ)^4461*25000000000000^3437 ≤ 2712449963569^3437*2500000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451622741 2500000000 2712449963569 25000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295401121/10000000000 : ℝ), (5436095297/10000000000 : ℝ), (-451622741/2500000000 : ℝ)] ![(10954155153211/25000000000000 : ℝ), (11333394877353/25000000000000 : ℝ), (2712449963569/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295401121/10000000000 : ℝ)|^4461 ≤ (10954155153211/25000000000000 : ℝ)^3437
        have hw : |(5295401121/10000000000 : ℝ)|=(5295401121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5436095297/10000000000 : ℝ)|^4461 ≤ (11333394877353/25000000000000 : ℝ)^3437
        have hw : |(5436095297/10000000000 : ℝ)|=(5436095297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-451622741/2500000000 : ℝ)|^4461 ≤ (2712449963569/25000000000000 : ℝ)^3437
        have hw : |(-451622741/2500000000 : ℝ)|=(451622741/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_s5_7 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (535501377/1250000000 : ℝ)*x 0 + (4533206859/10000000000 : ℝ)*x 1 + (1011740667/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535501377/1250000000 : ℝ)^4461 ≤ (8319673207799/25000000000000 : ℝ)^3437 := by
    have hnat : (535501377 : ℕ)^4461*25000000000000^3437 ≤ 8319673207799^3437*1250000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535501377 1250000000 8319673207799 25000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4533206859/10000000000 : ℝ)^4461 ≤ (17906346523117/50000000000000 : ℝ)^3437 := by
    have hnat : (4533206859 : ℕ)^4461*50000000000000^3437 ≤ 17906346523117^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4533206859 10000000000 17906346523117 50000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1011740667/2500000000 : ℝ)^4461 ≤ (30908614109237/100000000000000 : ℝ)^3437 := by
    have hnat : (1011740667 : ℕ)^4461*100000000000000^3437 ≤ 30908614109237^3437*2500000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1011740667 2500000000 30908614109237 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535501377/1250000000 : ℝ), (4533206859/10000000000 : ℝ), (1011740667/2500000000 : ℝ)] ![(8319673207799/25000000000000 : ℝ), (17906346523117/50000000000000 : ℝ), (30908614109237/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535501377/1250000000 : ℝ)|^4461 ≤ (8319673207799/25000000000000 : ℝ)^3437
        have hw : |(535501377/1250000000 : ℝ)|=(535501377/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4533206859/10000000000 : ℝ)|^4461 ≤ (17906346523117/50000000000000 : ℝ)^3437
        have hw : |(4533206859/10000000000 : ℝ)|=(4533206859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1011740667/2500000000 : ℝ)|^4461 ≤ (30908614109237/100000000000000 : ℝ)^3437
        have hw : |(1011740667/2500000000 : ℝ)|=(1011740667/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1482_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5030833/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10783/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10793/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7739/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15489/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10783/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15489/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10783/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15489/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10783/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15489/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10783/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15489/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10783/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15489/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10783/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10783/100000 : ℝ) ^ (4459/1024 : ℝ) ≤ (6138640037329513/100000000000000000000 : ℝ) := by
    have hpowers : (10783/100000 : ℝ)^4459 ≤ (6138640037329513/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10783 : ℕ)^4459*100000000000000000000^1024 ≤ 6138640037329513^1024*100000^4459 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10783 100000 6138640037329513 100000000000000000000 4459 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10783/100000 : ℝ)) (X := (6138640037329513/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4459 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15489/100000 : ℝ) ^ (4459/1024 : ℝ) ≤ (14857068970538379/50000000000000000000 : ℝ) := by
    have hpowers : (15489/100000 : ℝ)^4459 ≤ (14857068970538379/50000000000000000000 : ℝ)^1024 := by
      have hnat : (15489 : ℕ)^4459*50000000000000000000^1024 ≤ 14857068970538379^1024*100000^4459 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15489 100000 14857068970538379 50000000000000000000 4459 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15489/100000 : ℝ)) (X := (14857068970538379/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4459 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006138640037329513/50000000000000000000 : ℝ) ≤ (5000140965915267/5000000000000000 : ℝ) ^ (4459/1024 : ℝ) := by
    have hpowers : (50006138640037329513/50000000000000000000 : ℝ)^1024 ≤ (5000140965915267/5000000000000000 : ℝ)^4459 := by
      have hnat : (50006138640037329513 : ℕ)^1024*5000000000000000^4459 ≤ 5000140965915267^4459*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006138640037329513 50000000000000000000 5000140965915267 5000000000000000 1024 4459 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000140965915267/5000000000000000 : ℝ)) (X := (50006138640037329513/50000000000000000000 : ℝ)) (by norm_num) 4459 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100035852777978406271/100000000000000000000 : ℝ) ≤ (10000823237850607/10000000000000000 : ℝ) ^ (4459/1024 : ℝ) := by
    have hpowers : (100035852777978406271/100000000000000000000 : ℝ)^1024 ≤ (10000823237850607/10000000000000000 : ℝ)^4459 := by
      have hnat : (100035852777978406271 : ℕ)^1024*10000000000000000^4459 ≤ 10000823237850607^4459*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100035852777978406271 100000000000000000000 10000823237850607 10000000000000000 1024 4459 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000823237850607/10000000000000000 : ℝ)) (X := (100035852777978406271/100000000000000000000 : ℝ)) (by norm_num) 4459 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25014857068970538379/25000000000000000000 : ℝ) ≤ (250034113596767/250000000000000 : ℝ) ^ (4459/1024 : ℝ) := by
    have hpowers : (25014857068970538379/25000000000000000000 : ℝ)^1024 ≤ (250034113596767/250000000000000 : ℝ)^4459 := by
      have hnat : (25014857068970538379 : ℕ)^1024*250000000000000^4459 ≤ 250034113596767^4459*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014857068970538379 25000000000000000000 250034113596767 250000000000000 1024 4459 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250034113596767/250000000000000 : ℝ)) (X := (25014857068970538379/25000000000000000000 : ℝ)) (by norm_num) 4459 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6138640037329513/100000000000000000000 : ℝ) ≤ ((1809602037137138411/1810000000000000000 : ℝ)+2*(41638924621/36200000000000 : ℝ)*(10783/100000 : ℝ))^(4459/1024 : ℝ) := by
    rw [show (1809602037137138411/1810000000000000000 : ℝ)+2*(41638924621/36200000000000 : ℝ)*(10783/100000 : ℝ)=(5000140965915267/5000000000000000 : ℝ) by norm_num, show 1+2*(6138640037329513/100000000000000000000 : ℝ)=(50006138640037329513/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14857068970538379/50000000000000000000 : ℝ)+(6138640037329513/100000000000000000000 : ℝ) ≤ ((1809602037137138411/1810000000000000000 : ℝ)+(41638924621/36200000000000 : ℝ)*((15489/100000 : ℝ)+(10783/100000 : ℝ)))^(4459/1024 : ℝ) := by
    rw [show (1809602037137138411/1810000000000000000 : ℝ)+(41638924621/36200000000000 : ℝ)*((15489/100000 : ℝ)+(10783/100000 : ℝ))=(10000823237850607/10000000000000000 : ℝ) by norm_num, show 1+(14857068970538379/50000000000000000000 : ℝ)+(6138640037329513/100000000000000000000 : ℝ)=(100035852777978406271/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14857068970538379/50000000000000000000 : ℝ) ≤ ((1809602037137138411/1810000000000000000 : ℝ)+2*(41638924621/36200000000000 : ℝ)*(15489/100000 : ℝ))^(4459/1024 : ℝ) := by
    rw [show (1809602037137138411/1810000000000000000 : ℝ)+2*(41638924621/36200000000000 : ℝ)*(15489/100000 : ℝ)=(250034113596767/250000000000000 : ℝ) by norm_num, show 1+2*(14857068970538379/50000000000000000000 : ℝ)=(25014857068970538379/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1809602037137138411/1810000000000000000 : ℝ)*(X 1 0+X 2 0)+(41638924621/36200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4459/1024 : ℝ)) (lo := (10783/100000 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (1809602037137138411/1810000000000000000 : ℝ)) (alpha := (41638924621/36200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1809602037137138411/1810000000000000000 : ℝ)*(X 0 1+X 2 1)+(41638924621/36200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4459/1024 : ℝ)) (lo := (10783/100000 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (1809602037137138411/1810000000000000000 : ℝ)) (alpha := (41638924621/36200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1809602037137138411/1810000000000000000 : ℝ)*(X 0 2+X 1 2)+(41638924621/36200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4459/1024 : ℝ)) (lo := (10783/100000 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (1809602037137138411/1810000000000000000 : ℝ)) (alpha := (41638924621/36200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1913252003/10000000000 : ℝ)*X 0 0+(1087447399/2000000000 : ℝ)*X 0 1+(5215906687/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338306051/2500000000 : ℝ)*X 1 0+(-2026679571/10000000000 : ℝ)*X 1 1+(5215906677/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353224207/10000000000 : ℝ)*X 2 0+(5215906679/10000000000 : ℝ)*X 2 1+(-506669891/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4283943719/10000000000 : ℝ)*X 0 0+(4044428387/10000000000 : ℝ)*X 0 1+(2267861319/5000000000 : ℝ)*X 0 2+(4283943719/10000000000 : ℝ)*X 1 0+(4044428387/10000000000 : ℝ)*X 1 1+(2267861319/5000000000 : ℝ)*X 1 2+(4283943719/10000000000 : ℝ)*X 2 0+(4044428387/10000000000 : ℝ)*X 2 1+(2267861319/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1913282333/10000000000 : ℝ)*X 0 0+(5217040047/10000000000 : ℝ)*X 0 1+(543609529/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5295401137/10000000000 : ℝ)*X 1 0+(-225811369/1250000000 : ℝ)*X 1 1+(543609529/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5295401121/10000000000 : ℝ)*X 2 0+(5436095297/10000000000 : ℝ)*X 2 1+(-451622741/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((535501377/1250000000 : ℝ)*X 0 0+(4533206859/10000000000 : ℝ)*X 0 1+(1011740667/2500000000 : ℝ)*X 0 2+(535501377/1250000000 : ℝ)*X 1 0+(4533206859/10000000000 : ℝ)*X 1 1+(1011740667/2500000000 : ℝ)*X 1 2+(535501377/1250000000 : ℝ)*X 2 0+(4533206859/10000000000 : ℝ)*X 2 1+(1011740667/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (365454536103143208910148421/45250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (287699937/20000000000000 : ℝ)*(base19) + (1340113023/100000000000000 : ℝ)*(base23) + (54024039/100000000000000 : ℝ)*(lower2) + (198351773/100000000000000 : ℝ)*(upper3) + (130766311/100000000000000 : ℝ)*(upper5) + (1638409915634363/50000000000000 : ℝ)*(major0) + (1638409915634363/50000000000000 : ℝ)*(major1) + (1638409915634363/50000000000000 : ℝ)*(major2) + (45181568284657/1000000000000 : ℝ)*(sp0) + (4518177431148673/100000000000000 : ℝ)*(sp1) + (903635505907067/20000000000000 : ℝ)*(sp2) + (2035449719494971/100000000000000 : ℝ)*(sp3) + (22041182657/100000000000000 : ℝ)*(sp4) + (675261417/6250000000000 : ℝ)*(sp7) + (2035460523677643/100000000000000 : ℝ)*(f.failure) + (2259089434824179/50000000000000 : ℝ)*(f.sum) + (339935846677/905000000000000000000000000 : ℝ)*base66 + (1124804140107967193/90500000000000000000000000000000 : ℝ)*base67 + (551121163097967193/90500000000000000000000000000000 : ℝ)*base69 + (418088935203467193/90500000000000000000000000000000 : ℝ)*base71 + (5636074434913/905000000000000000000000000 : ℝ)*base73 + (78113408187532807/90500000000000000000000000000000 : ℝ)*base76 + (150410473906967193/90500000000000000000000000000000 : ℝ)*base77 + (291843590675032807/90500000000000000000000000000000 : ℝ)*base80 + (2119861000553/905000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (983381/312500000000000000000 : ℝ)*base90 + (983381/312500000000000000000 : ℝ)*base92 + (983381/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (21995512463205557180022081/1810000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2022389553/100000000000000 : ℝ)*(base19) + (1085275797/50000000000000 : ℝ)*(base23) + (31629901/12500000000000 : ℝ)*(upper3) + (18595661/25000000000000 : ℝ)*(lower4) + (124992663/50000000000000 : ℝ)*(upper5) + (132432739276343/4000000000000 : ℝ)*(major0) + (132432739276343/4000000000000 : ℝ)*(major1) + (132432739276343/4000000000000 : ℝ)*(major2) + (1217065867/4000000000000 : ℝ)*(sp1) + (4049321031/12500000000000 : ℝ)*(sp2) + (4565057110376689/100000000000000 : ℝ)*(sp4) + (228251233067023/5000000000000 : ℝ)*(sp5) + (4565022545256847/100000000000000 : ℝ)*(sp6) + (1028289724183281/50000000000000 : ℝ)*(sp7) + (1028289724183281/50000000000000 : ℝ)*(f.failure) + (4565057110376689/100000000000000 : ℝ)*(f.sum) + (217467015579/72400000000000000000000000 : ℝ)*base66 + (17432299878220973/7240000000000000000000000000000 : ℝ)*base67 + (9654446902820973/7240000000000000000000000000000 : ℝ)*base69 + (2180815824180973/7240000000000000000000000000000 : ℝ)*base71 + (726197007509/362000000000000000000000000 : ℝ)*base73 + (72308772932220973/7240000000000000000000000000000 : ℝ)*base75 + (14830868121539027/7240000000000000000000000000000 : ℝ)*base78 + (32419008885900973/7240000000000000000000000000000 : ℝ)*base79 + (84117774017/362000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (334427/156250000000000000000 : ℝ)*base90 + (334427/156250000000000000000 : ℝ)*base92 + (334427/156250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1482_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5030833/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10783/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10793/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7739/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1482_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1482_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5030833/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8061/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5101/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10793/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7739/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1482_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1482_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1482_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5030833/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8061/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5101/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10793/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7739/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1482_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
