-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1054_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:58:07.953037+00:00
-- url     : https://prove2.me/submissions/4a544842-4c2c-46b0-926f-29762aa65b15

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
theorem support_rectangle_w1054_box_0 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2079810577/10000000000 : ℝ)*x 0 + (107550621/200000000 : ℝ)*x 1 + (672191337/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2079810577/10000000000 : ℝ)^8247 ≤ (618992379883/5000000000000 : ℝ)^6199 := by
    have hnat : (2079810577 : ℕ)^8247*5000000000000^6199 ≤ 618992379883^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2079810577 10000000000 618992379883 5000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (107550621/200000000 : ℝ)^8247 ≤ (43810078110319/100000000000000 : ℝ)^6199 := by
    have hnat : (107550621 : ℕ)^8247*100000000000000^6199 ≤ 43810078110319^6199*200000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107550621 200000000 43810078110319 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (672191337/1250000000 : ℝ)^8247 ≤ (43810074273523/100000000000000 : ℝ)^6199 := by
    have hnat : (672191337 : ℕ)^8247*100000000000000^6199 ≤ 43810074273523^6199*1250000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672191337 1250000000 43810074273523 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2079810577/10000000000 : ℝ), (107550621/200000000 : ℝ), (672191337/1250000000 : ℝ)] ![(618992379883/5000000000000 : ℝ), (43810078110319/100000000000000 : ℝ), (43810074273523/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2079810577/10000000000 : ℝ)|^8247 ≤ (618992379883/5000000000000 : ℝ)^6199
        have hw : |(-2079810577/10000000000 : ℝ)|=(2079810577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(107550621/200000000 : ℝ)|^8247 ≤ (43810078110319/100000000000000 : ℝ)^6199
        have hw : |(107550621/200000000 : ℝ)|=(107550621/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(672191337/1250000000 : ℝ)|^8247 ≤ (43810074273523/100000000000000 : ℝ)^6199
        have hw : |(672191337/1250000000 : ℝ)|=(672191337/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_box_1 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5295064503/10000000000 : ℝ)*x 0 + (-2191415287/10000000000 : ℝ)*x 1 + (5377530987/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295064503/10000000000 : ℝ)^8247 ≤ (42918544111889/100000000000000 : ℝ)^6199 := by
    have hnat : (5295064503 : ℕ)^8247*100000000000000^6199 ≤ 42918544111889^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295064503 10000000000 42918544111889 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2191415287/10000000000 : ℝ)^8247 ≤ (13271378446679/100000000000000 : ℝ)^6199 := by
    have hnat : (2191415287 : ℕ)^8247*100000000000000^6199 ≤ 13271378446679^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2191415287 10000000000 13271378446679 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5377530987/10000000000 : ℝ)^8247 ≤ (43810077427499/100000000000000 : ℝ)^6199 := by
    have hnat : (5377530987 : ℕ)^8247*100000000000000^6199 ≤ 43810077427499^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377530987 10000000000 43810077427499 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295064503/10000000000 : ℝ), (-2191415287/10000000000 : ℝ), (5377530987/10000000000 : ℝ)] ![(42918544111889/100000000000000 : ℝ), (13271378446679/100000000000000 : ℝ), (43810077427499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295064503/10000000000 : ℝ)|^8247 ≤ (42918544111889/100000000000000 : ℝ)^6199
        have hw : |(5295064503/10000000000 : ℝ)|=(5295064503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2191415287/10000000000 : ℝ)|^8247 ≤ (13271378446679/100000000000000 : ℝ)^6199
        have hw : |(-2191415287/10000000000 : ℝ)|=(2191415287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5377530987/10000000000 : ℝ)|^8247 ≤ (43810077427499/100000000000000 : ℝ)^6199
        have hw : |(5377530987/10000000000 : ℝ)|=(5377530987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_box_2 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5295064587/10000000000 : ℝ)*x 0 + (268876537/500000000 : ℝ)*x 1 + (-1095707753/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295064587/10000000000 : ℝ)^8247 ≤ (42918545017679/100000000000000 : ℝ)^6199 := by
    have hnat : (5295064587 : ℕ)^8247*100000000000000^6199 ≤ 42918545017679^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295064587 10000000000 42918545017679 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (268876537/500000000 : ℝ)^8247 ≤ (43810074750413/100000000000000 : ℝ)^6199 := by
    have hnat : (268876537 : ℕ)^8247*100000000000000^6199 ≤ 43810074750413^6199*500000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268876537 500000000 43810074750413 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1095707753/5000000000 : ℝ)^8247 ≤ (13271380211131/100000000000000 : ℝ)^6199 := by
    have hnat : (1095707753 : ℕ)^8247*100000000000000^6199 ≤ 13271380211131^6199*5000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095707753 5000000000 13271380211131 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295064587/10000000000 : ℝ), (268876537/500000000 : ℝ), (-1095707753/5000000000 : ℝ)] ![(42918545017679/100000000000000 : ℝ), (43810074750413/100000000000000 : ℝ), (13271380211131/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295064587/10000000000 : ℝ)|^8247 ≤ (42918545017679/100000000000000 : ℝ)^6199
        have hw : |(5295064587/10000000000 : ℝ)|=(5295064587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(268876537/500000000 : ℝ)|^8247 ≤ (43810074750413/100000000000000 : ℝ)^6199
        have hw : |(268876537/500000000 : ℝ)|=(268876537/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1095707753/5000000000 : ℝ)|^8247 ≤ (13271380211131/100000000000000 : ℝ)^6199
        have hw : |(-1095707753/5000000000 : ℝ)|=(1095707753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_box_3 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4485750811/10000000000 : ℝ)*x 0 + (270320569/625000000 : ℝ)*x 1 + (4325128811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4485750811/10000000000 : ℝ)^8247 ≤ (17209960858017/50000000000000 : ℝ)^6199 := by
    have hnat : (4485750811 : ℕ)^8247*50000000000000^6199 ≤ 17209960858017^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4485750811 10000000000 17209960858017 50000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (270320569/625000000 : ℝ)^8247 ≤ (32790040610981/100000000000000 : ℝ)^6199 := by
    have hnat : (270320569 : ℕ)^8247*100000000000000^6199 ≤ 32790040610981^6199*625000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270320569 625000000 32790040610981 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4325128811/10000000000 : ℝ)^8247 ≤ (16395018827897/50000000000000 : ℝ)^6199 := by
    have hnat : (4325128811 : ℕ)^8247*50000000000000^6199 ≤ 16395018827897^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4325128811 10000000000 16395018827897 50000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4485750811/10000000000 : ℝ), (270320569/625000000 : ℝ), (4325128811/10000000000 : ℝ)] ![(17209960858017/50000000000000 : ℝ), (32790040610981/100000000000000 : ℝ), (16395018827897/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4485750811/10000000000 : ℝ)|^8247 ≤ (17209960858017/50000000000000 : ℝ)^6199
        have hw : |(4485750811/10000000000 : ℝ)|=(4485750811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(270320569/625000000 : ℝ)|^8247 ≤ (32790040610981/100000000000000 : ℝ)^6199
        have hw : |(270320569/625000000 : ℝ)|=(270320569/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4325128811/10000000000 : ℝ)|^8247 ≤ (16395018827897/50000000000000 : ℝ)^6199
        have hw : |(4325128811/10000000000 : ℝ)|=(4325128811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_box_4 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-117048143/500000000 : ℝ)*x 0 + (2639953681/5000000000 : ℝ)*x 1 + (2639953641/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (117048143/500000000 : ℝ)^8247 ≤ (14489643238873/100000000000000 : ℝ)^6199 := by
    have hnat : (117048143 : ℕ)^8247*100000000000000^6199 ≤ 14489643238873^6199*500000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      117048143 500000000 14489643238873 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2639953681/5000000000 : ℝ)^8247 ≤ (42755178802829/100000000000000 : ℝ)^6199 := by
    have hnat : (2639953681 : ℕ)^8247*100000000000000^6199 ≤ 42755178802829^6199*5000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639953681 5000000000 42755178802829 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2639953641/5000000000 : ℝ)^8247 ≤ (42755177940989/100000000000000 : ℝ)^6199 := by
    have hnat : (2639953641 : ℕ)^8247*100000000000000^6199 ≤ 42755177940989^6199*5000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639953641 5000000000 42755177940989 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-117048143/500000000 : ℝ), (2639953681/5000000000 : ℝ), (2639953641/5000000000 : ℝ)] ![(14489643238873/100000000000000 : ℝ), (42755178802829/100000000000000 : ℝ), (42755177940989/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-117048143/500000000 : ℝ)|^8247 ≤ (14489643238873/100000000000000 : ℝ)^6199
        have hw : |(-117048143/500000000 : ℝ)|=(117048143/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2639953681/5000000000 : ℝ)|^8247 ≤ (42755178802829/100000000000000 : ℝ)^6199
        have hw : |(2639953681/5000000000 : ℝ)|=(2639953681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2639953641/5000000000 : ℝ)|^8247 ≤ (42755177940989/100000000000000 : ℝ)^6199
        have hw : |(2639953641/5000000000 : ℝ)|=(2639953641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_box_5 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2682086797/5000000000 : ℝ)*x 0 + (-557386091/2500000000 : ℝ)*x 1 + (1319976809/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2682086797/5000000000 : ℝ)^8247 ≤ (21832682000243/50000000000000 : ℝ)^6199 := by
    have hnat : (2682086797 : ℕ)^8247*50000000000000^6199 ≤ 21832682000243^6199*5000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2682086797 5000000000 21832682000243 50000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (557386091/2500000000 : ℝ)^8247 ≤ (6789729269877/50000000000000 : ℝ)^6199 := by
    have hnat : (557386091 : ℕ)^8247*50000000000000^6199 ≤ 6789729269877^6199*2500000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      557386091 2500000000 6789729269877 50000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1319976809/2500000000 : ℝ)^8247 ≤ (4275517744543/10000000000000 : ℝ)^6199 := by
    have hnat : (1319976809 : ℕ)^8247*10000000000000^6199 ≤ 4275517744543^6199*2500000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319976809 2500000000 4275517744543 10000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2682086797/5000000000 : ℝ), (-557386091/2500000000 : ℝ), (1319976809/2500000000 : ℝ)] ![(21832682000243/50000000000000 : ℝ), (6789729269877/50000000000000 : ℝ), (4275517744543/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2682086797/5000000000 : ℝ)|^8247 ≤ (21832682000243/50000000000000 : ℝ)^6199
        have hw : |(2682086797/5000000000 : ℝ)|=(2682086797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-557386091/2500000000 : ℝ)|^8247 ≤ (6789729269877/50000000000000 : ℝ)^6199
        have hw : |(-557386091/2500000000 : ℝ)|=(557386091/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1319976809/2500000000 : ℝ)|^8247 ≤ (4275517744543/10000000000000 : ℝ)^6199
        have hw : |(1319976809/2500000000 : ℝ)|=(1319976809/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_box_6 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5364173333/10000000000 : ℝ)*x 0 + (1319976873/2500000000 : ℝ)*x 1 + (-557386093/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5364173333/10000000000 : ℝ)^8247 ≤ (8733072234797/20000000000000 : ℝ)^6199 := by
    have hnat : (5364173333 : ℕ)^8247*20000000000000^6199 ≤ 8733072234797^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5364173333 10000000000 8733072234797 20000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1319976873/2500000000 : ℝ)^8247 ≤ (42755180203319/100000000000000 : ℝ)^6199 := by
    have hnat : (1319976873 : ℕ)^8247*100000000000000^6199 ≤ 42755180203319^6199*2500000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319976873 2500000000 42755180203319 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (557386093/2500000000 : ℝ)^8247 ≤ (6789729302289/50000000000000 : ℝ)^6199 := by
    have hnat : (557386093 : ℕ)^8247*50000000000000^6199 ≤ 6789729302289^6199*2500000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      557386093 2500000000 6789729302289 50000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5364173333/10000000000 : ℝ), (1319976873/2500000000 : ℝ), (-557386093/2500000000 : ℝ)] ![(8733072234797/20000000000000 : ℝ), (42755180203319/100000000000000 : ℝ), (6789729302289/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5364173333/10000000000 : ℝ)|^8247 ≤ (8733072234797/20000000000000 : ℝ)^6199
        have hw : |(5364173333/10000000000 : ℝ)|=(5364173333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1319976873/2500000000 : ℝ)|^8247 ≤ (42755180203319/100000000000000 : ℝ)^6199
        have hw : |(1319976873/2500000000 : ℝ)|=(1319976873/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-557386093/2500000000 : ℝ)|^8247 ≤ (6789729302289/50000000000000 : ℝ)^6199
        have hw : |(-557386093/2500000000 : ℝ)|=(557386093/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_box_7 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4268369173/10000000000 : ℝ)*x 0 + (1108449579/2500000000 : ℝ)*x 1 + (2216899053/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4268369173/10000000000 : ℝ)^8247 ≤ (16109403451141/50000000000000 : ℝ)^6199 := by
    have hnat : (4268369173 : ℕ)^8247*50000000000000^6199 ≤ 16109403451141^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4268369173 10000000000 16109403451141 50000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1108449579/2500000000 : ℝ)^8247 ≤ (1059081175359/3125000000000 : ℝ)^6199 := by
    have hnat : (1108449579 : ℕ)^8247*3125000000000^6199 ≤ 1059081175359^6199*2500000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1108449579 2500000000 1059081175359 3125000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2216899053/5000000000 : ℝ)^8247 ≤ (33890595476001/100000000000000 : ℝ)^6199 := by
    have hnat : (2216899053 : ℕ)^8247*100000000000000^6199 ≤ 33890595476001^6199*5000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2216899053 5000000000 33890595476001 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4268369173/10000000000 : ℝ), (1108449579/2500000000 : ℝ), (2216899053/5000000000 : ℝ)] ![(16109403451141/50000000000000 : ℝ), (1059081175359/3125000000000 : ℝ), (33890595476001/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4268369173/10000000000 : ℝ)|^8247 ≤ (16109403451141/50000000000000 : ℝ)^6199
        have hw : |(4268369173/10000000000 : ℝ)|=(4268369173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1108449579/2500000000 : ℝ)|^8247 ≤ (1059081175359/3125000000000 : ℝ)^6199
        have hw : |(1108449579/2500000000 : ℝ)|=(1108449579/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2216899053/5000000000 : ℝ)|^8247 ≤ (33890595476001/100000000000000 : ℝ)^6199
        have hw : |(2216899053/5000000000 : ℝ)|=(2216899053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_box_8 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-228646023/1000000000 : ℝ)*x 0 + (2606843789/5000000000 : ℝ)*x 1 + (5387130253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (228646023/1000000000 : ℝ)^8247 ≤ (7021288074343/50000000000000 : ℝ)^6199 := by
    have hnat : (228646023 : ℕ)^8247*50000000000000^6199 ≤ 7021288074343^6199*1000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      228646023 1000000000 7021288074343 50000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2606843789/5000000000 : ℝ)^8247 ≤ (1681730999729/4000000000000 : ℝ)^6199 := by
    have hnat : (2606843789 : ℕ)^8247*4000000000000^6199 ≤ 1681730999729^6199*5000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2606843789 5000000000 1681730999729 4000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5387130253/10000000000 : ℝ)^8247 ≤ (43914148846241/100000000000000 : ℝ)^6199 := by
    have hnat : (5387130253 : ℕ)^8247*100000000000000^6199 ≤ 43914148846241^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387130253 10000000000 43914148846241 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-228646023/1000000000 : ℝ), (2606843789/5000000000 : ℝ), (5387130253/10000000000 : ℝ)] ![(7021288074343/50000000000000 : ℝ), (1681730999729/4000000000000 : ℝ), (43914148846241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-228646023/1000000000 : ℝ)|^8247 ≤ (7021288074343/50000000000000 : ℝ)^6199
        have hw : |(-228646023/1000000000 : ℝ)|=(228646023/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2606843789/5000000000 : ℝ)|^8247 ≤ (1681730999729/4000000000000 : ℝ)^6199
        have hw : |(2606843789/5000000000 : ℝ)|=(2606843789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5387130253/10000000000 : ℝ)|^8247 ≤ (43914148846241/100000000000000 : ℝ)^6199
        have hw : |(5387130253/10000000000 : ℝ)|=(5387130253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_box_9 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1057653041/2000000000 : ℝ)*x 0 + (-546898831/2500000000 : ℝ)*x 1 + (5387130191/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057653041/2000000000 : ℝ)^8247 ≤ (21422620703207/50000000000000 : ℝ)^6199 := by
    have hnat : (1057653041 : ℕ)^8247*50000000000000^6199 ≤ 21422620703207^6199*2000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057653041 2000000000 21422620703207 50000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (546898831/2500000000 : ℝ)^8247 ≤ (827538150819/6250000000000 : ℝ)^6199 := by
    have hnat : (546898831 : ℕ)^8247*6250000000000^6199 ≤ 827538150819^6199*2500000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546898831 2500000000 827538150819 6250000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5387130191/10000000000 : ℝ)^8247 ≤ (43914148173863/100000000000000 : ℝ)^6199 := by
    have hnat : (5387130191 : ℕ)^8247*100000000000000^6199 ≤ 43914148173863^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387130191 10000000000 43914148173863 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057653041/2000000000 : ℝ), (-546898831/2500000000 : ℝ), (5387130191/10000000000 : ℝ)] ![(21422620703207/50000000000000 : ℝ), (827538150819/6250000000000 : ℝ), (43914148173863/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057653041/2000000000 : ℝ)|^8247 ≤ (21422620703207/50000000000000 : ℝ)^6199
        have hw : |(1057653041/2000000000 : ℝ)|=(1057653041/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-546898831/2500000000 : ℝ)|^8247 ≤ (827538150819/6250000000000 : ℝ)^6199
        have hw : |(-546898831/2500000000 : ℝ)|=(546898831/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5387130191/10000000000 : ℝ)|^8247 ≤ (43914148173863/100000000000000 : ℝ)^6199
        have hw : |(5387130191/10000000000 : ℝ)|=(5387130191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_box_10 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (211530611/400000000 : ℝ)*x 0 + (5387130209/10000000000 : ℝ)*x 1 + (-546898801/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211530611/400000000 : ℝ)^8247 ≤ (21422621080459/50000000000000 : ℝ)^6199 := by
    have hnat : (211530611 : ℕ)^8247*50000000000000^6199 ≤ 21422621080459^6199*400000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211530611 400000000 21422621080459 50000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5387130209/10000000000 : ℝ)^8247 ≤ (4391414836907/10000000000000 : ℝ)^6199 := by
    have hnat : (5387130209 : ℕ)^8247*10000000000000^6199 ≤ 4391414836907^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387130209 10000000000 4391414836907 10000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (546898801/2500000000 : ℝ)^8247 ≤ (13240609446839/100000000000000 : ℝ)^6199 := by
    have hnat : (546898801 : ℕ)^8247*100000000000000^6199 ≤ 13240609446839^6199*2500000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546898801 2500000000 13240609446839 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(211530611/400000000 : ℝ), (5387130209/10000000000 : ℝ), (-546898801/2500000000 : ℝ)] ![(21422621080459/50000000000000 : ℝ), (4391414836907/10000000000000 : ℝ), (13240609446839/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(211530611/400000000 : ℝ)|^8247 ≤ (21422621080459/50000000000000 : ℝ)^6199
        have hw : |(211530611/400000000 : ℝ)|=(211530611/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5387130209/10000000000 : ℝ)|^8247 ≤ (4391414836907/10000000000000 : ℝ)^6199
        have hw : |(5387130209/10000000000 : ℝ)|=(5387130209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-546898801/2500000000 : ℝ)|^8247 ≤ (13240609446839/100000000000000 : ℝ)^6199
        have hw : |(-546898801/2500000000 : ℝ)|=(546898801/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_box_11 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4506852783/10000000000 : ℝ)*x 0 + (539304673/1250000000 : ℝ)*x 1 + (862887499/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4506852783/10000000000 : ℝ)^8247 ≤ (34635502045869/100000000000000 : ℝ)^6199 := by
    have hnat : (4506852783 : ℕ)^8247*100000000000000^6199 ≤ 34635502045869^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4506852783 10000000000 34635502045869 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539304673/1250000000 : ℝ)^8247 ≤ (6536449682093/20000000000000 : ℝ)^6199 := by
    have hnat : (539304673 : ℕ)^8247*20000000000000^6199 ≤ 6536449682093^6199*1250000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539304673 1250000000 6536449682093 20000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (862887499/2000000000 : ℝ)^8247 ≤ (8170562382273/25000000000000 : ℝ)^6199 := by
    have hnat : (862887499 : ℕ)^8247*25000000000000^6199 ≤ 8170562382273^6199*2000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      862887499 2000000000 8170562382273 25000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4506852783/10000000000 : ℝ), (539304673/1250000000 : ℝ), (862887499/2000000000 : ℝ)] ![(34635502045869/100000000000000 : ℝ), (6536449682093/20000000000000 : ℝ), (8170562382273/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4506852783/10000000000 : ℝ)|^8247 ≤ (34635502045869/100000000000000 : ℝ)^6199
        have hw : |(4506852783/10000000000 : ℝ)|=(4506852783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539304673/1250000000 : ℝ)|^8247 ≤ (6536449682093/20000000000000 : ℝ)^6199
        have hw : |(539304673/1250000000 : ℝ)|=(539304673/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(862887499/2000000000 : ℝ)|^8247 ≤ (8170562382273/25000000000000 : ℝ)^6199
        have hw : |(862887499/2000000000 : ℝ)|=(862887499/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_box_12 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2134689803/10000000000 : ℝ)*x 0 + (5442405503/10000000000 : ℝ)*x 1 + (1317978173/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2134689803/10000000000 : ℝ)^8247 ≤ (12816314926977/100000000000000 : ℝ)^6199 := by
    have hnat : (2134689803 : ℕ)^8247*100000000000000^6199 ≤ 12816314926977^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2134689803 10000000000 12816314926977 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5442405503/10000000000 : ℝ)^8247 ≤ (22257305656777/50000000000000 : ℝ)^6199 := by
    have hnat : (5442405503 : ℕ)^8247*50000000000000^6199 ≤ 22257305656777^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5442405503 10000000000 22257305656777 50000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1317978173/2500000000 : ℝ)^8247 ≤ (42669073748077/100000000000000 : ℝ)^6199 := by
    have hnat : (1317978173 : ℕ)^8247*100000000000000^6199 ≤ 42669073748077^6199*2500000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1317978173 2500000000 42669073748077 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2134689803/10000000000 : ℝ), (5442405503/10000000000 : ℝ), (1317978173/2500000000 : ℝ)] ![(12816314926977/100000000000000 : ℝ), (22257305656777/50000000000000 : ℝ), (42669073748077/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2134689803/10000000000 : ℝ)|^8247 ≤ (12816314926977/100000000000000 : ℝ)^6199
        have hw : |(-2134689803/10000000000 : ℝ)|=(2134689803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5442405503/10000000000 : ℝ)|^8247 ≤ (22257305656777/50000000000000 : ℝ)^6199
        have hw : |(5442405503/10000000000 : ℝ)|=(5442405503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1317978173/2500000000 : ℝ)|^8247 ≤ (42669073748077/100000000000000 : ℝ)^6199
        have hw : |(1317978173/2500000000 : ℝ)|=(1317978173/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_box_13 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (671228823/1250000000 : ℝ)*x 0 + (-558152001/2500000000 : ℝ)*x 1 + (5271912749/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (671228823/1250000000 : ℝ)^8247 ≤ (546582963419/1250000000000 : ℝ)^6199 := by
    have hnat : (671228823 : ℕ)^8247*1250000000000^6199 ≤ 546582963419^6199*1250000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671228823 1250000000 546582963419 1250000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (558152001/2500000000 : ℝ)^8247 ≤ (6802144276807/50000000000000 : ℝ)^6199 := by
    have hnat : (558152001 : ℕ)^8247*50000000000000^6199 ≤ 6802144276807^6199*2500000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      558152001 2500000000 6802144276807 50000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5271912749/10000000000 : ℝ)^8247 ≤ (4266907436183/10000000000000 : ℝ)^6199 := by
    have hnat : (5271912749 : ℕ)^8247*10000000000000^6199 ≤ 4266907436183^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271912749 10000000000 4266907436183 10000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(671228823/1250000000 : ℝ), (-558152001/2500000000 : ℝ), (5271912749/10000000000 : ℝ)] ![(546582963419/1250000000000 : ℝ), (6802144276807/50000000000000 : ℝ), (4266907436183/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(671228823/1250000000 : ℝ)|^8247 ≤ (546582963419/1250000000000 : ℝ)^6199
        have hw : |(671228823/1250000000 : ℝ)|=(671228823/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-558152001/2500000000 : ℝ)|^8247 ≤ (6802144276807/50000000000000 : ℝ)^6199
        have hw : |(-558152001/2500000000 : ℝ)|=(558152001/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5271912749/10000000000 : ℝ)|^8247 ≤ (4266907436183/10000000000000 : ℝ)^6199
        have hw : |(5271912749/10000000000 : ℝ)|=(5271912749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_box_14 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (107396613/200000000 : ℝ)*x 0 + (527191273/1000000000 : ℝ)*x 1 + (-2232607941/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107396613/200000000 : ℝ)^8247 ≤ (43726637788517/100000000000000 : ℝ)^6199 := by
    have hnat : (107396613 : ℕ)^8247*100000000000000^6199 ≤ 43726637788517^6199*200000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107396613 200000000 43726637788517 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (527191273/1000000000 : ℝ)^8247 ≤ (21334537078623/50000000000000 : ℝ)^6199 := by
    have hnat : (527191273 : ℕ)^8247*50000000000000^6199 ≤ 21334537078623^6199*1000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527191273 1000000000 21334537078623 50000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2232607941/10000000000 : ℝ)^8247 ≤ (13604288042899/100000000000000 : ℝ)^6199 := by
    have hnat : (2232607941 : ℕ)^8247*100000000000000^6199 ≤ 13604288042899^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2232607941 10000000000 13604288042899 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(107396613/200000000 : ℝ), (527191273/1000000000 : ℝ), (-2232607941/10000000000 : ℝ)] ![(43726637788517/100000000000000 : ℝ), (21334537078623/50000000000000 : ℝ), (13604288042899/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(107396613/200000000 : ℝ)|^8247 ≤ (43726637788517/100000000000000 : ℝ)^6199
        have hw : |(107396613/200000000 : ℝ)|=(107396613/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(527191273/1000000000 : ℝ)|^8247 ≤ (21334537078623/50000000000000 : ℝ)^6199
        have hw : |(527191273/1000000000 : ℝ)|=(527191273/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2232607941/10000000000 : ℝ)|^8247 ≤ (13604288042899/100000000000000 : ℝ)^6199
        have hw : |(-2232607941/10000000000 : ℝ)|=(2232607941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_box_15 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4250337111/10000000000 : ℝ)*x 0 + (2221346283/5000000000 : ℝ)*x 1 + (4442692477/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4250337111/10000000000 : ℝ)^8247 ≤ (500591480391/1562500000000 : ℝ)^6199 := by
    have hnat : (4250337111 : ℕ)^8247*1562500000000^6199 ≤ 500591480391^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4250337111 10000000000 500591480391 1562500000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2221346283/5000000000 : ℝ)^8247 ≤ (16990536536499/50000000000000 : ℝ)^6199 := by
    have hnat : (2221346283 : ℕ)^8247*50000000000000^6199 ≤ 16990536536499^6199*5000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2221346283 5000000000 16990536536499 50000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4442692477/10000000000 : ℝ)^8247 ≤ (33981072167359/100000000000000 : ℝ)^6199 := by
    have hnat : (4442692477 : ℕ)^8247*100000000000000^6199 ≤ 33981072167359^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4442692477 10000000000 33981072167359 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4250337111/10000000000 : ℝ), (2221346283/5000000000 : ℝ), (4442692477/10000000000 : ℝ)] ![(500591480391/1562500000000 : ℝ), (16990536536499/50000000000000 : ℝ), (33981072167359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4250337111/10000000000 : ℝ)|^8247 ≤ (500591480391/1562500000000 : ℝ)^6199
        have hw : |(4250337111/10000000000 : ℝ)|=(4250337111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2221346283/5000000000 : ℝ)|^8247 ≤ (16990536536499/50000000000000 : ℝ)^6199
        have hw : |(2221346283/5000000000 : ℝ)|=(2221346283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4442692477/10000000000 : ℝ)|^8247 ≤ (33981072167359/100000000000000 : ℝ)^6199
        have hw : |(4442692477/10000000000 : ℝ)|=(4442692477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1054_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36939913/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2799/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2247/20000 : ℝ)*pair X i i ≤ pair X i h) :
    -(3889/6250 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(1851/3125 : ℝ) ∧ (39767/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (3317/4000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2799/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2247/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2799/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2247/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2799/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2247/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2799/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2247/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2799/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2247/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2799/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2247/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2247/20000 : ℝ) ^ (4123/1024 : ℝ) ≤ (752018619630773/5000000000000000000 : ℝ) := by
    have hpowers : (2247/20000 : ℝ)^4123 ≤ (752018619630773/5000000000000000000 : ℝ)^1024 := by
      have hnat : (2247 : ℕ)^4123*5000000000000000000^1024 ≤ 752018619630773^1024*20000^4123 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2247 20000 752018619630773 5000000000000000000 4123 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2247/20000 : ℝ)) (X := (752018619630773/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4123 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2799/20000 : ℝ) ^ (4123/1024 : ℝ) ≤ (18211399560080677/50000000000000000000 : ℝ) := by
    have hpowers : (2799/20000 : ℝ)^4123 ≤ (18211399560080677/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2799 : ℕ)^4123*50000000000000000000^1024 ≤ 18211399560080677^1024*20000^4123 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2799 20000 18211399560080677 50000000000000000000 4123 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2799/20000 : ℝ)) (X := (18211399560080677/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4123 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500752018619630773/2500000000000000000 : ℝ) ≤ (10000747009484799/10000000000000000 : ℝ) ^ (4123/1024 : ℝ) := by
    have hpowers : (2500752018619630773/2500000000000000000 : ℝ)^1024 ≤ (10000747009484799/10000000000000000 : ℝ)^4123 := by
      have hnat : (2500752018619630773 : ℕ)^1024*10000000000000000^4123 ≤ 10000747009484799^4123*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500752018619630773 2500000000000000000 10000747009484799 10000000000000000 1024 4123 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000747009484799/10000000000000000 : ℝ)) (X := (2500752018619630773/2500000000000000000 : ℝ)) (by norm_num) 4123 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50025731585756388407/50000000000000000000 : ℝ) ≤ (10001277906825413/10000000000000000 : ℝ) ^ (4123/1024 : ℝ) := by
    have hpowers : (50025731585756388407/50000000000000000000 : ℝ)^1024 ≤ (10001277906825413/10000000000000000 : ℝ)^4123 := by
      have hnat : (50025731585756388407 : ℕ)^1024*10000000000000000^4123 ≤ 10001277906825413^4123*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025731585756388407 50000000000000000000 10001277906825413 10000000000000000 1024 4123 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001277906825413/10000000000000000 : ℝ)) (X := (50025731585756388407/50000000000000000000 : ℝ)) (by norm_num) 4123 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018211399560080677/25000000000000000000 : ℝ) ≤ (10001808804166027/10000000000000000 : ℝ) ^ (4123/1024 : ℝ) := by
    have hpowers : (25018211399560080677/25000000000000000000 : ℝ)^1024 ≤ (10001808804166027/10000000000000000 : ℝ)^4123 := by
      have hnat : (25018211399560080677 : ℕ)^1024*10000000000000000^4123 ≤ 10001808804166027^4123*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018211399560080677 25000000000000000000 10001808804166027 10000000000000000 1024 4123 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001808804166027/10000000000000000 : ℝ)) (X := (25018211399560080677/25000000000000000000 : ℝ)) (by norm_num) 4123 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(752018619630773/5000000000000000000 : ℝ) ≤ ((459835541382240811/460000000000000000 : ℝ)+2*(265448670307/138000000000000 : ℝ)*(2247/20000 : ℝ))^(4123/1024 : ℝ) := by
    rw [show (459835541382240811/460000000000000000 : ℝ)+2*(265448670307/138000000000000 : ℝ)*(2247/20000 : ℝ)=(10000747009484799/10000000000000000 : ℝ) by norm_num, show 1+2*(752018619630773/5000000000000000000 : ℝ)=(2500752018619630773/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18211399560080677/50000000000000000000 : ℝ)+(752018619630773/5000000000000000000 : ℝ) ≤ ((459835541382240811/460000000000000000 : ℝ)+(265448670307/138000000000000 : ℝ)*((2799/20000 : ℝ)+(2247/20000 : ℝ)))^(4123/1024 : ℝ) := by
    rw [show (459835541382240811/460000000000000000 : ℝ)+(265448670307/138000000000000 : ℝ)*((2799/20000 : ℝ)+(2247/20000 : ℝ))=(10001277906825413/10000000000000000 : ℝ) by norm_num, show 1+(18211399560080677/50000000000000000000 : ℝ)+(752018619630773/5000000000000000000 : ℝ)=(50025731585756388407/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18211399560080677/50000000000000000000 : ℝ) ≤ ((459835541382240811/460000000000000000 : ℝ)+2*(265448670307/138000000000000 : ℝ)*(2799/20000 : ℝ))^(4123/1024 : ℝ) := by
    rw [show (459835541382240811/460000000000000000 : ℝ)+2*(265448670307/138000000000000 : ℝ)*(2799/20000 : ℝ)=(10001808804166027/10000000000000000 : ℝ) by norm_num, show 1+2*(18211399560080677/50000000000000000000 : ℝ)=(25018211399560080677/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (459835541382240811/460000000000000000 : ℝ)*(X 1 0+X 2 0)+(265448670307/138000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4123/1024 : ℝ)) (lo := (2247/20000 : ℝ)) (hi := (2799/20000 : ℝ)) (c := (459835541382240811/460000000000000000 : ℝ)) (alpha := (265448670307/138000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (459835541382240811/460000000000000000 : ℝ)*(X 0 1+X 2 1)+(265448670307/138000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4123/1024 : ℝ)) (lo := (2247/20000 : ℝ)) (hi := (2799/20000 : ℝ)) (c := (459835541382240811/460000000000000000 : ℝ)) (alpha := (265448670307/138000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (459835541382240811/460000000000000000 : ℝ)*(X 0 2+X 1 2)+(265448670307/138000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4123/1024 : ℝ)) (lo := (2247/20000 : ℝ)) (hi := (2799/20000 : ℝ)) (c := (459835541382240811/460000000000000000 : ℝ)) (alpha := (265448670307/138000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2079810577/10000000000 : ℝ)*X 0 0+(107550621/200000000 : ℝ)*X 0 1+(672191337/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5295064503/10000000000 : ℝ)*X 1 0+(-2191415287/10000000000 : ℝ)*X 1 1+(5377530987/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5295064587/10000000000 : ℝ)*X 2 0+(268876537/500000000 : ℝ)*X 2 1+(-1095707753/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4485750811/10000000000 : ℝ)*X 0 0+(270320569/625000000 : ℝ)*X 0 1+(4325128811/10000000000 : ℝ)*X 0 2+(4485750811/10000000000 : ℝ)*X 1 0+(270320569/625000000 : ℝ)*X 1 1+(4325128811/10000000000 : ℝ)*X 1 2+(4485750811/10000000000 : ℝ)*X 2 0+(270320569/625000000 : ℝ)*X 2 1+(4325128811/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-117048143/500000000 : ℝ)*X 0 0+(2639953681/5000000000 : ℝ)*X 0 1+(2639953641/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2682086797/5000000000 : ℝ)*X 1 0+(-557386091/2500000000 : ℝ)*X 1 1+(1319976809/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5364173333/10000000000 : ℝ)*X 2 0+(1319976873/2500000000 : ℝ)*X 2 1+(-557386093/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4268369173/10000000000 : ℝ)*X 0 0+(1108449579/2500000000 : ℝ)*X 0 1+(2216899053/5000000000 : ℝ)*X 0 2+(4268369173/10000000000 : ℝ)*X 1 0+(1108449579/2500000000 : ℝ)*X 1 1+(2216899053/5000000000 : ℝ)*X 1 2+(4268369173/10000000000 : ℝ)*X 2 0+(1108449579/2500000000 : ℝ)*X 2 1+(2216899053/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-228646023/1000000000 : ℝ)*X 0 0+(2606843789/5000000000 : ℝ)*X 0 1+(5387130253/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1057653041/2000000000 : ℝ)*X 1 0+(-546898831/2500000000 : ℝ)*X 1 1+(5387130191/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((211530611/400000000 : ℝ)*X 2 0+(5387130209/10000000000 : ℝ)*X 2 1+(-546898801/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4506852783/10000000000 : ℝ)*X 0 0+(539304673/1250000000 : ℝ)*X 0 1+(862887499/2000000000 : ℝ)*X 0 2+(4506852783/10000000000 : ℝ)*X 1 0+(539304673/1250000000 : ℝ)*X 1 1+(862887499/2000000000 : ℝ)*X 1 2+(4506852783/10000000000 : ℝ)*X 2 0+(539304673/1250000000 : ℝ)*X 2 1+(862887499/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2134689803/10000000000 : ℝ)*X 0 0+(5442405503/10000000000 : ℝ)*X 0 1+(1317978173/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((671228823/1250000000 : ℝ)*X 1 0+(-558152001/2500000000 : ℝ)*X 1 1+(5271912749/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((107396613/200000000 : ℝ)*X 2 0+(527191273/1000000000 : ℝ)*X 2 1+(-2232607941/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4250337111/10000000000 : ℝ)*X 0 0+(2221346283/5000000000 : ℝ)*X 0 1+(4442692477/10000000000 : ℝ)*X 0 2+(4250337111/10000000000 : ℝ)*X 1 0+(2221346283/5000000000 : ℝ)*X 1 1+(4442692477/10000000000 : ℝ)*X 1 2+(4250337111/10000000000 : ℝ)*X 2 0+(2221346283/5000000000 : ℝ)*X 2 1+(4442692477/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-3889/6250 : ℝ) ≤ (-715547300587546214960713953/1150000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15270233/20000000000000 : ℝ)*(upper0) + (21670133/20000000000000 : ℝ)*(upper1) + (9052991/25000000000000 : ℝ)*(upper2) + (84843477/100000000000000 : ℝ)*(upper3) + (2736267/50000000000000 : ℝ)*(upper5) + (1923149021550643/50000000000000 : ℝ)*(major0) + (1923149021550643/50000000000000 : ℝ)*(major1) + (1923149021550643/50000000000000 : ℝ)*(major2) + (4155896503/50000000000000 : ℝ)*(sp3) + (255512961563651/5000000000000 : ℝ)*(sp4) + (255512961563651/5000000000000 : ℝ)*(sp5) + (511008747882881/10000000000000 : ℝ)*(sp6) + (2603069044602829/100000000000000 : ℝ)*(sp7) + (17175244421/10000000000000 : ℝ)*(sp14) + (520615471279167/20000000000000 : ℝ)*(f.failure) + (255512961563651/5000000000000 : ℝ)*(f.sum) + (12674916121051/3450000000000000000000000000 : ℝ)*base65 + (2591809668215684419/69000000000000000000000000000000 : ℝ)*base67 + (168342433127684419/69000000000000000000000000000000 : ℝ)*base69 + (73708378899315581/69000000000000000000000000000000 : ℝ)*base72 + (12756880444801/3450000000000000000000000000 : ℝ)*base73 + (3248402998607684419/69000000000000000000000000000000 : ℝ)*base75 + (284746697049315581/69000000000000000000000000000000 : ℝ)*base78 + (4010680587804315581/69000000000000000000000000000000 : ℝ)*base80 + (158788875462901/3450000000000000000000000000 : ℝ)*base81 + (2307529/500000000000000000000 : ℝ)*base90 + (2307529/500000000000000000000 : ℝ)*base92 + (2307529/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (1851/3125 : ℝ) ≤ (6811943602493166788335535850131/11500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7203169/100000000000000 : ℝ)*(upper2) + (83132513/100000000000000 : ℝ)*(upper3) + (1586189/2000000000000 : ℝ)*(lower5) + (1954505075610707/50000000000000 : ℝ)*(major0) + (1954505075610707/50000000000000 : ℝ)*(major1) + (1954505075610707/50000000000000 : ℝ)*(major2) + (5152751833748559/100000000000000 : ℝ)*(sp0) + (1030549959580469/20000000000000 : ℝ)*(sp1) + (5152747146267163/100000000000000 : ℝ)*(sp2) + (661379029038267/25000000000000 : ℝ)*(sp3) + (1282687817/20000000000000 : ℝ)*(sp5) + (4377592871/100000000000000 : ℝ)*(sp8) + (9065074267/100000000000000 : ℝ)*(sp10) + (3210883121/100000000000000 : ℝ)*(sp11) + (661379831759047/25000000000000 : ℝ)*(f.failure) + (5152756211341431/100000000000000 : ℝ)*(f.sum) + (1933426135051/3450000000000000000000000000 : ℝ)*base66 + (839338153093619869/69000000000000000000000000000000 : ℝ)*base68 + (66676176232380131/69000000000000000000000000000000 : ℝ)*base69 + (166532607541619869/69000000000000000000000000000000 : ℝ)*base72 + (47230154777401/3450000000000000000000000000 : ℝ)*base74 + (416872556020380131/69000000000000000000000000000000 : ℝ)*base75 + (39569439130619869/69000000000000000000000000000000 : ℝ)*base78 + (72058776508619869/69000000000000000000000000000000 : ℝ)*base80 + (6349543707601/3450000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (4357089/625000000000000000000 : ℝ)*base90 + (4357089/625000000000000000000 : ℝ)*base92 + (4357089/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (39767/50000 : ℝ) ≤ (9146733792239807575799854542351/11500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6830291/20000000000000 : ℝ)*(upper0) + (57425809/100000000000000 : ℝ)*(lower3) + (1844691/3125000000000 : ℝ)*(upper4) + (4377265992601047/100000000000000 : ℝ)*(major0) + (4377265992601047/100000000000000 : ℝ)*(major1) + (4377265992601047/100000000000000 : ℝ)*(major2) + (600219729/2000000000000 : ℝ)*(sp1) + (11494192101/20000000000000 : ℝ)*(sp2) + (30472356629/100000000000000 : ℝ)*(sp3) + (332440339/50000000000000 : ℝ)*(sp4) + (576559599632579/10000000000000 : ℝ)*(sp8) + (2882783325110009/50000000000000 : ℝ)*(sp9) + (5765539190245963/100000000000000 : ℝ)*(sp10) + (1481196289888709/50000000000000 : ℝ)*(sp11) + (2962423052134047/100000000000000 : ℝ)*(f.failure) + (1441399165301617/25000000000000 : ℝ)*(f.sum) + (858572181243/2300000000000000000000000000 : ℝ)*base65 + (141803872687840883/46000000000000000000000000000000 : ℝ)*base68 + (224508887793840883/46000000000000000000000000000000 : ℝ)*base70 + (58979744261840883/46000000000000000000000000000000 : ℝ)*base72 + (93360689061343/2300000000000000000000000000 : ℝ)*base73 + (108867993805840883/46000000000000000000000000000000 : ℝ)*base76 + (53715047618159117/46000000000000000000000000000000 : ℝ)*base77 + (2754292540593840883/46000000000000000000000000000000 : ℝ)*base80 + (1883005029043/2300000000000000000000000000 : ℝ)*base81 + (14482089/2500000000000000000000 : ℝ)*base90 + (14482089/2500000000000000000000 : ℝ)*base92 + (14482089/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-3317/4000 : ℝ) ≤ (-1907219304403087224549548233923/2300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10508713/100000000000000 : ℝ)*(lower0) + (1772189/12500000000000 : ℝ)*(upper1) + (38711309/100000000000000 : ℝ)*(lower2) + (4434047/10000000000000 : ℝ)*(upper3) + (3176177/4000000000000 : ℝ)*(upper5) + (441172731034531/10000000000000 : ℝ)*(major0) + (441172731034531/10000000000000 : ℝ)*(major1) + (441172731034531/10000000000000 : ℝ)*(major2) + (204484199/5000000000000 : ℝ)*(sp4) + (13852547389/20000000000000 : ℝ)*(sp7) + (586534578901537/10000000000000 : ℝ)*(sp12) + (117306997573987/2000000000000 : ℝ)*(sp13) + (117306997573987/2000000000000 : ℝ)*(sp14) + (1492838169369211/50000000000000 : ℝ)*(sp15) + (373218200184421/12500000000000 : ℝ)*(f.failure) + (117306997573987/2000000000000 : ℝ)*(f.sum) + (1267951716713/690000000000000000000000000 : ℝ)*base66 + (46268164614096077/13800000000000000000000000000000 : ℝ)*base68 + (237110715782303923/13800000000000000000000000000000 : ℝ)*base69 + (35768717672903923/13800000000000000000000000000000 : ℝ)*base71 + (1435304301337/690000000000000000000000000 : ℝ)*base73 + (10291228232303923/13800000000000000000000000000000 : ℝ)*base75 + (8249349692903923/13800000000000000000000000000000 : ℝ)*base77 + (21603198708096077/13800000000000000000000000000000 : ℝ)*base80 + (659246617643/690000000000000000000000000 : ℝ)*base82 + (1945373/312500000000000000000 : ℝ)*base89 + (1945373/312500000000000000000 : ℝ)*base91 + (1945373/312500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1054_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36939913/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2799/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2247/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(1851/3125 : ℝ) else (39767/50000 : ℝ) ≤ X j i ∧ X j i ≤ (3317/4000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1054_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1054_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36939913/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2799/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2247/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(1851/3125 : ℝ) else (39767/50000 : ℝ) ≤ X j i ∧ X j i ≤ (3317/4000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1054_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36939913/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2799/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2247/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(1851/3125 : ℝ) else (39767/50000 : ℝ) ≤ X j i ∧ X j i ≤ (3317/4000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1054_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
