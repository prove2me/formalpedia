-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1143_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:32:38.773175+00:00
-- url     : https://prove2.me/submissions/235a22e4-c48e-4401-b776-81d7e458c138

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
theorem support_rectangle_w1143_s6_0 (p : ℝ) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2166377583/10000000000 : ℝ)*x 0 + (2696679129/5000000000 : ℝ)*x 1 + (1053086653/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2166377583/10000000000 : ℝ)^521 ≤ (6581925164211/50000000000000 : ℝ)^393 := by
    have hnat : (2166377583 : ℕ)^521*50000000000000^393 ≤ 6581925164211^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2166377583 10000000000 6581925164211 50000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696679129/5000000000 : ℝ)^521 ≤ (44108866948137/100000000000000 : ℝ)^393 := by
    have hnat : (2696679129 : ℕ)^521*100000000000000^393 ≤ 44108866948137^393*5000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696679129 5000000000 44108866948137 100000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053086653/2000000000 : ℝ)^521 ≤ (21363641354859/50000000000000 : ℝ)^393 := by
    have hnat : (1053086653 : ℕ)^521*50000000000000^393 ≤ 21363641354859^393*2000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053086653 2000000000 21363641354859 50000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (521/128 : ℝ)) 521 393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2166377583/10000000000 : ℝ), (2696679129/5000000000 : ℝ), (1053086653/2000000000 : ℝ)] ![(6581925164211/50000000000000 : ℝ), (44108866948137/100000000000000 : ℝ), (21363641354859/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2166377583/10000000000 : ℝ)|^521 ≤ (6581925164211/50000000000000 : ℝ)^393
        have hw : |(-2166377583/10000000000 : ℝ)|=(2166377583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696679129/5000000000 : ℝ)|^521 ≤ (44108866948137/100000000000000 : ℝ)^393
        have hw : |(2696679129/5000000000 : ℝ)|=(2696679129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053086653/2000000000 : ℝ)|^521 ≤ (21363641354859/50000000000000 : ℝ)^393
        have hw : |(1053086653/2000000000 : ℝ)|=(1053086653/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1143_s6_1 (p : ℝ) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2672420351/5000000000 : ℝ)*x 0 + (-1115633921/5000000000 : ℝ)*x 1 + (329089579/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672420351/5000000000 : ℝ)^521 ≤ (348668871007/800000000000 : ℝ)^393 := by
    have hnat : (2672420351 : ℕ)^521*800000000000^393 ≤ 348668871007^393*5000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672420351 5000000000 348668871007 800000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1115633921/5000000000 : ℝ)^521 ≤ (13689108405399/100000000000000 : ℝ)^393 := by
    have hnat : (1115633921 : ℕ)^521*100000000000000^393 ≤ 13689108405399^393*5000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1115633921 5000000000 13689108405399 100000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (329089579/625000000 : ℝ)^521 ≤ (42727282698961/100000000000000 : ℝ)^393 := by
    have hnat : (329089579 : ℕ)^521*100000000000000^393 ≤ 42727282698961^393*625000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329089579 625000000 42727282698961 100000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (521/128 : ℝ)) 521 393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672420351/5000000000 : ℝ), (-1115633921/5000000000 : ℝ), (329089579/625000000 : ℝ)] ![(348668871007/800000000000 : ℝ), (13689108405399/100000000000000 : ℝ), (42727282698961/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672420351/5000000000 : ℝ)|^521 ≤ (348668871007/800000000000 : ℝ)^393
        have hw : |(2672420351/5000000000 : ℝ)|=(2672420351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1115633921/5000000000 : ℝ)|^521 ≤ (13689108405399/100000000000000 : ℝ)^393
        have hw : |(-1115633921/5000000000 : ℝ)|=(1115633921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(329089579/625000000 : ℝ)|^521 ≤ (42727282698961/100000000000000 : ℝ)^393
        have hw : |(329089579/625000000 : ℝ)|=(329089579/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1143_s6_2 (p : ℝ) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5344840659/10000000000 : ℝ)*x 0 + (5265433299/10000000000 : ℝ)*x 1 + (-2231267853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344840659/10000000000 : ℝ)^521 ≤ (10895902102759/25000000000000 : ℝ)^393 := by
    have hnat : (5344840659 : ℕ)^521*25000000000000^393 ≤ 10895902102759^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344840659 10000000000 10895902102759 25000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265433299/10000000000 : ℝ)^521 ≤ (21363641537739/50000000000000 : ℝ)^393 := by
    have hnat : (5265433299 : ℕ)^521*50000000000000^393 ≤ 21363641537739^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265433299 10000000000 21363641537739 50000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2231267853/10000000000 : ℝ)^521 ≤ (6844554247433/50000000000000 : ℝ)^393 := by
    have hnat : (2231267853 : ℕ)^521*50000000000000^393 ≤ 6844554247433^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2231267853 10000000000 6844554247433 50000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (521/128 : ℝ)) 521 393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344840659/10000000000 : ℝ), (5265433299/10000000000 : ℝ), (-2231267853/10000000000 : ℝ)] ![(10895902102759/25000000000000 : ℝ), (21363641537739/50000000000000 : ℝ), (6844554247433/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344840659/10000000000 : ℝ)|^521 ≤ (10895902102759/25000000000000 : ℝ)^393
        have hw : |(5344840659/10000000000 : ℝ)|=(5344840659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265433299/10000000000 : ℝ)|^521 ≤ (21363641537739/50000000000000 : ℝ)^393
        have hw : |(5265433299/10000000000 : ℝ)|=(5265433299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2231267853/10000000000 : ℝ)|^521 ≤ (6844554247433/50000000000000 : ℝ)^393
        have hw : |(-2231267853/10000000000 : ℝ)|=(2231267853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1143_s6_3 (p : ℝ) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2182257677/5000000000 : ℝ)*x 0 + (4239084887/10000000000 : ℝ)*x 1 + (4493638243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2182257677/5000000000 : ℝ)^521 ≤ (33316799926089/100000000000000 : ℝ)^393 := by
    have hnat : (2182257677 : ℕ)^521*100000000000000^393 ≤ 33316799926089^393*5000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182257677 5000000000 33316799926089 100000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4239084887/10000000000 : ℝ)^521 ≤ (32053446665499/100000000000000 : ℝ)^393 := by
    have hnat : (4239084887 : ℕ)^521*100000000000000^393 ≤ 32053446665499^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4239084887 10000000000 32053446665499 100000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4493638243/10000000000 : ℝ)^521 ≤ (17314876693337/50000000000000 : ℝ)^393 := by
    have hnat : (4493638243 : ℕ)^521*50000000000000^393 ≤ 17314876693337^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4493638243 10000000000 17314876693337 50000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (521/128 : ℝ)) 521 393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2182257677/5000000000 : ℝ), (4239084887/10000000000 : ℝ), (4493638243/10000000000 : ℝ)] ![(33316799926089/100000000000000 : ℝ), (32053446665499/100000000000000 : ℝ), (17314876693337/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2182257677/5000000000 : ℝ)|^521 ≤ (33316799926089/100000000000000 : ℝ)^393
        have hw : |(2182257677/5000000000 : ℝ)|=(2182257677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4239084887/10000000000 : ℝ)|^521 ≤ (32053446665499/100000000000000 : ℝ)^393
        have hw : |(4239084887/10000000000 : ℝ)|=(4239084887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4493638243/10000000000 : ℝ)|^521 ≤ (17314876693337/50000000000000 : ℝ)^393
        have hw : |(4493638243/10000000000 : ℝ)|=(4493638243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1143_s6_4 (p : ℝ) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1083191299/5000000000 : ℝ)*x 0 + (5265756307/10000000000 : ℝ)*x 1 + (5393033999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1083191299/5000000000 : ℝ)^521 ≤ (2632778145381/20000000000000 : ℝ)^393 := by
    have hnat : (1083191299 : ℕ)^521*20000000000000^393 ≤ 2632778145381^393*5000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083191299 5000000000 2632778145381 20000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265756307/10000000000 : ℝ)^521 ≤ (42730757908599/100000000000000 : ℝ)^393 := by
    have hnat : (5265756307 : ℕ)^521*100000000000000^393 ≤ 42730757908599^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265756307 10000000000 42730757908599 100000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393033999/10000000000 : ℝ)^521 ≤ (22052675673517/50000000000000 : ℝ)^393 := by
    have hnat : (5393033999 : ℕ)^521*50000000000000^393 ≤ 22052675673517^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393033999 10000000000 22052675673517 50000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (521/128 : ℝ)) 521 393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1083191299/5000000000 : ℝ), (5265756307/10000000000 : ℝ), (5393033999/10000000000 : ℝ)] ![(2632778145381/20000000000000 : ℝ), (42730757908599/100000000000000 : ℝ), (22052675673517/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1083191299/5000000000 : ℝ)|^521 ≤ (2632778145381/20000000000000 : ℝ)^393
        have hw : |(-1083191299/5000000000 : ℝ)|=(1083191299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265756307/10000000000 : ℝ)|^521 ≤ (42730757908599/100000000000000 : ℝ)^393
        have hw : |(5265756307/10000000000 : ℝ)|=(5265756307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393033999/10000000000 : ℝ)|^521 ≤ (22052675673517/50000000000000 : ℝ)^393
        have hw : |(5393033999/10000000000 : ℝ)|=(5393033999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1143_s6_5 (p : ℝ) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1328106981/2500000000 : ℝ)*x 0 + (-105183361/500000000 : ℝ)*x 1 + (5393033943/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328106981/2500000000 : ℝ)^521 ≤ (43233566877697/100000000000000 : ℝ)^393 := by
    have hnat : (1328106981 : ℕ)^521*100000000000000^393 ≤ 43233566877697^393*2500000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328106981 2500000000 43233566877697 100000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (105183361/500000000 : ℝ)^521 ≤ (3165270589379/25000000000000 : ℝ)^393 := by
    have hnat : (105183361 : ℕ)^521*25000000000000^393 ≤ 3165270589379^393*500000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105183361 500000000 3165270589379 25000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393033943/10000000000 : ℝ)^521 ≤ (4410535073989/10000000000000 : ℝ)^393 := by
    have hnat : (5393033943 : ℕ)^521*10000000000000^393 ≤ 4410535073989^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393033943 10000000000 4410535073989 10000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (521/128 : ℝ)) 521 393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328106981/2500000000 : ℝ), (-105183361/500000000 : ℝ), (5393033943/10000000000 : ℝ)] ![(43233566877697/100000000000000 : ℝ), (3165270589379/25000000000000 : ℝ), (4410535073989/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328106981/2500000000 : ℝ)|^521 ≤ (43233566877697/100000000000000 : ℝ)^393
        have hw : |(1328106981/2500000000 : ℝ)|=(1328106981/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-105183361/500000000 : ℝ)|^521 ≤ (3165270589379/25000000000000 : ℝ)^393
        have hw : |(-105183361/500000000 : ℝ)|=(105183361/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393033943/10000000000 : ℝ)|^521 ≤ (4410535073989/10000000000000 : ℝ)^393
        have hw : |(5393033943/10000000000 : ℝ)|=(5393033943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1143_s6_6 (p : ℝ) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2656213989/5000000000 : ℝ)*x 0 + (1348258461/2500000000 : ℝ)*x 1 + (-525916821/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656213989/5000000000 : ℝ)^521 ≤ (43233567460293/100000000000000 : ℝ)^393 := by
    have hnat : (2656213989 : ℕ)^521*100000000000000^393 ≤ 43233567460293^393*5000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656213989 5000000000 43233567460293 100000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348258461/2500000000 : ℝ)^521 ≤ (44105349666547/100000000000000 : ℝ)^393 := by
    have hnat : (1348258461 : ℕ)^521*100000000000000^393 ≤ 44105349666547^393*2500000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348258461 2500000000 44105349666547 100000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (525916821/2500000000 : ℝ)^521 ≤ (12661082868161/100000000000000 : ℝ)^393 := by
    have hnat : (525916821 : ℕ)^521*100000000000000^393 ≤ 12661082868161^393*2500000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525916821 2500000000 12661082868161 100000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (521/128 : ℝ)) 521 393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656213989/5000000000 : ℝ), (1348258461/2500000000 : ℝ), (-525916821/2500000000 : ℝ)] ![(43233567460293/100000000000000 : ℝ), (44105349666547/100000000000000 : ℝ), (12661082868161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656213989/5000000000 : ℝ)|^521 ≤ (43233567460293/100000000000000 : ℝ)^393
        have hw : |(2656213989/5000000000 : ℝ)|=(2656213989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348258461/2500000000 : ℝ)|^521 ≤ (44105349666547/100000000000000 : ℝ)^393
        have hw : |(1348258461/2500000000 : ℝ)|=(1348258461/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-525916821/2500000000 : ℝ)|^521 ≤ (12661082868161/100000000000000 : ℝ)^393
        have hw : |(-525916821/2500000000 : ℝ)|=(525916821/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1143_s6_7 (p : ℝ) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4364525111/10000000000 : ℝ)*x 0 + (4492995407/10000000000 : ℝ)*x 1 + (4239730169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4364525111/10000000000 : ℝ)^521 ≤ (33316898665127/100000000000000 : ℝ)^393 := by
    have hnat : (4364525111 : ℕ)^521*100000000000000^393 ≤ 33316898665127^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4364525111 10000000000 33316898665127 100000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4492995407/10000000000 : ℝ)^521 ≤ (6924637218299/20000000000000 : ℝ)^393 := by
    have hnat : (4492995407 : ℕ)^521*20000000000000^393 ≤ 6924637218299^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4492995407 10000000000 6924637218299 20000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4239730169/10000000000 : ℝ)^521 ≤ (32059915232951/100000000000000 : ℝ)^393 := by
    have hnat : (4239730169 : ℕ)^521*100000000000000^393 ≤ 32059915232951^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4239730169 10000000000 32059915232951 100000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (521/128 : ℝ)) 521 393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4364525111/10000000000 : ℝ), (4492995407/10000000000 : ℝ), (4239730169/10000000000 : ℝ)] ![(33316898665127/100000000000000 : ℝ), (6924637218299/20000000000000 : ℝ), (32059915232951/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4364525111/10000000000 : ℝ)|^521 ≤ (33316898665127/100000000000000 : ℝ)^393
        have hw : |(4364525111/10000000000 : ℝ)|=(4364525111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4492995407/10000000000 : ℝ)|^521 ≤ (6924637218299/20000000000000 : ℝ)^393
        have hw : |(4492995407/10000000000 : ℝ)|=(4492995407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4239730169/10000000000 : ℝ)|^521 ≤ (32059915232951/100000000000000 : ℝ)^393
        have hw : |(4239730169/10000000000 : ℝ)|=(4239730169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1143_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7474661/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14089/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11317/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11347/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14057/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14089/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11317/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14089/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11317/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14089/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11317/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14089/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11317/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14089/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11317/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14089/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11317/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11317/100000 : ℝ) ^ (8335/2048 : ℝ) ≤ (14088111881783339/100000000000000000000 : ℝ) := by
    have hpowers : (11317/100000 : ℝ)^8335 ≤ (14088111881783339/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11317 : ℕ)^8335*100000000000000000000^2048 ≤ 14088111881783339^2048*100000^8335 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11317 100000 14088111881783339 100000000000000000000 8335 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11317/100000 : ℝ)) (X := (14088111881783339/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8335 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14089/100000 : ℝ) ^ (8335/2048 : ℝ) ≤ (34363065446903897/100000000000000000000 : ℝ) := by
    have hpowers : (14089/100000 : ℝ)^8335 ≤ (34363065446903897/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14089 : ℕ)^8335*100000000000000000000^2048 ≤ 34363065446903897^2048*100000^8335 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14089 100000 34363065446903897 100000000000000000000 8335 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14089/100000 : ℝ)) (X := (34363065446903897/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8335 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014088111881783339/50000000000000000000 : ℝ) ≤ (5000346123426877/5000000000000000 : ℝ) ^ (8335/2048 : ℝ) := by
    have hpowers : (50014088111881783339/50000000000000000000 : ℝ)^2048 ≤ (5000346123426877/5000000000000000 : ℝ)^8335 := by
      have hnat : (50014088111881783339 : ℕ)^2048*5000000000000000^8335 ≤ 5000346123426877^8335*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014088111881783339 50000000000000000000 5000346123426877 5000000000000000 2048 8335 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000346123426877/5000000000000000 : ℝ)) (X := (50014088111881783339/50000000000000000000 : ℝ)) (by norm_num) 8335 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25012112794332171809/25000000000000000000 : ℝ) ≤ (10001190280555159/10000000000000000 : ℝ) ^ (8335/2048 : ℝ) := by
    have hpowers : (25012112794332171809/25000000000000000000 : ℝ)^2048 ≤ (10001190280555159/10000000000000000 : ℝ)^8335 := by
      have hnat : (25012112794332171809 : ℕ)^2048*10000000000000000^8335 ≤ 10001190280555159^8335*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012112794332171809 25000000000000000000 10001190280555159 10000000000000000 2048 8335 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001190280555159/10000000000000000 : ℝ)) (X := (25012112794332171809/25000000000000000000 : ℝ)) (by norm_num) 8335 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034363065446903897/50000000000000000000 : ℝ) ≤ (2500422078564141/2500000000000000 : ℝ) ^ (8335/2048 : ℝ) := by
    have hpowers : (50034363065446903897/50000000000000000000 : ℝ)^2048 ≤ (2500422078564141/2500000000000000 : ℝ)^8335 := by
      have hnat : (50034363065446903897 : ℕ)^2048*2500000000000000^8335 ≤ 2500422078564141^8335*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034363065446903897 50000000000000000000 2500422078564141 2500000000000000 2048 8335 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500422078564141/2500000000000000 : ℝ)) (X := (50034363065446903897/50000000000000000000 : ℝ)) (by norm_num) 8335 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14088111881783339/100000000000000000000 : ℝ) ≤ ((13855323206740502659/13860000000000000000 : ℝ)+2*(99606740281/55440000000000 : ℝ)*(11317/100000 : ℝ))^(8335/2048 : ℝ) := by
    rw [show (13855323206740502659/13860000000000000000 : ℝ)+2*(99606740281/55440000000000 : ℝ)*(11317/100000 : ℝ)=(5000346123426877/5000000000000000 : ℝ) by norm_num, show 1+2*(14088111881783339/100000000000000000000 : ℝ)=(50014088111881783339/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34363065446903897/100000000000000000000 : ℝ)+(14088111881783339/100000000000000000000 : ℝ) ≤ ((13855323206740502659/13860000000000000000 : ℝ)+(99606740281/55440000000000 : ℝ)*((14089/100000 : ℝ)+(11317/100000 : ℝ)))^(8335/2048 : ℝ) := by
    rw [show (13855323206740502659/13860000000000000000 : ℝ)+(99606740281/55440000000000 : ℝ)*((14089/100000 : ℝ)+(11317/100000 : ℝ))=(10001190280555159/10000000000000000 : ℝ) by norm_num, show 1+(34363065446903897/100000000000000000000 : ℝ)+(14088111881783339/100000000000000000000 : ℝ)=(25012112794332171809/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34363065446903897/100000000000000000000 : ℝ) ≤ ((13855323206740502659/13860000000000000000 : ℝ)+2*(99606740281/55440000000000 : ℝ)*(14089/100000 : ℝ))^(8335/2048 : ℝ) := by
    rw [show (13855323206740502659/13860000000000000000 : ℝ)+2*(99606740281/55440000000000 : ℝ)*(14089/100000 : ℝ)=(2500422078564141/2500000000000000 : ℝ) by norm_num, show 1+2*(34363065446903897/100000000000000000000 : ℝ)=(50034363065446903897/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13855323206740502659/13860000000000000000 : ℝ)*(X 1 0+X 2 0)+(99606740281/55440000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8335/2048 : ℝ)) (lo := (11317/100000 : ℝ)) (hi := (14089/100000 : ℝ)) (c := (13855323206740502659/13860000000000000000 : ℝ)) (alpha := (99606740281/55440000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13855323206740502659/13860000000000000000 : ℝ)*(X 0 1+X 2 1)+(99606740281/55440000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8335/2048 : ℝ)) (lo := (11317/100000 : ℝ)) (hi := (14089/100000 : ℝ)) (c := (13855323206740502659/13860000000000000000 : ℝ)) (alpha := (99606740281/55440000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13855323206740502659/13860000000000000000 : ℝ)*(X 0 2+X 1 2)+(99606740281/55440000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8335/2048 : ℝ)) (lo := (11317/100000 : ℝ)) (hi := (14089/100000 : ℝ)) (c := (13855323206740502659/13860000000000000000 : ℝ)) (alpha := (99606740281/55440000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2166377583/10000000000 : ℝ)*X 0 0+(2696679129/5000000000 : ℝ)*X 0 1+(1053086653/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1143_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672420351/5000000000 : ℝ)*X 1 0+(-1115633921/5000000000 : ℝ)*X 1 1+(329089579/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1143_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344840659/10000000000 : ℝ)*X 2 0+(5265433299/10000000000 : ℝ)*X 2 1+(-2231267853/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1143_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2182257677/5000000000 : ℝ)*X 0 0+(4239084887/10000000000 : ℝ)*X 0 1+(4493638243/10000000000 : ℝ)*X 0 2+(2182257677/5000000000 : ℝ)*X 1 0+(4239084887/10000000000 : ℝ)*X 1 1+(4493638243/10000000000 : ℝ)*X 1 2+(2182257677/5000000000 : ℝ)*X 2 0+(4239084887/10000000000 : ℝ)*X 2 1+(4493638243/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1143_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1083191299/5000000000 : ℝ)*X 0 0+(5265756307/10000000000 : ℝ)*X 0 1+(5393033999/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1143_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328106981/2500000000 : ℝ)*X 1 0+(-105183361/500000000 : ℝ)*X 1 1+(5393033943/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1143_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656213989/5000000000 : ℝ)*X 2 0+(1348258461/2500000000 : ℝ)*X 2 1+(-525916821/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1143_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4364525111/10000000000 : ℝ)*X 0 0+(4492995407/10000000000 : ℝ)*X 0 1+(4239730169/10000000000 : ℝ)*X 0 2+(4364525111/10000000000 : ℝ)*X 1 0+(4492995407/10000000000 : ℝ)*X 1 1+(4239730169/10000000000 : ℝ)*X 1 2+(4364525111/10000000000 : ℝ)*X 2 0+(4492995407/10000000000 : ℝ)*X 2 1+(4239730169/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1143_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (459187602337796014059117247/46200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2177329281/100000000000000 : ℝ)*(base19) + (1924654319/100000000000000 : ℝ)*(base23) + (50718387/50000000000000 : ℝ)*(lower2) + (35231139/12500000000000 : ℝ)*(upper3) + (112175477/100000000000000 : ℝ)*(upper5) + (1174571507566489/20000000000000 : ℝ)*(major0) + (1174571507566489/20000000000000 : ℝ)*(major1) + (1174571507566489/20000000000000 : ℝ)*(major2) + (1563429028276727/20000000000000 : ℝ)*(sp0) + (488575100202181/6250000000000 : ℝ)*(sp1) + (7817201855909859/100000000000000 : ℝ)*(sp2) + (3928478084183597/100000000000000 : ℝ)*(sp3) + (29319590271/50000000000000 : ℝ)*(sp4) + (16439806459/50000000000000 : ℝ)*(sp7) + (982127740949129/25000000000000 : ℝ)*(f.failure) + (3908601890282089/50000000000000 : ℝ)*(f.sum) + (2324065437467/554400000000000000000000000 : ℝ)*base66 + (3004579586345244251/277200000000000000000000000000000 : ℝ)*base67 + (1350683372744844251/277200000000000000000000000000000 : ℝ)*base69 + (2452503398574444251/277200000000000000000000000000000 : ℝ)*base71 + (7577209213169/2772000000000000000000000000 : ℝ)*base73 + (5496731947135644251/277200000000000000000000000000000 : ℝ)*base75 + (563490709903644251/277200000000000000000000000000000 : ℝ)*base77 + (288155797712844251/277200000000000000000000000000000 : ℝ)*base79 + (4275609850147/2772000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1270269/125000000000000000000 : ℝ)*base89 + (1270269/125000000000000000000 : ℝ)*base91 + (1270269/125000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (187665536852527473618115247/38500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (252610543/25000000000000 : ℝ)*(base19) + (138691521/12500000000000 : ℝ)*(base23) + (22711147/100000000000000 : ℝ)*(upper2) + (18914407/25000000000000 : ℝ)*(upper3) + (114796631/100000000000000 : ℝ)*(upper5) + (5902633626657401/100000000000000 : ℝ)*(major0) + (5902633626657401/100000000000000 : ℝ)*(major1) + (5902633626657401/100000000000000 : ℝ)*(major2) + (542083883/2000000000000 : ℝ)*(sp1) + (4649723417/20000000000000 : ℝ)*(sp2) + (7856838107460921/100000000000000 : ℝ)*(sp4) + (7856809992824599/100000000000000 : ℝ)*(sp5) + (1964203437327917/25000000000000 : ℝ)*(sp6) + (987107245843223/25000000000000 : ℝ)*(sp7) + (987107245843223/25000000000000 : ℝ)*(f.failure) + (7856838107460921/100000000000000 : ℝ)*(f.sum) + (12404938970407/2772000000000000000000000000 : ℝ)*base66 + (2847003685816779259/1386000000000000000000000000000000 : ℝ)*base67 + (2907039120079220741/1386000000000000000000000000000000 : ℝ)*base70 + (1094959703974779259/1386000000000000000000000000000000 : ℝ)*base71 + (5924634633473/2772000000000000000000000000 : ℝ)*base73 + (336593980012779259/1386000000000000000000000000000000 : ℝ)*base75 + (18332488491376779259/1386000000000000000000000000000000 : ℝ)*base77 + (11473985412256779259/1386000000000000000000000000000000 : ℝ)*base79 + (18613670882251/2772000000000000000000000000 : ℝ)*base82 + (177597/125000000000000000000 : ℝ)*base90 + (177597/125000000000000000000 : ℝ)*base92 + (177597/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1143_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7474661/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14089/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11317/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11347/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14057/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1143_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1143_s7_0 (p : ℝ) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2166407039/10000000000 : ℝ)*x 0 + (2696520613/5000000000 : ℝ)*x 1 + (2632865361/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2166407039/10000000000 : ℝ)^521 ≤ (263281752251/2000000000000 : ℝ)^393 := by
    have hnat : (2166407039 : ℕ)^521*2000000000000^393 ≤ 263281752251^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2166407039 10000000000 263281752251 2000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696520613/5000000000 : ℝ)^521 ≤ (11026357425271/25000000000000 : ℝ)^393 := by
    have hnat : (2696520613 : ℕ)^521*25000000000000^393 ≤ 11026357425271^393*5000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696520613 5000000000 11026357425271 25000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632865361/5000000000 : ℝ)^521 ≤ (10682620667381/25000000000000 : ℝ)^393 := by
    have hnat : (2632865361 : ℕ)^521*25000000000000^393 ≤ 10682620667381^393*5000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632865361 5000000000 10682620667381 25000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (521/128 : ℝ)) 521 393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2166407039/10000000000 : ℝ), (2696520613/5000000000 : ℝ), (2632865361/5000000000 : ℝ)] ![(263281752251/2000000000000 : ℝ), (11026357425271/25000000000000 : ℝ), (10682620667381/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2166407039/10000000000 : ℝ)|^521 ≤ (263281752251/2000000000000 : ℝ)^393
        have hw : |(-2166407039/10000000000 : ℝ)|=(2166407039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696520613/5000000000 : ℝ)|^521 ≤ (11026357425271/25000000000000 : ℝ)^393
        have hw : |(2696520613/5000000000 : ℝ)|=(2696520613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632865361/5000000000 : ℝ)|^521 ≤ (10682620667381/25000000000000 : ℝ)^393
        have hw : |(2632865361/5000000000 : ℝ)|=(2632865361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1143_s7_1 (p : ℝ) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2672380189/5000000000 : ℝ)*x 0 + (-557745233/2500000000 : ℝ)*x 1 + (1316432723/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672380189/5000000000 : ℝ)^521 ≤ (21791370279881/50000000000000 : ℝ)^393 := by
    have hnat : (2672380189 : ℕ)^521*50000000000000^393 ≤ 21791370279881^393*5000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672380189 5000000000 21791370279881 50000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (557745233/2500000000 : ℝ)^521 ≤ (1710846864911/12500000000000 : ℝ)^393 := by
    have hnat : (557745233 : ℕ)^521*12500000000000^393 ≤ 1710846864911^393*2500000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      557745233 2500000000 1710846864911 12500000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316432723/2500000000 : ℝ)^521 ≤ (21365242249177/50000000000000 : ℝ)^393 := by
    have hnat : (1316432723 : ℕ)^521*50000000000000^393 ≤ 21365242249177^393*2500000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316432723 2500000000 21365242249177 50000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (521/128 : ℝ)) 521 393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672380189/5000000000 : ℝ), (-557745233/2500000000 : ℝ), (1316432723/2500000000 : ℝ)] ![(21791370279881/50000000000000 : ℝ), (1710846864911/12500000000000 : ℝ), (21365242249177/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672380189/5000000000 : ℝ)|^521 ≤ (21791370279881/50000000000000 : ℝ)^393
        have hw : |(2672380189/5000000000 : ℝ)|=(2672380189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-557745233/2500000000 : ℝ)|^521 ≤ (1710846864911/12500000000000 : ℝ)^393
        have hw : |(-557745233/2500000000 : ℝ)|=(557745233/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316432723/2500000000 : ℝ)|^521 ≤ (21365242249177/50000000000000 : ℝ)^393
        have hw : |(1316432723/2500000000 : ℝ)|=(1316432723/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1143_s7_2 (p : ℝ) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5344760479/10000000000 : ℝ)*x 0 + (1316432697/2500000000 : ℝ)*x 1 + (-2230980937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344760479/10000000000 : ℝ)^521 ≤ (21791370825793/50000000000000 : ℝ)^393 := by
    have hnat : (5344760479 : ℕ)^521*50000000000000^393 ≤ 21791370825793^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344760479 10000000000 21791370825793 50000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316432697/2500000000 : ℝ)^521 ≤ (2136524168977/5000000000000 : ℝ)^393 := by
    have hnat : (1316432697 : ℕ)^521*5000000000000^393 ≤ 2136524168977^393*2500000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316432697 2500000000 2136524168977 5000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2230980937/10000000000 : ℝ)^521 ≤ (13686774959953/100000000000000 : ℝ)^393 := by
    have hnat : (2230980937 : ℕ)^521*100000000000000^393 ≤ 13686774959953^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2230980937 10000000000 13686774959953 100000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (521/128 : ℝ)) 521 393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344760479/10000000000 : ℝ), (1316432697/2500000000 : ℝ), (-2230980937/10000000000 : ℝ)] ![(21791370825793/50000000000000 : ℝ), (2136524168977/5000000000000 : ℝ), (13686774959953/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344760479/10000000000 : ℝ)|^521 ≤ (21791370825793/50000000000000 : ℝ)^393
        have hw : |(5344760479/10000000000 : ℝ)|=(5344760479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316432697/2500000000 : ℝ)|^521 ≤ (2136524168977/5000000000000 : ℝ)^393
        have hw : |(1316432697/2500000000 : ℝ)|=(1316432697/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2230980937/10000000000 : ℝ)|^521 ≤ (13686774959953/100000000000000 : ℝ)^393
        have hw : |(-2230980937/10000000000 : ℝ)|=(2230980937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1143_s7_3 (p : ℝ) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2182265577/5000000000 : ℝ)*x 0 + (4239694153/10000000000 : ℝ)*x 1 + (4493024763/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2182265577/5000000000 : ℝ)^521 ≤ (33316959819207/100000000000000 : ℝ)^393 := by
    have hnat : (2182265577 : ℕ)^521*100000000000000^393 ≤ 33316959819207^393*5000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182265577 5000000000 33316959819207 100000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4239694153/10000000000 : ℝ)^521 ≤ (32059554185567/100000000000000 : ℝ)^393 := by
    have hnat : (4239694153 : ℕ)^521*100000000000000^393 ≤ 32059554185567^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4239694153 10000000000 32059554185567 100000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4493024763/10000000000 : ℝ)^521 ≤ (6924697197899/20000000000000 : ℝ)^393 := by
    have hnat : (4493024763 : ℕ)^521*20000000000000^393 ≤ 6924697197899^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4493024763 10000000000 6924697197899 20000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (521/128 : ℝ)) 521 393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2182265577/5000000000 : ℝ), (4239694153/10000000000 : ℝ), (4493024763/10000000000 : ℝ)] ![(33316959819207/100000000000000 : ℝ), (32059554185567/100000000000000 : ℝ), (6924697197899/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2182265577/5000000000 : ℝ)|^521 ≤ (33316959819207/100000000000000 : ℝ)^393
        have hw : |(2182265577/5000000000 : ℝ)|=(2182265577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4239694153/10000000000 : ℝ)|^521 ≤ (32059554185567/100000000000000 : ℝ)^393
        have hw : |(4239694153/10000000000 : ℝ)|=(4239694153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4493024763/10000000000 : ℝ)|^521 ≤ (6924697197899/20000000000000 : ℝ)^393
        have hw : |(4493024763/10000000000 : ℝ)|=(4493024763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1143_s7_4 (p : ℝ) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-21664117/100000000 : ℝ)*x 0 + (2633025419/5000000000 : ℝ)*x 1 + (2696360061/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21664117/100000000 : ℝ)^521 ≤ (658206257977/5000000000000 : ℝ)^393 := by
    have hnat : (21664117 : ℕ)^521*5000000000000^393 ≤ 658206257977^393*100000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21664117 100000000 658206257977 5000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633025419/5000000000 : ℝ)^521 ≤ (42733926454333/100000000000000 : ℝ)^393 := by
    have hnat : (2633025419 : ℕ)^521*100000000000000^393 ≤ 42733926454333^393*5000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633025419 5000000000 42733926454333 100000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696360061/5000000000 : ℝ)^521 ≤ (44101948372669/100000000000000 : ℝ)^393 := by
    have hnat : (2696360061 : ℕ)^521*100000000000000^393 ≤ 44101948372669^393*5000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696360061 5000000000 44101948372669 100000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (521/128 : ℝ)) 521 393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-21664117/100000000 : ℝ), (2633025419/5000000000 : ℝ), (2696360061/5000000000 : ℝ)] ![(658206257977/5000000000000 : ℝ), (42733926454333/100000000000000 : ℝ), (44101948372669/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-21664117/100000000 : ℝ)|^521 ≤ (658206257977/5000000000000 : ℝ)^393
        have hw : |(-21664117/100000000 : ℝ)|=(21664117/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633025419/5000000000 : ℝ)|^521 ≤ (42733926454333/100000000000000 : ℝ)^393
        have hw : |(2633025419/5000000000 : ℝ)|=(2633025419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696360061/5000000000 : ℝ)|^521 ≤ (44101948372669/100000000000000 : ℝ)^393
        have hw : |(2696360061/5000000000 : ℝ)|=(2696360061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1143_s7_5 (p : ℝ) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5312503303/10000000000 : ℝ)*x 0 + (-1051995849/5000000000 : ℝ)*x 1 + (5392720131/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312503303/10000000000 : ℝ)^521 ≤ (2161719006431/5000000000000 : ℝ)^393 := by
    have hnat : (5312503303 : ℕ)^521*5000000000000^393 ≤ 2161719006431^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312503303 10000000000 2161719006431 5000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1051995849/5000000000 : ℝ)^521 ≤ (6331835687943/50000000000000 : ℝ)^393 := by
    have hnat : (1051995849 : ℕ)^521*50000000000000^393 ≤ 6331835687943^393*5000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051995849 5000000000 6331835687943 50000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392720131/10000000000 : ℝ)^521 ≤ (11025487117561/25000000000000 : ℝ)^393 := by
    have hnat : (5392720131 : ℕ)^521*25000000000000^393 ≤ 11025487117561^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392720131 10000000000 11025487117561 25000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (521/128 : ℝ)) 521 393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312503303/10000000000 : ℝ), (-1051995849/5000000000 : ℝ), (5392720131/10000000000 : ℝ)] ![(2161719006431/5000000000000 : ℝ), (6331835687943/50000000000000 : ℝ), (11025487117561/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312503303/10000000000 : ℝ)|^521 ≤ (2161719006431/5000000000000 : ℝ)^393
        have hw : |(5312503303/10000000000 : ℝ)|=(5312503303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1051995849/5000000000 : ℝ)|^521 ≤ (6331835687943/50000000000000 : ℝ)^393
        have hw : |(-1051995849/5000000000 : ℝ)|=(1051995849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392720131/10000000000 : ℝ)|^521 ≤ (11025487117561/25000000000000 : ℝ)^393
        have hw : |(5392720131/10000000000 : ℝ)|=(5392720131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1143_s7_6 (p : ℝ) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5312503303/10000000000 : ℝ)*x 0 + (1348180033/2500000000 : ℝ)*x 1 + (-2103991697/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312503303/10000000000 : ℝ)^521 ≤ (2161719006431/5000000000000 : ℝ)^393 := by
    have hnat : (5312503303 : ℕ)^521*5000000000000^393 ≤ 2161719006431^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312503303 10000000000 2161719006431 5000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348180033/2500000000 : ℝ)^521 ≤ (8820389696217/20000000000000 : ℝ)^393 := by
    have hnat : (1348180033 : ℕ)^521*20000000000000^393 ≤ 8820389696217^393*2500000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348180033 2500000000 8820389696217 20000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2103991697/10000000000 : ℝ)^521 ≤ (6331835683953/50000000000000 : ℝ)^393 := by
    have hnat : (2103991697 : ℕ)^521*50000000000000^393 ≤ 6331835683953^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2103991697 10000000000 6331835683953 50000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (521/128 : ℝ)) 521 393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312503303/10000000000 : ℝ), (1348180033/2500000000 : ℝ), (-2103991697/10000000000 : ℝ)] ![(2161719006431/5000000000000 : ℝ), (8820389696217/20000000000000 : ℝ), (6331835683953/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312503303/10000000000 : ℝ)|^521 ≤ (2161719006431/5000000000000 : ℝ)^393
        have hw : |(5312503303/10000000000 : ℝ)|=(5312503303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348180033/2500000000 : ℝ)|^521 ≤ (8820389696217/20000000000000 : ℝ)^393
        have hw : |(1348180033/2500000000 : ℝ)|=(1348180033/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2103991697/10000000000 : ℝ)|^521 ≤ (6331835683953/50000000000000 : ℝ)^393
        have hw : |(-2103991697/10000000000 : ℝ)|=(2103991697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1143_s7_7 (p : ℝ) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2182270351/5000000000 : ℝ)*x 0 + (2246194027/5000000000 : ℝ)*x 1 + (4240333341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2182270351/5000000000 : ℝ)^521 ≤ (8329264110829/25000000000000 : ℝ)^393 := by
    have hnat : (2182270351 : ℕ)^521*25000000000000^393 ≤ 8329264110829^393*5000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182270351 5000000000 8329264110829 25000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2246194027/5000000000 : ℝ)^521 ≤ (17308490788179/50000000000000 : ℝ)^393 := by
    have hnat : (2246194027 : ℕ)^521*50000000000000^393 ≤ 17308490788179^393*5000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246194027 5000000000 17308490788179 50000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4240333341/10000000000 : ℝ)^521 ≤ (8016490490677/25000000000000 : ℝ)^393 := by
    have hnat : (4240333341 : ℕ)^521*25000000000000^393 ≤ 8016490490677^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4240333341 10000000000 8016490490677 25000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (521/128 : ℝ)) 521 393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2182270351/5000000000 : ℝ), (2246194027/5000000000 : ℝ), (4240333341/10000000000 : ℝ)] ![(8329264110829/25000000000000 : ℝ), (17308490788179/50000000000000 : ℝ), (8016490490677/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2182270351/5000000000 : ℝ)|^521 ≤ (8329264110829/25000000000000 : ℝ)^393
        have hw : |(2182270351/5000000000 : ℝ)|=(2182270351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2246194027/5000000000 : ℝ)|^521 ≤ (17308490788179/50000000000000 : ℝ)^393
        have hw : |(2246194027/5000000000 : ℝ)|=(2246194027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4240333341/10000000000 : ℝ)|^521 ≤ (8016490490677/25000000000000 : ℝ)^393
        have hw : |(4240333341/10000000000 : ℝ)|=(4240333341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1143_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7474661/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14057/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11347/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5677/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14051/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14057/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11347/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14057/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11347/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14057/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11347/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14057/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11347/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14057/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11347/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14057/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11347/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11347/100000 : ℝ) ^ (8335/2048 : ℝ) ≤ (569628904963059/4000000000000000000 : ℝ) := by
    have hpowers : (11347/100000 : ℝ)^8335 ≤ (569628904963059/4000000000000000000 : ℝ)^2048 := by
      have hnat : (11347 : ℕ)^8335*4000000000000000000^2048 ≤ 569628904963059^2048*100000^8335 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11347 100000 569628904963059 4000000000000000000 8335 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11347/100000 : ℝ)) (X := (569628904963059/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8335 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14057/100000 : ℝ) ^ (8335/2048 : ℝ) ≤ (2127908093005541/6250000000000000000 : ℝ) := by
    have hpowers : (14057/100000 : ℝ)^8335 ≤ (2127908093005541/6250000000000000000 : ℝ)^2048 := by
      have hnat : (14057 : ℕ)^8335*6250000000000000000^2048 ≤ 2127908093005541^2048*100000^8335 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14057 100000 2127908093005541 6250000000000000000 8335 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14057/100000 : ℝ)) (X := (2127908093005541/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 8335 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000569628904963059/2000000000000000000 : ℝ) ≤ (1250087468109363/1250000000000000 : ℝ) ^ (8335/2048 : ℝ) := by
    have hpowers : (2000569628904963059/2000000000000000000 : ℝ)^2048 ≤ (1250087468109363/1250000000000000 : ℝ)^8335 := by
      have hnat : (2000569628904963059 : ℕ)^2048*1250000000000000^8335 ≤ 1250087468109363^8335*2000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000569628904963059 2000000000000000000 1250087468109363 1250000000000000 2048 8335 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250087468109363/1250000000000000 : ℝ)) (X := (2000569628904963059/2000000000000000000 : ℝ)) (by norm_num) 8335 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048287252112165131/100000000000000000000 : ℝ) ≤ (625074140887719/625000000000000 : ℝ) ^ (8335/2048 : ℝ) := by
    have hpowers : (100048287252112165131/100000000000000000000 : ℝ)^2048 ≤ (625074140887719/625000000000000 : ℝ)^8335 := by
      have hnat : (100048287252112165131 : ℕ)^2048*625000000000000^8335 ≤ 625074140887719^8335*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048287252112165131 100000000000000000000 625074140887719 625000000000000 2048 8335 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625074140887719/625000000000000 : ℝ)) (X := (100048287252112165131/100000000000000000000 : ℝ)) (by norm_num) 8335 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (3127127908093005541/3125000000000000000 : ℝ) ≤ (1250209095441513/1250000000000000 : ℝ) ^ (8335/2048 : ℝ) := by
    have hpowers : (3127127908093005541/3125000000000000000 : ℝ)^2048 ≤ (1250209095441513/1250000000000000 : ℝ)^8335 := by
      have hnat : (3127127908093005541 : ℕ)^2048*1250000000000000^8335 ≤ 1250209095441513^8335*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3127127908093005541 3125000000000000000 1250209095441513 1250000000000000 2048 8335 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250209095441513/1250000000000000 : ℝ)) (X := (3127127908093005541/3125000000000000000 : ℝ)) (by norm_num) 8335 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(569628904963059/4000000000000000000 : ℝ) ≤ ((21164730832740423/21171875000000000 : ℝ)+2*(2432546643/1355000000000 : ℝ)*(11347/100000 : ℝ))^(8335/2048 : ℝ) := by
    rw [show (21164730832740423/21171875000000000 : ℝ)+2*(2432546643/1355000000000 : ℝ)*(11347/100000 : ℝ)=(1250087468109363/1250000000000000 : ℝ) by norm_num, show 1+2*(569628904963059/4000000000000000000 : ℝ)=(2000569628904963059/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2127908093005541/6250000000000000000 : ℝ)+(569628904963059/4000000000000000000 : ℝ) ≤ ((21164730832740423/21171875000000000 : ℝ)+(2432546643/1355000000000 : ℝ)*((14057/100000 : ℝ)+(11347/100000 : ℝ)))^(8335/2048 : ℝ) := by
    rw [show (21164730832740423/21171875000000000 : ℝ)+(2432546643/1355000000000 : ℝ)*((14057/100000 : ℝ)+(11347/100000 : ℝ))=(625074140887719/625000000000000 : ℝ) by norm_num, show 1+(2127908093005541/6250000000000000000 : ℝ)+(569628904963059/4000000000000000000 : ℝ)=(100048287252112165131/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2127908093005541/6250000000000000000 : ℝ) ≤ ((21164730832740423/21171875000000000 : ℝ)+2*(2432546643/1355000000000 : ℝ)*(14057/100000 : ℝ))^(8335/2048 : ℝ) := by
    rw [show (21164730832740423/21171875000000000 : ℝ)+2*(2432546643/1355000000000 : ℝ)*(14057/100000 : ℝ)=(1250209095441513/1250000000000000 : ℝ) by norm_num, show 1+2*(2127908093005541/6250000000000000000 : ℝ)=(3127127908093005541/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (21164730832740423/21171875000000000 : ℝ)*(X 1 0+X 2 0)+(2432546643/1355000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8335/2048 : ℝ)) (lo := (11347/100000 : ℝ)) (hi := (14057/100000 : ℝ)) (c := (21164730832740423/21171875000000000 : ℝ)) (alpha := (2432546643/1355000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (21164730832740423/21171875000000000 : ℝ)*(X 0 1+X 2 1)+(2432546643/1355000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8335/2048 : ℝ)) (lo := (11347/100000 : ℝ)) (hi := (14057/100000 : ℝ)) (c := (21164730832740423/21171875000000000 : ℝ)) (alpha := (2432546643/1355000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (21164730832740423/21171875000000000 : ℝ)*(X 0 2+X 1 2)+(2432546643/1355000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8335/2048 : ℝ)) (lo := (11347/100000 : ℝ)) (hi := (14057/100000 : ℝ)) (c := (21164730832740423/21171875000000000 : ℝ)) (alpha := (2432546643/1355000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2166407039/10000000000 : ℝ)*X 0 0+(2696520613/5000000000 : ℝ)*X 0 1+(2632865361/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1143_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672380189/5000000000 : ℝ)*X 1 0+(-557745233/2500000000 : ℝ)*X 1 1+(1316432723/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1143_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344760479/10000000000 : ℝ)*X 2 0+(1316432697/2500000000 : ℝ)*X 2 1+(-2230980937/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1143_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2182265577/5000000000 : ℝ)*X 0 0+(4239694153/10000000000 : ℝ)*X 0 1+(4493024763/10000000000 : ℝ)*X 0 2+(2182265577/5000000000 : ℝ)*X 1 0+(4239694153/10000000000 : ℝ)*X 1 1+(4493024763/10000000000 : ℝ)*X 1 2+(2182265577/5000000000 : ℝ)*X 2 0+(4239694153/10000000000 : ℝ)*X 2 1+(4493024763/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1143_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-21664117/100000000 : ℝ)*X 0 0+(2633025419/5000000000 : ℝ)*X 0 1+(2696360061/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1143_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312503303/10000000000 : ℝ)*X 1 0+(-1051995849/5000000000 : ℝ)*X 1 1+(5392720131/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1143_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312503303/10000000000 : ℝ)*X 2 0+(1348180033/2500000000 : ℝ)*X 2 1+(-2103991697/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1143_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2182270351/5000000000 : ℝ)*X 0 0+(2246194027/5000000000 : ℝ)*X 0 1+(4240333341/10000000000 : ℝ)*X 0 2+(2182270351/5000000000 : ℝ)*X 1 0+(2246194027/5000000000 : ℝ)*X 1 1+(4240333341/10000000000 : ℝ)*X 1 2+(2182270351/5000000000 : ℝ)*X 2 0+(2246194027/5000000000 : ℝ)*X 2 1+(4240333341/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1143_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10637183088162109342740453/4234375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1211006433/100000000000000 : ℝ)*(base19) + (30181987/2500000000000 : ℝ)*(base23) + (218277121/100000000000000 : ℝ)*(upper3) + (20331583/25000000000000 : ℝ)*(upper4) + (6446817/5000000000000 : ℝ)*(upper5) + (2950584488833011/50000000000000 : ℝ)*(major0) + (2950584488833011/50000000000000 : ℝ)*(major1) + (2950584488833011/50000000000000 : ℝ)*(major2) + (7854850156976651/100000000000000 : ℝ)*(sp0) + (196372185499261/2500000000000 : ℝ)*(sp1) + (7854887423697393/100000000000000 : ℝ)*(sp2) + (197371416305211/5000000000000 : ℝ)*(sp3) + (19237000111/50000000000000 : ℝ)*(sp4) + (10457257099/50000000000000 : ℝ)*(sp7) + (1973724620309209/50000000000000 : ℝ)*(f.failure) + (7854888630976873/100000000000000 : ℝ)*(f.sum) + (800340210007/271000000000000000000000000 : ℝ)*base65 + (1255725502054181/2117187500000000000000000000000 : ℝ)*base67 + (8667143415597403/1058593750000000000000000000000 : ℝ)*base69 + (3874089478746347/1058593750000000000000000000000 : ℝ)*base72 + (188818175391/33875000000000000000000000 : ℝ)*base74 + (19841897734679181/2117187500000000000000000000000 : ℝ)*base75 + (66995597784748987/4234375000000000000000000000000 : ℝ)*base77 + (1995052586715097/1058593750000000000000000000000 : ℝ)*base80 + (1258220518543/271000000000000000000000000 : ℝ)*base82 + (2546851/250000000000000000000 : ℝ)*base90 + (2546851/250000000000000000000 : ℝ)*base92 + (2546851/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12031833580885000216503531/1058593750000000000000000000000 : ℝ) := by norm_num
    linear_combination (201767939/10000000000000 : ℝ)*(base19) + (1109087237/50000000000000 : ℝ)*(base23) + (226230817/100000000000000 : ℝ)*(upper3) + (45255643/50000000000000 : ℝ)*(lower4) + (113045101/50000000000000 : ℝ)*(upper5) + (5930981750059463/100000000000000 : ℝ)*(major0) + (5930981750059463/100000000000000 : ℝ)*(major1) + (5930981750059463/100000000000000 : ℝ)*(major2) + (55947705943/100000000000000 : ℝ)*(sp1) + (30454111747/50000000000000 : ℝ)*(sp2) + (493410707652819/6250000000000 : ℝ)*(sp4) + (789451335705977/10000000000000 : ℝ)*(sp5) + (246703381126473/3125000000000 : ℝ)*(sp6) + (1983695899405827/50000000000000 : ℝ)*(sp7) + (1983695899405827/50000000000000 : ℝ)*(f.failure) + (493410707652819/6250000000000 : ℝ)*(f.sum) + (96319507079/33875000000000000000000000 : ℝ)*base66 + (105068749898889/132324218750000000000000000000 : ℝ)*base67 + (5931014659210349/2117187500000000000000000000000 : ℝ)*base69 + (5865684575425487/1058593750000000000000000000000 : ℝ)*base71 + (58314760843/33875000000000000000000000 : ℝ)*base74 + (2271981979612987/1058593750000000000000000000000 : ℝ)*base75 + (4654046833289651/2117187500000000000000000000000 : ℝ)*base78 + (557533285704931/529296875000000000000000000000 : ℝ)*base79 + (253171701403/67750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (749647/250000000000000000000 : ℝ)*base89 + (749647/250000000000000000000 : ℝ)*base91 + (749647/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1143_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7474661/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14057/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11347/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5677/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14051/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1143_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1143_s8_0 (p : ℝ) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1083204137/5000000000 : ℝ)*x 0 + (5392977753/10000000000 : ℝ)*x 1 + (2632896883/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1083204137/5000000000 : ℝ)^521 ≤ (13164097561171/100000000000000 : ℝ)^393 := by
    have hnat : (1083204137 : ℕ)^521*100000000000000^393 ≤ 13164097561171^393*5000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083204137 5000000000 13164097561171 100000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392977753/10000000000 : ℝ)^521 ≤ (22052370768753/50000000000000 : ℝ)^393 := by
    have hnat : (5392977753 : ℕ)^521*50000000000000^393 ≤ 22052370768753^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392977753 10000000000 22052370768753 50000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632896883/5000000000 : ℝ)^521 ≤ (42731160886931/100000000000000 : ℝ)^393 := by
    have hnat : (2632896883 : ℕ)^521*100000000000000^393 ≤ 42731160886931^393*5000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632896883 5000000000 42731160886931 100000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (521/128 : ℝ)) 521 393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1083204137/5000000000 : ℝ), (5392977753/10000000000 : ℝ), (2632896883/5000000000 : ℝ)] ![(13164097561171/100000000000000 : ℝ), (22052370768753/50000000000000 : ℝ), (42731160886931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1083204137/5000000000 : ℝ)|^521 ≤ (13164097561171/100000000000000 : ℝ)^393
        have hw : |(-1083204137/5000000000 : ℝ)|=(1083204137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392977753/10000000000 : ℝ)|^521 ≤ (22052370768753/50000000000000 : ℝ)^393
        have hw : |(5392977753/10000000000 : ℝ)|=(5392977753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632896883/5000000000 : ℝ)|^521 ≤ (42731160886931/100000000000000 : ℝ)^393
        have hw : |(2632896883/5000000000 : ℝ)|=(2632896883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1143_s8_1 (p : ℝ) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5344745611/10000000000 : ℝ)*x 0 + (-1115458697/5000000000 : ℝ)*x 1 + (5265793767/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344745611/10000000000 : ℝ)^521 ≤ (43582580926441/100000000000000 : ℝ)^393 := by
    have hnat : (5344745611 : ℕ)^521*100000000000000^393 ≤ 43582580926441^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344745611 10000000000 43582580926441 100000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1115458697/5000000000 : ℝ)^521 ≤ (13686258167527/100000000000000 : ℝ)^393 := by
    have hnat : (1115458697 : ℕ)^521*100000000000000^393 ≤ 13686258167527^393*5000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1115458697 5000000000 13686258167527 100000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265793767/10000000000 : ℝ)^521 ≤ (42731160897689/100000000000000 : ℝ)^393 := by
    have hnat : (5265793767 : ℕ)^521*100000000000000^393 ≤ 42731160897689^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265793767 10000000000 42731160897689 100000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (521/128 : ℝ)) 521 393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344745611/10000000000 : ℝ), (-1115458697/5000000000 : ℝ), (5265793767/10000000000 : ℝ)] ![(43582580926441/100000000000000 : ℝ), (13686258167527/100000000000000 : ℝ), (42731160897689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344745611/10000000000 : ℝ)|^521 ≤ (43582580926441/100000000000000 : ℝ)^393
        have hw : |(5344745611/10000000000 : ℝ)|=(5344745611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1115458697/5000000000 : ℝ)|^521 ≤ (13686258167527/100000000000000 : ℝ)^393
        have hw : |(-1115458697/5000000000 : ℝ)|=(1115458697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265793767/10000000000 : ℝ)|^521 ≤ (42731160897689/100000000000000 : ℝ)^393
        have hw : |(5265793767/10000000000 : ℝ)|=(5265793767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1143_s8_2 (p : ℝ) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2672372813/5000000000 : ℝ)*x 0 + (5265793751/10000000000 : ℝ)*x 1 + (-1115458697/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672372813/5000000000 : ℝ)^521 ≤ (43582581088593/100000000000000 : ℝ)^393 := by
    have hnat : (2672372813 : ℕ)^521*100000000000000^393 ≤ 43582581088593^393*5000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672372813 5000000000 43582581088593 100000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265793751/10000000000 : ℝ)^521 ≤ (42731160725563/100000000000000 : ℝ)^393 := by
    have hnat : (5265793751 : ℕ)^521*100000000000000^393 ≤ 42731160725563^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265793751 10000000000 42731160725563 100000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1115458697/5000000000 : ℝ)^521 ≤ (13686258167527/100000000000000 : ℝ)^393 := by
    have hnat : (1115458697 : ℕ)^521*100000000000000^393 ≤ 13686258167527^393*5000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1115458697 5000000000 13686258167527 100000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (521/128 : ℝ)) 521 393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672372813/5000000000 : ℝ), (5265793751/10000000000 : ℝ), (-1115458697/5000000000 : ℝ)] ![(43582581088593/100000000000000 : ℝ), (42731160725563/100000000000000 : ℝ), (13686258167527/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672372813/5000000000 : ℝ)|^521 ≤ (43582581088593/100000000000000 : ℝ)^393
        have hw : |(2672372813/5000000000 : ℝ)|=(2672372813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265793751/10000000000 : ℝ)|^521 ≤ (42731160725563/100000000000000 : ℝ)^393
        have hw : |(5265793751/10000000000 : ℝ)|=(5265793751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1115458697/5000000000 : ℝ)|^521 ≤ (13686258167527/100000000000000 : ℝ)^393
        have hw : |(-1115458697/5000000000 : ℝ)|=(1115458697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1143_s8_3 (p : ℝ) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4364534181/10000000000 : ℝ)*x 0 + (4239819689/10000000000 : ℝ)*x 1 + (280806161/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4364534181/10000000000 : ℝ)^521 ≤ (8329247612979/25000000000000 : ℝ)^393 := by
    have hnat : (4364534181 : ℕ)^521*25000000000000^393 ≤ 8329247612979^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4364534181 10000000000 8329247612979 25000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4239819689/10000000000 : ℝ)^521 ≤ (1282432505717/4000000000000 : ℝ)^393 := by
    have hnat : (4239819689 : ℕ)^521*4000000000000^393 ≤ 1282432505717^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4239819689 10000000000 1282432505717 4000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (280806161/625000000 : ℝ)^521 ≤ (8655549220019/25000000000000 : ℝ)^393 := by
    have hnat : (280806161 : ℕ)^521*25000000000000^393 ≤ 8655549220019^393*625000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280806161 625000000 8655549220019 25000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (521/128 : ℝ)) 521 393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4364534181/10000000000 : ℝ), (4239819689/10000000000 : ℝ), (280806161/625000000 : ℝ)] ![(8329247612979/25000000000000 : ℝ), (1282432505717/4000000000000 : ℝ), (8655549220019/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4364534181/10000000000 : ℝ)|^521 ≤ (8329247612979/25000000000000 : ℝ)^393
        have hw : |(4364534181/10000000000 : ℝ)|=(4364534181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4239819689/10000000000 : ℝ)|^521 ≤ (1282432505717/4000000000000 : ℝ)^393
        have hw : |(4239819689/10000000000 : ℝ)|=(4239819689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(280806161/625000000 : ℝ)|^521 ≤ (8655549220019/25000000000000 : ℝ)^393
        have hw : |(280806161/625000000 : ℝ)|=(280806161/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1143_s8_4 (p : ℝ) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2166413063/10000000000 : ℝ)*x 0 + (105322263/200000000 : ℝ)*x 1 + (5392657277/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2166413063/10000000000 : ℝ)^521 ≤ (13164136139281/100000000000000 : ℝ)^393 := by
    have hnat : (2166413063 : ℕ)^521*100000000000000^393 ≤ 13164136139281^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2166413063 10000000000 13164136139281 100000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (105322263/200000000 : ℝ)^521 ≤ (42734596810257/100000000000000 : ℝ)^393 := by
    have hnat : (105322263 : ℕ)^521*100000000000000^393 ≤ 42734596810257^393*200000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105322263 200000000 42734596810257 100000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392657277/10000000000 : ℝ)^521 ≤ (44101267030961/100000000000000 : ℝ)^393 := by
    have hnat : (5392657277 : ℕ)^521*100000000000000^393 ≤ 44101267030961^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392657277 10000000000 44101267030961 100000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (521/128 : ℝ)) 521 393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2166413063/10000000000 : ℝ), (105322263/200000000 : ℝ), (5392657277/10000000000 : ℝ)] ![(13164136139281/100000000000000 : ℝ), (42734596810257/100000000000000 : ℝ), (44101267030961/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2166413063/10000000000 : ℝ)|^521 ≤ (13164136139281/100000000000000 : ℝ)^393
        have hw : |(-2166413063/10000000000 : ℝ)|=(2166413063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(105322263/200000000 : ℝ)|^521 ≤ (42734596810257/100000000000000 : ℝ)^393
        have hw : |(105322263/200000000 : ℝ)|=(105322263/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392657277/10000000000 : ℝ)|^521 ≤ (44101267030961/100000000000000 : ℝ)^393
        have hw : |(5392657277/10000000000 : ℝ)|=(5392657277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1143_s8_5 (p : ℝ) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1328130139/2500000000 : ℝ)*x 0 + (-1052026877/5000000000 : ℝ)*x 1 + (5392657291/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328130139/2500000000 : ℝ)^521 ≤ (8646913253753/20000000000000 : ℝ)^393 := by
    have hnat : (1328130139 : ℕ)^521*20000000000000^393 ≤ 8646913253753^393*2500000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328130139 2500000000 8646913253753 20000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052026877/5000000000 : ℝ)^521 ≤ (3166041634283/25000000000000 : ℝ)^393 := by
    have hnat : (1052026877 : ℕ)^521*25000000000000^393 ≤ 3166041634283^393*5000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052026877 5000000000 3166041634283 25000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392657291/10000000000 : ℝ)^521 ≤ (5512658397843/12500000000000 : ℝ)^393 := by
    have hnat : (5392657291 : ℕ)^521*12500000000000^393 ≤ 5512658397843^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392657291 10000000000 5512658397843 12500000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (521/128 : ℝ)) 521 393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328130139/2500000000 : ℝ), (-1052026877/5000000000 : ℝ), (5392657291/10000000000 : ℝ)] ![(8646913253753/20000000000000 : ℝ), (3166041634283/25000000000000 : ℝ), (5512658397843/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328130139/2500000000 : ℝ)|^521 ≤ (8646913253753/20000000000000 : ℝ)^393
        have hw : |(1328130139/2500000000 : ℝ)|=(1328130139/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1052026877/5000000000 : ℝ)|^521 ≤ (3166041634283/25000000000000 : ℝ)^393
        have hw : |(-1052026877/5000000000 : ℝ)|=(1052026877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392657291/10000000000 : ℝ)|^521 ≤ (5512658397843/12500000000000 : ℝ)^393
        have hw : |(5392657291/10000000000 : ℝ)|=(5392657291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1143_s8_6 (p : ℝ) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5312520401/10000000000 : ℝ)*x 0 + (5392657251/10000000000 : ℝ)*x 1 + (-1052027009/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312520401/10000000000 : ℝ)^521 ≤ (10808641149123/25000000000000 : ℝ)^393 := by
    have hnat : (5312520401 : ℕ)^521*25000000000000^393 ≤ 10808641149123^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312520401 10000000000 10808641149123 25000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392657251/10000000000 : ℝ)^521 ≤ (1102531668727/2500000000000 : ℝ)^393 := by
    have hnat : (5392657251 : ℕ)^521*2500000000000^393 ≤ 1102531668727^393*10000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392657251 10000000000 1102531668727 2500000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052027009/5000000000 : ℝ)^521 ≤ (3166042160917/25000000000000 : ℝ)^393 := by
    have hnat : (1052027009 : ℕ)^521*25000000000000^393 ≤ 3166042160917^393*5000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052027009 5000000000 3166042160917 25000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (521/128 : ℝ)) 521 393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312520401/10000000000 : ℝ), (5392657251/10000000000 : ℝ), (-1052027009/5000000000 : ℝ)] ![(10808641149123/25000000000000 : ℝ), (1102531668727/2500000000000 : ℝ), (3166042160917/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312520401/10000000000 : ℝ)|^521 ≤ (10808641149123/25000000000000 : ℝ)^393
        have hw : |(5312520401/10000000000 : ℝ)|=(5312520401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392657251/10000000000 : ℝ)|^521 ≤ (1102531668727/2500000000000 : ℝ)^393
        have hw : |(5392657251/10000000000 : ℝ)|=(5392657251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1052027009/5000000000 : ℝ)|^521 ≤ (3166042160917/25000000000000 : ℝ)^393
        have hw : |(-1052027009/5000000000 : ℝ)|=(1052027009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1143_s8_7 (p : ℝ) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2182271849/5000000000 : ℝ)*x 0 + (44922631/100000000 : ℝ)*x 1 + (2120228821/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2182271849/5000000000 : ℝ)^521 ≤ (33317086762333/100000000000000 : ℝ)^393 := by
    have hnat : (2182271849 : ℕ)^521*100000000000000^393 ≤ 33317086762333^393*5000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182271849 5000000000 33317086762333 100000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (44922631/100000000 : ℝ)^521 ≤ (6923141024393/20000000000000 : ℝ)^393 := by
    have hnat : (44922631 : ℕ)^521*20000000000000^393 ≤ 6923141024393^393*100000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44922631 100000000 6923141024393 20000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2120228821/5000000000 : ℝ)^521 ≤ (32067208100717/100000000000000 : ℝ)^393 := by
    have hnat : (2120228821 : ℕ)^521*100000000000000^393 ≤ 32067208100717^393*5000000000^521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2120228821 5000000000 32067208100717 100000000000000 521 393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (521/128 : ℝ)) 521 393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2182271849/5000000000 : ℝ), (44922631/100000000 : ℝ), (2120228821/5000000000 : ℝ)] ![(33317086762333/100000000000000 : ℝ), (6923141024393/20000000000000 : ℝ), (32067208100717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2182271849/5000000000 : ℝ)|^521 ≤ (33317086762333/100000000000000 : ℝ)^393
        have hw : |(2182271849/5000000000 : ℝ)|=(2182271849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(44922631/100000000 : ℝ)|^521 ≤ (6923141024393/20000000000000 : ℝ)^393
        have hw : |(44922631/100000000 : ℝ)|=(44922631/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2120228821/5000000000 : ℝ)|^521 ≤ (32067208100717/100000000000000 : ℝ)^393
        have hw : |(2120228821/5000000000 : ℝ)|=(2120228821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1143_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7474661/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14051/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5677/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2271/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14049/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14051/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5677/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14051/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5677/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14051/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5677/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14051/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5677/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14051/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5677/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14051/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5677/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5677/50000 : ℝ) ^ (8335/2048 : ℝ) ≤ (2855302099206547/20000000000000000000 : ℝ) := by
    have hpowers : (5677/50000 : ℝ)^8335 ≤ (2855302099206547/20000000000000000000 : ℝ)^2048 := by
      have hnat : (5677 : ℕ)^8335*20000000000000000000^2048 ≤ 2855302099206547^2048*50000^8335 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5677 50000 2855302099206547 20000000000000000000 8335 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5677/50000 : ℝ)) (X := (2855302099206547/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8335 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14051/100000 : ℝ) ^ (8335/2048 : ℝ) ≤ (33987424713137917/100000000000000000000 : ℝ) := by
    have hpowers : (14051/100000 : ℝ)^8335 ≤ (33987424713137917/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14051 : ℕ)^8335*100000000000000000000^2048 ≤ 33987424713137917^2048*100000^8335 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14051 100000 33987424713137917 100000000000000000000 8335 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14051/100000 : ℝ)) (X := (33987424713137917/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8335 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002855302099206547/10000000000000000000 : ℝ) ≤ (10000701503190443/10000000000000000 : ℝ) ^ (8335/2048 : ℝ) := by
    have hpowers : (10002855302099206547/10000000000000000000 : ℝ)^2048 ≤ (10000701503190443/10000000000000000 : ℝ)^8335 := by
      have hnat : (10002855302099206547 : ℕ)^2048*10000000000000000^8335 ≤ 10000701503190443^8335*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002855302099206547 10000000000000000000 10000701503190443 10000000000000000 2048 8335 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000701503190443/10000000000000000 : ℝ)) (X := (10002855302099206547/10000000000000000000 : ℝ)) (by norm_num) 8335 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25012065983802292663/25000000000000000000 : ℝ) ≤ (5000592840745207/5000000000000000 : ℝ) ^ (8335/2048 : ℝ) := by
    have hpowers : (25012065983802292663/25000000000000000000 : ℝ)^2048 ≤ (5000592840745207/5000000000000000 : ℝ)^8335 := by
      have hnat : (25012065983802292663 : ℕ)^2048*5000000000000000^8335 ≤ 5000592840745207^8335*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012065983802292663 25000000000000000000 5000592840745207 5000000000000000 2048 8335 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000592840745207/5000000000000000 : ℝ)) (X := (25012065983802292663/25000000000000000000 : ℝ)) (by norm_num) 8335 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033987424713137917/50000000000000000000 : ℝ) ≤ (2000333971958077/2000000000000000 : ℝ) ^ (8335/2048 : ℝ) := by
    have hpowers : (50033987424713137917/50000000000000000000 : ℝ)^2048 ≤ (2000333971958077/2000000000000000 : ℝ)^8335 := by
      have hnat : (50033987424713137917 : ℕ)^2048*2000000000000000^8335 ≤ 2000333971958077^8335*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033987424713137917 50000000000000000000 2000333971958077 2000000000000000 2048 8335 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000333971958077/2000000000000000 : ℝ)) (X := (50033987424713137917/50000000000000000000 : ℝ)) (by norm_num) 8335 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2855302099206547/20000000000000000000 : ℝ) ≤ ((8986965744422961101/8990000000000000000 : ℝ)+2*(161392766657/89900000000000 : ℝ)*(5677/50000 : ℝ))^(8335/2048 : ℝ) := by
    rw [show (8986965744422961101/8990000000000000000 : ℝ)+2*(161392766657/89900000000000 : ℝ)*(5677/50000 : ℝ)=(10000701503190443/10000000000000000 : ℝ) by norm_num, show 1+2*(2855302099206547/20000000000000000000 : ℝ)=(10002855302099206547/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33987424713137917/100000000000000000000 : ℝ)+(2855302099206547/20000000000000000000 : ℝ) ≤ ((8986965744422961101/8990000000000000000 : ℝ)+(161392766657/89900000000000 : ℝ)*((14051/100000 : ℝ)+(5677/50000 : ℝ)))^(8335/2048 : ℝ) := by
    rw [show (8986965744422961101/8990000000000000000 : ℝ)+(161392766657/89900000000000 : ℝ)*((14051/100000 : ℝ)+(5677/50000 : ℝ))=(5000592840745207/5000000000000000 : ℝ) by norm_num, show 1+(33987424713137917/100000000000000000000 : ℝ)+(2855302099206547/20000000000000000000 : ℝ)=(25012065983802292663/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33987424713137917/100000000000000000000 : ℝ) ≤ ((8986965744422961101/8990000000000000000 : ℝ)+2*(161392766657/89900000000000 : ℝ)*(14051/100000 : ℝ))^(8335/2048 : ℝ) := by
    rw [show (8986965744422961101/8990000000000000000 : ℝ)+2*(161392766657/89900000000000 : ℝ)*(14051/100000 : ℝ)=(2000333971958077/2000000000000000 : ℝ) by norm_num, show 1+2*(33987424713137917/100000000000000000000 : ℝ)=(50033987424713137917/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8986965744422961101/8990000000000000000 : ℝ)*(X 1 0+X 2 0)+(161392766657/89900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8335/2048 : ℝ)) (lo := (5677/50000 : ℝ)) (hi := (14051/100000 : ℝ)) (c := (8986965744422961101/8990000000000000000 : ℝ)) (alpha := (161392766657/89900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8986965744422961101/8990000000000000000 : ℝ)*(X 0 1+X 2 1)+(161392766657/89900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8335/2048 : ℝ)) (lo := (5677/50000 : ℝ)) (hi := (14051/100000 : ℝ)) (c := (8986965744422961101/8990000000000000000 : ℝ)) (alpha := (161392766657/89900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8986965744422961101/8990000000000000000 : ℝ)*(X 0 2+X 1 2)+(161392766657/89900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8335/2048 : ℝ)) (lo := (5677/50000 : ℝ)) (hi := (14051/100000 : ℝ)) (c := (8986965744422961101/8990000000000000000 : ℝ)) (alpha := (161392766657/89900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1083204137/5000000000 : ℝ)*X 0 0+(5392977753/10000000000 : ℝ)*X 0 1+(2632896883/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1143_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344745611/10000000000 : ℝ)*X 1 0+(-1115458697/5000000000 : ℝ)*X 1 1+(5265793767/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1143_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672372813/5000000000 : ℝ)*X 2 0+(5265793751/10000000000 : ℝ)*X 2 1+(-1115458697/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1143_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4364534181/10000000000 : ℝ)*X 0 0+(4239819689/10000000000 : ℝ)*X 0 1+(280806161/625000000 : ℝ)*X 0 2+(4364534181/10000000000 : ℝ)*X 1 0+(4239819689/10000000000 : ℝ)*X 1 1+(280806161/625000000 : ℝ)*X 1 2+(4364534181/10000000000 : ℝ)*X 2 0+(4239819689/10000000000 : ℝ)*X 2 1+(280806161/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1143_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2166413063/10000000000 : ℝ)*X 0 0+(105322263/200000000 : ℝ)*X 0 1+(5392657277/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1143_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328130139/2500000000 : ℝ)*X 1 0+(-1052026877/5000000000 : ℝ)*X 1 1+(5392657291/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1143_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312520401/10000000000 : ℝ)*X 2 0+(5392657251/10000000000 : ℝ)*X 2 1+(-1052027009/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1143_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2182271849/5000000000 : ℝ)*X 0 0+(44922631/100000000 : ℝ)*X 0 1+(2120228821/5000000000 : ℝ)*X 0 2+(2182271849/5000000000 : ℝ)*X 1 0+(44922631/100000000 : ℝ)*X 1 1+(2120228821/5000000000 : ℝ)*X 1 2+(2182271849/5000000000 : ℝ)*X 2 0+(44922631/100000000 : ℝ)*X 2 1+(2120228821/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1143_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8195441734688011826253/1123750000000000000000000000 : ℝ) := by norm_num
    linear_combination (285823171/20000000000000 : ℝ)*(base19) + (672865261/50000000000000 : ℝ)*(base23) + (28180697/50000000000000 : ℝ)*(lower2) + (90627817/50000000000000 : ℝ)*(upper3) + (106490401/100000000000000 : ℝ)*(upper5) + (5907041201697671/100000000000000 : ℝ)*(major0) + (5907041201697671/100000000000000 : ℝ)*(major1) + (5907041201697671/100000000000000 : ℝ)*(major2) + (1965666431796253/25000000000000 : ℝ)*(sp0) + (314508136134737/4000000000000 : ℝ)*(sp1) + (7862703486753759/100000000000000 : ℝ)*(sp2) + (987839014960071/25000000000000 : ℝ)*(sp3) + (9776324817/25000000000000 : ℝ)*(sp4) + (21267972757/100000000000000 : ℝ)*(sp7) + (1975688663906521/50000000000000 : ℝ)*(f.failure) + (196567620812107/2500000000000 : ℝ)*(f.sum) + (1972881352937/4495000000000000000000000000 : ℝ)*base65 + (2451123749391995771/899000000000000000000000000000000 : ℝ)*base67 + (5311986132814004229/899000000000000000000000000000000 : ℝ)*base70 + (2331390566544995771/899000000000000000000000000000000 : ℝ)*base71 + (21848070858477/4495000000000000000000000000 : ℝ)*base73 + (4209863573432995771/899000000000000000000000000000000 : ℝ)*base75 + (6856007771096004229/899000000000000000000000000000000 : ℝ)*base78 + (14168462498535004229/899000000000000000000000000000000 : ℝ)*base80 + (14478623514507/4495000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (2664381/250000000000000000000 : ℝ)*base89 + (2664381/250000000000000000000 : ℝ)*base91 + (2664381/250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1285298121316648090569/224750000000000000000000000 : ℝ) := by norm_num
    linear_combination (11172383/1250000000000 : ℝ)*(base19) + (155544607/25000000000000 : ℝ)*(base23) + (43022013/25000000000000 : ℝ)*(lower1) + (3601837/50000000000000 : ℝ)*(upper3) + (4006261/10000000000000 : ℝ)*(lower4) + (15419487/20000000000000 : ℝ)*(upper5) + (593683815491697/10000000000000 : ℝ)*(major0) + (593683815491697/10000000000000 : ℝ)*(major1) + (593683815491697/10000000000000 : ℝ)*(major2) + (19199495489/100000000000000 : ℝ)*(sp1) + (7902366815068599/100000000000000 : ℝ)*(sp4) + (790234672178247/10000000000000 : ℝ)*(sp5) + (1975591548222543/25000000000000 : ℝ)*(sp6) + (397130930413899/10000000000000 : ℝ)*(sp7) + (397130930413899/10000000000000 : ℝ)*(f.failure) + (7902366815068599/100000000000000 : ℝ)*(f.sum) + (437998884559/899000000000000000000000000 : ℝ)*base66 + (679827569797378397/89900000000000000000000000000000 : ℝ)*base67 + (639744697092678397/89900000000000000000000000000000 : ℝ)*base69 + (285432559714278397/89900000000000000000000000000000 : ℝ)*base71 + (1231613944053/224750000000000000000000000 : ℝ)*base73 + (10300708716321603/89900000000000000000000000000000 : ℝ)*base76 + (327676169168421603/89900000000000000000000000000000 : ℝ)*base78 + (519120213150421603/89900000000000000000000000000000 : ℝ)*base80 + (1156257404371/449500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (286761/50000000000000000000 : ℝ)*base90 + (286761/50000000000000000000 : ℝ)*base92 + (286761/50000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1143_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7474661/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14051/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5677/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2271/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14049/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1143_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1143_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7474661/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14089/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11317/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2271/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14049/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1143_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1143_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1143_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8335/2048 : ℝ) ≤ p) (hpb : p ≤ (521/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7474661/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14089/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11317/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2271/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14049/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1143_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
