-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1311_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:39:21.935444+00:00
-- url     : https://prove2.me/submissions/3ec18528-2cd0-4807-b7b8-6b2f4077097d

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
theorem support_rectangle_w1311_s0_0 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-913807579/5000000000 : ℝ)*x 0 + (3005206839/5000000000 : ℝ)*x 1 + (2401729529/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (913807579/5000000000 : ℝ)^4271 ≤ (1336647255561/12500000000000 : ℝ)^3247 := by
    have hnat : (913807579 : ℕ)^4271*12500000000000^3247 ≤ 1336647255561^3247*5000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      913807579 5000000000 1336647255561 12500000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3005206839/5000000000 : ℝ)^4271 ≤ (10237828832767/20000000000000 : ℝ)^3247 := by
    have hnat : (3005206839 : ℕ)^4271*20000000000000^3247 ≤ 10237828832767^3247*5000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3005206839 5000000000 10237828832767 20000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2401729529/5000000000 : ℝ)^4271 ≤ (38117677777677/100000000000000 : ℝ)^3247 := by
    have hnat : (2401729529 : ℕ)^4271*100000000000000^3247 ≤ 38117677777677^3247*5000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2401729529 5000000000 38117677777677 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-913807579/5000000000 : ℝ), (3005206839/5000000000 : ℝ), (2401729529/5000000000 : ℝ)] ![(1336647255561/12500000000000 : ℝ), (10237828832767/20000000000000 : ℝ), (38117677777677/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-913807579/5000000000 : ℝ)|^4271 ≤ (1336647255561/12500000000000 : ℝ)^3247
        have hw : |(-913807579/5000000000 : ℝ)|=(913807579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3005206839/5000000000 : ℝ)|^4271 ≤ (10237828832767/20000000000000 : ℝ)^3247
        have hw : |(3005206839/5000000000 : ℝ)|=(3005206839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2401729529/5000000000 : ℝ)|^4271 ≤ (38117677777677/100000000000000 : ℝ)^3247
        have hw : |(2401729529/5000000000 : ℝ)|=(2401729529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_s0_1 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2752643637/5000000000 : ℝ)*x 0 + (-2515203467/10000000000 : ℝ)*x 1 + (4803458987/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2752643637/5000000000 : ℝ)^4271 ≤ (45606871336447/100000000000000 : ℝ)^3247 := by
    have hnat : (2752643637 : ℕ)^4271*100000000000000^3247 ≤ 45606871336447^3247*5000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2752643637 5000000000 45606871336447 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2515203467/10000000000 : ℝ)^4271 ≤ (16275451620321/100000000000000 : ℝ)^3247 := by
    have hnat : (2515203467 : ℕ)^4271*100000000000000^3247 ≤ 16275451620321^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2515203467 10000000000 16275451620321 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4803458987/10000000000 : ℝ)^4271 ≤ (1524707081463/4000000000000 : ℝ)^3247 := by
    have hnat : (4803458987 : ℕ)^4271*4000000000000^3247 ≤ 1524707081463^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4803458987 10000000000 1524707081463 4000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2752643637/5000000000 : ℝ), (-2515203467/10000000000 : ℝ), (4803458987/10000000000 : ℝ)] ![(45606871336447/100000000000000 : ℝ), (16275451620321/100000000000000 : ℝ), (1524707081463/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2752643637/5000000000 : ℝ)|^4271 ≤ (45606871336447/100000000000000 : ℝ)^3247
        have hw : |(2752643637/5000000000 : ℝ)|=(2752643637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2515203467/10000000000 : ℝ)|^4271 ≤ (16275451620321/100000000000000 : ℝ)^3247
        have hw : |(-2515203467/10000000000 : ℝ)|=(2515203467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4803458987/10000000000 : ℝ)|^4271 ≤ (1524707081463/4000000000000 : ℝ)^3247
        have hw : |(4803458987/10000000000 : ℝ)|=(4803458987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_s0_2 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (550528663/1000000000 : ℝ)*x 0 + (4803459529/10000000000 : ℝ)*x 1 + (-1257601813/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (550528663/1000000000 : ℝ)^4271 ≤ (4560686431893/10000000000000 : ℝ)^3247 := by
    have hnat : (550528663 : ℕ)^4271*10000000000000^3247 ≤ 4560686431893^3247*1000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550528663 1000000000 4560686431893 10000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4803459529/10000000000 : ℝ)^4271 ≤ (19058841347001/50000000000000 : ℝ)^3247 := by
    have hnat : (4803459529 : ℕ)^4271*50000000000000^3247 ≤ 19058841347001^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4803459529 10000000000 19058841347001 50000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1257601813/5000000000 : ℝ)^4271 ≤ (16275452973653/100000000000000 : ℝ)^3247 := by
    have hnat : (1257601813 : ℕ)^4271*100000000000000^3247 ≤ 16275452973653^3247*5000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1257601813 5000000000 16275452973653 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(550528663/1000000000 : ℝ), (4803459529/10000000000 : ℝ), (-1257601813/5000000000 : ℝ)] ![(4560686431893/10000000000000 : ℝ), (19058841347001/50000000000000 : ℝ), (16275452973653/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(550528663/1000000000 : ℝ)|^4271 ≤ (4560686431893/10000000000000 : ℝ)^3247
        have hw : |(550528663/1000000000 : ℝ)|=(550528663/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4803459529/10000000000 : ℝ)|^4271 ≤ (19058841347001/50000000000000 : ℝ)^3247
        have hw : |(4803459529/10000000000 : ℝ)|=(4803459529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1257601813/5000000000 : ℝ)|^4271 ≤ (16275452973653/100000000000000 : ℝ)^3247
        have hw : |(-1257601813/5000000000 : ℝ)|=(1257601813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_s0_3 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4183425417/10000000000 : ℝ)*x 0 + (621650219/2000000000 : ℝ)*x 1 + (5606849399/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4183425417/10000000000 : ℝ)^4271 ≤ (31781568873947/100000000000000 : ℝ)^3247 := by
    have hnat : (4183425417 : ℕ)^4271*100000000000000^3247 ≤ 31781568873947^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4183425417 10000000000 31781568873947 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (621650219/2000000000 : ℝ)^4271 ≤ (4300331057507/20000000000000 : ℝ)^3247 := by
    have hnat : (621650219 : ℕ)^4271*20000000000000^3247 ≤ 4300331057507^3247*2000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      621650219 2000000000 4300331057507 20000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5606849399/10000000000 : ℝ)^4271 ≤ (5839596978839/12500000000000 : ℝ)^3247 := by
    have hnat : (5606849399 : ℕ)^4271*12500000000000^3247 ≤ 5839596978839^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5606849399 10000000000 5839596978839 12500000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4183425417/10000000000 : ℝ), (621650219/2000000000 : ℝ), (5606849399/10000000000 : ℝ)] ![(31781568873947/100000000000000 : ℝ), (4300331057507/20000000000000 : ℝ), (5839596978839/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4183425417/10000000000 : ℝ)|^4271 ≤ (31781568873947/100000000000000 : ℝ)^3247
        have hw : |(4183425417/10000000000 : ℝ)|=(4183425417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(621650219/2000000000 : ℝ)|^4271 ≤ (4300331057507/20000000000000 : ℝ)^3247
        have hw : |(621650219/2000000000 : ℝ)|=(621650219/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5606849399/10000000000 : ℝ)|^4271 ≤ (5839596978839/12500000000000 : ℝ)^3247
        have hw : |(5606849399/10000000000 : ℝ)|=(5606849399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_s0_4 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-45805919/250000000 : ℝ)*x 0 + (12086443/25000000 : ℝ)*x 1 + (1195637257/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (45805919/250000000 : ℝ)^4271 ≤ (10728760417691/100000000000000 : ℝ)^3247 := by
    have hnat : (45805919 : ℕ)^4271*100000000000000^3247 ≤ 10728760417691^3247*250000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45805919 250000000 10728760417691 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (12086443/25000000 : ℝ)^4271 ≤ (38442822001497/100000000000000 : ℝ)^3247 := by
    have hnat : (12086443 : ℕ)^4271*100000000000000^3247 ≤ 38442822001497^3247*25000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12086443 25000000 38442822001497 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1195637257/2000000000 : ℝ)^4271 ≤ (50828417566897/100000000000000 : ℝ)^3247 := by
    have hnat : (1195637257 : ℕ)^4271*100000000000000^3247 ≤ 50828417566897^3247*2000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1195637257 2000000000 50828417566897 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-45805919/250000000 : ℝ), (12086443/25000000 : ℝ), (1195637257/2000000000 : ℝ)] ![(10728760417691/100000000000000 : ℝ), (38442822001497/100000000000000 : ℝ), (50828417566897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-45805919/250000000 : ℝ)|^4271 ≤ (10728760417691/100000000000000 : ℝ)^3247
        have hw : |(-45805919/250000000 : ℝ)|=(45805919/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(12086443/25000000 : ℝ)|^4271 ≤ (38442822001497/100000000000000 : ℝ)^3247
        have hw : |(12086443/25000000 : ℝ)|=(12086443/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1195637257/2000000000 : ℝ)|^4271 ≤ (50828417566897/100000000000000 : ℝ)^3247
        have hw : |(1195637257/2000000000 : ℝ)|=(1195637257/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_s0_5 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (517656329/1000000000 : ℝ)*x 0 + (-335119231/2500000000 : ℝ)*x 1 + (2989093113/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (517656329/1000000000 : ℝ)^4271 ≤ (420590411629/1000000000000 : ℝ)^3247 := by
    have hnat : (517656329 : ℕ)^4271*1000000000000^3247 ≤ 420590411629^3247*1000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517656329 1000000000 420590411629 1000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (335119231/2500000000 : ℝ)^4271 ≤ (7112541908371/100000000000000 : ℝ)^3247 := by
    have hnat : (335119231 : ℕ)^4271*100000000000000^3247 ≤ 7112541908371^3247*2500000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335119231 2500000000 7112541908371 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2989093113/5000000000 : ℝ)^4271 ≤ (2541420845353/5000000000000 : ℝ)^3247 := by
    have hnat : (2989093113 : ℕ)^4271*5000000000000^3247 ≤ 2541420845353^3247*5000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2989093113 5000000000 2541420845353 5000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(517656329/1000000000 : ℝ), (-335119231/2500000000 : ℝ), (2989093113/5000000000 : ℝ)] ![(420590411629/1000000000000 : ℝ), (7112541908371/100000000000000 : ℝ), (2541420845353/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(517656329/1000000000 : ℝ)|^4271 ≤ (420590411629/1000000000000 : ℝ)^3247
        have hw : |(517656329/1000000000 : ℝ)|=(517656329/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-335119231/2500000000 : ℝ)|^4271 ≤ (7112541908371/100000000000000 : ℝ)^3247
        have hw : |(-335119231/2500000000 : ℝ)|=(335119231/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2989093113/5000000000 : ℝ)|^4271 ≤ (2541420845353/5000000000000 : ℝ)^3247
        have hw : |(2989093113/5000000000 : ℝ)|=(2989093113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_s0_6 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5176563303/10000000000 : ℝ)*x 0 + (298909313/500000000 : ℝ)*x 1 + (-1340476851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5176563303/10000000000 : ℝ)^4271 ≤ (21029520650917/50000000000000 : ℝ)^3247 := by
    have hnat : (5176563303 : ℕ)^4271*50000000000000^3247 ≤ 21029520650917^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176563303 10000000000 21029520650917 50000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (298909313/500000000 : ℝ)^4271 ≤ (10165683457461/20000000000000 : ℝ)^3247 := by
    have hnat : (298909313 : ℕ)^4271*20000000000000^3247 ≤ 10165683457461^3247*500000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      298909313 500000000 10165683457461 20000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1340476851/10000000000 : ℝ)^4271 ≤ (7112541398881/100000000000000 : ℝ)^3247 := by
    have hnat : (1340476851 : ℕ)^4271*100000000000000^3247 ≤ 7112541398881^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1340476851 10000000000 7112541398881 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5176563303/10000000000 : ℝ), (298909313/500000000 : ℝ), (-1340476851/10000000000 : ℝ)] ![(21029520650917/50000000000000 : ℝ), (10165683457461/20000000000000 : ℝ), (7112541398881/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5176563303/10000000000 : ℝ)|^4271 ≤ (21029520650917/50000000000000 : ℝ)^3247
        have hw : |(5176563303/10000000000 : ℝ)|=(5176563303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(298909313/500000000 : ℝ)|^4271 ≤ (10165683457461/20000000000000 : ℝ)^3247
        have hw : |(298909313/500000000 : ℝ)|=(298909313/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1340476851/10000000000 : ℝ)|^4271 ≤ (7112541398881/100000000000000 : ℝ)^3247
        have hw : |(-1340476851/10000000000 : ℝ)|=(1340476851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_s0_7 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4192992311/10000000000 : ℝ)*x 0 + (2771215033/5000000000 : ℝ)*x 1 + (634993339/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4192992311/10000000000 : ℝ)^4271 ≤ (31877204134023/100000000000000 : ℝ)^3247 := by
    have hnat : (4192992311 : ℕ)^4271*100000000000000^3247 ≤ 31877204134023^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4192992311 10000000000 31877204134023 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2771215033/5000000000 : ℝ)^4271 ≤ (4601203752441/10000000000000 : ℝ)^3247 := by
    have hnat : (2771215033 : ℕ)^4271*10000000000000^3247 ≤ 4601203752441^3247*5000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2771215033 5000000000 4601203752441 10000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (634993339/2000000000 : ℝ)^4271 ≤ (11055379165809/50000000000000 : ℝ)^3247 := by
    have hnat : (634993339 : ℕ)^4271*50000000000000^3247 ≤ 11055379165809^3247*2000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      634993339 2000000000 11055379165809 50000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4192992311/10000000000 : ℝ), (2771215033/5000000000 : ℝ), (634993339/2000000000 : ℝ)] ![(31877204134023/100000000000000 : ℝ), (4601203752441/10000000000000 : ℝ), (11055379165809/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4192992311/10000000000 : ℝ)|^4271 ≤ (31877204134023/100000000000000 : ℝ)^3247
        have hw : |(4192992311/10000000000 : ℝ)|=(4192992311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2771215033/5000000000 : ℝ)|^4271 ≤ (4601203752441/10000000000000 : ℝ)^3247
        have hw : |(2771215033/5000000000 : ℝ)|=(2771215033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(634993339/2000000000 : ℝ)|^4271 ≤ (11055379165809/50000000000000 : ℝ)^3247
        have hw : |(634993339/2000000000 : ℝ)|=(634993339/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1311_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153508417/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1179/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3387/12500 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (2135/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2135 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2135*1^512 ≤ 0^512*1^2135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2135 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2135 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2135/512 : ℝ) ≤ (43817868588886989/2000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2135 ≤ (43817868588886989/2000000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2135*2000000000000000000^512 ≤ 43817868588886989^512*5^2135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 43817868588886989 2000000000000000000 2135 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (43817868588886989/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2135 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2135/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2135 := by
      have hnat : (1 : ℕ)^512*1^2135 ≤ 1^2135*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2135 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (2043817868588886989/2000000000000000000 : ℝ) ≤ (5026054204169491/5000000000000000 : ℝ) ^ (2135/512 : ℝ) := by
    have hpowers : (2043817868588886989/2000000000000000000 : ℝ)^512 ≤ (5026054204169491/5000000000000000 : ℝ)^2135 := by
      have hnat : (2043817868588886989 : ℕ)^512*5000000000000000^2135 ≤ 5026054204169491^2135*2000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2043817868588886989 2000000000000000000 5026054204169491 5000000000000000 512 2135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5026054204169491/5000000000000000 : ℝ)) (X := (2043817868588886989/2000000000000000000 : ℝ)) (by norm_num) 2135 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (1043817868588886989/1000000000000000000 : ℝ) ≤ (2526054204169491/2500000000000000 : ℝ) ^ (2135/512 : ℝ) := by
    have hpowers : (1043817868588886989/1000000000000000000 : ℝ)^512 ≤ (2526054204169491/2500000000000000 : ℝ)^2135 := by
      have hnat : (1043817868588886989 : ℕ)^512*2500000000000000^2135 ≤ 2526054204169491^2135*1000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1043817868588886989 1000000000000000000 2526054204169491 2500000000000000 512 2135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2526054204169491/2500000000000000 : ℝ)) (X := (1043817868588886989/1000000000000000000 : ℝ)) (by norm_num) 2135 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(26054204169491/2000000000000000 : ℝ)*(0 : ℝ))^(2135/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(26054204169491/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(43817868588886989/2000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(26054204169491/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2135/512 : ℝ) := by
    rw [show (1 : ℝ)+(26054204169491/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5026054204169491/5000000000000000 : ℝ) by norm_num, show 1+(43817868588886989/2000000000000000000 : ℝ)+(0 : ℝ)=(2043817868588886989/2000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(43817868588886989/2000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(26054204169491/2000000000000000 : ℝ)*(2/5 : ℝ))^(2135/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(26054204169491/2000000000000000 : ℝ)*(2/5 : ℝ)=(2526054204169491/2500000000000000 : ℝ) by norm_num, show 1+2*(43817868588886989/2000000000000000000 : ℝ)=(1043817868588886989/1000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(26054204169491/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2135/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (26054204169491/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(26054204169491/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2135/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (26054204169491/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(26054204169491/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2135/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (26054204169491/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-913807579/5000000000 : ℝ)*X 0 0+(3005206839/5000000000 : ℝ)*X 0 1+(2401729529/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2752643637/5000000000 : ℝ)*X 1 0+(-2515203467/10000000000 : ℝ)*X 1 1+(4803458987/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((550528663/1000000000 : ℝ)*X 2 0+(4803459529/10000000000 : ℝ)*X 2 1+(-1257601813/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4183425417/10000000000 : ℝ)*X 0 0+(621650219/2000000000 : ℝ)*X 0 1+(5606849399/10000000000 : ℝ)*X 0 2+(4183425417/10000000000 : ℝ)*X 1 0+(621650219/2000000000 : ℝ)*X 1 1+(5606849399/10000000000 : ℝ)*X 1 2+(4183425417/10000000000 : ℝ)*X 2 0+(621650219/2000000000 : ℝ)*X 2 1+(5606849399/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-45805919/250000000 : ℝ)*X 0 0+(12086443/25000000 : ℝ)*X 0 1+(1195637257/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((517656329/1000000000 : ℝ)*X 1 0+(-335119231/2500000000 : ℝ)*X 1 1+(2989093113/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5176563303/10000000000 : ℝ)*X 2 0+(298909313/500000000 : ℝ)*X 2 1+(-1340476851/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4192992311/10000000000 : ℝ)*X 0 0+(2771215033/5000000000 : ℝ)*X 0 1+(634993339/2000000000 : ℝ)*X 0 2+(4192992311/10000000000 : ℝ)*X 1 0+(2771215033/5000000000 : ℝ)*X 1 1+(634993339/2000000000 : ℝ)*X 1 2+(4192992311/10000000000 : ℝ)*X 2 0+(2771215033/5000000000 : ℝ)*X 2 1+(634993339/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (47361801158028392853771/10000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (75832587/100000000000000 : ℝ)*(base1) + (38690379/3125000000000 : ℝ)*(base19) + (1141171011/100000000000000 : ℝ)*(base23) + (40363987/25000000000000 : ℝ)*(upper3) + (11221561/12500000000000 : ℝ)*(upper5) + (122876755585009/20000000000000 : ℝ)*(major0) + (122876755585009/20000000000000 : ℝ)*(major1) + (122876755585009/20000000000000 : ℝ)*(major2) + (414267829699813/50000000000000 : ℝ)*(sp0) + (414269043874823/50000000000000 : ℝ)*(sp1) + (828538184670763/100000000000000 : ℝ)*(sp2) + (80045215619899/20000000000000 : ℝ)*(sp3) + (748454947/20000000000000 : ℝ)*(sp4) + (959101781/50000000000000 : ℝ)*(sp7) + (100057018033911/25000000000000 : ℝ)*(f.failure) + (414269662920887/50000000000000 : ℝ)*(f.sum) + (5857039019581/20000000000000000000000000000 : ℝ)*base66 + (129404047039581/40000000000000000000000000000 : ℝ)*base68 + (92545020359581/40000000000000000000000000000 : ℝ)*base70 + (22330553279581/40000000000000000000000000000 : ℝ)*base72 + (46842693939581/20000000000000000000000000000 : ℝ)*base74 + (86714893119581/40000000000000000000000000000 : ℝ)*base76 + (65290300719581/40000000000000000000000000000 : ℝ)*base78 + (5985014999581/40000000000000000000000000000 : ℝ)*base80 + (1381994379581/20000000000000000000000000000 : ℝ)*base82 + (4928887/2500000000000000000000 : ℝ)*base89 + (4928887/2500000000000000000000 : ℝ)*base91 + (4928887/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (624937651419203180621121/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1496364617/100000000000000 : ℝ)*(base19) + (378222573/25000000000000 : ℝ)*(base23) + (72415101/100000000000000 : ℝ)*(base32) + (4156931/2000000000000 : ℝ)*(upper3) + (37461369/25000000000000 : ℝ)*(upper5) + (648408738130659/100000000000000 : ℝ)*(major0) + (648408738130659/100000000000000 : ℝ)*(major1) + (648408738130659/100000000000000 : ℝ)*(major2) + (3309741329/100000000000000 : ℝ)*(sp1) + (3535404899/100000000000000 : ℝ)*(sp2) + (437212156672859/50000000000000 : ℝ)*(sp4) + (874419507239773/100000000000000 : ℝ)*(sp5) + (27325602032829/3125000000000 : ℝ)*(sp6) + (422392882187941/100000000000000 : ℝ)*(sp7) + (211196477301521/50000000000000 : ℝ)*(f.failure) + (437212156672859/50000000000000 : ℝ)*(f.sum) + (22497857575431/100000000000000000000000000000 : ℝ)*base66 + (1409382198324569/200000000000000000000000000000 : ℝ)*base67 + (29665585475431/200000000000000000000000000000 : ℝ)*base70 + (263365453875431/200000000000000000000000000000 : ℝ)*base72 + (429120118424569/100000000000000000000000000000 : ℝ)*base73 + (1199118143675431/200000000000000000000000000000 : ℝ)*base76 + (37664261475431/200000000000000000000000000000 : ℝ)*base78 + (932567451875431/200000000000000000000000000000 : ℝ)*base80 + (179658449775431/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (29597743/5000000000000000000000 : ℝ)*base90 + (29597743/5000000000000000000000 : ℝ)*base92 + (29597743/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1311_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153508417/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1179/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3387/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1311_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1311_s1_0 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1008454529/5000000000 : ℝ)*x 0 + (707041247/1250000000 : ℝ)*x 1 + (5036343759/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1008454529/5000000000 : ℝ)^4271 ≤ (2434650376887/20000000000000 : ℝ)^3247 := by
    have hnat : (1008454529 : ℕ)^4271*20000000000000^3247 ≤ 2434650376887^3247*5000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1008454529 5000000000 2434650376887 20000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (707041247/1250000000 : ℝ)^4271 ≤ (23629912233441/50000000000000 : ℝ)^3247 := by
    have hnat : (707041247 : ℕ)^4271*50000000000000^3247 ≤ 23629912233441^3247*1250000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      707041247 1250000000 23629912233441 50000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5036343759/10000000000 : ℝ)^4271 ≤ (50708654547/125000000000 : ℝ)^3247 := by
    have hnat : (5036343759 : ℕ)^4271*125000000000^3247 ≤ 50708654547^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5036343759 10000000000 50708654547 125000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1008454529/5000000000 : ℝ), (707041247/1250000000 : ℝ), (5036343759/10000000000 : ℝ)] ![(2434650376887/20000000000000 : ℝ), (23629912233441/50000000000000 : ℝ), (50708654547/125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1008454529/5000000000 : ℝ)|^4271 ≤ (2434650376887/20000000000000 : ℝ)^3247
        have hw : |(-1008454529/5000000000 : ℝ)|=(1008454529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(707041247/1250000000 : ℝ)|^4271 ≤ (23629912233441/50000000000000 : ℝ)^3247
        have hw : |(707041247/1250000000 : ℝ)|=(707041247/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5036343759/10000000000 : ℝ)|^4271 ≤ (50708654547/125000000000 : ℝ)^3247
        have hw : |(5036343759/10000000000 : ℝ)|=(5036343759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_s1_1 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5408972867/10000000000 : ℝ)*x 0 + (-2348644277/10000000000 : ℝ)*x 1 + (2518171907/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5408972867/10000000000 : ℝ)^4271 ≤ (44560262802969/100000000000000 : ℝ)^3247 := by
    have hnat : (5408972867 : ℕ)^4271*100000000000000^3247 ≤ 44560262802969^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408972867 10000000000 44560262802969 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2348644277/10000000000 : ℝ)^4271 ≤ (1859101620701/12500000000000 : ℝ)^3247 := by
    have hnat : (2348644277 : ℕ)^4271*12500000000000^3247 ≤ 1859101620701^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2348644277 10000000000 1859101620701 12500000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2518171907/5000000000 : ℝ)^4271 ≤ (40566924220329/100000000000000 : ℝ)^3247 := by
    have hnat : (2518171907 : ℕ)^4271*100000000000000^3247 ≤ 40566924220329^3247*5000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2518171907 5000000000 40566924220329 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5408972867/10000000000 : ℝ), (-2348644277/10000000000 : ℝ), (2518171907/5000000000 : ℝ)] ![(44560262802969/100000000000000 : ℝ), (1859101620701/12500000000000 : ℝ), (40566924220329/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5408972867/10000000000 : ℝ)|^4271 ≤ (44560262802969/100000000000000 : ℝ)^3247
        have hw : |(5408972867/10000000000 : ℝ)|=(5408972867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2348644277/10000000000 : ℝ)|^4271 ≤ (1859101620701/12500000000000 : ℝ)^3247
        have hw : |(-2348644277/10000000000 : ℝ)|=(2348644277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2518171907/5000000000 : ℝ)|^4271 ≤ (40566924220329/100000000000000 : ℝ)^3247
        have hw : |(2518171907/5000000000 : ℝ)|=(2518171907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_s1_2 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1081794607/2000000000 : ℝ)*x 0 + (1007268693/2000000000 : ℝ)*x 1 + (-1174322251/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081794607/2000000000 : ℝ)^4271 ≤ (5570033077933/12500000000000 : ℝ)^3247 := by
    have hnat : (1081794607 : ℕ)^4271*12500000000000^3247 ≤ 5570033077933^3247*2000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081794607 2000000000 5570033077933 12500000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1007268693/2000000000 : ℝ)^4271 ≤ (40566920522649/100000000000000 : ℝ)^3247 := by
    have hnat : (1007268693 : ℕ)^4271*100000000000000^3247 ≤ 40566920522649^3247*2000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1007268693 2000000000 40566920522649 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1174322251/5000000000 : ℝ)^4271 ≤ (3718203709941/25000000000000 : ℝ)^3247 := by
    have hnat : (1174322251 : ℕ)^4271*25000000000000^3247 ≤ 3718203709941^3247*5000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1174322251 5000000000 3718203709941 25000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1081794607/2000000000 : ℝ), (1007268693/2000000000 : ℝ), (-1174322251/5000000000 : ℝ)] ![(5570033077933/12500000000000 : ℝ), (40566920522649/100000000000000 : ℝ), (3718203709941/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1081794607/2000000000 : ℝ)|^4271 ≤ (5570033077933/12500000000000 : ℝ)^3247
        have hw : |(1081794607/2000000000 : ℝ)|=(1081794607/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1007268693/2000000000 : ℝ)|^4271 ≤ (40566920522649/100000000000000 : ℝ)^3247
        have hw : |(1007268693/2000000000 : ℝ)|=(1007268693/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1174322251/5000000000 : ℝ)|^4271 ≤ (3718203709941/25000000000000 : ℝ)^3247
        have hw : |(-1174322251/5000000000 : ℝ)|=(1174322251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_s1_3 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4297801839/10000000000 : ℝ)*x 0 + (3701072837/10000000000 : ℝ)*x 1 + (249227449/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4297801839/10000000000 : ℝ)^4271 ≤ (52687064837/160000000000 : ℝ)^3247 := by
    have hnat : (4297801839 : ℕ)^4271*160000000000^3247 ≤ 52687064837^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4297801839 10000000000 52687064837 160000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3701072837/10000000000 : ℝ)^4271 ≤ (27051538324889/100000000000000 : ℝ)^3247 := by
    have hnat : (3701072837 : ℕ)^4271*100000000000000^3247 ≤ 27051538324889^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3701072837 10000000000 27051538324889 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (249227449/500000000 : ℝ)^4271 ≤ (5002380767073/12500000000000 : ℝ)^3247 := by
    have hnat : (249227449 : ℕ)^4271*12500000000000^3247 ≤ 5002380767073^3247*500000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249227449 500000000 5002380767073 12500000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4297801839/10000000000 : ℝ), (3701072837/10000000000 : ℝ), (249227449/500000000 : ℝ)] ![(52687064837/160000000000 : ℝ), (27051538324889/100000000000000 : ℝ), (5002380767073/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4297801839/10000000000 : ℝ)|^4271 ≤ (52687064837/160000000000 : ℝ)^3247
        have hw : |(4297801839/10000000000 : ℝ)|=(4297801839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3701072837/10000000000 : ℝ)|^4271 ≤ (27051538324889/100000000000000 : ℝ)^3247
        have hw : |(3701072837/10000000000 : ℝ)|=(3701072837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(249227449/500000000 : ℝ)|^4271 ≤ (5002380767073/12500000000000 : ℝ)^3247
        have hw : |(249227449/500000000 : ℝ)|=(249227449/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_s1_4 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2017505859/10000000000 : ℝ)*x 0 + (2522155067/5000000000 : ℝ)*x 1 + (564821511/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2017505859/10000000000 : ℝ)^4271 ≤ (12177990127969/100000000000000 : ℝ)^3247 := by
    have hnat : (2017505859 : ℕ)^4271*100000000000000^3247 ≤ 12177990127969^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2017505859 10000000000 12177990127969 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2522155067/5000000000 : ℝ)^4271 ≤ (20325674507187/50000000000000 : ℝ)^3247 := by
    have hnat : (2522155067 : ℕ)^4271*50000000000000^3247 ≤ 20325674507187^3247*5000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2522155067 5000000000 20325674507187 50000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (564821511/1000000000 : ℝ)^4271 ≤ (47170660842743/100000000000000 : ℝ)^3247 := by
    have hnat : (564821511 : ℕ)^4271*100000000000000^3247 ≤ 47170660842743^3247*1000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      564821511 1000000000 47170660842743 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2017505859/10000000000 : ℝ), (2522155067/5000000000 : ℝ), (564821511/1000000000 : ℝ)] ![(12177990127969/100000000000000 : ℝ), (20325674507187/50000000000000 : ℝ), (47170660842743/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2017505859/10000000000 : ℝ)|^4271 ≤ (12177990127969/100000000000000 : ℝ)^3247
        have hw : |(-2017505859/10000000000 : ℝ)|=(2017505859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2522155067/5000000000 : ℝ)|^4271 ≤ (20325674507187/50000000000000 : ℝ)^3247
        have hw : |(2522155067/5000000000 : ℝ)|=(2522155067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(564821511/1000000000 : ℝ)|^4271 ≤ (47170660842743/100000000000000 : ℝ)^3247
        have hw : |(564821511/1000000000 : ℝ)|=(564821511/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_s1_5 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (656065113/1250000000 : ℝ)*x 0 + (-434193257/2500000000 : ℝ)*x 1 + (5648214831/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (656065113/1250000000 : ℝ)^4271 ≤ (21414874498969/50000000000000 : ℝ)^3247 := by
    have hnat : (656065113 : ℕ)^4271*50000000000000^3247 ≤ 21414874498969^3247*1250000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656065113 1250000000 21414874498969 50000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (434193257/2500000000 : ℝ)^4271 ≤ (4999796602879/50000000000000 : ℝ)^3247 := by
    have hnat : (434193257 : ℕ)^4271*50000000000000^3247 ≤ 4999796602879^3247*2500000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434193257 2500000000 4999796602879 50000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5648214831/10000000000 : ℝ)^4271 ≤ (2948166111117/6250000000000 : ℝ)^3247 := by
    have hnat : (5648214831 : ℕ)^4271*6250000000000^3247 ≤ 2948166111117^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5648214831 10000000000 2948166111117 6250000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(656065113/1250000000 : ℝ), (-434193257/2500000000 : ℝ), (5648214831/10000000000 : ℝ)] ![(21414874498969/50000000000000 : ℝ), (4999796602879/50000000000000 : ℝ), (2948166111117/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(656065113/1250000000 : ℝ)|^4271 ≤ (21414874498969/50000000000000 : ℝ)^3247
        have hw : |(656065113/1250000000 : ℝ)|=(656065113/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-434193257/2500000000 : ℝ)|^4271 ≤ (4999796602879/50000000000000 : ℝ)^3247
        have hw : |(-434193257/2500000000 : ℝ)|=(434193257/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5648214831/10000000000 : ℝ)|^4271 ≤ (2948166111117/6250000000000 : ℝ)^3247
        have hw : |(5648214831/10000000000 : ℝ)|=(5648214831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_s1_6 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1049704169/2000000000 : ℝ)*x 0 + (2824107341/5000000000 : ℝ)*x 1 + (-108548333/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1049704169/2000000000 : ℝ)^4271 ≤ (267685927279/625000000000 : ℝ)^3247 := by
    have hnat : (1049704169 : ℕ)^4271*625000000000^3247 ≤ 267685927279^3247*2000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049704169 2000000000 267685927279 625000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2824107341/5000000000 : ℝ)^4271 ≤ (47170656141077/100000000000000 : ℝ)^3247 := by
    have hnat : (2824107341 : ℕ)^4271*100000000000000^3247 ≤ 47170656141077^3247*5000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2824107341 5000000000 47170656141077 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (108548333/625000000 : ℝ)^4271 ≤ (2499898869439/25000000000000 : ℝ)^3247 := by
    have hnat : (108548333 : ℕ)^4271*25000000000000^3247 ≤ 2499898869439^3247*625000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108548333 625000000 2499898869439 25000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1049704169/2000000000 : ℝ), (2824107341/5000000000 : ℝ), (-108548333/625000000 : ℝ)] ![(267685927279/625000000000 : ℝ), (47170656141077/100000000000000 : ℝ), (2499898869439/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1049704169/2000000000 : ℝ)|^4271 ≤ (267685927279/625000000000 : ℝ)^3247
        have hw : |(1049704169/2000000000 : ℝ)|=(1049704169/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2824107341/5000000000 : ℝ)|^4271 ≤ (47170656141077/100000000000000 : ℝ)^3247
        have hw : |(2824107341/5000000000 : ℝ)|=(2824107341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-108548333/625000000 : ℝ)|^4271 ≤ (2499898869439/25000000000000 : ℝ)^3247
        have hw : |(-108548333/625000000 : ℝ)|=(108548333/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_s1_7 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (429903673/1000000000 : ℝ)*x 0 + (2484028287/5000000000 : ℝ)*x 1 + (1858936367/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (429903673/1000000000 : ℝ)^4271 ≤ (32941861621181/100000000000000 : ℝ)^3247 := by
    have hnat : (429903673 : ℕ)^4271*100000000000000^3247 ≤ 32941861621181^3247*1000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429903673 1000000000 32941861621181 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2484028287/5000000000 : ℝ)^4271 ≤ (39844967550621/100000000000000 : ℝ)^3247 := by
    have hnat : (2484028287 : ℕ)^4271*100000000000000^3247 ≤ 39844967550621^3247*5000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2484028287 5000000000 39844967550621 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1858936367/5000000000 : ℝ)^4271 ≤ (3401646351443/12500000000000 : ℝ)^3247 := by
    have hnat : (1858936367 : ℕ)^4271*12500000000000^3247 ≤ 3401646351443^3247*5000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1858936367 5000000000 3401646351443 12500000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(429903673/1000000000 : ℝ), (2484028287/5000000000 : ℝ), (1858936367/5000000000 : ℝ)] ![(32941861621181/100000000000000 : ℝ), (39844967550621/100000000000000 : ℝ), (3401646351443/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(429903673/1000000000 : ℝ)|^4271 ≤ (32941861621181/100000000000000 : ℝ)^3247
        have hw : |(429903673/1000000000 : ℝ)|=(429903673/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2484028287/5000000000 : ℝ)|^4271 ≤ (39844967550621/100000000000000 : ℝ)^3247
        have hw : |(2484028287/5000000000 : ℝ)|=(2484028287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1858936367/5000000000 : ℝ)|^4271 ≤ (3401646351443/12500000000000 : ℝ)^3247
        have hw : |(1858936367/5000000000 : ℝ)|=(1858936367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1311_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153508417/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3387/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1179/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1319/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (19699/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3387/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1179/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3387/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1179/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3387/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1179/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3387/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1179/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3387/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1179/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3387/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1179/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1179/100000 : ℝ) ^ (2135/512 : ℝ) ≤ (908580120291/100000000000000000000 : ℝ) := by
    have hpowers : (1179/100000 : ℝ)^2135 ≤ (908580120291/100000000000000000000 : ℝ)^512 := by
      have hnat : (1179 : ℕ)^2135*100000000000000000000^512 ≤ 908580120291^512*100000^2135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1179 100000 908580120291 100000000000000000000 2135 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1179/100000 : ℝ)) (X := (908580120291/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2135 512 (by norm_num) hpowers
    exact h
  have hpowhi : (3387/12500 : ℝ) ^ (2135/512 : ℝ) ≤ (431776418922891727/100000000000000000000 : ℝ) := by
    have hpowers : (3387/12500 : ℝ)^2135 ≤ (431776418922891727/100000000000000000000 : ℝ)^512 := by
      have hnat : (3387 : ℕ)^2135*100000000000000000000^512 ≤ 431776418922891727^512*12500^2135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3387 12500 431776418922891727 100000000000000000000 2135 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3387/12500 : ℝ)) (X := (431776418922891727/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2135 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000908580120291/50000000000000000000 : ℝ) ≤ (10000000043577801/10000000000000000 : ℝ) ^ (2135/512 : ℝ) := by
    have hpowers : (50000000908580120291/50000000000000000000 : ℝ)^512 ≤ (10000000043577801/10000000000000000 : ℝ)^2135 := by
      have hnat : (50000000908580120291 : ℕ)^512*10000000000000000^2135 ≤ 10000000043577801^2135*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000908580120291 50000000000000000000 10000000043577801 10000000000000000 512 2135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000043577801/10000000000000000 : ℝ)) (X := (50000000908580120291/50000000000000000000 : ℝ)) (by norm_num) 2135 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50215888663751506009/50000000000000000000 : ℝ) ≤ (10010337615795199/10000000000000000 : ℝ) ^ (2135/512 : ℝ) := by
    have hpowers : (50215888663751506009/50000000000000000000 : ℝ)^512 ≤ (10010337615795199/10000000000000000 : ℝ)^2135 := by
      have hnat : (50215888663751506009 : ℕ)^512*10000000000000000^2135 ≤ 10010337615795199^2135*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50215888663751506009 50000000000000000000 10010337615795199 10000000000000000 512 2135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10010337615795199/10000000000000000 : ℝ)) (X := (50215888663751506009/50000000000000000000 : ℝ)) (by norm_num) 2135 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50431776418922891727/50000000000000000000 : ℝ) ≤ (10020675188012597/10000000000000000 : ℝ) ^ (2135/512 : ℝ) := by
    have hpowers : (50431776418922891727/50000000000000000000 : ℝ)^512 ≤ (10020675188012597/10000000000000000 : ℝ)^2135 := by
      have hnat : (50431776418922891727 : ℕ)^512*10000000000000000^2135 ≤ 10020675188012597^2135*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50431776418922891727 50000000000000000000 10020675188012597 10000000000000000 512 2135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10020675188012597/10000000000000000 : ℝ)) (X := (50431776418922891727/50000000000000000000 : ℝ)) (by norm_num) 2135 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(908580120291/100000000000000000000 : ℝ) ≤ ((86381875044705748011/86390000000000000000 : ℝ)+2*(5168786108699/1295850000000000 : ℝ)*(1179/100000 : ℝ))^(2135/512 : ℝ) := by
    rw [show (86381875044705748011/86390000000000000000 : ℝ)+2*(5168786108699/1295850000000000 : ℝ)*(1179/100000 : ℝ)=(10000000043577801/10000000000000000 : ℝ) by norm_num, show 1+2*(908580120291/100000000000000000000 : ℝ)=(50000000908580120291/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(431776418922891727/100000000000000000000 : ℝ)+(908580120291/100000000000000000000 : ℝ) ≤ ((86381875044705748011/86390000000000000000 : ℝ)+(5168786108699/1295850000000000 : ℝ)*((3387/12500 : ℝ)+(1179/100000 : ℝ)))^(2135/512 : ℝ) := by
    rw [show (86381875044705748011/86390000000000000000 : ℝ)+(5168786108699/1295850000000000 : ℝ)*((3387/12500 : ℝ)+(1179/100000 : ℝ))=(10010337615795199/10000000000000000 : ℝ) by norm_num, show 1+(431776418922891727/100000000000000000000 : ℝ)+(908580120291/100000000000000000000 : ℝ)=(50215888663751506009/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(431776418922891727/100000000000000000000 : ℝ) ≤ ((86381875044705748011/86390000000000000000 : ℝ)+2*(5168786108699/1295850000000000 : ℝ)*(3387/12500 : ℝ))^(2135/512 : ℝ) := by
    rw [show (86381875044705748011/86390000000000000000 : ℝ)+2*(5168786108699/1295850000000000 : ℝ)*(3387/12500 : ℝ)=(10020675188012597/10000000000000000 : ℝ) by norm_num, show 1+2*(431776418922891727/100000000000000000000 : ℝ)=(50431776418922891727/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (86381875044705748011/86390000000000000000 : ℝ)*(X 1 0+X 2 0)+(5168786108699/1295850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2135/512 : ℝ)) (lo := (1179/100000 : ℝ)) (hi := (3387/12500 : ℝ)) (c := (86381875044705748011/86390000000000000000 : ℝ)) (alpha := (5168786108699/1295850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (86381875044705748011/86390000000000000000 : ℝ)*(X 0 1+X 2 1)+(5168786108699/1295850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2135/512 : ℝ)) (lo := (1179/100000 : ℝ)) (hi := (3387/12500 : ℝ)) (c := (86381875044705748011/86390000000000000000 : ℝ)) (alpha := (5168786108699/1295850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (86381875044705748011/86390000000000000000 : ℝ)*(X 0 2+X 1 2)+(5168786108699/1295850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2135/512 : ℝ)) (lo := (1179/100000 : ℝ)) (hi := (3387/12500 : ℝ)) (c := (86381875044705748011/86390000000000000000 : ℝ)) (alpha := (5168786108699/1295850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1008454529/5000000000 : ℝ)*X 0 0+(707041247/1250000000 : ℝ)*X 0 1+(5036343759/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5408972867/10000000000 : ℝ)*X 1 0+(-2348644277/10000000000 : ℝ)*X 1 1+(2518171907/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1081794607/2000000000 : ℝ)*X 2 0+(1007268693/2000000000 : ℝ)*X 2 1+(-1174322251/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4297801839/10000000000 : ℝ)*X 0 0+(3701072837/10000000000 : ℝ)*X 0 1+(249227449/500000000 : ℝ)*X 0 2+(4297801839/10000000000 : ℝ)*X 1 0+(3701072837/10000000000 : ℝ)*X 1 1+(249227449/500000000 : ℝ)*X 1 2+(4297801839/10000000000 : ℝ)*X 2 0+(3701072837/10000000000 : ℝ)*X 2 1+(249227449/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2017505859/10000000000 : ℝ)*X 0 0+(2522155067/5000000000 : ℝ)*X 0 1+(564821511/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((656065113/1250000000 : ℝ)*X 1 0+(-434193257/2500000000 : ℝ)*X 1 1+(5648214831/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1049704169/2000000000 : ℝ)*X 2 0+(2824107341/5000000000 : ℝ)*X 2 1+(-108548333/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((429903673/1000000000 : ℝ)*X 0 0+(2484028287/5000000000 : ℝ)*X 0 1+(1858936367/5000000000 : ℝ)*X 0 2+(429903673/1000000000 : ℝ)*X 1 0+(2484028287/5000000000 : ℝ)*X 1 1+(1858936367/5000000000 : ℝ)*X 1 2+(429903673/1000000000 : ℝ)*X 2 0+(2484028287/5000000000 : ℝ)*X 2 1+(1858936367/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (386577921051740795747454069/43195000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5174403/5000000000000 : ℝ)*(base1) + (398069167/25000000000000 : ℝ)*(base19) + (410593557/25000000000000 : ℝ)*(base23) + (240688539/100000000000000 : ℝ)*(upper3) + (4098569/2500000000000 : ℝ)*(upper5) + (11960494741907/1000000000000 : ℝ)*(major0) + (11960494741907/1000000000000 : ℝ)*(major1) + (11960494741907/1000000000000 : ℝ)*(major2) + (322589575054993/20000000000000 : ℝ)*(sp0) + (1612954455988087/100000000000000 : ℝ)*(sp1) + (1612954405890527/100000000000000 : ℝ)*(sp2) + (389569013104289/50000000000000 : ℝ)*(sp3) + (165529557/2000000000000 : ℝ)*(sp4) + (1118025011/25000000000000 : ℝ)*(sp7) + (389571300898341/50000000000000 : ℝ)*(f.failure) + (322591209652951/20000000000000 : ℝ)*(f.sum) + (847090766047/12958500000000000000000000000 : ℝ)*base66 + (1850128227208450931/259170000000000000000000000000000 : ℝ)*base67 + (610662385323679069/259170000000000000000000000000000 : ℝ)*base70 + (219022517403079069/259170000000000000000000000000000 : ℝ)*base72 + (109991968067989/25917000000000000000000000000 : ℝ)*base73 + (197135028709210931/259170000000000000000000000000000 : ℝ)*base75 + (442715202770200931/259170000000000000000000000000000 : ℝ)*base77 + (85576198159900931/259170000000000000000000000000000 : ℝ)*base79 + (61541895881587/12958500000000000000000000000 : ℝ)*base82 + (4836197/5000000000000000000000 : ℝ)*base89 + (4836197/5000000000000000000000 : ℝ)*base91 + (4836197/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7655320485996694509497567061/2159750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (601104797/100000000000000 : ℝ)*(base19) + (14531541/2500000000000 : ℝ)*(base23) + (3579891/20000000000000 : ℝ)*(upper2) + (1935913/4000000000000 : ℝ)*(upper3) + (58596639/50000000000000 : ℝ)*(upper5) + (1227886119555483/100000000000000 : ℝ)*(major0) + (1227886119555483/100000000000000 : ℝ)*(major1) + (1227886119555483/100000000000000 : ℝ)*(major2) + (1364590969/50000000000000 : ℝ)*(sp1) + (1573417683/100000000000000 : ℝ)*(sp2) + (1655890170802137/100000000000000 : ℝ)*(sp4) + (1655886840515403/100000000000000 : ℝ)*(sp5) + (1655888016122813/100000000000000 : ℝ)*(sp6) + (199970487539371/25000000000000 : ℝ)*(sp7) + (199970487539371/25000000000000 : ℝ)*(f.failure) + (1655890170802137/100000000000000 : ℝ)*(f.sum) + (191892366745863/43195000000000000000000000000 : ℝ)*base65 + (38582987118253194313/8639000000000000000000000000000000 : ℝ)*base67 + (18600330880125194313/8639000000000000000000000000000000 : ℝ)*base69 + (20295159687397194313/8639000000000000000000000000000000 : ℝ)*base71 + (15438306158463/2699687500000000000000000000 : ℝ)*base73 + (73074001623719805687/8639000000000000000000000000000000 : ℝ)*base76 + (91810924013249194313/8639000000000000000000000000000000 : ℝ)*base77 + (38442381320036194313/8639000000000000000000000000000000 : ℝ)*base79 + (50368102292877/10798750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (7614293/2500000000000000000000 : ℝ)*base90 + (7614293/2500000000000000000000 : ℝ)*base92 + (7614293/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1311_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153508417/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3387/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1179/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1319/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (19699/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1311_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1311_s2_0 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2059837611/10000000000 : ℝ)*x 0 + (548854181/1000000000 : ℝ)*x 1 + (2588341057/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2059837611/10000000000 : ℝ)^4271 ≤ (312880034527/2500000000000 : ℝ)^3247 := by
    have hnat : (2059837611 : ℕ)^4271*2500000000000^3247 ≤ 312880034527^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2059837611 10000000000 312880034527 2500000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (548854181/1000000000 : ℝ)^4271 ≤ (45424487533007/100000000000000 : ℝ)^3247 := by
    have hnat : (548854181 : ℕ)^4271*100000000000000^3247 ≤ 45424487533007^3247*1000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548854181 1000000000 45424487533007 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2588341057/5000000000 : ℝ)^4271 ≤ (657192360419/1562500000000 : ℝ)^3247 := by
    have hnat : (2588341057 : ℕ)^4271*1562500000000^3247 ≤ 657192360419^3247*5000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588341057 5000000000 657192360419 1562500000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2059837611/10000000000 : ℝ), (548854181/1000000000 : ℝ), (2588341057/5000000000 : ℝ)] ![(312880034527/2500000000000 : ℝ), (45424487533007/100000000000000 : ℝ), (657192360419/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2059837611/10000000000 : ℝ)|^4271 ≤ (312880034527/2500000000000 : ℝ)^3247
        have hw : |(-2059837611/10000000000 : ℝ)|=(2059837611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(548854181/1000000000 : ℝ)|^4271 ≤ (45424487533007/100000000000000 : ℝ)^3247
        have hw : |(548854181/1000000000 : ℝ)|=(548854181/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2588341057/5000000000 : ℝ)|^4271 ≤ (657192360419/1562500000000 : ℝ)^3247
        have hw : |(2588341057/5000000000 : ℝ)|=(2588341057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_s2_1 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2684088641/5000000000 : ℝ)*x 0 + (-222126379/1000000000 : ℝ)*x 1 + (5176681739/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684088641/5000000000 : ℝ)^4271 ≤ (44118717073921/100000000000000 : ℝ)^3247 := by
    have hnat : (2684088641 : ℕ)^4271*100000000000000^3247 ≤ 44118717073921^3247*5000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684088641 5000000000 44118717073921 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (222126379/1000000000 : ℝ)^4271 ≤ (6910487924441/50000000000000 : ℝ)^3247 := by
    have hnat : (222126379 : ℕ)^4271*50000000000000^3247 ≤ 6910487924441^3247*1000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      222126379 1000000000 6910487924441 50000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5176681739/10000000000 : ℝ)^4271 ≤ (10515076764769/25000000000000 : ℝ)^3247 := by
    have hnat : (5176681739 : ℕ)^4271*25000000000000^3247 ≤ 10515076764769^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176681739 10000000000 10515076764769 25000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684088641/5000000000 : ℝ), (-222126379/1000000000 : ℝ), (5176681739/10000000000 : ℝ)] ![(44118717073921/100000000000000 : ℝ), (6910487924441/50000000000000 : ℝ), (10515076764769/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684088641/5000000000 : ℝ)|^4271 ≤ (44118717073921/100000000000000 : ℝ)^3247
        have hw : |(2684088641/5000000000 : ℝ)|=(2684088641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-222126379/1000000000 : ℝ)|^4271 ≤ (6910487924441/50000000000000 : ℝ)^3247
        have hw : |(-222126379/1000000000 : ℝ)|=(222126379/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5176681739/10000000000 : ℝ)|^4271 ≤ (10515076764769/25000000000000 : ℝ)^3247
        have hw : |(5176681739/10000000000 : ℝ)|=(5176681739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_s2_2 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1073635349/2000000000 : ℝ)*x 0 + (5176682241/10000000000 : ℝ)*x 1 + (-444252769/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073635349/2000000000 : ℝ)^4271 ≤ (11029677817179/25000000000000 : ℝ)^3247 := by
    have hnat : (1073635349 : ℕ)^4271*25000000000000^3247 ≤ 11029677817179^3247*2000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073635349 2000000000 11029677817179 25000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5176682241/10000000000 : ℝ)^4271 ≤ (5257539053013/12500000000000 : ℝ)^3247 := by
    have hnat : (5176682241 : ℕ)^4271*12500000000000^3247 ≤ 5257539053013^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176682241 10000000000 5257539053013 12500000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (444252769/2000000000 : ℝ)^4271 ≤ (6910488149511/50000000000000 : ℝ)^3247 := by
    have hnat : (444252769 : ℕ)^4271*50000000000000^3247 ≤ 6910488149511^3247*2000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      444252769 2000000000 6910488149511 50000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073635349/2000000000 : ℝ), (5176682241/10000000000 : ℝ), (-444252769/2000000000 : ℝ)] ![(11029677817179/25000000000000 : ℝ), (5257539053013/12500000000000 : ℝ), (6910488149511/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073635349/2000000000 : ℝ)|^4271 ≤ (11029677817179/25000000000000 : ℝ)^3247
        have hw : |(1073635349/2000000000 : ℝ)|=(1073635349/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5176682241/10000000000 : ℝ)|^4271 ≤ (5257539053013/12500000000000 : ℝ)^3247
        have hw : |(5176682241/10000000000 : ℝ)|=(5176682241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-444252769/2000000000 : ℝ)|^4271 ≤ (6910488149511/50000000000000 : ℝ)^3247
        have hw : |(-444252769/2000000000 : ℝ)|=(444252769/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_s2_3 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (270481963/625000000 : ℝ)*x 0 + (4016280227/10000000000 : ℝ)*x 1 + (4661890409/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (270481963/625000000 : ℝ)^4271 ≤ (16615590876617/50000000000000 : ℝ)^3247 := by
    have hnat : (270481963 : ℕ)^4271*50000000000000^3247 ≤ 16615590876617^3247*625000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270481963 625000000 16615590876617 50000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4016280227/10000000000 : ℝ)^4271 ≤ (1882620490519/6250000000000 : ℝ)^3247 := by
    have hnat : (4016280227 : ℕ)^4271*6250000000000^3247 ≤ 1882620490519^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4016280227 10000000000 1882620490519 6250000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4661890409/10000000000 : ℝ)^4271 ≤ (36646890379559/100000000000000 : ℝ)^3247 := by
    have hnat : (4661890409 : ℕ)^4271*100000000000000^3247 ≤ 36646890379559^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4661890409 10000000000 36646890379559 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(270481963/625000000 : ℝ), (4016280227/10000000000 : ℝ), (4661890409/10000000000 : ℝ)] ![(16615590876617/50000000000000 : ℝ), (1882620490519/6250000000000 : ℝ), (36646890379559/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(270481963/625000000 : ℝ)|^4271 ≤ (16615590876617/50000000000000 : ℝ)^3247
        have hw : |(270481963/625000000 : ℝ)|=(270481963/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4016280227/10000000000 : ℝ)|^4271 ≤ (1882620490519/6250000000000 : ℝ)^3247
        have hw : |(4016280227/10000000000 : ℝ)|=(4016280227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4661890409/10000000000 : ℝ)|^4271 ≤ (36646890379559/100000000000000 : ℝ)^3247
        have hw : |(4661890409/10000000000 : ℝ)|=(4661890409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_s2_4 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2059913097/10000000000 : ℝ)*x 0 + (2589353537/5000000000 : ℝ)*x 1 + (2743249103/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2059913097/10000000000 : ℝ)^4271 ≤ (12515804664047/100000000000000 : ℝ)^3247 := by
    have hnat : (2059913097 : ℕ)^4271*100000000000000^3247 ≤ 12515804664047^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2059913097 10000000000 12515804664047 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2589353537/5000000000 : ℝ)^4271 ≤ (21040976884903/50000000000000 : ℝ)^3247 := by
    have hnat : (2589353537 : ℕ)^4271*50000000000000^3247 ≤ 21040976884903^3247*5000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2589353537 5000000000 21040976884903 50000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2743249103/5000000000 : ℝ)^4271 ≤ (22701120775409/50000000000000 : ℝ)^3247 := by
    have hnat : (2743249103 : ℕ)^4271*50000000000000^3247 ≤ 22701120775409^3247*5000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2743249103 5000000000 22701120775409 50000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2059913097/10000000000 : ℝ), (2589353537/5000000000 : ℝ), (2743249103/5000000000 : ℝ)] ![(12515804664047/100000000000000 : ℝ), (21040976884903/50000000000000 : ℝ), (22701120775409/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2059913097/10000000000 : ℝ)|^4271 ≤ (12515804664047/100000000000000 : ℝ)^3247
        have hw : |(-2059913097/10000000000 : ℝ)|=(2059913097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2589353537/5000000000 : ℝ)|^4271 ≤ (21040976884903/50000000000000 : ℝ)^3247
        have hw : |(2589353537/5000000000 : ℝ)|=(2589353537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2743249103/5000000000 : ℝ)|^4271 ≤ (22701120775409/50000000000000 : ℝ)^3247
        have hw : |(2743249103/5000000000 : ℝ)|=(2743249103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_s2_5 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (66100897/125000000 : ℝ)*x 0 + (-47786171/250000000 : ℝ)*x 1 + (5486498297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66100897/125000000 : ℝ)^4271 ≤ (43254785889917/100000000000000 : ℝ)^3247 := by
    have hnat : (66100897 : ℕ)^4271*100000000000000^3247 ≤ 43254785889917^3247*125000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66100897 125000000 43254785889917 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (47786171/250000000 : ℝ)^4271 ≤ (708935722341/6250000000000 : ℝ)^3247 := by
    have hnat : (47786171 : ℕ)^4271*6250000000000^3247 ≤ 708935722341^3247*250000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47786171 250000000 708935722341 6250000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5486498297/10000000000 : ℝ)^4271 ≤ (9080448508271/20000000000000 : ℝ)^3247 := by
    have hnat : (5486498297 : ℕ)^4271*20000000000000^3247 ≤ 9080448508271^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5486498297 10000000000 9080448508271 20000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66100897/125000000 : ℝ), (-47786171/250000000 : ℝ), (5486498297/10000000000 : ℝ)] ![(43254785889917/100000000000000 : ℝ), (708935722341/6250000000000 : ℝ), (9080448508271/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66100897/125000000 : ℝ)|^4271 ≤ (43254785889917/100000000000000 : ℝ)^3247
        have hw : |(66100897/125000000 : ℝ)|=(66100897/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-47786171/250000000 : ℝ)|^4271 ≤ (708935722341/6250000000000 : ℝ)^3247
        have hw : |(-47786171/250000000 : ℝ)|=(47786171/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5486498297/10000000000 : ℝ)|^4271 ≤ (9080448508271/20000000000000 : ℝ)^3247
        have hw : |(5486498297/10000000000 : ℝ)|=(5486498297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_s2_6 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644035939/5000000000 : ℝ)*x 0 + (5486498213/10000000000 : ℝ)*x 1 + (-955723397/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644035939/5000000000 : ℝ)^4271 ≤ (8650957431903/20000000000000 : ℝ)^3247 := by
    have hnat : (2644035939 : ℕ)^4271*20000000000000^3247 ≤ 8650957431903^3247*5000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644035939 5000000000 8650957431903 20000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5486498213/10000000000 : ℝ)^4271 ≤ (45402241627013/100000000000000 : ℝ)^3247 := by
    have hnat : (5486498213 : ℕ)^4271*100000000000000^3247 ≤ 45402241627013^3247*10000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5486498213 10000000000 45402241627013 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (955723397/5000000000 : ℝ)^4271 ≤ (5671485599197/50000000000000 : ℝ)^3247 := by
    have hnat : (955723397 : ℕ)^4271*50000000000000^3247 ≤ 5671485599197^3247*5000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      955723397 5000000000 5671485599197 50000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644035939/5000000000 : ℝ), (5486498213/10000000000 : ℝ), (-955723397/5000000000 : ℝ)] ![(8650957431903/20000000000000 : ℝ), (45402241627013/100000000000000 : ℝ), (5671485599197/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644035939/5000000000 : ℝ)|^4271 ≤ (8650957431903/20000000000000 : ℝ)^3247
        have hw : |(2644035939/5000000000 : ℝ)|=(2644035939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5486498213/10000000000 : ℝ)|^4271 ≤ (45402241627013/100000000000000 : ℝ)^3247
        have hw : |(5486498213/10000000000 : ℝ)|=(5486498213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-955723397/5000000000 : ℝ)|^4271 ≤ (5671485599197/50000000000000 : ℝ)^3247
        have hw : |(-955723397/5000000000 : ℝ)|=(955723397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1311_s2_7 (p : ℝ) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (865573291/2000000000 : ℝ)*x 0 + (1164424089/2500000000 : ℝ)*x 1 + (50256451/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (865573291/2000000000 : ℝ)^4271 ≤ (8308186946277/25000000000000 : ℝ)^3247 := by
    have hnat : (865573291 : ℕ)^4271*25000000000000^3247 ≤ 8308186946277^3247*2000000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      865573291 2000000000 8308186946277 25000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1164424089/2500000000 : ℝ)^4271 ≤ (18301764921871/50000000000000 : ℝ)^3247 := by
    have hnat : (1164424089 : ℕ)^4271*50000000000000^3247 ≤ 18301764921871^3247*2500000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1164424089 2500000000 18301764921871 50000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (50256451/125000000 : ℝ)^4271 ≤ (30163722347099/100000000000000 : ℝ)^3247 := by
    have hnat : (50256451 : ℕ)^4271*100000000000000^3247 ≤ 30163722347099^3247*125000000^4271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50256451 125000000 30163722347099 100000000000000 4271 3247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4271/1024 : ℝ)) 4271 3247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(865573291/2000000000 : ℝ), (1164424089/2500000000 : ℝ), (50256451/125000000 : ℝ)] ![(8308186946277/25000000000000 : ℝ), (18301764921871/50000000000000 : ℝ), (30163722347099/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(865573291/2000000000 : ℝ)|^4271 ≤ (8308186946277/25000000000000 : ℝ)^3247
        have hw : |(865573291/2000000000 : ℝ)|=(865573291/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1164424089/2500000000 : ℝ)|^4271 ≤ (18301764921871/50000000000000 : ℝ)^3247
        have hw : |(1164424089/2500000000 : ℝ)|=(1164424089/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(50256451/125000000 : ℝ)|^4271 ≤ (30163722347099/100000000000000 : ℝ)^3247
        have hw : |(50256451/125000000 : ℝ)|=(50256451/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1311_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153508417/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19699/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1319/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (9641/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16233/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (19699/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1319/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (19699/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1319/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (19699/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1319/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (19699/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1319/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (19699/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1319/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (19699/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1319/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1319/20000 : ℝ) ^ (2135/512 : ℝ) ≤ (595920010185723/50000000000000000000 : ℝ) := by
    have hpowers : (1319/20000 : ℝ)^2135 ≤ (595920010185723/50000000000000000000 : ℝ)^512 := by
      have hnat : (1319 : ℕ)^2135*50000000000000000000^512 ≤ 595920010185723^512*20000^2135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1319 20000 595920010185723 50000000000000000000 2135 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1319/20000 : ℝ)) (X := (595920010185723/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2135 512 (by norm_num) hpowers
    exact h
  have hpowhi : (19699/100000 : ℝ) ^ (2135/512 : ℝ) ≤ (114258193416510967/100000000000000000000 : ℝ) := by
    have hpowers : (19699/100000 : ℝ)^2135 ≤ (114258193416510967/100000000000000000000 : ℝ)^512 := by
      have hnat : (19699 : ℕ)^2135*100000000000000000000^512 ≤ 114258193416510967^512*100000^2135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19699 100000 114258193416510967 100000000000000000000 2135 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19699/100000 : ℝ)) (X := (114258193416510967/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2135 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000595920010185723/25000000000000000000 : ℝ) ≤ (250001429078599/250000000000000 : ℝ) ^ (2135/512 : ℝ) := by
    have hpowers : (25000595920010185723/25000000000000000000 : ℝ)^512 ≤ (250001429078599/250000000000000 : ℝ)^2135 := by
      have hnat : (25000595920010185723 : ℕ)^512*250000000000000^2135 ≤ 250001429078599^2135*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000595920010185723 25000000000000000000 250001429078599 250000000000000 512 2135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250001429078599/250000000000000 : ℝ)) (X := (25000595920010185723/25000000000000000000 : ℝ)) (by norm_num) 2135 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100115450033436882413/100000000000000000000 : ℝ) ≤ (10002767423697643/10000000000000000 : ℝ) ^ (2135/512 : ℝ) := by
    have hpowers : (100115450033436882413/100000000000000000000 : ℝ)^512 ≤ (10002767423697643/10000000000000000 : ℝ)^2135 := by
      have hnat : (100115450033436882413 : ℕ)^512*10000000000000000^2135 ≤ 10002767423697643^2135*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100115450033436882413 100000000000000000000 10002767423697643 10000000000000000 512 2135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002767423697643/10000000000000000 : ℝ)) (X := (100115450033436882413/100000000000000000000 : ℝ)) (by norm_num) 2135 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50114258193416510967/50000000000000000000 : ℝ) ≤ (5002738842125663/5000000000000000 : ℝ) ^ (2135/512 : ℝ) := by
    have hpowers : (50114258193416510967/50000000000000000000 : ℝ)^512 ≤ (5002738842125663/5000000000000000 : ℝ)^2135 := by
      have hnat : (50114258193416510967 : ℕ)^512*5000000000000000^2135 ≤ 5002738842125663^2135*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50114258193416510967 50000000000000000000 5002738842125663 5000000000000000 512 2135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002738842125663/5000000000000000 : ℝ)) (X := (50114258193416510967/50000000000000000000 : ℝ)) (by norm_num) 2135 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(595920010185723/50000000000000000000 : ℝ) ≤ ((4366833357637845769/4368000000000000000 : ℝ)+2*(903420184561/436800000000000 : ℝ)*(1319/20000 : ℝ))^(2135/512 : ℝ) := by
    rw [show (4366833357637845769/4368000000000000000 : ℝ)+2*(903420184561/436800000000000 : ℝ)*(1319/20000 : ℝ)=(250001429078599/250000000000000 : ℝ) by norm_num, show 1+2*(595920010185723/50000000000000000000 : ℝ)=(25000595920010185723/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(114258193416510967/100000000000000000000 : ℝ)+(595920010185723/50000000000000000000 : ℝ) ≤ ((4366833357637845769/4368000000000000000 : ℝ)+(903420184561/436800000000000 : ℝ)*((19699/100000 : ℝ)+(1319/20000 : ℝ)))^(2135/512 : ℝ) := by
    rw [show (4366833357637845769/4368000000000000000 : ℝ)+(903420184561/436800000000000 : ℝ)*((19699/100000 : ℝ)+(1319/20000 : ℝ))=(10002767423697643/10000000000000000 : ℝ) by norm_num, show 1+(114258193416510967/100000000000000000000 : ℝ)+(595920010185723/50000000000000000000 : ℝ)=(100115450033436882413/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(114258193416510967/100000000000000000000 : ℝ) ≤ ((4366833357637845769/4368000000000000000 : ℝ)+2*(903420184561/436800000000000 : ℝ)*(19699/100000 : ℝ))^(2135/512 : ℝ) := by
    rw [show (4366833357637845769/4368000000000000000 : ℝ)+2*(903420184561/436800000000000 : ℝ)*(19699/100000 : ℝ)=(5002738842125663/5000000000000000 : ℝ) by norm_num, show 1+2*(114258193416510967/100000000000000000000 : ℝ)=(50114258193416510967/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4366833357637845769/4368000000000000000 : ℝ)*(X 1 0+X 2 0)+(903420184561/436800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2135/512 : ℝ)) (lo := (1319/20000 : ℝ)) (hi := (19699/100000 : ℝ)) (c := (4366833357637845769/4368000000000000000 : ℝ)) (alpha := (903420184561/436800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4366833357637845769/4368000000000000000 : ℝ)*(X 0 1+X 2 1)+(903420184561/436800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2135/512 : ℝ)) (lo := (1319/20000 : ℝ)) (hi := (19699/100000 : ℝ)) (c := (4366833357637845769/4368000000000000000 : ℝ)) (alpha := (903420184561/436800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4366833357637845769/4368000000000000000 : ℝ)*(X 0 2+X 1 2)+(903420184561/436800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2135/512 : ℝ)) (lo := (1319/20000 : ℝ)) (hi := (19699/100000 : ℝ)) (c := (4366833357637845769/4368000000000000000 : ℝ)) (alpha := (903420184561/436800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2059837611/10000000000 : ℝ)*X 0 0+(548854181/1000000000 : ℝ)*X 0 1+(2588341057/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2684088641/5000000000 : ℝ)*X 1 0+(-222126379/1000000000 : ℝ)*X 1 1+(5176681739/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1073635349/2000000000 : ℝ)*X 2 0+(5176682241/10000000000 : ℝ)*X 2 1+(-444252769/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((270481963/625000000 : ℝ)*X 0 0+(4016280227/10000000000 : ℝ)*X 0 1+(4661890409/10000000000 : ℝ)*X 0 2+(270481963/625000000 : ℝ)*X 1 0+(4016280227/10000000000 : ℝ)*X 1 1+(4661890409/10000000000 : ℝ)*X 1 2+(270481963/625000000 : ℝ)*X 2 0+(4016280227/10000000000 : ℝ)*X 2 1+(4661890409/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2059913097/10000000000 : ℝ)*X 0 0+(2589353537/5000000000 : ℝ)*X 0 1+(2743249103/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((66100897/125000000 : ℝ)*X 1 0+(-47786171/250000000 : ℝ)*X 1 1+(5486498297/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2644035939/5000000000 : ℝ)*X 2 0+(5486498213/10000000000 : ℝ)*X 2 1+(-955723397/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((865573291/2000000000 : ℝ)*X 0 0+(1164424089/2500000000 : ℝ)*X 0 1+(50256451/125000000 : ℝ)*X 0 2+(865573291/2000000000 : ℝ)*X 1 0+(1164424089/2500000000 : ℝ)*X 1 1+(50256451/125000000 : ℝ)*X 1 2+(865573291/2000000000 : ℝ)*X 2 0+(1164424089/2500000000 : ℝ)*X 2 1+(50256451/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1311_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (481964040683962677240441731/72800000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (144313689/6250000000000 : ℝ)*(base19) + (743812709/50000000000000 : ℝ)*(base23) + (268744409/100000000000000 : ℝ)*(lower2) + (349764801/50000000000000 : ℝ)*(upper3) + (8975627/5000000000000 : ℝ)*(upper5) + (2377776877612501/100000000000000 : ℝ)*(major0) + (2377776877612501/100000000000000 : ℝ)*(major1) + (2377776877612501/100000000000000 : ℝ)*(major2) + (1603294335589559/50000000000000 : ℝ)*(sp0) + (1603297924802807/50000000000000 : ℝ)*(sp1) + (160329833549961/5000000000000 : ℝ)*(sp2) + (387234057260387/25000000000000 : ℝ)*(sp3) + (118593069/1250000000000 : ℝ)*(sp4) + (3829375861/20000000000000 : ℝ)*(sp7) + (1548955375920853/100000000000000 : ℝ)*(f.failure) + (1603299079312319/50000000000000 : ℝ)*(f.sum) + (40250240466421/21840000000000000000000000000 : ℝ)*base65 + (401089905030168269/436800000000000000000000000000000 : ℝ)*base67 + (3555810608127768269/436800000000000000000000000000000 : ℝ)*base69 + (205117939102631731/436800000000000000000000000000000 : ℝ)*base72 + (98928568648379/21840000000000000000000000000 : ℝ)*base74 + (3598595092124568269/436800000000000000000000000000000 : ℝ)*base75 + (2860048418823768269/436800000000000000000000000000000 : ℝ)*base77 + (535112253497831731/436800000000000000000000000000000 : ℝ)*base80 + (14647347245819/21840000000000000000000000000 : ℝ)*base82 + (38680299/10000000000000000000000 : ℝ)*base90 + (38680299/10000000000000000000000 : ℝ)*base92 + (38680299/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (36517024032896036026647/3640000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1939881887/100000000000000 : ℝ)*(base19) + (284680621/12500000000000 : ℝ)*(base23) + (267983843/100000000000000 : ℝ)*(upper3) + (51576967/50000000000000 : ℝ)*(lower4) + (78830091/50000000000000 : ℝ)*(upper5) + (1204592282290353/50000000000000 : ℝ)*(major0) + (1204592282290353/50000000000000 : ℝ)*(major1) + (1204592282290353/50000000000000 : ℝ)*(major2) + (20565319613/100000000000000 : ℝ)*(sp1) + (25186208349/100000000000000 : ℝ)*(sp2) + (3248953506876343/100000000000000 : ℝ)*(sp4) + (812232750418711/25000000000000 : ℝ)*(sp5) + (1624463021611513/50000000000000 : ℝ)*(sp6) + (784707643940041/50000000000000 : ℝ)*(sp7) + (784707643940041/50000000000000 : ℝ)*(f.failure) + (3248953506876343/100000000000000 : ℝ)*(f.sum) + (14621154261949/3640000000000000000000000000 : ℝ)*base66 + (246163459643098819/72800000000000000000000000000000 : ℝ)*base67 + (350323687159898819/72800000000000000000000000000000 : ℝ)*base69 + (633031587414501181/72800000000000000000000000000000 : ℝ)*base72 + (17971078418331/3640000000000000000000000000 : ℝ)*base73 + (271100535677701181/72800000000000000000000000000000 : ℝ)*base76 + (2885911019898819/72800000000000000000000000000000 : ℝ)*base77 + (202745529248901181/72800000000000000000000000000000 : ℝ)*base80 + (1387882519971/3640000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (36825097/5000000000000000000000 : ℝ)*base89 + (36825097/5000000000000000000000 : ℝ)*base91 + (36825097/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1311_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153508417/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19699/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1319/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9641/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16233/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1311_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1311_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153508417/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9641/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16233/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1311_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1311_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1311_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2135/512 : ℝ) ≤ p) (hpb : p ≤ (4271/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153508417/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9641/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16233/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1311_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
