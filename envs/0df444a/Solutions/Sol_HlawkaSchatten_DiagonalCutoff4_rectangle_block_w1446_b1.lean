-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1446_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:58:13.570354+00:00
-- url     : https://prove2.me/submissions/7f80e3e7-c54f-41af-bbf9-7cac16dc1c32

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
theorem support_rectangle_w1446_s3_0 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-978231781/5000000000 : ℝ)*x 0 + (1353900671/2500000000 : ℝ)*x 1 + (261982217/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (978231781/5000000000 : ℝ)^2203 ≤ (186536584751/1562500000000 : ℝ)^1691 := by
    have hnat : (978231781 : ℕ)^2203*1562500000000^1691 ≤ 186536584751^1691*5000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      978231781 5000000000 186536584751 1562500000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353900671/2500000000 : ℝ)^2203 ≤ (44978039933801/100000000000000 : ℝ)^1691 := by
    have hnat : (1353900671 : ℕ)^2203*100000000000000^1691 ≤ 44978039933801^1691*2500000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353900671 2500000000 44978039933801 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (261982217/500000000 : ℝ)^2203 ≤ (43083618633783/100000000000000 : ℝ)^1691 := by
    have hnat : (261982217 : ℕ)^2203*100000000000000^1691 ≤ 43083618633783^1691*500000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261982217 500000000 43083618633783 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-978231781/5000000000 : ℝ), (1353900671/2500000000 : ℝ), (261982217/500000000 : ℝ)] ![(186536584751/1562500000000 : ℝ), (44978039933801/100000000000000 : ℝ), (43083618633783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-978231781/5000000000 : ℝ)|^2203 ≤ (186536584751/1562500000000 : ℝ)^1691
        have hw : |(-978231781/5000000000 : ℝ)|=(978231781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353900671/2500000000 : ℝ)|^2203 ≤ (44978039933801/100000000000000 : ℝ)^1691
        have hw : |(1353900671/2500000000 : ℝ)|=(1353900671/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(261982217/500000000 : ℝ)|^2203 ≤ (43083618633783/100000000000000 : ℝ)^1691
        have hw : |(261982217/500000000 : ℝ)|=(261982217/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_s3_1 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1337275321/2500000000 : ℝ)*x 0 + (-409238421/2000000000 : ℝ)*x 1 + (5239643971/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337275321/2500000000 : ℝ)^2203 ≤ (11064960156751/25000000000000 : ℝ)^1691 := by
    have hnat : (1337275321 : ℕ)^2203*25000000000000^1691 ≤ 11064960156751^1691*2500000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337275321 2500000000 11064960156751 25000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (409238421/2000000000 : ℝ)^2203 ≤ (6328272336817/50000000000000 : ℝ)^1691 := by
    have hnat : (409238421 : ℕ)^2203*50000000000000^1691 ≤ 6328272336817^1691*2000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      409238421 2000000000 6328272336817 50000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5239643971/10000000000 : ℝ)^2203 ≤ (21541807340479/50000000000000 : ℝ)^1691 := by
    have hnat : (5239643971 : ℕ)^2203*50000000000000^1691 ≤ 21541807340479^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239643971 10000000000 21541807340479 50000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337275321/2500000000 : ℝ), (-409238421/2000000000 : ℝ), (5239643971/10000000000 : ℝ)] ![(11064960156751/25000000000000 : ℝ), (6328272336817/50000000000000 : ℝ), (21541807340479/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337275321/2500000000 : ℝ)|^2203 ≤ (11064960156751/25000000000000 : ℝ)^1691
        have hw : |(1337275321/2500000000 : ℝ)|=(1337275321/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-409238421/2000000000 : ℝ)|^2203 ≤ (6328272336817/50000000000000 : ℝ)^1691
        have hw : |(-409238421/2000000000 : ℝ)|=(409238421/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5239643971/10000000000 : ℝ)|^2203 ≤ (21541807340479/50000000000000 : ℝ)^1691
        have hw : |(5239643971/10000000000 : ℝ)|=(5239643971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_s3_2 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5349101343/10000000000 : ℝ)*x 0 + (523964399/1000000000 : ℝ)*x 1 + (-2046192001/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349101343/10000000000 : ℝ)^2203 ≤ (11064960315749/25000000000000 : ℝ)^1691 := by
    have hnat : (5349101343 : ℕ)^2203*25000000000000^1691 ≤ 11064960315749^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349101343 10000000000 11064960315749 25000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (523964399/1000000000 : ℝ)^2203 ≤ (43083614884491/100000000000000 : ℝ)^1691 := by
    have hnat : (523964399 : ℕ)^2203*100000000000000^1691 ≤ 43083614884491^1691*1000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523964399 1000000000 43083614884491 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2046192001/10000000000 : ℝ)^2203 ≤ (6328271917789/50000000000000 : ℝ)^1691 := by
    have hnat : (2046192001 : ℕ)^2203*50000000000000^1691 ≤ 6328271917789^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2046192001 10000000000 6328271917789 50000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349101343/10000000000 : ℝ), (523964399/1000000000 : ℝ), (-2046192001/10000000000 : ℝ)] ![(11064960315749/25000000000000 : ℝ), (43083614884491/100000000000000 : ℝ), (6328271917789/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349101343/10000000000 : ℝ)|^2203 ≤ (11064960315749/25000000000000 : ℝ)^1691
        have hw : |(5349101343/10000000000 : ℝ)|=(5349101343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(523964399/1000000000 : ℝ)|^2203 ≤ (43083614884491/100000000000000 : ℝ)^1691
        have hw : |(523964399/1000000000 : ℝ)|=(523964399/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2046192001/10000000000 : ℝ)|^2203 ≤ (6328271917789/50000000000000 : ℝ)^1691
        have hw : |(-2046192001/10000000000 : ℝ)|=(2046192001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_s3_3 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (429955469/1000000000 : ℝ)*x 0 + (4111847613/10000000000 : ℝ)*x 1 + (898975377/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (429955469/1000000000 : ℝ)^2203 ≤ (16649517598339/50000000000000 : ℝ)^1691 := by
    have hnat : (429955469 : ℕ)^2203*50000000000000^1691 ≤ 16649517598339^1691*1000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429955469 1000000000 16649517598339 50000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4111847613/10000000000 : ℝ)^2203 ≤ (15708885180937/50000000000000 : ℝ)^1691 := by
    have hnat : (4111847613 : ℕ)^2203*50000000000000^1691 ≤ 15708885180937^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4111847613 10000000000 15708885180937 50000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (898975377/2000000000 : ℝ)^2203 ≤ (28226555543/80000000000 : ℝ)^1691 := by
    have hnat : (898975377 : ℕ)^2203*80000000000^1691 ≤ 28226555543^1691*2000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898975377 2000000000 28226555543 80000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(429955469/1000000000 : ℝ), (4111847613/10000000000 : ℝ), (898975377/2000000000 : ℝ)] ![(16649517598339/50000000000000 : ℝ), (15708885180937/50000000000000 : ℝ), (28226555543/80000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(429955469/1000000000 : ℝ)|^2203 ≤ (16649517598339/50000000000000 : ℝ)^1691
        have hw : |(429955469/1000000000 : ℝ)|=(429955469/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4111847613/10000000000 : ℝ)|^2203 ≤ (15708885180937/50000000000000 : ℝ)^1691
        have hw : |(4111847613/10000000000 : ℝ)|=(4111847613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(898975377/2000000000 : ℝ)|^2203 ≤ (28226555543/80000000000 : ℝ)^1691
        have hw : |(898975377/2000000000 : ℝ)|=(898975377/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_s3_4 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-39129561/200000000 : ℝ)*x 0 + (81880353/156250000 : ℝ)*x 1 + (5414900707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (39129561/200000000 : ℝ)^2203 ≤ (5969228298713/50000000000000 : ℝ)^1691 := by
    have hnat : (39129561 : ℕ)^2203*50000000000000^1691 ≤ 5969228298713^1691*200000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39129561 200000000 5969228298713 50000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (81880353/156250000 : ℝ)^2203 ≤ (5386387330527/12500000000000 : ℝ)^1691 := by
    have hnat : (81880353 : ℕ)^2203*12500000000000^1691 ≤ 5386387330527^1691*156250000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81880353 156250000 5386387330527 12500000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5414900707/10000000000 : ℝ)^2203 ≤ (1405326398059/3125000000000 : ℝ)^1691 := by
    have hnat : (5414900707 : ℕ)^2203*3125000000000^1691 ≤ 1405326398059^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414900707 10000000000 1405326398059 3125000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-39129561/200000000 : ℝ), (81880353/156250000 : ℝ), (5414900707/10000000000 : ℝ)] ![(5969228298713/50000000000000 : ℝ), (5386387330527/12500000000000 : ℝ), (1405326398059/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-39129561/200000000 : ℝ)|^2203 ≤ (5969228298713/50000000000000 : ℝ)^1691
        have hw : |(-39129561/200000000 : ℝ)|=(39129561/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(81880353/156250000 : ℝ)|^2203 ≤ (5386387330527/12500000000000 : ℝ)^1691
        have hw : |(81880353/156250000 : ℝ)|=(81880353/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5414900707/10000000000 : ℝ)|^2203 ≤ (1405326398059/3125000000000 : ℝ)^1691
        have hw : |(5414900707/10000000000 : ℝ)|=(5414900707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_s3_5 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2651641191/5000000000 : ℝ)*x 0 + (-1870935813/10000000000 : ℝ)*x 1 + (2707450331/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651641191/5000000000 : ℝ)^2203 ≤ (273541100351/625000000000 : ℝ)^1691 := by
    have hnat : (2651641191 : ℕ)^2203*625000000000^1691 ≤ 273541100351^1691*5000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651641191 5000000000 273541100351 625000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1870935813/10000000000 : ℝ)^2203 ≤ (11262979671961/100000000000000 : ℝ)^1691 := by
    have hnat : (1870935813 : ℕ)^2203*100000000000000^1691 ≤ 11262979671961^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1870935813 10000000000 11262979671961 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707450331/5000000000 : ℝ)^2203 ≤ (4497044425101/10000000000000 : ℝ)^1691 := by
    have hnat : (2707450331 : ℕ)^2203*10000000000000^1691 ≤ 4497044425101^1691*5000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707450331 5000000000 4497044425101 10000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651641191/5000000000 : ℝ), (-1870935813/10000000000 : ℝ), (2707450331/5000000000 : ℝ)] ![(273541100351/625000000000 : ℝ), (11262979671961/100000000000000 : ℝ), (4497044425101/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651641191/5000000000 : ℝ)|^2203 ≤ (273541100351/625000000000 : ℝ)^1691
        have hw : |(2651641191/5000000000 : ℝ)|=(2651641191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1870935813/10000000000 : ℝ)|^2203 ≤ (11262979671961/100000000000000 : ℝ)^1691
        have hw : |(-1870935813/10000000000 : ℝ)|=(1870935813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707450331/5000000000 : ℝ)|^2203 ≤ (4497044425101/10000000000000 : ℝ)^1691
        have hw : |(2707450331/5000000000 : ℝ)|=(2707450331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_s3_6 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (530328117/1000000000 : ℝ)*x 0 + (1082980327/2000000000 : ℝ)*x 1 + (-1870936133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530328117/1000000000 : ℝ)^2203 ≤ (5470820378169/12500000000000 : ℝ)^1691 := by
    have hnat : (530328117 : ℕ)^2203*12500000000000^1691 ≤ 5470820378169^1691*1000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530328117 1000000000 5470820378169 12500000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082980327/2000000000 : ℝ)^2203 ≤ (44970454778393/100000000000000 : ℝ)^1691 := by
    have hnat : (1082980327 : ℕ)^2203*100000000000000^1691 ≤ 44970454778393^1691*2000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082980327 2000000000 44970454778393 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1870936133/10000000000 : ℝ)^2203 ≤ (11262982181623/100000000000000 : ℝ)^1691 := by
    have hnat : (1870936133 : ℕ)^2203*100000000000000^1691 ≤ 11262982181623^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1870936133 10000000000 11262982181623 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530328117/1000000000 : ℝ), (1082980327/2000000000 : ℝ), (-1870936133/10000000000 : ℝ)] ![(5470820378169/12500000000000 : ℝ), (44970454778393/100000000000000 : ℝ), (11262982181623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530328117/1000000000 : ℝ)|^2203 ≤ (5470820378169/12500000000000 : ℝ)^1691
        have hw : |(530328117/1000000000 : ℝ)|=(530328117/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1082980327/2000000000 : ℝ)|^2203 ≤ (44970454778393/100000000000000 : ℝ)^1691
        have hw : |(1082980327/2000000000 : ℝ)|=(1082980327/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1870936133/10000000000 : ℝ)|^2203 ≤ (11262982181623/100000000000000 : ℝ)^1691
        have hw : |(-1870936133/10000000000 : ℝ)|=(1870936133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_s3_7 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (859917231/2000000000 : ℝ)*x 0 + (449335743/1000000000 : ℝ)*x 1 + (2056688271/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (859917231/2000000000 : ℝ)^2203 ≤ (2081209541877/6250000000000 : ℝ)^1691 := by
    have hnat : (859917231 : ℕ)^2203*6250000000000^1691 ≤ 2081209541877^1691*2000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      859917231 2000000000 2081209541877 6250000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (449335743/1000000000 : ℝ)^2203 ≤ (35267656733419/100000000000000 : ℝ)^1691 := by
    have hnat : (449335743 : ℕ)^2203*100000000000000^1691 ≤ 35267656733419^1691*1000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449335743 1000000000 35267656733419 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2056688271/5000000000 : ℝ)^2203 ≤ (6286598116881/20000000000000 : ℝ)^1691 := by
    have hnat : (2056688271 : ℕ)^2203*20000000000000^1691 ≤ 6286598116881^1691*5000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2056688271 5000000000 6286598116881 20000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(859917231/2000000000 : ℝ), (449335743/1000000000 : ℝ), (2056688271/5000000000 : ℝ)] ![(2081209541877/6250000000000 : ℝ), (35267656733419/100000000000000 : ℝ), (6286598116881/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(859917231/2000000000 : ℝ)|^2203 ≤ (2081209541877/6250000000000 : ℝ)^1691
        have hw : |(859917231/2000000000 : ℝ)|=(859917231/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(449335743/1000000000 : ℝ)|^2203 ≤ (35267656733419/100000000000000 : ℝ)^1691
        have hw : |(449335743/1000000000 : ℝ)|=(449335743/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2056688271/5000000000 : ℝ)|^2203 ≤ (6286598116881/20000000000000 : ℝ)^1691
        have hw : |(2056688271/5000000000 : ℝ)|=(2056688271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1446_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158840811/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15749/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1307/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (11211/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7469/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15749/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1307/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15749/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1307/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15749/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1307/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15749/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1307/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15749/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1307/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15749/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1307/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base29 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0, f.sum]
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
  have hpowlo : (1307/12500 : ℝ) ^ (4405/1024 : ℝ) ≤ (6047114601821981/100000000000000000000 : ℝ) := by
    have hpowers : (1307/12500 : ℝ)^4405 ≤ (6047114601821981/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1307 : ℕ)^4405*100000000000000000000^1024 ≤ 6047114601821981^1024*12500^4405 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1307 12500 6047114601821981 100000000000000000000 4405 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1307/12500 : ℝ)) (X := (6047114601821981/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4405 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15749/100000 : ℝ) ^ (4405/1024 : ℝ) ≤ (17609488954776577/50000000000000000000 : ℝ) := by
    have hpowers : (15749/100000 : ℝ)^4405 ≤ (17609488954776577/50000000000000000000 : ℝ)^1024 := by
      have hnat : (15749 : ℕ)^4405*50000000000000000000^1024 ≤ 17609488954776577^1024*100000^4405 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15749 100000 17609488954776577 50000000000000000000 4405 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15749/100000 : ℝ)) (X := (17609488954776577/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4405 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006047114601821981/50000000000000000000 : ℝ) ≤ (10000281133165353/10000000000000000 : ℝ) ^ (4405/1024 : ℝ) := by
    have hpowers : (50006047114601821981/50000000000000000000 : ℝ)^1024 ≤ (10000281133165353/10000000000000000 : ℝ)^4405 := by
      have hnat : (50006047114601821981 : ℕ)^1024*10000000000000000^4405 ≤ 10000281133165353^4405*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006047114601821981 50000000000000000000 10000281133165353 10000000000000000 1024 4405 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000281133165353/10000000000000000 : ℝ)) (X := (50006047114601821981/50000000000000000000 : ℝ)) (by norm_num) 4405 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20008253218502275027/20000000000000000000 : ℝ) ≤ (5000479566269677/5000000000000000 : ℝ) ^ (4405/1024 : ℝ) := by
    have hpowers : (20008253218502275027/20000000000000000000 : ℝ)^1024 ≤ (5000479566269677/5000000000000000 : ℝ)^4405 := by
      have hnat : (20008253218502275027 : ℕ)^1024*5000000000000000^4405 ≤ 5000479566269677^4405*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20008253218502275027 20000000000000000000 5000479566269677 5000000000000000 1024 4405 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000479566269677/5000000000000000 : ℝ)) (X := (20008253218502275027/20000000000000000000 : ℝ)) (by norm_num) 4405 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017609488954776577/25000000000000000000 : ℝ) ≤ (2000327426382671/2000000000000000 : ℝ) ^ (4405/1024 : ℝ) := by
    have hpowers : (25017609488954776577/25000000000000000000 : ℝ)^1024 ≤ (2000327426382671/2000000000000000 : ℝ)^4405 := by
      have hnat : (25017609488954776577 : ℕ)^1024*2000000000000000^4405 ≤ 2000327426382671^4405*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017609488954776577 25000000000000000000 2000327426382671 2000000000000000 1024 4405 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000327426382671/2000000000000000 : ℝ)) (X := (25017609488954776577/25000000000000000000 : ℝ)) (by norm_num) 4405 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6047114601821981/100000000000000000000 : ℝ) ≤ ((52917309714935104517/52930000000000000000 : ℝ)+2*(677999374001/529300000000000 : ℝ)*(1307/12500 : ℝ))^(4405/1024 : ℝ) := by
    rw [show (52917309714935104517/52930000000000000000 : ℝ)+2*(677999374001/529300000000000 : ℝ)*(1307/12500 : ℝ)=(10000281133165353/10000000000000000 : ℝ) by norm_num, show 1+2*(6047114601821981/100000000000000000000 : ℝ)=(50006047114601821981/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17609488954776577/50000000000000000000 : ℝ)+(6047114601821981/100000000000000000000 : ℝ) ≤ ((52917309714935104517/52930000000000000000 : ℝ)+(677999374001/529300000000000 : ℝ)*((15749/100000 : ℝ)+(1307/12500 : ℝ)))^(4405/1024 : ℝ) := by
    rw [show (52917309714935104517/52930000000000000000 : ℝ)+(677999374001/529300000000000 : ℝ)*((15749/100000 : ℝ)+(1307/12500 : ℝ))=(5000479566269677/5000000000000000 : ℝ) by norm_num, show 1+(17609488954776577/50000000000000000000 : ℝ)+(6047114601821981/100000000000000000000 : ℝ)=(20008253218502275027/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17609488954776577/50000000000000000000 : ℝ) ≤ ((52917309714935104517/52930000000000000000 : ℝ)+2*(677999374001/529300000000000 : ℝ)*(15749/100000 : ℝ))^(4405/1024 : ℝ) := by
    rw [show (52917309714935104517/52930000000000000000 : ℝ)+2*(677999374001/529300000000000 : ℝ)*(15749/100000 : ℝ)=(2000327426382671/2000000000000000 : ℝ) by norm_num, show 1+2*(17609488954776577/50000000000000000000 : ℝ)=(25017609488954776577/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (52917309714935104517/52930000000000000000 : ℝ)*(X 1 0+X 2 0)+(677999374001/529300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4405/1024 : ℝ)) (lo := (1307/12500 : ℝ)) (hi := (15749/100000 : ℝ)) (c := (52917309714935104517/52930000000000000000 : ℝ)) (alpha := (677999374001/529300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (52917309714935104517/52930000000000000000 : ℝ)*(X 0 1+X 2 1)+(677999374001/529300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4405/1024 : ℝ)) (lo := (1307/12500 : ℝ)) (hi := (15749/100000 : ℝ)) (c := (52917309714935104517/52930000000000000000 : ℝ)) (alpha := (677999374001/529300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (52917309714935104517/52930000000000000000 : ℝ)*(X 0 2+X 1 2)+(677999374001/529300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4405/1024 : ℝ)) (lo := (1307/12500 : ℝ)) (hi := (15749/100000 : ℝ)) (c := (52917309714935104517/52930000000000000000 : ℝ)) (alpha := (677999374001/529300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-978231781/5000000000 : ℝ)*X 0 0+(1353900671/2500000000 : ℝ)*X 0 1+(261982217/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337275321/2500000000 : ℝ)*X 1 0+(-409238421/2000000000 : ℝ)*X 1 1+(5239643971/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349101343/10000000000 : ℝ)*X 2 0+(523964399/1000000000 : ℝ)*X 2 1+(-2046192001/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((429955469/1000000000 : ℝ)*X 0 0+(4111847613/10000000000 : ℝ)*X 0 1+(898975377/2000000000 : ℝ)*X 0 2+(429955469/1000000000 : ℝ)*X 1 0+(4111847613/10000000000 : ℝ)*X 1 1+(898975377/2000000000 : ℝ)*X 1 2+(429955469/1000000000 : ℝ)*X 2 0+(4111847613/10000000000 : ℝ)*X 2 1+(898975377/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-39129561/200000000 : ℝ)*X 0 0+(81880353/156250000 : ℝ)*X 0 1+(5414900707/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2651641191/5000000000 : ℝ)*X 1 0+(-1870935813/10000000000 : ℝ)*X 1 1+(2707450331/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((530328117/1000000000 : ℝ)*X 2 0+(1082980327/2000000000 : ℝ)*X 2 1+(-1870936133/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((859917231/2000000000 : ℝ)*X 0 0+(449335743/1000000000 : ℝ)*X 0 1+(2056688271/5000000000 : ℝ)*X 0 2+(859917231/2000000000 : ℝ)*X 1 0+(449335743/1000000000 : ℝ)*X 1 1+(2056688271/5000000000 : ℝ)*X 1 2+(859917231/2000000000 : ℝ)*X 2 0+(449335743/1000000000 : ℝ)*X 2 1+(2056688271/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (307616065927303437891759/26465000000000000000000000000 : ℝ) := by norm_num
    linear_combination (253752149/12500000000000 : ℝ)*(base19) + (1904698519/100000000000000 : ℝ)*(base23) + (5028263/5000000000000 : ℝ)*(lower2) + (83963203/50000000000000 : ℝ)*(upper3) + (162134219/100000000000000 : ℝ)*(upper5) + (1036753308079729/25000000000000 : ℝ)*(major0) + (1036753308079729/25000000000000 : ℝ)*(major1) + (1036753308079729/25000000000000 : ℝ)*(major2) + (2841597080259461/50000000000000 : ℝ)*(sp0) + (2841612861301011/50000000000000 : ℝ)*(sp1) + (2841612923960347/50000000000000 : ℝ)*(sp2) + (1305390922453211/50000000000000 : ℝ)*(sp3) + (33592100291/100000000000000 : ℝ)*(sp4) + (8239831007/50000000000000 : ℝ)*(sp7) + (652699581142109/25000000000000 : ℝ)*(f.failure) + (2841613876309607/50000000000000 : ℝ)*(f.sum) + (2858226857353/3308125000000000000000000000 : ℝ)*base66 + (909530501347564107/1323250000000000000000000000000000 : ℝ)*base68 + (8155231328363185893/1323250000000000000000000000000000 : ℝ)*base69 + (4428438863703435893/1323250000000000000000000000000000 : ℝ)*base71 + (14042652643403/3308125000000000000000000000 : ℝ)*base74 + (26955490035008064107/1323250000000000000000000000000000 : ℝ)*base76 + (11929022404292935893/1323250000000000000000000000000000 : ℝ)*base77 + (11276993302602564107/1323250000000000000000000000000000 : ℝ)*base80 + (9528596882543/3308125000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (189601/2500000000000000000000 : ℝ)*base90 + (189601/2500000000000000000000 : ℝ)*base92 + (189601/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1493033569519526328020404767/1323250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (93641919/25000000000000 : ℝ)*(base8) + (858050943/100000000000000 : ℝ)*(base21) + (133251483/50000000000000 : ℝ)*(base29) + (288102751/100000000000000 : ℝ)*(upper2) + (2090114926083817/50000000000000 : ℝ)*(major0) + (20901150593353/500000000000 : ℝ)*(major1) + (20901150593353/500000000000 : ℝ)*(major2) + (1450077961/100000000000000 : ℝ)*(sp0) + (834369101/25000000000000 : ℝ)*(sp1) + (807995269/20000000000000 : ℝ)*(sp2) + (2864373995053541/50000000000000 : ℝ)*(sp4) + (1432186552693337/25000000000000 : ℝ)*(sp5) + (1145748930044493/20000000000000 : ℝ)*(sp6) + (657927596244551/25000000000000 : ℝ)*(sp7) + (657927596244551/25000000000000 : ℝ)*(f.failure) + (5728749814752719/100000000000000 : ℝ)*(f.sum) + (35086243549107/2646500000000000000000000000 : ℝ)*base66 + (325036229540644499/26465000000000000000000000000000 : ℝ)*base68 + (243707926727354499/26465000000000000000000000000000 : ℝ)*base70 + (25137305252350698611/2646500000000000000000000000000000 : ℝ)*base72 + (185818314918723/26465000000000000000000000000 : ℝ)*base74 + (141219762026727499/26465000000000000000000000000000 : ℝ)*base76 + (11040875739805198611/2646500000000000000000000000000000 : ℝ)*base78 + (398983445091132499/26465000000000000000000000000000 : ℝ)*base80 + (33541166216653/26465000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (35170861/2500000000000000000000 : ℝ)*base89 + (35170861/2500000000000000000000 : ℝ)*base91 + (35170861/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1446_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158840811/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15749/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1307/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11211/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7469/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1446_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1446_s4_0 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-391456943/2000000000 : ℝ)*x 0 + (1352139561/2500000000 : ℝ)*x 1 + (2623073773/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (391456943/2000000000 : ℝ)^2203 ≤ (2986217411071/25000000000000 : ℝ)^1691 := by
    have hnat : (391456943 : ℕ)^2203*25000000000000^1691 ≤ 2986217411071^1691*2000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      391456943 2000000000 2986217411071 25000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352139561/2500000000 : ℝ)^2203 ≤ (44901834570461/100000000000000 : ℝ)^1691 := by
    have hnat : (1352139561 : ℕ)^2203*100000000000000^1691 ≤ 44901834570461^1691*2500000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352139561 2500000000 44901834570461 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623073773/5000000000 : ℝ)^2203 ≤ (21576647888563/50000000000000 : ℝ)^1691 := by
    have hnat : (2623073773 : ℕ)^2203*50000000000000^1691 ≤ 21576647888563^1691*5000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623073773 5000000000 21576647888563 50000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-391456943/2000000000 : ℝ), (1352139561/2500000000 : ℝ), (2623073773/5000000000 : ℝ)] ![(2986217411071/25000000000000 : ℝ), (44901834570461/100000000000000 : ℝ), (21576647888563/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-391456943/2000000000 : ℝ)|^2203 ≤ (2986217411071/25000000000000 : ℝ)^1691
        have hw : |(-391456943/2000000000 : ℝ)|=(391456943/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352139561/2500000000 : ℝ)|^2203 ≤ (44901834570461/100000000000000 : ℝ)^1691
        have hw : |(1352139561/2500000000 : ℝ)|=(1352139561/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623073773/5000000000 : ℝ)|^2203 ≤ (21576647888563/50000000000000 : ℝ)^1691
        have hw : |(2623073773/5000000000 : ℝ)|=(2623073773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_s4_1 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5347278467/10000000000 : ℝ)*x 0 + (-2039980363/10000000000 : ℝ)*x 1 + (5246147511/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347278467/10000000000 : ℝ)^2203 ≤ (44240192526223/100000000000000 : ℝ)^1691 := by
    have hnat : (5347278467 : ℕ)^2203*100000000000000^1691 ≤ 44240192526223^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347278467 10000000000 44240192526223 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2039980363/10000000000 : ℝ)^2203 ≤ (6303256025439/50000000000000 : ℝ)^1691 := by
    have hnat : (2039980363 : ℕ)^2203*50000000000000^1691 ≤ 6303256025439^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2039980363 10000000000 6303256025439 50000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246147511/10000000000 : ℝ)^2203 ≤ (5394161925257/12500000000000 : ℝ)^1691 := by
    have hnat : (5246147511 : ℕ)^2203*12500000000000^1691 ≤ 5394161925257^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246147511 10000000000 5394161925257 12500000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347278467/10000000000 : ℝ), (-2039980363/10000000000 : ℝ), (5246147511/10000000000 : ℝ)] ![(44240192526223/100000000000000 : ℝ), (6303256025439/50000000000000 : ℝ), (5394161925257/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347278467/10000000000 : ℝ)|^2203 ≤ (44240192526223/100000000000000 : ℝ)^1691
        have hw : |(5347278467/10000000000 : ℝ)|=(5347278467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2039980363/10000000000 : ℝ)|^2203 ≤ (6303256025439/50000000000000 : ℝ)^1691
        have hw : |(-2039980363/10000000000 : ℝ)|=(2039980363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246147511/10000000000 : ℝ)|^2203 ≤ (5394161925257/12500000000000 : ℝ)^1691
        have hw : |(5246147511/10000000000 : ℝ)|=(5246147511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_s4_2 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1336819611/2500000000 : ℝ)*x 0 + (209845901/400000000 : ℝ)*x 1 + (-254997547/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336819611/2500000000 : ℝ)^2203 ≤ (44240192278319/100000000000000 : ℝ)^1691 := by
    have hnat : (1336819611 : ℕ)^2203*100000000000000^1691 ≤ 44240192278319^1691*2500000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336819611 2500000000 44240192278319 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209845901/400000000 : ℝ)^2203 ≤ (10788323888021/25000000000000 : ℝ)^1691 := by
    have hnat : (209845901 : ℕ)^2203*25000000000000^1691 ≤ 10788323888021^1691*400000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209845901 400000000 10788323888021 25000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (254997547/1250000000 : ℝ)^2203 ≤ (12606512155539/100000000000000 : ℝ)^1691 := by
    have hnat : (254997547 : ℕ)^2203*100000000000000^1691 ≤ 12606512155539^1691*1250000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      254997547 1250000000 12606512155539 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336819611/2500000000 : ℝ), (209845901/400000000 : ℝ), (-254997547/1250000000 : ℝ)] ![(44240192278319/100000000000000 : ℝ), (10788323888021/25000000000000 : ℝ), (12606512155539/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336819611/2500000000 : ℝ)|^2203 ≤ (44240192278319/100000000000000 : ℝ)^1691
        have hw : |(1336819611/2500000000 : ℝ)|=(1336819611/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(209845901/400000000 : ℝ)|^2203 ≤ (10788323888021/25000000000000 : ℝ)^1691
        have hw : |(209845901/400000000 : ℝ)|=(209845901/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-254997547/1250000000 : ℝ)|^2203 ≤ (12606512155539/100000000000000 : ℝ)^1691
        have hw : |(-254997547/1250000000 : ℝ)|=(254997547/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_s4_3 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4300057813/10000000000 : ℝ)*x 0 + (825306533/2000000000 : ℝ)*x 1 + (4480071037/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4300057813/10000000000 : ℝ)^2203 ≤ (6660822331239/20000000000000 : ℝ)^1691 := by
    have hnat : (4300057813 : ℕ)^2203*20000000000000^1691 ≤ 6660822331239^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4300057813 10000000000 6660822331239 20000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (825306533/2000000000 : ℝ)^2203 ≤ (31564028244413/100000000000000 : ℝ)^1691 := by
    have hnat : (825306533 : ℕ)^2203*100000000000000^1691 ≤ 31564028244413^1691*2000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      825306533 2000000000 31564028244413 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4480071037/10000000000 : ℝ)^2203 ≤ (8782965022451/25000000000000 : ℝ)^1691 := by
    have hnat : (4480071037 : ℕ)^2203*25000000000000^1691 ≤ 8782965022451^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4480071037 10000000000 8782965022451 25000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4300057813/10000000000 : ℝ), (825306533/2000000000 : ℝ), (4480071037/10000000000 : ℝ)] ![(6660822331239/20000000000000 : ℝ), (31564028244413/100000000000000 : ℝ), (8782965022451/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4300057813/10000000000 : ℝ)|^2203 ≤ (6660822331239/20000000000000 : ℝ)^1691
        have hw : |(4300057813/10000000000 : ℝ)|=(4300057813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(825306533/2000000000 : ℝ)|^2203 ≤ (31564028244413/100000000000000 : ℝ)^1691
        have hw : |(825306533/2000000000 : ℝ)|=(825306533/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4480071037/10000000000 : ℝ)|^2203 ≤ (8782965022451/25000000000000 : ℝ)^1691
        have hw : |(4480071037/10000000000 : ℝ)|=(4480071037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_s4_4 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-195729637/1000000000 : ℝ)*x 0 + (2623371357/5000000000 : ℝ)*x 1 + (1351989989/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (195729637/1000000000 : ℝ)^2203 ≤ (2986240577067/25000000000000 : ℝ)^1691 := by
    have hnat : (195729637 : ℕ)^2203*25000000000000^1691 ≤ 2986240577067^1691*1000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      195729637 1000000000 2986240577067 25000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623371357/5000000000 : ℝ)^2203 ≤ (43159673878097/100000000000000 : ℝ)^1691 := by
    have hnat : (2623371357 : ℕ)^2203*100000000000000^1691 ≤ 43159673878097^1691*5000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623371357 5000000000 43159673878097 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1351989989/2500000000 : ℝ)^2203 ≤ (11223840948179/25000000000000 : ℝ)^1691 := by
    have hnat : (1351989989 : ℕ)^2203*25000000000000^1691 ≤ 11223840948179^1691*2500000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351989989 2500000000 11223840948179 25000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-195729637/1000000000 : ℝ), (2623371357/5000000000 : ℝ), (1351989989/2500000000 : ℝ)] ![(2986240577067/25000000000000 : ℝ), (43159673878097/100000000000000 : ℝ), (11223840948179/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-195729637/1000000000 : ℝ)|^2203 ≤ (2986240577067/25000000000000 : ℝ)^1691
        have hw : |(-195729637/1000000000 : ℝ)|=(195729637/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623371357/5000000000 : ℝ)|^2203 ≤ (43159673878097/100000000000000 : ℝ)^1691
        have hw : |(2623371357/5000000000 : ℝ)|=(2623371357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1351989989/2500000000 : ℝ)|^2203 ≤ (11223840948179/25000000000000 : ℝ)^1691
        have hw : |(1351989989/2500000000 : ℝ)|=(1351989989/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_s4_5 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5304986997/10000000000 : ℝ)*x 0 + (-1878167921/10000000000 : ℝ)*x 1 + (135198999/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304986997/10000000000 : ℝ)^2203 ≤ (4378490410131/10000000000000 : ℝ)^1691 := by
    have hnat : (5304986997 : ℕ)^2203*10000000000000^1691 ≤ 4378490410131^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304986997 10000000000 4378490410131 10000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1878167921/10000000000 : ℝ)^2203 ≤ (5659866024111/50000000000000 : ℝ)^1691 := by
    have hnat : (1878167921 : ℕ)^2203*50000000000000^1691 ≤ 5659866024111^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1878167921 10000000000 5659866024111 50000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (135198999/250000000 : ℝ)^2203 ≤ (44895363835977/100000000000000 : ℝ)^1691 := by
    have hnat : (135198999 : ℕ)^2203*100000000000000^1691 ≤ 44895363835977^1691*250000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135198999 250000000 44895363835977 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304986997/10000000000 : ℝ), (-1878167921/10000000000 : ℝ), (135198999/250000000 : ℝ)] ![(4378490410131/10000000000000 : ℝ), (5659866024111/50000000000000 : ℝ), (44895363835977/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304986997/10000000000 : ℝ)|^2203 ≤ (4378490410131/10000000000000 : ℝ)^1691
        have hw : |(5304986997/10000000000 : ℝ)|=(5304986997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1878167921/10000000000 : ℝ)|^2203 ≤ (5659866024111/50000000000000 : ℝ)^1691
        have hw : |(-1878167921/10000000000 : ℝ)|=(1878167921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(135198999/250000000 : ℝ)|^2203 ≤ (44895363835977/100000000000000 : ℝ)^1691
        have hw : |(135198999/250000000 : ℝ)|=(135198999/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_s4_6 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652493497/5000000000 : ℝ)*x 0 + (5407959959/10000000000 : ℝ)*x 1 + (-939083963/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652493497/5000000000 : ℝ)^2203 ≤ (43784904069053/100000000000000 : ℝ)^1691 := by
    have hnat : (2652493497 : ℕ)^2203*100000000000000^1691 ≤ 43784904069053^1691*5000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652493497 5000000000 43784904069053 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407959959/10000000000 : ℝ)^2203 ≤ (22447681912581/50000000000000 : ℝ)^1691 := by
    have hnat : (5407959959 : ℕ)^2203*50000000000000^1691 ≤ 22447681912581^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407959959 10000000000 22447681912581 50000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (939083963/5000000000 : ℝ)^2203 ≤ (5659866043741/50000000000000 : ℝ)^1691 := by
    have hnat : (939083963 : ℕ)^2203*50000000000000^1691 ≤ 5659866043741^1691*5000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      939083963 5000000000 5659866043741 50000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652493497/5000000000 : ℝ), (5407959959/10000000000 : ℝ), (-939083963/5000000000 : ℝ)] ![(43784904069053/100000000000000 : ℝ), (22447681912581/50000000000000 : ℝ), (5659866043741/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652493497/5000000000 : ℝ)|^2203 ≤ (43784904069053/100000000000000 : ℝ)^1691
        have hw : |(2652493497/5000000000 : ℝ)|=(2652493497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407959959/10000000000 : ℝ)|^2203 ≤ (22447681912581/50000000000000 : ℝ)^1691
        have hw : |(5407959959/10000000000 : ℝ)|=(5407959959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-939083963/5000000000 : ℝ)|^2203 ≤ (5659866043741/50000000000000 : ℝ)^1691
        have hw : |(-939083963/5000000000 : ℝ)|=(939083963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_s4_7 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4300083187/10000000000 : ℝ)*x 0 + (4478775433/10000000000 : ℝ)*x 1 + (2063917553/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4300083187/10000000000 : ℝ)^2203 ≤ (33304367682019/100000000000000 : ℝ)^1691 := by
    have hnat : (4300083187 : ℕ)^2203*100000000000000^1691 ≤ 33304367682019^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4300083187 10000000000 33304367682019 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4478775433/10000000000 : ℝ)^2203 ≤ (35118624588399/100000000000000 : ℝ)^1691 := by
    have hnat : (4478775433 : ℕ)^2203*100000000000000^1691 ≤ 35118624588399^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4478775433 10000000000 35118624588399 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2063917553/5000000000 : ℝ)^2203 ≤ (31577007710689/100000000000000 : ℝ)^1691 := by
    have hnat : (2063917553 : ℕ)^2203*100000000000000^1691 ≤ 31577007710689^1691*5000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2063917553 5000000000 31577007710689 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4300083187/10000000000 : ℝ), (4478775433/10000000000 : ℝ), (2063917553/5000000000 : ℝ)] ![(33304367682019/100000000000000 : ℝ), (35118624588399/100000000000000 : ℝ), (31577007710689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4300083187/10000000000 : ℝ)|^2203 ≤ (33304367682019/100000000000000 : ℝ)^1691
        have hw : |(4300083187/10000000000 : ℝ)|=(4300083187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4478775433/10000000000 : ℝ)|^2203 ≤ (35118624588399/100000000000000 : ℝ)^1691
        have hw : |(4478775433/10000000000 : ℝ)|=(4478775433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2063917553/5000000000 : ℝ)|^2203 ≤ (31577007710689/100000000000000 : ℝ)^1691
        have hw : |(2063917553/5000000000 : ℝ)|=(2063917553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1446_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158840811/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7469/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11211/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (227/2000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14791/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7469/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11211/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7469/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11211/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7469/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11211/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7469/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11211/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7469/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11211/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7469/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11211/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11211/100000 : ℝ) ^ (4405/1024 : ℝ) ≤ (8162067254926073/100000000000000000000 : ℝ) := by
    have hpowers : (11211/100000 : ℝ)^4405 ≤ (8162067254926073/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11211 : ℕ)^4405*100000000000000000000^1024 ≤ 8162067254926073^1024*100000^4405 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11211 100000 8162067254926073 100000000000000000000 4405 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11211/100000 : ℝ)) (X := (8162067254926073/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4405 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7469/50000 : ℝ) ^ (4405/1024 : ℝ) ≤ (28054731583189063/100000000000000000000 : ℝ) := by
    have hpowers : (7469/50000 : ℝ)^4405 ≤ (28054731583189063/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7469 : ℕ)^4405*100000000000000000000^1024 ≤ 28054731583189063^1024*50000^4405 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7469 50000 28054731583189063 100000000000000000000 4405 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7469/50000 : ℝ)) (X := (28054731583189063/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4405 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008162067254926073/50000000000000000000 : ℝ) ≤ (2000075890427419/2000000000000000 : ℝ) ^ (4405/1024 : ℝ) := by
    have hpowers : (50008162067254926073/50000000000000000000 : ℝ)^1024 ≤ (2000075890427419/2000000000000000 : ℝ)^4405 := by
      have hnat : (50008162067254926073 : ℕ)^1024*2000000000000000^4405 ≤ 2000075890427419^4405*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008162067254926073 50000000000000000000 2000075890427419 2000000000000000 1024 4405 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000075890427419/2000000000000000 : ℝ)) (X := (50008162067254926073/50000000000000000000 : ℝ)) (by norm_num) 4405 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (1563065887481845549/1562500000000000000 : ℝ) ≤ (10000841789979039/10000000000000000 : ℝ) ^ (4405/1024 : ℝ) := by
    have hpowers : (1563065887481845549/1562500000000000000 : ℝ)^1024 ≤ (10000841789979039/10000000000000000 : ℝ)^4405 := by
      have hnat : (1563065887481845549 : ℕ)^1024*10000000000000000^4405 ≤ 10000841789979039^4405*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1563065887481845549 1562500000000000000 10000841789979039 10000000000000000 1024 4405 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000841789979039/10000000000000000 : ℝ)) (X := (1563065887481845549/1562500000000000000 : ℝ)) (by norm_num) 4405 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50028054731583189063/50000000000000000000 : ℝ) ≤ (10001304127820983/10000000000000000 : ℝ) ^ (4405/1024 : ℝ) := by
    have hpowers : (50028054731583189063/50000000000000000000 : ℝ)^1024 ≤ (10001304127820983/10000000000000000 : ℝ)^4405 := by
      have hnat : (50028054731583189063 : ℕ)^1024*10000000000000000^4405 ≤ 10001304127820983^4405*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50028054731583189063 50000000000000000000 10001304127820983 10000000000000000 1024 4405 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001304127820983/10000000000000000 : ℝ)) (X := (50028054731583189063/50000000000000000000 : ℝ)) (by norm_num) 4405 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8162067254926073/100000000000000000000 : ℝ) ≤ ((37261047679022884697/37270000000000000000 : ℝ)+2*(57792230243/46587500000000 : ℝ)*(11211/100000 : ℝ))^(4405/1024 : ℝ) := by
    rw [show (37261047679022884697/37270000000000000000 : ℝ)+2*(57792230243/46587500000000 : ℝ)*(11211/100000 : ℝ)=(2000075890427419/2000000000000000 : ℝ) by norm_num, show 1+2*(8162067254926073/100000000000000000000 : ℝ)=(50008162067254926073/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(28054731583189063/100000000000000000000 : ℝ)+(8162067254926073/100000000000000000000 : ℝ) ≤ ((37261047679022884697/37270000000000000000 : ℝ)+(57792230243/46587500000000 : ℝ)*((7469/50000 : ℝ)+(11211/100000 : ℝ)))^(4405/1024 : ℝ) := by
    rw [show (37261047679022884697/37270000000000000000 : ℝ)+(57792230243/46587500000000 : ℝ)*((7469/50000 : ℝ)+(11211/100000 : ℝ))=(10000841789979039/10000000000000000 : ℝ) by norm_num, show 1+(28054731583189063/100000000000000000000 : ℝ)+(8162067254926073/100000000000000000000 : ℝ)=(1563065887481845549/1562500000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(28054731583189063/100000000000000000000 : ℝ) ≤ ((37261047679022884697/37270000000000000000 : ℝ)+2*(57792230243/46587500000000 : ℝ)*(7469/50000 : ℝ))^(4405/1024 : ℝ) := by
    rw [show (37261047679022884697/37270000000000000000 : ℝ)+2*(57792230243/46587500000000 : ℝ)*(7469/50000 : ℝ)=(10001304127820983/10000000000000000 : ℝ) by norm_num, show 1+2*(28054731583189063/100000000000000000000 : ℝ)=(50028054731583189063/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (37261047679022884697/37270000000000000000 : ℝ)*(X 1 0+X 2 0)+(57792230243/46587500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4405/1024 : ℝ)) (lo := (11211/100000 : ℝ)) (hi := (7469/50000 : ℝ)) (c := (37261047679022884697/37270000000000000000 : ℝ)) (alpha := (57792230243/46587500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (37261047679022884697/37270000000000000000 : ℝ)*(X 0 1+X 2 1)+(57792230243/46587500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4405/1024 : ℝ)) (lo := (11211/100000 : ℝ)) (hi := (7469/50000 : ℝ)) (c := (37261047679022884697/37270000000000000000 : ℝ)) (alpha := (57792230243/46587500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (37261047679022884697/37270000000000000000 : ℝ)*(X 0 2+X 1 2)+(57792230243/46587500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4405/1024 : ℝ)) (lo := (11211/100000 : ℝ)) (hi := (7469/50000 : ℝ)) (c := (37261047679022884697/37270000000000000000 : ℝ)) (alpha := (57792230243/46587500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-391456943/2000000000 : ℝ)*X 0 0+(1352139561/2500000000 : ℝ)*X 0 1+(2623073773/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347278467/10000000000 : ℝ)*X 1 0+(-2039980363/10000000000 : ℝ)*X 1 1+(5246147511/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336819611/2500000000 : ℝ)*X 2 0+(209845901/400000000 : ℝ)*X 2 1+(-254997547/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4300057813/10000000000 : ℝ)*X 0 0+(825306533/2000000000 : ℝ)*X 0 1+(4480071037/10000000000 : ℝ)*X 0 2+(4300057813/10000000000 : ℝ)*X 1 0+(825306533/2000000000 : ℝ)*X 1 1+(4480071037/10000000000 : ℝ)*X 1 2+(4300057813/10000000000 : ℝ)*X 2 0+(825306533/2000000000 : ℝ)*X 2 1+(4480071037/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-195729637/1000000000 : ℝ)*X 0 0+(2623371357/5000000000 : ℝ)*X 0 1+(1351989989/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5304986997/10000000000 : ℝ)*X 1 0+(-1878167921/10000000000 : ℝ)*X 1 1+(135198999/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652493497/5000000000 : ℝ)*X 2 0+(5407959959/10000000000 : ℝ)*X 2 1+(-939083963/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4300083187/10000000000 : ℝ)*X 0 0+(4478775433/10000000000 : ℝ)*X 0 1+(2063917553/5000000000 : ℝ)*X 0 2+(4300083187/10000000000 : ℝ)*X 1 0+(4478775433/10000000000 : ℝ)*X 1 1+(2063917553/5000000000 : ℝ)*X 1 2+(4300083187/10000000000 : ℝ)*X 2 0+(4478775433/10000000000 : ℝ)*X 2 1+(2063917553/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18745231160990945857720910517/1863500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1862821443/100000000000000 : ℝ)*(base19) + (429010039/25000000000000 : ℝ)*(base23) + (32163121/50000000000000 : ℝ)*(lower2) + (133894401/50000000000000 : ℝ)*(upper3) + (15975771/10000000000000 : ℝ)*(upper5) + (140404531833583/3125000000000 : ℝ)*(major0) + (140404531833583/3125000000000 : ℝ)*(major1) + (4492945018674657/100000000000000 : ℝ)*(major2) + (6157269325888227/100000000000000 : ℝ)*(sp0) + (6157304309342243/100000000000000 : ℝ)*(sp1) + (6157304456123531/100000000000000 : ℝ)*(sp2) + (2828564342565113/100000000000000 : ℝ)*(sp3) + (1842313773/5000000000000 : ℝ)*(sp4) + (9593657707/50000000000000 : ℝ)*(sp7) + (2828583529880527/100000000000000 : ℝ)*(f.failure) + (6157306172163687/100000000000000 : ℝ)*(f.sum) + (18171413817333/9317500000000000000000000000 : ℝ)*base65 + (740774479552501899/116468750000000000000000000000000 : ℝ)*base68 + (8841797078384423929/3727000000000000000000000000000000 : ℝ)*base69 + (99166520338404351/116468750000000000000000000000000 : ℝ)*base71 + (31419809803747/9317500000000000000000000000 : ℝ)*base74 + (81929062900967423929/3727000000000000000000000000000000 : ℝ)*base75 + (308520335746673101/116468750000000000000000000000000 : ℝ)*base77 + (108640961083016851/116468750000000000000000000000000 : ℝ)*base79 + (93327880169549/18635000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (41787397/10000000000000000000000 : ℝ)*base89 + (41787397/10000000000000000000000 : ℝ)*base91 + (58212603/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (65754648273737044983117/9317500000000000000000000000 : ℝ) := by norm_num
    linear_combination (597263041/50000000000000 : ℝ)*(base19) + (1291033161/100000000000000 : ℝ)*(base23) + (9166403/6250000000000 : ℝ)*(upper3) + (45638767/100000000000000 : ℝ)*(lower4) + (142937817/100000000000000 : ℝ)*(upper5) + (282884267408867/6250000000000 : ℝ)*(major0) + (282884267408867/6250000000000 : ℝ)*(major1) + (282884267408867/6250000000000 : ℝ)*(major2) + (12494398187/50000000000000 : ℝ)*(sp1) + (6685763219/25000000000000 : ℝ)*(sp2) + (6202809310261273/100000000000000 : ℝ)*(sp4) + (6202783126938817/100000000000000 : ℝ)*(sp5) + (1550695319043809/25000000000000 : ℝ)*(sp6) + (1424743505792687/50000000000000 : ℝ)*(sp7) + (1424743505792687/50000000000000 : ℝ)*(f.failure) + (6202809310261273/100000000000000 : ℝ)*(f.sum) + (4198791069889/2329375000000000000000000000 : ℝ)*base66 + (231673748679291701/232937500000000000000000000000000 : ℝ)*base68 + (1690792331137791701/232937500000000000000000000000000 : ℝ)*base70 + (162010127615270799/232937500000000000000000000000000 : ℝ)*base71 + (23980718801063/18635000000000000000000000000 : ℝ)*base73 + (5364241967277916701/232937500000000000000000000000000 : ℝ)*base76 + (605885503592333299/232937500000000000000000000000000 : ℝ)*base77 + (1217711756973583299/232937500000000000000000000000000 : ℝ)*base79 + (10141211589163/4658750000000000000000000000 : ℝ)*base82 + (949157/5000000000000000000000 : ℝ)*base89 + (949157/5000000000000000000000 : ℝ)*base91 + (949157/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1446_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158840811/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7469/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11211/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (227/2000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14791/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1446_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1446_s5_0 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-978701521/5000000000 : ℝ)*x 0 + (5407498629/10000000000 : ℝ)*x 1 + (2623564569/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (978701521/5000000000 : ℝ)^2203 ≤ (373306575627/3125000000000 : ℝ)^1691 := by
    have hnat : (978701521 : ℕ)^2203*3125000000000^1691 ≤ 373306575627^1691*5000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      978701521 5000000000 373306575627 3125000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407498629/10000000000 : ℝ)^2203 ≤ (1402824201977/3125000000000 : ℝ)^1691 := by
    have hnat : (5407498629 : ℕ)^2203*3125000000000^1691 ≤ 1402824201977^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407498629 10000000000 1402824201977 3125000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623564569/5000000000 : ℝ)^2203 ≤ (43163815097211/100000000000000 : ℝ)^1691 := by
    have hnat : (2623564569 : ℕ)^2203*100000000000000^1691 ≤ 43163815097211^1691*5000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623564569 5000000000 43163815097211 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-978701521/5000000000 : ℝ), (5407498629/10000000000 : ℝ), (2623564569/5000000000 : ℝ)] ![(373306575627/3125000000000 : ℝ), (1402824201977/3125000000000 : ℝ), (43163815097211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-978701521/5000000000 : ℝ)|^2203 ≤ (373306575627/3125000000000 : ℝ)^1691
        have hw : |(-978701521/5000000000 : ℝ)|=(978701521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407498629/10000000000 : ℝ)|^2203 ≤ (1402824201977/3125000000000 : ℝ)^1691
        have hw : |(5407498629/10000000000 : ℝ)|=(5407498629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623564569/5000000000 : ℝ)|^2203 ≤ (43163815097211/100000000000000 : ℝ)^1691
        have hw : |(2623564569/5000000000 : ℝ)|=(2623564569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_s5_1 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (668375477/1250000000 : ℝ)*x 0 + (-1019520439/5000000000 : ℝ)*x 1 + (2623564741/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668375477/1250000000 : ℝ)^2203 ≤ (44237232245451/100000000000000 : ℝ)^1691 := by
    have hnat : (668375477 : ℕ)^2203*100000000000000^1691 ≤ 44237232245451^1691*1250000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668375477 1250000000 44237232245451 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1019520439/5000000000 : ℝ)^2203 ≤ (12598948958363/100000000000000 : ℝ)^1691 := by
    have hnat : (1019520439 : ℕ)^2203*100000000000000^1691 ≤ 12598948958363^1691*5000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1019520439 5000000000 12598948958363 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623564741/5000000000 : ℝ)^2203 ≤ (21581909391911/50000000000000 : ℝ)^1691 := by
    have hnat : (2623564741 : ℕ)^2203*50000000000000^1691 ≤ 21581909391911^1691*5000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623564741 5000000000 21581909391911 50000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668375477/1250000000 : ℝ), (-1019520439/5000000000 : ℝ), (2623564741/5000000000 : ℝ)] ![(44237232245451/100000000000000 : ℝ), (12598948958363/100000000000000 : ℝ), (21581909391911/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668375477/1250000000 : ℝ)|^2203 ≤ (44237232245451/100000000000000 : ℝ)^1691
        have hw : |(668375477/1250000000 : ℝ)|=(668375477/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1019520439/5000000000 : ℝ)|^2203 ≤ (12598948958363/100000000000000 : ℝ)^1691
        have hw : |(-1019520439/5000000000 : ℝ)|=(1019520439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623564741/5000000000 : ℝ)|^2203 ≤ (21581909391911/50000000000000 : ℝ)^1691
        have hw : |(2623564741/5000000000 : ℝ)|=(2623564741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_s5_2 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5347003999/10000000000 : ℝ)*x 0 + (1311782229/2500000000 : ℝ)*x 1 + (-1019520693/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347003999/10000000000 : ℝ)^2203 ≤ (2764827138617/6250000000000 : ℝ)^1691 := by
    have hnat : (5347003999 : ℕ)^2203*6250000000000^1691 ≤ 2764827138617^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347003999 10000000000 2764827138617 6250000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311782229/2500000000 : ℝ)^2203 ≤ (2158190635903/5000000000000 : ℝ)^1691 := by
    have hnat : (1311782229 : ℕ)^2203*5000000000000^1691 ≤ 2158190635903^1691*2500000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311782229 2500000000 2158190635903 5000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1019520693/5000000000 : ℝ)^2203 ≤ (12598953047607/100000000000000 : ℝ)^1691 := by
    have hnat : (1019520693 : ℕ)^2203*100000000000000^1691 ≤ 12598953047607^1691*5000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1019520693 5000000000 12598953047607 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347003999/10000000000 : ℝ), (1311782229/2500000000 : ℝ), (-1019520693/5000000000 : ℝ)] ![(2764827138617/6250000000000 : ℝ), (2158190635903/5000000000000 : ℝ), (12598953047607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347003999/10000000000 : ℝ)|^2203 ≤ (2764827138617/6250000000000 : ℝ)^1691
        have hw : |(5347003999/10000000000 : ℝ)|=(5347003999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311782229/2500000000 : ℝ)|^2203 ≤ (2158190635903/5000000000000 : ℝ)^1691
        have hw : |(1311782229/2500000000 : ℝ)|=(1311782229/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1019520693/5000000000 : ℝ)|^2203 ≤ (12598953047607/100000000000000 : ℝ)^1691
        have hw : |(-1019520693/5000000000 : ℝ)|=(1019520693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_s5_3 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (430012981/1000000000 : ℝ)*x 0 + (4128745803/10000000000 : ℝ)*x 1 + (4477840849/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (430012981/1000000000 : ℝ)^2203 ≤ (33304838113257/100000000000000 : ℝ)^1691 := by
    have hnat : (430012981 : ℕ)^2203*100000000000000^1691 ≤ 33304838113257^1691*1000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430012981 1000000000 33304838113257 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4128745803/10000000000 : ℝ)^2203 ≤ (7896520997921/25000000000000 : ℝ)^1691 := by
    have hnat : (4128745803 : ℕ)^2203*25000000000000^1691 ≤ 7896520997921^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4128745803 10000000000 7896520997921 25000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4477840849/10000000000 : ℝ)^2203 ≤ (1755453893929/5000000000000 : ℝ)^1691 := by
    have hnat : (4477840849 : ℕ)^2203*5000000000000^1691 ≤ 1755453893929^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4477840849 10000000000 1755453893929 5000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(430012981/1000000000 : ℝ), (4128745803/10000000000 : ℝ), (4477840849/10000000000 : ℝ)] ![(33304838113257/100000000000000 : ℝ), (7896520997921/25000000000000 : ℝ), (1755453893929/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(430012981/1000000000 : ℝ)|^2203 ≤ (33304838113257/100000000000000 : ℝ)^1691
        have hw : |(430012981/1000000000 : ℝ)|=(430012981/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4128745803/10000000000 : ℝ)|^2203 ≤ (7896520997921/25000000000000 : ℝ)^1691
        have hw : |(4128745803/10000000000 : ℝ)|=(4128745803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4477840849/10000000000 : ℝ)|^2203 ≤ (1755453893929/5000000000000 : ℝ)^1691
        have hw : |(4477840849/10000000000 : ℝ)|=(4477840849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_s5_4 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-391482843/2000000000 : ℝ)*x 0 + (2623854719/5000000000 : ℝ)*x 1 + (2703457681/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (391482843/2000000000 : ℝ)^2203 ≤ (11945899253493/100000000000000 : ℝ)^1691 := by
    have hnat : (391482843 : ℕ)^2203*100000000000000^1691 ≤ 11945899253493^1691*2000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      391482843 2000000000 11945899253493 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623854719/5000000000 : ℝ)^2203 ≤ (21585017107639/50000000000000 : ℝ)^1691 := by
    have hnat : (2623854719 : ℕ)^2203*50000000000000^1691 ≤ 21585017107639^1691*5000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623854719 5000000000 21585017107639 50000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703457681/5000000000 : ℝ)^2203 ≤ (44884066516587/100000000000000 : ℝ)^1691 := by
    have hnat : (2703457681 : ℕ)^2203*100000000000000^1691 ≤ 44884066516587^1691*5000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703457681 5000000000 44884066516587 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-391482843/2000000000 : ℝ), (2623854719/5000000000 : ℝ), (2703457681/5000000000 : ℝ)] ![(11945899253493/100000000000000 : ℝ), (21585017107639/50000000000000 : ℝ), (44884066516587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-391482843/2000000000 : ℝ)|^2203 ≤ (11945899253493/100000000000000 : ℝ)^1691
        have hw : |(-391482843/2000000000 : ℝ)|=(391482843/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623854719/5000000000 : ℝ)|^2203 ≤ (21585017107639/50000000000000 : ℝ)^1691
        have hw : |(2623854719/5000000000 : ℝ)|=(2623854719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703457681/5000000000 : ℝ)|^2203 ≤ (44884066516587/100000000000000 : ℝ)^1691
        have hw : |(2703457681/5000000000 : ℝ)|=(2703457681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_s5_5 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1061048797/2000000000 : ℝ)*x 0 + (-939627321/5000000000 : ℝ)*x 1 + (5406915407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061048797/2000000000 : ℝ)^2203 ≤ (437876673947/1000000000000 : ℝ)^1691 := by
    have hnat : (1061048797 : ℕ)^2203*1000000000000^1691 ≤ 437876673947^1691*2000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061048797 2000000000 437876673947 1000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (939627321/5000000000 : ℝ)^2203 ≤ (11328265578083/100000000000000 : ℝ)^1691 := by
    have hnat : (939627321 : ℕ)^2203*100000000000000^1691 ≤ 11328265578083^1691*5000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      939627321 5000000000 11328265578083 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406915407/10000000000 : ℝ)^2203 ≤ (2805254187703/6250000000000 : ℝ)^1691 := by
    have hnat : (5406915407 : ℕ)^2203*6250000000000^1691 ≤ 2805254187703^1691*10000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406915407 10000000000 2805254187703 6250000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061048797/2000000000 : ℝ), (-939627321/5000000000 : ℝ), (5406915407/10000000000 : ℝ)] ![(437876673947/1000000000000 : ℝ), (11328265578083/100000000000000 : ℝ), (2805254187703/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061048797/2000000000 : ℝ)|^2203 ≤ (437876673947/1000000000000 : ℝ)^1691
        have hw : |(1061048797/2000000000 : ℝ)|=(1061048797/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-939627321/5000000000 : ℝ)|^2203 ≤ (11328265578083/100000000000000 : ℝ)^1691
        have hw : |(-939627321/5000000000 : ℝ)|=(939627321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406915407/10000000000 : ℝ)|^2203 ≤ (2805254187703/6250000000000 : ℝ)^1691
        have hw : |(5406915407/10000000000 : ℝ)|=(5406915407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_s5_6 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652622013/5000000000 : ℝ)*x 0 + (540691539/1000000000 : ℝ)*x 1 + (-187925461/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652622013/5000000000 : ℝ)^2203 ≤ (43787667835561/100000000000000 : ℝ)^1691 := by
    have hnat : (2652622013 : ℕ)^2203*100000000000000^1691 ≤ 43787667835561^1691*5000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652622013 5000000000 43787667835561 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (540691539/1000000000 : ℝ)^2203 ≤ (22442033409699/50000000000000 : ℝ)^1691 := by
    have hnat : (540691539 : ℕ)^2203*50000000000000^1691 ≤ 22442033409699^1691*1000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540691539 1000000000 22442033409699 50000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (187925461/1000000000 : ℝ)^2203 ≤ (566413266339/5000000000000 : ℝ)^1691 := by
    have hnat : (187925461 : ℕ)^2203*5000000000000^1691 ≤ 566413266339^1691*1000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      187925461 1000000000 566413266339 5000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652622013/5000000000 : ℝ), (540691539/1000000000 : ℝ), (-187925461/1000000000 : ℝ)] ![(43787667835561/100000000000000 : ℝ), (22442033409699/50000000000000 : ℝ), (566413266339/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652622013/5000000000 : ℝ)|^2203 ≤ (43787667835561/100000000000000 : ℝ)^1691
        have hw : |(2652622013/5000000000 : ℝ)|=(2652622013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(540691539/1000000000 : ℝ)|^2203 ≤ (22442033409699/50000000000000 : ℝ)^1691
        have hw : |(540691539/1000000000 : ℝ)|=(540691539/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-187925461/1000000000 : ℝ)|^2203 ≤ (566413266339/5000000000000 : ℝ)^1691
        have hw : |(-187925461/1000000000 : ℝ)|=(187925461/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1446_s5_7 (p : ℝ) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2150077261/5000000000 : ℝ)*x 0 + (2238288733/5000000000 : ℝ)*x 1 + (16132873/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2150077261/5000000000 : ℝ)^2203 ≤ (33305087460703/100000000000000 : ℝ)^1691 := by
    have hnat : (2150077261 : ℕ)^2203*100000000000000^1691 ≤ 33305087460703^1691*5000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2150077261 5000000000 33305087460703 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2238288733/5000000000 : ℝ)^2203 ≤ (35096173469093/100000000000000 : ℝ)^1691 := by
    have hnat : (2238288733 : ℕ)^2203*100000000000000^1691 ≤ 35096173469093^1691*5000000000^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2238288733 5000000000 35096173469093 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (16132873/39062500 : ℝ)^2203 ≤ (31598739067057/100000000000000 : ℝ)^1691 := by
    have hnat : (16132873 : ℕ)^2203*100000000000000^1691 ≤ 31598739067057^1691*39062500^2203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16132873 39062500 31598739067057 100000000000000 2203 1691 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2203/512 : ℝ)) 2203 1691 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2150077261/5000000000 : ℝ), (2238288733/5000000000 : ℝ), (16132873/39062500 : ℝ)] ![(33305087460703/100000000000000 : ℝ), (35096173469093/100000000000000 : ℝ), (31598739067057/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2150077261/5000000000 : ℝ)|^2203 ≤ (33305087460703/100000000000000 : ℝ)^1691
        have hw : |(2150077261/5000000000 : ℝ)|=(2150077261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2238288733/5000000000 : ℝ)|^2203 ≤ (35096173469093/100000000000000 : ℝ)^1691
        have hw : |(2238288733/5000000000 : ℝ)|=(2238288733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(16132873/39062500 : ℝ)|^2203 ≤ (31598739067057/100000000000000 : ℝ)^1691
        have hw : |(16132873/39062500 : ℝ)|=(16132873/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1446_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158840811/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14791/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (227/2000 : ℝ)*pair X i i ≤ pair X i h) :
    (11371/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14769/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14791/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (227/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14791/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (227/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14791/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (227/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14791/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (227/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14791/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (227/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14791/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (227/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (227/2000 : ℝ) ^ (4405/1024 : ℝ) ≤ (8606390835655453/100000000000000000000 : ℝ) := by
    have hpowers : (227/2000 : ℝ)^4405 ≤ (8606390835655453/100000000000000000000 : ℝ)^1024 := by
      have hnat : (227 : ℕ)^4405*100000000000000000000^1024 ≤ 8606390835655453^1024*2000^4405 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        227 2000 8606390835655453 100000000000000000000 4405 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (227/2000 : ℝ)) (X := (8606390835655453/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4405 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14791/100000 : ℝ) ^ (4405/1024 : ℝ) ≤ (6721565411345213/25000000000000000000 : ℝ) := by
    have hpowers : (14791/100000 : ℝ)^4405 ≤ (6721565411345213/25000000000000000000 : ℝ)^1024 := by
      have hnat : (14791 : ℕ)^4405*25000000000000000000^1024 ≤ 6721565411345213^1024*100000^4405 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14791 100000 6721565411345213 25000000000000000000 4405 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14791/100000 : ℝ)) (X := (6721565411345213/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4405 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008606390835655453/50000000000000000000 : ℝ) ≤ (10000400107247043/10000000000000000 : ℝ) ^ (4405/1024 : ℝ) := by
    have hpowers : (50008606390835655453/50000000000000000000 : ℝ)^1024 ≤ (10000400107247043/10000000000000000 : ℝ)^4405 := by
      have hnat : (50008606390835655453 : ℕ)^1024*10000000000000000^4405 ≤ 10000400107247043^4405*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008606390835655453 50000000000000000000 10000400107247043 10000000000000000 1024 4405 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000400107247043/10000000000000000 : ℝ)) (X := (50008606390835655453/50000000000000000000 : ℝ)) (by norm_num) 4405 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20007098530496207261/20000000000000000000 : ℝ) ≤ (10000824960878751/10000000000000000 : ℝ) ^ (4405/1024 : ℝ) := by
    have hpowers : (20007098530496207261/20000000000000000000 : ℝ)^1024 ≤ (10000824960878751/10000000000000000 : ℝ)^4405 := by
      have hnat : (20007098530496207261 : ℕ)^1024*10000000000000000^4405 ≤ 10000824960878751^4405*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20007098530496207261 20000000000000000000 10000824960878751 10000000000000000 1024 4405 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000824960878751/10000000000000000 : ℝ)) (X := (20007098530496207261/20000000000000000000 : ℝ)) (by norm_num) 4405 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12506721565411345213/12500000000000000000 : ℝ) ≤ (10001249814510459/10000000000000000 : ℝ) ^ (4405/1024 : ℝ) := by
    have hpowers : (12506721565411345213/12500000000000000000 : ℝ)^1024 ≤ (10001249814510459/10000000000000000 : ℝ)^4405 := by
      have hnat : (12506721565411345213 : ℕ)^1024*10000000000000000^4405 ≤ 10001249814510459^4405*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506721565411345213 12500000000000000000 10001249814510459 10000000000000000 1024 4405 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001249814510459/10000000000000000 : ℝ)) (X := (12506721565411345213/12500000000000000000 : ℝ)) (by norm_num) 4405 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8606390835655453/100000000000000000000 : ℝ) ≤ ((11467244197199101121/11470000000000000000 : ℝ)+2*(35404469309/28675000000000 : ℝ)*(227/2000 : ℝ))^(4405/1024 : ℝ) := by
    rw [show (11467244197199101121/11470000000000000000 : ℝ)+2*(35404469309/28675000000000 : ℝ)*(227/2000 : ℝ)=(10000400107247043/10000000000000000 : ℝ) by norm_num, show 1+2*(8606390835655453/100000000000000000000 : ℝ)=(50008606390835655453/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6721565411345213/25000000000000000000 : ℝ)+(8606390835655453/100000000000000000000 : ℝ) ≤ ((11467244197199101121/11470000000000000000 : ℝ)+(35404469309/28675000000000 : ℝ)*((14791/100000 : ℝ)+(227/2000 : ℝ)))^(4405/1024 : ℝ) := by
    rw [show (11467244197199101121/11470000000000000000 : ℝ)+(35404469309/28675000000000 : ℝ)*((14791/100000 : ℝ)+(227/2000 : ℝ))=(10000824960878751/10000000000000000 : ℝ) by norm_num, show 1+(6721565411345213/25000000000000000000 : ℝ)+(8606390835655453/100000000000000000000 : ℝ)=(20007098530496207261/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6721565411345213/25000000000000000000 : ℝ) ≤ ((11467244197199101121/11470000000000000000 : ℝ)+2*(35404469309/28675000000000 : ℝ)*(14791/100000 : ℝ))^(4405/1024 : ℝ) := by
    rw [show (11467244197199101121/11470000000000000000 : ℝ)+2*(35404469309/28675000000000 : ℝ)*(14791/100000 : ℝ)=(10001249814510459/10000000000000000 : ℝ) by norm_num, show 1+2*(6721565411345213/25000000000000000000 : ℝ)=(12506721565411345213/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11467244197199101121/11470000000000000000 : ℝ)*(X 1 0+X 2 0)+(35404469309/28675000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4405/1024 : ℝ)) (lo := (227/2000 : ℝ)) (hi := (14791/100000 : ℝ)) (c := (11467244197199101121/11470000000000000000 : ℝ)) (alpha := (35404469309/28675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11467244197199101121/11470000000000000000 : ℝ)*(X 0 1+X 2 1)+(35404469309/28675000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4405/1024 : ℝ)) (lo := (227/2000 : ℝ)) (hi := (14791/100000 : ℝ)) (c := (11467244197199101121/11470000000000000000 : ℝ)) (alpha := (35404469309/28675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11467244197199101121/11470000000000000000 : ℝ)*(X 0 2+X 1 2)+(35404469309/28675000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4405/1024 : ℝ)) (lo := (227/2000 : ℝ)) (hi := (14791/100000 : ℝ)) (c := (11467244197199101121/11470000000000000000 : ℝ)) (alpha := (35404469309/28675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-978701521/5000000000 : ℝ)*X 0 0+(5407498629/10000000000 : ℝ)*X 0 1+(2623564569/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668375477/1250000000 : ℝ)*X 1 0+(-1019520439/5000000000 : ℝ)*X 1 1+(2623564741/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347003999/10000000000 : ℝ)*X 2 0+(1311782229/2500000000 : ℝ)*X 2 1+(-1019520693/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((430012981/1000000000 : ℝ)*X 0 0+(4128745803/10000000000 : ℝ)*X 0 1+(4477840849/10000000000 : ℝ)*X 0 2+(430012981/1000000000 : ℝ)*X 1 0+(4128745803/10000000000 : ℝ)*X 1 1+(4477840849/10000000000 : ℝ)*X 1 2+(430012981/1000000000 : ℝ)*X 2 0+(4128745803/10000000000 : ℝ)*X 2 1+(4477840849/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-391482843/2000000000 : ℝ)*X 0 0+(2623854719/5000000000 : ℝ)*X 0 1+(2703457681/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1061048797/2000000000 : ℝ)*X 1 0+(-939627321/5000000000 : ℝ)*X 1 1+(5406915407/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652622013/5000000000 : ℝ)*X 2 0+(540691539/1000000000 : ℝ)*X 2 1+(-187925461/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2150077261/5000000000 : ℝ)*X 0 0+(2238288733/5000000000 : ℝ)*X 0 1+(16132873/39062500 : ℝ)*X 0 2+(2150077261/5000000000 : ℝ)*X 1 0+(2238288733/5000000000 : ℝ)*X 1 1+(16132873/39062500 : ℝ)*X 1 2+(2150077261/5000000000 : ℝ)*X 2 0+(2238288733/5000000000 : ℝ)*X 2 1+(16132873/39062500 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1446_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13204155779277767709459/1147000000000000000000000000 : ℝ) := by norm_num
    linear_combination (20770173/2000000000000 : ℝ)*(base19) + (1306848061/100000000000000 : ℝ)*(base23) + (22290541/50000000000000 : ℝ)*(upper2) + (443186951/100000000000000 : ℝ)*(upper3) + (4550112206018389/100000000000000 : ℝ)*(major0) + (4550112206018389/100000000000000 : ℝ)*(major1) + (455011220601839/10000000000000 : ℝ)*(major2) + (6235633680557761/100000000000000 : ℝ)*(sp0) + (6235649221021099/100000000000000 : ℝ)*(sp1) + (6235645309893521/100000000000000 : ℝ)*(sp2) + (179034880812363/6250000000000 : ℝ)*(sp3) + (16578971989/100000000000000 : ℝ)*(sp4) + (3642788167/100000000000000 : ℝ)*(sp6) + (15675779027/100000000000000 : ℝ)*(sp7) + (572914753755367/20000000000000 : ℝ)*(f.failure) + (6235650259529749/100000000000000 : ℝ)*(f.sum) + (3666030073327/5735000000000000000000000000 : ℝ)*base65 + (2318772089578485931/1147000000000000000000000000000000 : ℝ)*base68 + (593166881831198481/114700000000000000000000000000000 : ℝ)*base70 + (6154951556425485931/1147000000000000000000000000000000 : ℝ)*base72 + (8752609272159/2867500000000000000000000000 : ℝ)*base74 + (854346466443401519/114700000000000000000000000000000 : ℝ)*base75 + (7317407814411914069/1147000000000000000000000000000000 : ℝ)*base77 + (6835494184992914069/1147000000000000000000000000000000 : ℝ)*base79 + (8515534455829/1433750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (9882637/2000000000000000000000 : ℝ)*base89 + (9882637/2000000000000000000000 : ℝ)*base91 + (10117363/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2608067947716491144455164477/286750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (283909973/20000000000000 : ℝ)*(base19) + (63587197/4000000000000 : ℝ)*(base23) + (45588587/25000000000000 : ℝ)*(upper3) + (10283207/20000000000000 : ℝ)*(lower4) + (99117917/50000000000000 : ℝ)*(upper5) + (2291664969245893/50000000000000 : ℝ)*(major0) + (2291664969245893/50000000000000 : ℝ)*(major1) + (2291664969245893/50000000000000 : ℝ)*(major2) + (31161830591/100000000000000 : ℝ)*(sp1) + (34296139717/100000000000000 : ℝ)*(sp2) + (3140586605968021/50000000000000 : ℝ)*(sp4) + (3140570315277793/50000000000000 : ℝ)*(sp5) + (15702843315291/250000000000 : ℝ)*(sp6) + (1442743180935971/50000000000000 : ℝ)*(sp7) + (1442743180935971/50000000000000 : ℝ)*(f.failure) + (3140586605968021/50000000000000 : ℝ)*(f.sum) + (11255350418297/2867500000000000000000000000 : ℝ)*base66 + (3718699373552253947/573500000000000000000000000000000 : ℝ)*base68 + (951958467154253947/573500000000000000000000000000000 : ℝ)*base70 + (3930655695469253947/573500000000000000000000000000000 : ℝ)*base72 + (20577148937537/2867500000000000000000000000 : ℝ)*base74 + (2550658628914253947/573500000000000000000000000000000 : ℝ)*base76 + (3061900241418753947/573500000000000000000000000000000 : ℝ)*base78 + (1701349107188253947/573500000000000000000000000000000 : ℝ)*base80 + (7069148073997/2867500000000000000000000000 : ℝ)*base82 + (72712481/5000000000000000000000 : ℝ)*base89 + (72712481/5000000000000000000000 : ℝ)*base91 + (72712481/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1446_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158840811/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14791/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (227/2000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11371/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14769/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1446_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1446_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158840811/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15749/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1307/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11371/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14769/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1446_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1446_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1446_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4405/1024 : ℝ) ≤ p) (hpb : p ≤ (2203/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158840811/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15749/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1307/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11371/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14769/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1446_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
