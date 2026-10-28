-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1129_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:26:36.407568+00:00
-- url     : https://prove2.me/submissions/2b5369c6-bbec-4352-8143-78df2894505c

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
theorem support_rectangle_w1129_s3_0 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2169172779/10000000000 : ℝ)*x 0 + (1357632101/2500000000 : ℝ)*x 1 + (5230849/10000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2169172779/10000000000 : ℝ)^4161 ≤ (131717340139/1000000000000 : ℝ)^3137 := by
    have hnat : (2169172779 : ℕ)^4161*1000000000000^3137 ≤ 131717340139^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2169172779 10000000000 131717340139 1000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1357632101/2500000000 : ℝ)^4161 ≤ (5561571540419/12500000000000 : ℝ)^3137 := by
    have hnat : (1357632101 : ℕ)^4161*12500000000000^3137 ≤ 5561571540419^3137*2500000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357632101 2500000000 5561571540419 12500000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5230849/10000000 : ℝ)^4161 ≤ (10583923413409/25000000000000 : ℝ)^3137 := by
    have hnat : (5230849 : ℕ)^4161*25000000000000^3137 ≤ 10583923413409^3137*10000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230849 10000000 10583923413409 25000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2169172779/10000000000 : ℝ), (1357632101/2500000000 : ℝ), (5230849/10000000 : ℝ)] ![(131717340139/1000000000000 : ℝ), (5561571540419/12500000000000 : ℝ), (10583923413409/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2169172779/10000000000 : ℝ)|^4161 ≤ (131717340139/1000000000000 : ℝ)^3137
        have hw : |(-2169172779/10000000000 : ℝ)|=(2169172779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1357632101/2500000000 : ℝ)|^4161 ≤ (5561571540419/12500000000000 : ℝ)^3137
        have hw : |(1357632101/2500000000 : ℝ)|=(1357632101/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5230849/10000000 : ℝ)|^4161 ≤ (10583923413409/25000000000000 : ℝ)^3137
        have hw : |(5230849/10000000 : ℝ)|=(5230849/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_s3_1 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354107217/10000000000 : ℝ)*x 0 + (-283908927/1250000000 : ℝ)*x 1 + (5230848893/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354107217/10000000000 : ℝ)^4161 ≤ (43663980620919/100000000000000 : ℝ)^3137 := by
    have hnat : (5354107217 : ℕ)^4161*100000000000000^3137 ≤ 43663980620919^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354107217 10000000000 43663980620919 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (283908927/1250000000 : ℝ)^4161 ≤ (1400032686767/10000000000000 : ℝ)^3137 := by
    have hnat : (283908927 : ℕ)^4161*10000000000000^3137 ≤ 1400032686767^3137*1250000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283908927 1250000000 1400032686767 10000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5230848893/10000000000 : ℝ)^4161 ≤ (846713850099/2000000000000 : ℝ)^3137 := by
    have hnat : (5230848893 : ℕ)^4161*2000000000000^3137 ≤ 846713850099^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230848893 10000000000 846713850099 2000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354107217/10000000000 : ℝ), (-283908927/1250000000 : ℝ), (5230848893/10000000000 : ℝ)] ![(43663980620919/100000000000000 : ℝ), (1400032686767/10000000000000 : ℝ), (846713850099/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354107217/10000000000 : ℝ)|^4161 ≤ (43663980620919/100000000000000 : ℝ)^3137
        have hw : |(5354107217/10000000000 : ℝ)|=(5354107217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-283908927/1250000000 : ℝ)|^4161 ≤ (1400032686767/10000000000000 : ℝ)^3137
        have hw : |(-283908927/1250000000 : ℝ)|=(283908927/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5230848893/10000000000 : ℝ)|^4161 ≤ (846713850099/2000000000000 : ℝ)^3137
        have hw : |(5230848893/10000000000 : ℝ)|=(5230848893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_s3_2 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (535410731/1000000000 : ℝ)*x 0 + (163464031/312500000 : ℝ)*x 1 + (-1135635581/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535410731/1000000000 : ℝ)^4161 ≤ (43663981626929/100000000000000 : ℝ)^3137 := by
    have hnat : (535410731 : ℕ)^4161*100000000000000^3137 ≤ 43663981626929^3137*1000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535410731 1000000000 43663981626929 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (163464031/312500000 : ℝ)^4161 ≤ (42335693567753/100000000000000 : ℝ)^3137 := by
    have hnat : (163464031 : ℕ)^4161*100000000000000^3137 ≤ 42335693567753^3137*312500000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163464031 312500000 42335693567753 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1135635581/5000000000 : ℝ)^4161 ≤ (14000324790911/100000000000000 : ℝ)^3137 := by
    have hnat : (1135635581 : ℕ)^4161*100000000000000^3137 ≤ 14000324790911^3137*5000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1135635581 5000000000 14000324790911 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535410731/1000000000 : ℝ), (163464031/312500000 : ℝ), (-1135635581/5000000000 : ℝ)] ![(43663981626929/100000000000000 : ℝ), (42335693567753/100000000000000 : ℝ), (14000324790911/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535410731/1000000000 : ℝ)|^4161 ≤ (43663981626929/100000000000000 : ℝ)^3137
        have hw : |(535410731/1000000000 : ℝ)|=(535410731/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(163464031/312500000 : ℝ)|^4161 ≤ (42335693567753/100000000000000 : ℝ)^3137
        have hw : |(163464031/312500000 : ℝ)|=(163464031/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1135635581/5000000000 : ℝ)|^4161 ≤ (14000324790911/100000000000000 : ℝ)^3137
        have hw : |(-1135635581/5000000000 : ℝ)|=(1135635581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_s3_3 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (872833139/2000000000 : ℝ)*x 0 + (2085263039/5000000000 : ℝ)*x 1 + (228338497/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (872833139/2000000000 : ℝ)^4161 ≤ (16646596271381/50000000000000 : ℝ)^3137 := by
    have hnat : (872833139 : ℕ)^4161*50000000000000^3137 ≤ 16646596271381^3137*2000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      872833139 2000000000 16646596271381 50000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2085263039/5000000000 : ℝ)^4161 ≤ (31348088079547/100000000000000 : ℝ)^3137 := by
    have hnat : (2085263039 : ℕ)^4161*100000000000000^3137 ≤ 31348088079547^3137*5000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085263039 5000000000 31348088079547 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (228338497/500000000 : ℝ)^4161 ≤ (1104959979847/3125000000000 : ℝ)^3137 := by
    have hnat : (228338497 : ℕ)^4161*3125000000000^3137 ≤ 1104959979847^3137*500000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      228338497 500000000 1104959979847 3125000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(872833139/2000000000 : ℝ), (2085263039/5000000000 : ℝ), (228338497/500000000 : ℝ)] ![(16646596271381/50000000000000 : ℝ), (31348088079547/100000000000000 : ℝ), (1104959979847/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(872833139/2000000000 : ℝ)|^4161 ≤ (16646596271381/50000000000000 : ℝ)^3137
        have hw : |(872833139/2000000000 : ℝ)|=(872833139/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2085263039/5000000000 : ℝ)|^4161 ≤ (31348088079547/100000000000000 : ℝ)^3137
        have hw : |(2085263039/5000000000 : ℝ)|=(2085263039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(228338497/500000000 : ℝ)|^4161 ≤ (1104959979847/3125000000000 : ℝ)^3137
        have hw : |(228338497/500000000 : ℝ)|=(228338497/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_s3_4 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1084595747/5000000000 : ℝ)*x 0 + (653953827/1250000000 : ℝ)*x 1 + (5429742379/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1084595747/5000000000 : ℝ)^4161 ≤ (2634376950359/20000000000000 : ℝ)^3137 := by
    have hnat : (1084595747 : ℕ)^4161*20000000000000^3137 ≤ 2634376950359^3137*5000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084595747 5000000000 2634376950359 20000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (653953827/1250000000 : ℝ)^4161 ≤ (5293010601037/12500000000000 : ℝ)^3137 := by
    have hnat : (653953827 : ℕ)^4161*12500000000000^3137 ≤ 5293010601037^3137*1250000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      653953827 1250000000 5293010601037 12500000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5429742379/10000000000 : ℝ)^4161 ≤ (22242015209327/50000000000000 : ℝ)^3137 := by
    have hnat : (5429742379 : ℕ)^4161*50000000000000^3137 ≤ 22242015209327^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429742379 10000000000 22242015209327 50000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1084595747/5000000000 : ℝ), (653953827/1250000000 : ℝ), (5429742379/10000000000 : ℝ)] ![(2634376950359/20000000000000 : ℝ), (5293010601037/12500000000000 : ℝ), (22242015209327/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1084595747/5000000000 : ℝ)|^4161 ≤ (2634376950359/20000000000000 : ℝ)^3137
        have hw : |(-1084595747/5000000000 : ℝ)|=(1084595747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(653953827/1250000000 : ℝ)|^4161 ≤ (5293010601037/12500000000000 : ℝ)^3137
        have hw : |(653953827/1250000000 : ℝ)|=(653953827/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5429742379/10000000000 : ℝ)|^4161 ≤ (22242015209327/50000000000000 : ℝ)^3137
        have hw : |(5429742379/10000000000 : ℝ)|=(5429742379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_s3_5 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2651783743/5000000000 : ℝ)*x 0 + (-1036189269/5000000000 : ℝ)*x 1 + (678717757/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651783743/5000000000 : ℝ)^4161 ≤ (8623624103927/20000000000000 : ℝ)^3137 := by
    have hnat : (2651783743 : ℕ)^4161*20000000000000^3137 ≤ 8623624103927^3137*5000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651783743 5000000000 8623624103927 20000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036189269/5000000000 : ℝ)^4161 ≤ (6198926275649/50000000000000 : ℝ)^3137 := by
    have hnat : (1036189269 : ℕ)^4161*50000000000000^3137 ≤ 6198926275649^3137*5000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036189269 5000000000 6198926275649 50000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (678717757/1250000000 : ℝ)^4161 ≤ (22242013454313/50000000000000 : ℝ)^3137 := by
    have hnat : (678717757 : ℕ)^4161*50000000000000^3137 ≤ 22242013454313^3137*1250000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678717757 1250000000 22242013454313 50000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651783743/5000000000 : ℝ), (-1036189269/5000000000 : ℝ), (678717757/1250000000 : ℝ)] ![(8623624103927/20000000000000 : ℝ), (6198926275649/50000000000000 : ℝ), (22242013454313/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651783743/5000000000 : ℝ)|^4161 ≤ (8623624103927/20000000000000 : ℝ)^3137
        have hw : |(2651783743/5000000000 : ℝ)|=(2651783743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1036189269/5000000000 : ℝ)|^4161 ≤ (6198926275649/50000000000000 : ℝ)^3137
        have hw : |(-1036189269/5000000000 : ℝ)|=(1036189269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(678717757/1250000000 : ℝ)|^4161 ≤ (22242013454313/50000000000000 : ℝ)^3137
        have hw : |(678717757/1250000000 : ℝ)|=(678717757/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_s3_6 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5303568331/10000000000 : ℝ)*x 0 + (271487077/500000000 : ℝ)*x 1 + (-129523631/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5303568331/10000000000 : ℝ)^4161 ≤ (43118129632011/100000000000000 : ℝ)^3137 := by
    have hnat : (5303568331 : ℕ)^4161*100000000000000^3137 ≤ 43118129632011^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5303568331 10000000000 43118129632011 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (271487077/500000000 : ℝ)^4161 ≤ (22242010650637/50000000000000 : ℝ)^3137 := by
    have hnat : (271487077 : ℕ)^4161*50000000000000^3137 ≤ 22242010650637^3137*500000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271487077 500000000 22242010650637 50000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (129523631/625000000 : ℝ)^4161 ≤ (6198924521959/50000000000000 : ℝ)^3137 := by
    have hnat : (129523631 : ℕ)^4161*50000000000000^3137 ≤ 6198924521959^3137*625000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129523631 625000000 6198924521959 50000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5303568331/10000000000 : ℝ), (271487077/500000000 : ℝ), (-129523631/625000000 : ℝ)] ![(43118129632011/100000000000000 : ℝ), (22242010650637/50000000000000 : ℝ), (6198924521959/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5303568331/10000000000 : ℝ)|^4161 ≤ (43118129632011/100000000000000 : ℝ)^3137
        have hw : |(5303568331/10000000000 : ℝ)|=(5303568331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(271487077/500000000 : ℝ)|^4161 ≤ (22242010650637/50000000000000 : ℝ)^3137
        have hw : |(271487077/500000000 : ℝ)|=(271487077/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-129523631/625000000 : ℝ)|^4161 ≤ (6198924521959/50000000000000 : ℝ)^3137
        have hw : |(-129523631/625000000 : ℝ)|=(129523631/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_s3_7 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (436420261/1000000000 : ℝ)*x 0 + (2282609477/5000000000 : ℝ)*x 1 + (2086043027/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (436420261/1000000000 : ℝ)^4161 ≤ (16646783043001/50000000000000 : ℝ)^3137 := by
    have hnat : (436420261 : ℕ)^4161*50000000000000^3137 ≤ 16646783043001^3137*1000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436420261 1000000000 16646783043001 50000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2282609477/5000000000 : ℝ)^4161 ≤ (35342791606509/100000000000000 : ℝ)^3137 := by
    have hnat : (2282609477 : ℕ)^4161*100000000000000^3137 ≤ 35342791606509^3137*5000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2282609477 5000000000 35342791606509 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2086043027/5000000000 : ℝ)^4161 ≤ (7840910571343/25000000000000 : ℝ)^3137 := by
    have hnat : (2086043027 : ℕ)^4161*25000000000000^3137 ≤ 7840910571343^3137*5000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086043027 5000000000 7840910571343 25000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(436420261/1000000000 : ℝ), (2282609477/5000000000 : ℝ), (2086043027/5000000000 : ℝ)] ![(16646783043001/50000000000000 : ℝ), (35342791606509/100000000000000 : ℝ), (7840910571343/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(436420261/1000000000 : ℝ)|^4161 ≤ (16646783043001/50000000000000 : ℝ)^3137
        have hw : |(436420261/1000000000 : ℝ)|=(436420261/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2282609477/5000000000 : ℝ)|^4161 ≤ (35342791606509/100000000000000 : ℝ)^3137
        have hw : |(2282609477/5000000000 : ℝ)|=(2282609477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2086043027/5000000000 : ℝ)|^4161 ≤ (7840910571343/25000000000000 : ℝ)^3137
        have hw : |(2086043027/5000000000 : ℝ)|=(2086043027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1129_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1193761/800000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16541/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9011/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2649/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14821/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16541/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9011/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16541/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9011/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16541/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9011/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16541/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9011/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16541/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9011/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16541/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9011/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9011/100000 : ℝ) ^ (8321/2048 : ℝ) ≤ (354107335289371/6250000000000000000 : ℝ) := by
    have hpowers : (9011/100000 : ℝ)^8321 ≤ (354107335289371/6250000000000000000 : ℝ)^2048 := by
      have hnat : (9011 : ℕ)^8321*6250000000000000000^2048 ≤ 354107335289371^2048*100000^8321 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9011 100000 354107335289371 6250000000000000000 8321 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9011/100000 : ℝ)) (X := (354107335289371/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 8321 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (16541/100000 : ℝ) ^ (8321/2048 : ℝ) ≤ (2088697835721361/3125000000000000000 : ℝ) := by
    have hpowers : (16541/100000 : ℝ)^8321 ≤ (2088697835721361/3125000000000000000 : ℝ)^2048 := by
      have hnat : (16541 : ℕ)^8321*3125000000000000000^2048 ≤ 2088697835721361^2048*100000^8321 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16541 100000 2088697835721361 3125000000000000000 8321 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16541/100000 : ℝ)) (X := (2088697835721361/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 8321 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125354107335289371/3125000000000000000 : ℝ) ≤ (10000278882191713/10000000000000000 : ℝ) ^ (8321/2048 : ℝ) := by
    have hpowers : (3125354107335289371/3125000000000000000 : ℝ)^2048 ≤ (10000278882191713/10000000000000000 : ℝ)^8321 := by
      have hnat : (3125354107335289371 : ℕ)^2048*10000000000000000^8321 ≤ 10000278882191713^8321*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125354107335289371 3125000000000000000 10000278882191713 10000000000000000 2048 8321 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000278882191713/10000000000000000 : ℝ)) (X := (3125354107335289371/3125000000000000000 : ℝ)) (by norm_num) 8321 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (6254531503006732093/6250000000000000000 : ℝ) ≤ (2500446003264567/2500000000000000 : ℝ) ^ (8321/2048 : ℝ) := by
    have hpowers : (6254531503006732093/6250000000000000000 : ℝ)^2048 ≤ (2500446003264567/2500000000000000 : ℝ)^8321 := by
      have hnat : (6254531503006732093 : ℕ)^2048*2500000000000000^8321 ≤ 2500446003264567^8321*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254531503006732093 6250000000000000000 2500446003264567 2500000000000000 2048 8321 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500446003264567/2500000000000000 : ℝ)) (X := (6254531503006732093/6250000000000000000 : ℝ)) (by norm_num) 8321 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (1564588697835721361/1562500000000000000 : ℝ) ≤ (10003289143924823/10000000000000000 : ℝ) ^ (8321/2048 : ℝ) := by
    have hpowers : (1564588697835721361/1562500000000000000 : ℝ)^2048 ≤ (10003289143924823/10000000000000000 : ℝ)^8321 := by
      have hnat : (1564588697835721361 : ℕ)^2048*10000000000000000^8321 ≤ 10003289143924823^8321*1562500000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1564588697835721361 1562500000000000000 10003289143924823 10000000000000000 2048 8321 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003289143924823/10000000000000000 : ℝ)) (X := (1564588697835721361/1562500000000000000 : ℝ)) (by norm_num) 8321 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(354107335289371/6250000000000000000 : ℝ) ≤ ((1881874362860663617/1882500000000000000 : ℝ)+2*(301026173311/150600000000000 : ℝ)*(9011/100000 : ℝ))^(8321/2048 : ℝ) := by
    rw [show (1881874362860663617/1882500000000000000 : ℝ)+2*(301026173311/150600000000000 : ℝ)*(9011/100000 : ℝ)=(10000278882191713/10000000000000000 : ℝ) by norm_num, show 1+2*(354107335289371/6250000000000000000 : ℝ)=(3125354107335289371/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2088697835721361/3125000000000000000 : ℝ)+(354107335289371/6250000000000000000 : ℝ) ≤ ((1881874362860663617/1882500000000000000 : ℝ)+(301026173311/150600000000000 : ℝ)*((16541/100000 : ℝ)+(9011/100000 : ℝ)))^(8321/2048 : ℝ) := by
    rw [show (1881874362860663617/1882500000000000000 : ℝ)+(301026173311/150600000000000 : ℝ)*((16541/100000 : ℝ)+(9011/100000 : ℝ))=(2500446003264567/2500000000000000 : ℝ) by norm_num, show 1+(2088697835721361/3125000000000000000 : ℝ)+(354107335289371/6250000000000000000 : ℝ)=(6254531503006732093/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2088697835721361/3125000000000000000 : ℝ) ≤ ((1881874362860663617/1882500000000000000 : ℝ)+2*(301026173311/150600000000000 : ℝ)*(16541/100000 : ℝ))^(8321/2048 : ℝ) := by
    rw [show (1881874362860663617/1882500000000000000 : ℝ)+2*(301026173311/150600000000000 : ℝ)*(16541/100000 : ℝ)=(10003289143924823/10000000000000000 : ℝ) by norm_num, show 1+2*(2088697835721361/3125000000000000000 : ℝ)=(1564588697835721361/1562500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1881874362860663617/1882500000000000000 : ℝ)*(X 1 0+X 2 0)+(301026173311/150600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8321/2048 : ℝ)) (lo := (9011/100000 : ℝ)) (hi := (16541/100000 : ℝ)) (c := (1881874362860663617/1882500000000000000 : ℝ)) (alpha := (301026173311/150600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1881874362860663617/1882500000000000000 : ℝ)*(X 0 1+X 2 1)+(301026173311/150600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8321/2048 : ℝ)) (lo := (9011/100000 : ℝ)) (hi := (16541/100000 : ℝ)) (c := (1881874362860663617/1882500000000000000 : ℝ)) (alpha := (301026173311/150600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1881874362860663617/1882500000000000000 : ℝ)*(X 0 2+X 1 2)+(301026173311/150600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8321/2048 : ℝ)) (lo := (9011/100000 : ℝ)) (hi := (16541/100000 : ℝ)) (c := (1881874362860663617/1882500000000000000 : ℝ)) (alpha := (301026173311/150600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2169172779/10000000000 : ℝ)*X 0 0+(1357632101/2500000000 : ℝ)*X 0 1+(5230849/10000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5354107217/10000000000 : ℝ)*X 1 0+(-283908927/1250000000 : ℝ)*X 1 1+(5230848893/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((535410731/1000000000 : ℝ)*X 2 0+(163464031/312500000 : ℝ)*X 2 1+(-1135635581/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((872833139/2000000000 : ℝ)*X 0 0+(2085263039/5000000000 : ℝ)*X 0 1+(228338497/500000000 : ℝ)*X 0 2+(872833139/2000000000 : ℝ)*X 1 0+(2085263039/5000000000 : ℝ)*X 1 1+(228338497/500000000 : ℝ)*X 1 2+(872833139/2000000000 : ℝ)*X 2 0+(2085263039/5000000000 : ℝ)*X 2 1+(228338497/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1084595747/5000000000 : ℝ)*X 0 0+(653953827/1250000000 : ℝ)*X 0 1+(5429742379/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2651783743/5000000000 : ℝ)*X 1 0+(-1036189269/5000000000 : ℝ)*X 1 1+(678717757/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5303568331/10000000000 : ℝ)*X 2 0+(271487077/500000000 : ℝ)*X 2 1+(-129523631/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((436420261/1000000000 : ℝ)*X 0 0+(2282609477/5000000000 : ℝ)*X 0 1+(2086043027/5000000000 : ℝ)*X 0 2+(436420261/1000000000 : ℝ)*X 1 0+(2282609477/5000000000 : ℝ)*X 1 1+(2086043027/5000000000 : ℝ)*X 1 2+(436420261/1000000000 : ℝ)*X 2 0+(2282609477/5000000000 : ℝ)*X 2 1+(2086043027/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (92753184715599144672632259/15687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1600122621/100000000000000 : ℝ)*(base19) + (755043069/50000000000000 : ℝ)*(base23) + (47390837/50000000000000 : ℝ)*(lower2) + (17054361/25000000000000 : ℝ)*(upper3) + (42864217/20000000000000 : ℝ)*(upper5) + (3765904860707577/100000000000000 : ℝ)*(major0) + (3765904860707577/100000000000000 : ℝ)*(major1) + (3765904860707577/100000000000000 : ℝ)*(major2) + (5008052775190617/100000000000000 : ℝ)*(sp0) + (5008083419414517/100000000000000 : ℝ)*(sp1) + (5008083509450999/100000000000000 : ℝ)*(sp2) + (252371189874319/10000000000000 : ℝ)*(sp3) + (32244346521/100000000000000 : ℝ)*(sp4) + (6303024849/50000000000000 : ℝ)*(sp7) + (315465563099111/12500000000000 : ℝ)*(f.failure) + (2504042509768569/50000000000000 : ℝ)*(f.sum) + (9567047291481/2510000000000000000000000000 : ℝ)*base66 + (820458296689595497/62750000000000000000000000000000 : ℝ)*base68 + (687598338835845497/62750000000000000000000000000000 : ℝ)*base70 + (84557113402845497/62750000000000000000000000000000 : ℝ)*base72 + (15686595027251/2510000000000000000000000000 : ℝ)*base74 + (623520123516345497/62750000000000000000000000000000 : ℝ)*base76 + (363696315590595497/62750000000000000000000000000000 : ℝ)*base78 + (40279010359404503/62750000000000000000000000000000 : ℝ)*base79 + (2712481029609/2510000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (146471/10000000000000000000 : ℝ)*base89 + (146471/10000000000000000000 : ℝ)*base91 + (146471/10000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (88427960452917166184511039/31375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (559050341/100000000000000 : ℝ)*(base19) + (379998733/25000000000000 : ℝ)*(base23) + (8044669/50000000000000 : ℝ)*(lower4) + (344883/400000000000 : ℝ)*(upper5) + (3795668915311167/100000000000000 : ℝ)*(major0) + (3795668915311167/100000000000000 : ℝ)*(major1) + (3795668915311167/100000000000000 : ℝ)*(major2) + (1158231661/100000000000000 : ℝ)*(sp0) + (2903499723/50000000000000 : ℝ)*(sp1) + (1906940211/10000000000000 : ℝ)*(sp2) + (5047665665882967/100000000000000 : ℝ)*(sp4) + (5047660458064841/100000000000000 : ℝ)*(sp5) + (1009529246943517/20000000000000 : ℝ)*(sp6) + (635917728140083/25000000000000 : ℝ)*(sp7) + (635917728140083/25000000000000 : ℝ)*(f.failure) + (1261916706028657/25000000000000 : ℝ)*(f.sum) + (20418596148551/2510000000000000000000000000 : ℝ)*base66 + (3450144121025487/62750000000000000000000000000000 : ℝ)*base68 + (375827969677775487/62750000000000000000000000000000 : ℝ)*base70 + (519893850267025487/62750000000000000000000000000000 : ℝ)*base72 + (3369459905639/2510000000000000000000000000 : ℝ)*base73 + (327448904460525487/62750000000000000000000000000000 : ℝ)*base76 + (53373632238724513/62750000000000000000000000000000 : ℝ)*base77 + (230203415052974513/62750000000000000000000000000000 : ℝ)*base79 + (4811446381501/2510000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (222163/20000000000000000000 : ℝ)*base89 + (222163/20000000000000000000 : ℝ)*base91 + (222163/20000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1129_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1193761/800000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16541/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9011/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2649/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14821/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1129_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1129_s4_0 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-434456003/2000000000 : ℝ)*x 0 + (1350630021/2500000000 : ℝ)*x 1 + (2628412607/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (434456003/2000000000 : ℝ)^4161 ≤ (13196766716211/100000000000000 : ℝ)^3137 := by
    have hnat : (434456003 : ℕ)^4161*100000000000000^3137 ≤ 13196766716211^3137*2000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434456003 2000000000 13196766716211 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1350630021/2500000000 : ℝ)^4161 ≤ (44188449144193/100000000000000 : ℝ)^3137 := by
    have hnat : (1350630021 : ℕ)^4161*100000000000000^3137 ≤ 44188449144193^3137*2500000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350630021 2500000000 44188449144193 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2628412607/5000000000 : ℝ)^4161 ≤ (21307392064003/50000000000000 : ℝ)^3137 := by
    have hnat : (2628412607 : ℕ)^4161*50000000000000^3137 ≤ 21307392064003^3137*5000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628412607 5000000000 21307392064003 50000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-434456003/2000000000 : ℝ), (1350630021/2500000000 : ℝ), (2628412607/5000000000 : ℝ)] ![(13196766716211/100000000000000 : ℝ), (44188449144193/100000000000000 : ℝ), (21307392064003/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-434456003/2000000000 : ℝ)|^4161 ≤ (13196766716211/100000000000000 : ℝ)^3137
        have hw : |(-434456003/2000000000 : ℝ)|=(434456003/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1350630021/2500000000 : ℝ)|^4161 ≤ (44188449144193/100000000000000 : ℝ)^3137
        have hw : |(1350630021/2500000000 : ℝ)|=(1350630021/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2628412607/5000000000 : ℝ)|^4161 ≤ (21307392064003/50000000000000 : ℝ)^3137
        have hw : |(2628412607/5000000000 : ℝ)|=(2628412607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_s4_1 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668390233/1250000000 : ℝ)*x 0 + (-1123165819/5000000000 : ℝ)*x 1 + (5256825371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668390233/1250000000 : ℝ)^4161 ≤ (43588433955231/100000000000000 : ℝ)^3137 := by
    have hnat : (668390233 : ℕ)^4161*100000000000000^3137 ≤ 43588433955231^3137*1250000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668390233 1250000000 43588433955231 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1123165819/5000000000 : ℝ)^4161 ≤ (1379678021643/10000000000000 : ℝ)^3137 := by
    have hnat : (1123165819 : ℕ)^4161*10000000000000^3137 ≤ 1379678021643^3137*5000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123165819 5000000000 1379678021643 10000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5256825371/10000000000 : ℝ)^4161 ≤ (4261478581619/10000000000000 : ℝ)^3137 := by
    have hnat : (5256825371 : ℕ)^4161*10000000000000^3137 ≤ 4261478581619^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256825371 10000000000 4261478581619 10000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668390233/1250000000 : ℝ), (-1123165819/5000000000 : ℝ), (5256825371/10000000000 : ℝ)] ![(43588433955231/100000000000000 : ℝ), (1379678021643/10000000000000 : ℝ), (4261478581619/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668390233/1250000000 : ℝ)|^4161 ≤ (43588433955231/100000000000000 : ℝ)^3137
        have hw : |(668390233/1250000000 : ℝ)|=(668390233/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1123165819/5000000000 : ℝ)|^4161 ≤ (1379678021643/10000000000000 : ℝ)^3137
        have hw : |(-1123165819/5000000000 : ℝ)|=(1123165819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5256825371/10000000000 : ℝ)|^4161 ≤ (4261478581619/10000000000000 : ℝ)^3137
        have hw : |(5256825371/10000000000 : ℝ)|=(5256825371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_s4_2 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069424489/2000000000 : ℝ)*x 0 + (2628412341/5000000000 : ℝ)*x 1 + (-17549467/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069424489/2000000000 : ℝ)^4161 ≤ (43588440237413/100000000000000 : ℝ)^3137 := by
    have hnat : (1069424489 : ℕ)^4161*100000000000000^3137 ≤ 43588440237413^3137*2000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069424489 2000000000 43588440237413 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2628412341/5000000000 : ℝ)^4161 ≤ (21307389203769/50000000000000 : ℝ)^3137 := by
    have hnat : (2628412341 : ℕ)^4161*50000000000000^3137 ≤ 21307389203769^3137*5000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628412341 5000000000 21307389203769 50000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (17549467/78125000 : ℝ)^4161 ≤ (862298833793/6250000000000 : ℝ)^3137 := by
    have hnat : (17549467 : ℕ)^4161*6250000000000^3137 ≤ 862298833793^3137*78125000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17549467 78125000 862298833793 6250000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069424489/2000000000 : ℝ), (2628412341/5000000000 : ℝ), (-17549467/78125000 : ℝ)] ![(43588440237413/100000000000000 : ℝ), (21307389203769/50000000000000 : ℝ), (862298833793/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069424489/2000000000 : ℝ)|^4161 ≤ (43588440237413/100000000000000 : ℝ)^3137
        have hw : |(1069424489/2000000000 : ℝ)|=(1069424489/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2628412341/5000000000 : ℝ)|^4161 ≤ (21307389203769/50000000000000 : ℝ)^3137
        have hw : |(2628412341/5000000000 : ℝ)|=(2628412341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-17549467/78125000 : ℝ)|^4161 ≤ (862298833793/6250000000000 : ℝ)^3137
        have hw : |(-17549467/78125000 : ℝ)|=(17549467/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_s4_3 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4366019743/10000000000 : ℝ)*x 0 + (844769557/2000000000 : ℝ)*x 1 + (564120813/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4366019743/10000000000 : ℝ)^4161 ≤ (33311954947117/100000000000000 : ℝ)^3137 := by
    have hnat : (4366019743 : ℕ)^4161*100000000000000^3137 ≤ 33311954947117^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4366019743 10000000000 33311954947117 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (844769557/2000000000 : ℝ)^4161 ≤ (31880821806061/100000000000000 : ℝ)^3137 := by
    have hnat : (844769557 : ℕ)^4161*100000000000000^3137 ≤ 31880821806061^3137*2000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      844769557 2000000000 31880821806061 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (564120813/1250000000 : ℝ)^4161 ≤ (108772572577/312500000000 : ℝ)^3137 := by
    have hnat : (564120813 : ℕ)^4161*312500000000^3137 ≤ 108772572577^3137*1250000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      564120813 1250000000 108772572577 312500000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4366019743/10000000000 : ℝ), (844769557/2000000000 : ℝ), (564120813/1250000000 : ℝ)] ![(33311954947117/100000000000000 : ℝ), (31880821806061/100000000000000 : ℝ), (108772572577/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4366019743/10000000000 : ℝ)|^4161 ≤ (33311954947117/100000000000000 : ℝ)^3137
        have hw : |(4366019743/10000000000 : ℝ)|=(4366019743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(844769557/2000000000 : ℝ)|^4161 ≤ (31880821806061/100000000000000 : ℝ)^3137
        have hw : |(844769557/2000000000 : ℝ)|=(844769557/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(564120813/1250000000 : ℝ)|^4161 ≤ (108772572577/312500000000 : ℝ)^3137
        have hw : |(564120813/1250000000 : ℝ)|=(564120813/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_s4_4 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2172288013/10000000000 : ℝ)*x 0 + (5257241633/10000000000 : ℝ)*x 1 + (5402101413/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2172288013/10000000000 : ℝ)^4161 ≤ (1649603895659/12500000000000 : ℝ)^3137 := by
    have hnat : (2172288013 : ℕ)^4161*12500000000000^3137 ≤ 1649603895659^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2172288013 10000000000 1649603895659 12500000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5257241633/10000000000 : ℝ)^4161 ≤ (5327407729933/12500000000000 : ℝ)^3137 := by
    have hnat : (5257241633 : ℕ)^4161*12500000000000^3137 ≤ 5327407729933^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257241633 10000000000 5327407729933 12500000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5402101413/10000000000 : ℝ)^4161 ≤ (2761494186169/6250000000000 : ℝ)^3137 := by
    have hnat : (5402101413 : ℕ)^4161*6250000000000^3137 ≤ 2761494186169^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402101413 10000000000 2761494186169 6250000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2172288013/10000000000 : ℝ), (5257241633/10000000000 : ℝ), (5402101413/10000000000 : ℝ)] ![(1649603895659/12500000000000 : ℝ), (5327407729933/12500000000000 : ℝ), (2761494186169/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2172288013/10000000000 : ℝ)|^4161 ≤ (1649603895659/12500000000000 : ℝ)^3137
        have hw : |(-2172288013/10000000000 : ℝ)|=(2172288013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5257241633/10000000000 : ℝ)|^4161 ≤ (5327407729933/12500000000000 : ℝ)^3137
        have hw : |(5257241633/10000000000 : ℝ)|=(5257241633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5402101413/10000000000 : ℝ)|^4161 ≤ (2761494186169/6250000000000 : ℝ)^3137
        have hw : |(5402101413/10000000000 : ℝ)|=(5402101413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_s4_5 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5310247503/10000000000 : ℝ)*x 0 + (-2101054971/10000000000 : ℝ)*x 1 + (5402101567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310247503/10000000000 : ℝ)^4161 ≤ (43190171804859/100000000000000 : ℝ)^3137 := by
    have hnat : (5310247503 : ℕ)^4161*100000000000000^3137 ≤ 43190171804859^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310247503 10000000000 43190171804859 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2101054971/10000000000 : ℝ)^4161 ≤ (2525183906407/20000000000000 : ℝ)^3137 := by
    have hnat : (2101054971 : ℕ)^4161*20000000000000^3137 ≤ 2525183906407^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2101054971 10000000000 2525183906407 20000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5402101567/10000000000 : ℝ)^4161 ≤ (4418390864943/10000000000000 : ℝ)^3137 := by
    have hnat : (5402101567 : ℕ)^4161*10000000000000^3137 ≤ 4418390864943^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402101567 10000000000 4418390864943 10000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310247503/10000000000 : ℝ), (-2101054971/10000000000 : ℝ), (5402101567/10000000000 : ℝ)] ![(43190171804859/100000000000000 : ℝ), (2525183906407/20000000000000 : ℝ), (4418390864943/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310247503/10000000000 : ℝ)|^4161 ≤ (43190171804859/100000000000000 : ℝ)^3137
        have hw : |(5310247503/10000000000 : ℝ)|=(5310247503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2101054971/10000000000 : ℝ)|^4161 ≤ (2525183906407/20000000000000 : ℝ)^3137
        have hw : |(-2101054971/10000000000 : ℝ)|=(2101054971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5402101567/10000000000 : ℝ)|^4161 ≤ (4418390864943/10000000000000 : ℝ)^3137
        have hw : |(5402101567/10000000000 : ℝ)|=(5402101567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_s4_6 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5310247631/10000000000 : ℝ)*x 0 + (5402101509/10000000000 : ℝ)*x 1 + (-525263719/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310247631/10000000000 : ℝ)^4161 ≤ (43190173185763/100000000000000 : ℝ)^3137 := by
    have hnat : (5310247631 : ℕ)^4161*100000000000000^3137 ≤ 43190173185763^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310247631 10000000000 43190173185763 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5402101509/10000000000 : ℝ)^4161 ≤ (11045977005049/25000000000000 : ℝ)^3137 := by
    have hnat : (5402101509 : ℕ)^4161*25000000000000^3137 ≤ 11045977005049^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402101509 10000000000 11045977005049 25000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (525263719/2500000000 : ℝ)^4161 ≤ (12625918774797/100000000000000 : ℝ)^3137 := by
    have hnat : (525263719 : ℕ)^4161*100000000000000^3137 ≤ 12625918774797^3137*2500000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525263719 2500000000 12625918774797 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310247631/10000000000 : ℝ), (5402101509/10000000000 : ℝ), (-525263719/2500000000 : ℝ)] ![(43190173185763/100000000000000 : ℝ), (11045977005049/25000000000000 : ℝ), (12625918774797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310247631/10000000000 : ℝ)|^4161 ≤ (43190173185763/100000000000000 : ℝ)^3137
        have hw : |(5310247631/10000000000 : ℝ)|=(5310247631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5402101509/10000000000 : ℝ)|^4161 ≤ (11045977005049/25000000000000 : ℝ)^3137
        have hw : |(5402101509/10000000000 : ℝ)|=(5402101509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-525263719/2500000000 : ℝ)|^4161 ≤ (12625918774797/100000000000000 : ℝ)^3137
        have hw : |(-525263719/2500000000 : ℝ)|=(525263719/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_s4_7 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (545754287/1250000000 : ℝ)*x 0 + (2256069351/5000000000 : ℝ)*x 1 + (4224678909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (545754287/1250000000 : ℝ)^4161 ≤ (33312102229359/100000000000000 : ℝ)^3137 := by
    have hnat : (545754287 : ℕ)^4161*100000000000000^3137 ≤ 33312102229359^3137*1250000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545754287 1250000000 33312102229359 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2256069351/5000000000 : ℝ)^4161 ≤ (2174922173407/6250000000000 : ℝ)^3137 := by
    have hnat : (2256069351 : ℕ)^4161*6250000000000^3137 ≤ 2174922173407^3137*5000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2256069351 5000000000 2174922173407 6250000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4224678909/10000000000 : ℝ)^4161 ≤ (31889142972637/100000000000000 : ℝ)^3137 := by
    have hnat : (4224678909 : ℕ)^4161*100000000000000^3137 ≤ 31889142972637^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4224678909 10000000000 31889142972637 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(545754287/1250000000 : ℝ), (2256069351/5000000000 : ℝ), (4224678909/10000000000 : ℝ)] ![(33312102229359/100000000000000 : ℝ), (2174922173407/6250000000000 : ℝ), (31889142972637/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(545754287/1250000000 : ℝ)|^4161 ≤ (33312102229359/100000000000000 : ℝ)^3137
        have hw : |(545754287/1250000000 : ℝ)|=(545754287/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2256069351/5000000000 : ℝ)|^4161 ≤ (2174922173407/6250000000000 : ℝ)^3137
        have hw : |(2256069351/5000000000 : ℝ)|=(2256069351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4224678909/10000000000 : ℝ)|^4161 ≤ (31889142972637/100000000000000 : ℝ)^3137
        have hw : |(4224678909/10000000000 : ℝ)|=(4224678909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1129_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1193761/800000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14821/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2649/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (223/2000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3559/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14821/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2649/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14821/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2649/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14821/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2649/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14821/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2649/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14821/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2649/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14821/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2649/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2649/25000 : ℝ) ^ (8321/2048 : ℝ) ≤ (2188734890870129/20000000000000000000 : ℝ) := by
    have hpowers : (2649/25000 : ℝ)^8321 ≤ (2188734890870129/20000000000000000000 : ℝ)^2048 := by
      have hnat : (2649 : ℕ)^8321*20000000000000000000^2048 ≤ 2188734890870129^2048*25000^8321 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2649 25000 2188734890870129 20000000000000000000 8321 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2649/25000 : ℝ)) (X := (2188734890870129/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8321 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14821/100000 : ℝ) ^ (8321/2048 : ℝ) ≤ (5348044857930081/12500000000000000000 : ℝ) := by
    have hpowers : (14821/100000 : ℝ)^8321 ≤ (5348044857930081/12500000000000000000 : ℝ)^2048 := by
      have hnat : (14821 : ℕ)^8321*12500000000000000000^2048 ≤ 5348044857930081^2048*100000^8321 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14821 100000 5348044857930081 12500000000000000000 8321 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14821/100000 : ℝ)) (X := (5348044857930081/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8321 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002188734890870129/10000000000000000000 : ℝ) ≤ (2000107731265173/2000000000000000 : ℝ) ^ (8321/2048 : ℝ) := by
    have hpowers : (10002188734890870129/10000000000000000000 : ℝ)^2048 ≤ (2000107731265173/2000000000000000 : ℝ)^8321 := by
      have hnat : (10002188734890870129 : ℕ)^2048*2000000000000000^8321 ≤ 2000107731265173^8321*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002188734890870129 10000000000000000000 2000107731265173 2000000000000000 2048 8321 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000107731265173/2000000000000000 : ℝ)) (X := (10002188734890870129/10000000000000000000 : ℝ)) (by norm_num) 8321 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100053728033317791293/100000000000000000000 : ℝ) ≤ (5000661054769847/5000000000000000 : ℝ) ^ (8321/2048 : ℝ) := by
    have hpowers : (100053728033317791293/100000000000000000000 : ℝ)^2048 ≤ (5000661054769847/5000000000000000 : ℝ)^8321 := by
      have hnat : (100053728033317791293 : ℕ)^2048*5000000000000000^8321 ≤ 5000661054769847^8321*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100053728033317791293 100000000000000000000 5000661054769847 5000000000000000 2048 8321 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000661054769847/5000000000000000 : ℝ)) (X := (100053728033317791293/100000000000000000000 : ℝ)) (by norm_num) 8321 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (6255348044857930081/6250000000000000000 : ℝ) ≤ (10002105562753523/10000000000000000 : ℝ) ^ (8321/2048 : ℝ) := by
    have hpowers : (6255348044857930081/6250000000000000000 : ℝ)^2048 ≤ (10002105562753523/10000000000000000 : ℝ)^8321 := by
      have hnat : (6255348044857930081 : ℕ)^2048*10000000000000000^8321 ≤ 10002105562753523^8321*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6255348044857930081 6250000000000000000 10002105562753523 10000000000000000 2048 8321 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002105562753523/10000000000000000 : ℝ)) (X := (6255348044857930081/6250000000000000000 : ℝ)) (by norm_num) 8321 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2188734890870129/20000000000000000000 : ℝ) ≤ ((3248897914036101189/3250000000000000000 : ℝ)+2*(60265631833/32500000000000 : ℝ)*(2649/25000 : ℝ))^(8321/2048 : ℝ) := by
    rw [show (3248897914036101189/3250000000000000000 : ℝ)+2*(60265631833/32500000000000 : ℝ)*(2649/25000 : ℝ)=(2000107731265173/2000000000000000 : ℝ) by norm_num, show 1+2*(2188734890870129/20000000000000000000 : ℝ)=(10002188734890870129/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5348044857930081/12500000000000000000 : ℝ)+(2188734890870129/20000000000000000000 : ℝ) ≤ ((3248897914036101189/3250000000000000000 : ℝ)+(60265631833/32500000000000 : ℝ)*((14821/100000 : ℝ)+(2649/25000 : ℝ)))^(8321/2048 : ℝ) := by
    rw [show (3248897914036101189/3250000000000000000 : ℝ)+(60265631833/32500000000000 : ℝ)*((14821/100000 : ℝ)+(2649/25000 : ℝ))=(5000661054769847/5000000000000000 : ℝ) by norm_num, show 1+(5348044857930081/12500000000000000000 : ℝ)+(2188734890870129/20000000000000000000 : ℝ)=(100053728033317791293/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5348044857930081/12500000000000000000 : ℝ) ≤ ((3248897914036101189/3250000000000000000 : ℝ)+2*(60265631833/32500000000000 : ℝ)*(14821/100000 : ℝ))^(8321/2048 : ℝ) := by
    rw [show (3248897914036101189/3250000000000000000 : ℝ)+2*(60265631833/32500000000000 : ℝ)*(14821/100000 : ℝ)=(10002105562753523/10000000000000000 : ℝ) by norm_num, show 1+2*(5348044857930081/12500000000000000000 : ℝ)=(6255348044857930081/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3248897914036101189/3250000000000000000 : ℝ)*(X 1 0+X 2 0)+(60265631833/32500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8321/2048 : ℝ)) (lo := (2649/25000 : ℝ)) (hi := (14821/100000 : ℝ)) (c := (3248897914036101189/3250000000000000000 : ℝ)) (alpha := (60265631833/32500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3248897914036101189/3250000000000000000 : ℝ)*(X 0 1+X 2 1)+(60265631833/32500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8321/2048 : ℝ)) (lo := (2649/25000 : ℝ)) (hi := (14821/100000 : ℝ)) (c := (3248897914036101189/3250000000000000000 : ℝ)) (alpha := (60265631833/32500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3248897914036101189/3250000000000000000 : ℝ)*(X 0 2+X 1 2)+(60265631833/32500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8321/2048 : ℝ)) (lo := (2649/25000 : ℝ)) (hi := (14821/100000 : ℝ)) (c := (3248897914036101189/3250000000000000000 : ℝ)) (alpha := (60265631833/32500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-434456003/2000000000 : ℝ)*X 0 0+(1350630021/2500000000 : ℝ)*X 0 1+(2628412607/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668390233/1250000000 : ℝ)*X 1 0+(-1123165819/5000000000 : ℝ)*X 1 1+(5256825371/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069424489/2000000000 : ℝ)*X 2 0+(2628412341/5000000000 : ℝ)*X 2 1+(-17549467/78125000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4366019743/10000000000 : ℝ)*X 0 0+(844769557/2000000000 : ℝ)*X 0 1+(564120813/1250000000 : ℝ)*X 0 2+(4366019743/10000000000 : ℝ)*X 1 0+(844769557/2000000000 : ℝ)*X 1 1+(564120813/1250000000 : ℝ)*X 1 2+(4366019743/10000000000 : ℝ)*X 2 0+(844769557/2000000000 : ℝ)*X 2 1+(564120813/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2172288013/10000000000 : ℝ)*X 0 0+(5257241633/10000000000 : ℝ)*X 0 1+(5402101413/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5310247503/10000000000 : ℝ)*X 1 0+(-2101054971/10000000000 : ℝ)*X 1 1+(5402101567/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5310247631/10000000000 : ℝ)*X 2 0+(5402101509/10000000000 : ℝ)*X 2 1+(-525263719/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((545754287/1250000000 : ℝ)*X 0 0+(2256069351/5000000000 : ℝ)*X 0 1+(4224678909/10000000000 : ℝ)*X 0 2+(545754287/1250000000 : ℝ)*X 1 0+(2256069351/5000000000 : ℝ)*X 1 1+(4224678909/10000000000 : ℝ)*X 1 2+(545754287/1250000000 : ℝ)*X 2 0+(2256069351/5000000000 : ℝ)*X 2 1+(4224678909/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11478653511680279705176137/781250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (900930131/100000000000000 : ℝ)*(base19) + (298904997/25000000000000 : ℝ)*(base23) + (98153737/25000000000000 : ℝ)*(lower2) + (394574587/100000000000000 : ℝ)*(upper3) + (151409283/100000000000000 : ℝ)*(lower4) + (645156244218257/12500000000000 : ℝ)*(major0) + (645156244218257/12500000000000 : ℝ)*(major1) + (645156244218257/12500000000000 : ℝ)*(major2) + (1372734696188177/20000000000000 : ℝ)*(sp0) + (274547290083161/4000000000000 : ℝ)*(sp1) + (6863681957389167/100000000000000 : ℝ)*(sp2) + (3458795125813783/100000000000000 : ℝ)*(sp3) + (9672068271/100000000000000 : ℝ)*(sp4) + (10569456641/50000000000000 : ℝ)*(sp7) + (432352033090883/12500000000000 : ℝ)*(f.failure) + (1715920788252289/25000000000000 : ℝ)*(f.sum) + (7701115580773/1625000000000000000000000000 : ℝ)*base65 + (25733287942557573/40625000000000000000000000000000 : ℝ)*base67 + (699790853089432573/40625000000000000000000000000000 : ℝ)*base69 + (29925042920682573/40625000000000000000000000000000 : ℝ)*base71 + (1136900661477/1625000000000000000000000000 : ℝ)*base74 + (293382335883182573/40625000000000000000000000000000 : ℝ)*base75 + (662364857623807573/40625000000000000000000000000000 : ℝ)*base77 + (438052234379317427/40625000000000000000000000000000 : ℝ)*base80 + (396408094301/812500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (19037/10000000000000000000 : ℝ)*base90 + (19037/10000000000000000000 : ℝ)*base92 + (19037/10000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13974120788958744347144577/1625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (356649777/20000000000000 : ℝ)*(base19) + (412441141/20000000000000 : ℝ)*(base23) + (2295253/800000000000 : ℝ)*(upper3) + (10954067/25000000000000 : ℝ)*(lower4) + (383248789/100000000000000 : ℝ)*(upper5) + (51909893627031/1000000000000 : ℝ)*(major0) + (51909893627031/1000000000000 : ℝ)*(major1) + (51909893627031/1000000000000 : ℝ)*(major2) + (22003703821/50000000000000 : ℝ)*(sp1) + (48333766201/100000000000000 : ℝ)*(sp2) + (1725808070641273/25000000000000 : ℝ)*(sp4) + (1380637298381713/20000000000000 : ℝ)*(sp5) + (1380636377318637/20000000000000 : ℝ)*(sp6) + (3478746156192471/100000000000000 : ℝ)*(sp7) + (3478746156192471/100000000000000 : ℝ)*(f.failure) + (1725808070641273/25000000000000 : ℝ)*(f.sum) + (52086599751/8125000000000000000000000 : ℝ)*base66 + (8342664479560141/3250000000000000000000000000000 : ℝ)*base68 + (8308153564810141/3250000000000000000000000000000 : ℝ)*base70 + (10016237097810141/3250000000000000000000000000000 : ℝ)*base72 + (292066036723/65000000000000000000000000 : ℝ)*base74 + (35056073060141/3250000000000000000000000000000 : ℝ)*base76 + (27157170936939859/3250000000000000000000000000000 : ℝ)*base77 + (26442364984689859/3250000000000000000000000000000 : ℝ)*base79 + (262345610403/65000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (373431/80000000000000000000 : ℝ)*base89 + (373431/80000000000000000000 : ℝ)*base91 + (373431/80000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1129_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1193761/800000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14821/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2649/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (223/2000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1129_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1129_s5_0 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-543236513/2500000000 : ℝ)*x 0 + (2697630277/5000000000 : ℝ)*x 1 + (5263647611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (543236513/2500000000 : ℝ)^4161 ≤ (412566687677/3125000000000 : ℝ)^3137 := by
    have hnat : (543236513 : ℕ)^4161*3125000000000^3137 ≤ 412566687677^3137*2500000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543236513 2500000000 412566687677 3125000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697630277/5000000000 : ℝ)^4161 ≤ (5513713339917/12500000000000 : ℝ)^3137 := by
    have hnat : (2697630277 : ℕ)^4161*12500000000000^3137 ≤ 5513713339917^3137*5000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697630277 5000000000 5513713339917 12500000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263647611/10000000000 : ℝ)^4161 ≤ (8537631852033/20000000000000 : ℝ)^3137 := by
    have hnat : (5263647611 : ℕ)^4161*20000000000000^3137 ≤ 8537631852033^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263647611 10000000000 8537631852033 20000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-543236513/2500000000 : ℝ), (2697630277/5000000000 : ℝ), (5263647611/10000000000 : ℝ)] ![(412566687677/3125000000000 : ℝ), (5513713339917/12500000000000 : ℝ), (8537631852033/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-543236513/2500000000 : ℝ)|^4161 ≤ (412566687677/3125000000000 : ℝ)^3137
        have hw : |(-543236513/2500000000 : ℝ)|=(543236513/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697630277/5000000000 : ℝ)|^4161 ≤ (5513713339917/12500000000000 : ℝ)^3137
        have hw : |(2697630277/5000000000 : ℝ)|=(2697630277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263647611/10000000000 : ℝ)|^4161 ≤ (8537631852033/20000000000000 : ℝ)^3137
        have hw : |(5263647611/10000000000 : ℝ)|=(5263647611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_s5_1 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672652077/5000000000 : ℝ)*x 0 + (-1119867281/5000000000 : ℝ)*x 1 + (657955941/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672652077/5000000000 : ℝ)^4161 ≤ (43568780682587/100000000000000 : ℝ)^3137 := by
    have hnat : (2672652077 : ℕ)^4161*100000000000000^3137 ≤ 43568780682587^3137*5000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672652077 5000000000 43568780682587 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1119867281/5000000000 : ℝ)^4161 ≤ (6871530467207/50000000000000 : ℝ)^3137 := by
    have hnat : (1119867281 : ℕ)^4161*50000000000000^3137 ≤ 6871530467207^3137*5000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119867281 5000000000 6871530467207 50000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (657955941/1250000000 : ℝ)^4161 ≤ (10672039591827/25000000000000 : ℝ)^3137 := by
    have hnat : (657955941 : ℕ)^4161*25000000000000^3137 ≤ 10672039591827^3137*1250000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657955941 1250000000 10672039591827 25000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672652077/5000000000 : ℝ), (-1119867281/5000000000 : ℝ), (657955941/1250000000 : ℝ)] ![(43568780682587/100000000000000 : ℝ), (6871530467207/50000000000000 : ℝ), (10672039591827/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672652077/5000000000 : ℝ)|^4161 ≤ (43568780682587/100000000000000 : ℝ)^3137
        have hw : |(2672652077/5000000000 : ℝ)|=(2672652077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1119867281/5000000000 : ℝ)|^4161 ≤ (6871530467207/50000000000000 : ℝ)^3137
        have hw : |(-1119867281/5000000000 : ℝ)|=(1119867281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(657955941/1250000000 : ℝ)|^4161 ≤ (10672039591827/25000000000000 : ℝ)^3137
        have hw : |(657955941/1250000000 : ℝ)|=(657955941/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_s5_2 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672652003/5000000000 : ℝ)*x 0 + (1052729531/2000000000 : ℝ)*x 1 + (-34995853/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672652003/5000000000 : ℝ)^4161 ≤ (8713755816497/20000000000000 : ℝ)^3137 := by
    have hnat : (2672652003 : ℕ)^4161*20000000000000^3137 ≤ 8713755816497^3137*5000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672652003 5000000000 8713755816497 20000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052729531/2000000000 : ℝ)^4161 ≤ (42688159733487/100000000000000 : ℝ)^3137 := by
    have hnat : (1052729531 : ℕ)^4161*100000000000000^3137 ≤ 42688159733487^3137*2000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052729531 2000000000 42688159733487 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (34995853/156250000 : ℝ)^4161 ≤ (1717882647323/12500000000000 : ℝ)^3137 := by
    have hnat : (34995853 : ℕ)^4161*12500000000000^3137 ≤ 1717882647323^3137*156250000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34995853 156250000 1717882647323 12500000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672652003/5000000000 : ℝ), (1052729531/2000000000 : ℝ), (-34995853/156250000 : ℝ)] ![(8713755816497/20000000000000 : ℝ), (42688159733487/100000000000000 : ℝ), (1717882647323/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672652003/5000000000 : ℝ)|^4161 ≤ (8713755816497/20000000000000 : ℝ)^3137
        have hw : |(2672652003/5000000000 : ℝ)|=(2672652003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1052729531/2000000000 : ℝ)|^4161 ≤ (42688159733487/100000000000000 : ℝ)^3137
        have hw : |(1052729531/2000000000 : ℝ)|=(1052729531/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-34995853/156250000 : ℝ)|^4161 ≤ (1717882647323/12500000000000 : ℝ)^3137
        have hw : |(-34995853/156250000 : ℝ)|=(34995853/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_s5_3 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (545800967/1250000000 : ℝ)*x 0 + (169510813/400000000 : ℝ)*x 1 + (4498943363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (545800967/1250000000 : ℝ)^4161 ≤ (33315881647923/100000000000000 : ℝ)^3137 := by
    have hnat : (545800967 : ℕ)^4161*100000000000000^3137 ≤ 33315881647923^3137*1250000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545800967 1250000000 33315881647923 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169510813/400000000 : ℝ)^4161 ≤ (8005070986613/25000000000000 : ℝ)^3137 := by
    have hnat : (169510813 : ℕ)^4161*25000000000000^3137 ≤ 8005070986613^3137*400000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169510813 400000000 8005070986613 25000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4498943363/10000000000 : ℝ)^4161 ≤ (6932766880131/20000000000000 : ℝ)^3137 := by
    have hnat : (4498943363 : ℕ)^4161*20000000000000^3137 ≤ 6932766880131^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4498943363 10000000000 6932766880131 20000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(545800967/1250000000 : ℝ), (169510813/400000000 : ℝ), (4498943363/10000000000 : ℝ)] ![(33315881647923/100000000000000 : ℝ), (8005070986613/25000000000000 : ℝ), (6932766880131/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(545800967/1250000000 : ℝ)|^4161 ≤ (33315881647923/100000000000000 : ℝ)^3137
        have hw : |(545800967/1250000000 : ℝ)|=(545800967/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(169510813/400000000 : ℝ)|^4161 ≤ (8005070986613/25000000000000 : ℝ)^3137
        have hw : |(169510813/400000000 : ℝ)|=(169510813/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4498943363/10000000000 : ℝ)|^4161 ≤ (6932766880131/20000000000000 : ℝ)^3137
        have hw : |(4498943363/10000000000 : ℝ)|=(4498943363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_s5_4 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-271618913/1250000000 : ℝ)*x 0 + (1052797623/2000000000 : ℝ)*x 1 + (5394918873/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (271618913/1250000000 : ℝ)^4161 ≤ (165027204141/1250000000000 : ℝ)^3137 := by
    have hnat : (271618913 : ℕ)^4161*1250000000000^3137 ≤ 165027204141^3137*1250000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271618913 1250000000 165027204141 1250000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052797623/2000000000 : ℝ)^4161 ≤ (21345911103529/50000000000000 : ℝ)^3137 := by
    have hnat : (1052797623 : ℕ)^4161*50000000000000^3137 ≤ 21345911103529^3137*2000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052797623 2000000000 21345911103529 50000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394918873/10000000000 : ℝ)^4161 ≤ (22053000718591/50000000000000 : ℝ)^3137 := by
    have hnat : (5394918873 : ℕ)^4161*50000000000000^3137 ≤ 22053000718591^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394918873 10000000000 22053000718591 50000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-271618913/1250000000 : ℝ), (1052797623/2000000000 : ℝ), (5394918873/10000000000 : ℝ)] ![(165027204141/1250000000000 : ℝ), (21345911103529/50000000000000 : ℝ), (22053000718591/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-271618913/1250000000 : ℝ)|^4161 ≤ (165027204141/1250000000000 : ℝ)^3137
        have hw : |(-271618913/1250000000 : ℝ)|=(271618913/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1052797623/2000000000 : ℝ)|^4161 ≤ (21345911103529/50000000000000 : ℝ)^3137
        have hw : |(1052797623/2000000000 : ℝ)|=(1052797623/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394918873/10000000000 : ℝ)|^4161 ≤ (22053000718591/50000000000000 : ℝ)^3137
        have hw : |(5394918873/10000000000 : ℝ)|=(5394918873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_s5_5 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (66399901/125000000 : ℝ)*x 0 + (-2108463299/10000000000 : ℝ)*x 1 + (5394918871/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66399901/125000000 : ℝ)^4161 ≤ (43208993849219/100000000000000 : ℝ)^3137 := by
    have hnat : (66399901 : ℕ)^4161*100000000000000^3137 ≤ 43208993849219^3137*125000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66399901 125000000 43208993849219 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2108463299/10000000000 : ℝ)^4161 ≤ (12685004725829/100000000000000 : ℝ)^3137 := by
    have hnat : (2108463299 : ℕ)^4161*100000000000000^3137 ≤ 12685004725829^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108463299 10000000000 12685004725829 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394918871/10000000000 : ℝ)^4161 ≤ (22053000707747/50000000000000 : ℝ)^3137 := by
    have hnat : (5394918871 : ℕ)^4161*50000000000000^3137 ≤ 22053000707747^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394918871 10000000000 22053000707747 50000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66399901/125000000 : ℝ), (-2108463299/10000000000 : ℝ), (5394918871/10000000000 : ℝ)] ![(43208993849219/100000000000000 : ℝ), (12685004725829/100000000000000 : ℝ), (22053000707747/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66399901/125000000 : ℝ)|^4161 ≤ (43208993849219/100000000000000 : ℝ)^3137
        have hw : |(66399901/125000000 : ℝ)|=(66399901/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2108463299/10000000000 : ℝ)|^4161 ≤ (12685004725829/100000000000000 : ℝ)^3137
        have hw : |(-2108463299/10000000000 : ℝ)|=(2108463299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394918871/10000000000 : ℝ)|^4161 ≤ (22053000707747/50000000000000 : ℝ)^3137
        have hw : |(5394918871/10000000000 : ℝ)|=(5394918871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_s5_6 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (212479683/400000000 : ℝ)*x 0 + (1348729717/2500000000 : ℝ)*x 1 + (-527115827/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212479683/400000000 : ℝ)^4161 ≤ (5401124224409/12500000000000 : ℝ)^3137 := by
    have hnat : (212479683 : ℕ)^4161*12500000000000^3137 ≤ 5401124224409^3137*400000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212479683 400000000 5401124224409 12500000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348729717/2500000000 : ℝ)^4161 ≤ (44106001382961/100000000000000 : ℝ)^3137 := by
    have hnat : (1348729717 : ℕ)^4161*100000000000000^3137 ≤ 44106001382961^3137*2500000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348729717 2500000000 44106001382961 100000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (527115827/2500000000 : ℝ)^4161 ≤ (253700095953/2000000000000 : ℝ)^3137 := by
    have hnat : (527115827 : ℕ)^4161*2000000000000^3137 ≤ 253700095953^3137*2500000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527115827 2500000000 253700095953 2000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212479683/400000000 : ℝ), (1348729717/2500000000 : ℝ), (-527115827/2500000000 : ℝ)] ![(5401124224409/12500000000000 : ℝ), (44106001382961/100000000000000 : ℝ), (253700095953/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212479683/400000000 : ℝ)|^4161 ≤ (5401124224409/12500000000000 : ℝ)^3137
        have hw : |(212479683/400000000 : ℝ)|=(212479683/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348729717/2500000000 : ℝ)|^4161 ≤ (44106001382961/100000000000000 : ℝ)^3137
        have hw : |(1348729717/2500000000 : ℝ)|=(1348729717/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-527115827/2500000000 : ℝ)|^4161 ≤ (253700095953/2000000000000 : ℝ)^3137
        have hw : |(-527115827/2500000000 : ℝ)|=(527115827/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1129_s5_7 (p : ℝ) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (873283701/2000000000 : ℝ)*x 0 + (899653541/2000000000 : ℝ)*x 1 + (4238448393/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (873283701/2000000000 : ℝ)^4161 ≤ (16657995318851/50000000000000 : ℝ)^3137 := by
    have hnat : (873283701 : ℕ)^4161*50000000000000^3137 ≤ 16657995318851^3137*2000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873283701 2000000000 16657995318851 50000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (899653541/2000000000 : ℝ)^4161 ≤ (4332116171371/12500000000000 : ℝ)^3137 := by
    have hnat : (899653541 : ℕ)^4161*12500000000000^3137 ≤ 4332116171371^3137*2000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899653541 2000000000 4332116171371 12500000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4238448393/10000000000 : ℝ)^4161 ≤ (16013539990287/50000000000000 : ℝ)^3137 := by
    have hnat : (4238448393 : ℕ)^4161*50000000000000^3137 ≤ 16013539990287^3137*10000000000^4161 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4238448393 10000000000 16013539990287 50000000000000 4161 3137 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4161/1024 : ℝ)) 4161 3137 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(873283701/2000000000 : ℝ), (899653541/2000000000 : ℝ), (4238448393/10000000000 : ℝ)] ![(16657995318851/50000000000000 : ℝ), (4332116171371/12500000000000 : ℝ), (16013539990287/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(873283701/2000000000 : ℝ)|^4161 ≤ (16657995318851/50000000000000 : ℝ)^3137
        have hw : |(873283701/2000000000 : ℝ)|=(873283701/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(899653541/2000000000 : ℝ)|^4161 ≤ (4332116171371/12500000000000 : ℝ)^3137
        have hw : |(899653541/2000000000 : ℝ)|=(899653541/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4238448393/10000000000 : ℝ)|^4161 ≤ (16013539990287/50000000000000 : ℝ)^3137
        have hw : |(4238448393/10000000000 : ℝ)|=(4238448393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1129_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1193761/800000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (223/2000 : ℝ)*pair X i i ≤ pair X i h) :
    (353/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3521/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3559/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (223/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3559/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (223/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3559/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (223/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3559/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (223/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3559/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (223/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3559/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (223/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (223/2000 : ℝ) ^ (8321/2048 : ℝ) ≤ (13461360374810949/100000000000000000000 : ℝ) := by
    have hpowers : (223/2000 : ℝ)^8321 ≤ (13461360374810949/100000000000000000000 : ℝ)^2048 := by
      have hnat : (223 : ℕ)^8321*100000000000000000000^2048 ≤ 13461360374810949^2048*2000^8321 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        223 2000 13461360374810949 100000000000000000000 8321 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (223/2000 : ℝ)) (X := (13461360374810949/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8321 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3559/25000 : ℝ) ^ (8321/2048 : ℝ) ≤ (36326644284154459/100000000000000000000 : ℝ) := by
    have hpowers : (3559/25000 : ℝ)^8321 ≤ (36326644284154459/100000000000000000000 : ℝ)^2048 := by
      have hnat : (3559 : ℕ)^8321*100000000000000000000^2048 ≤ 36326644284154459^2048*25000^8321 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3559 25000 36326644284154459 100000000000000000000 8321 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3559/25000 : ℝ)) (X := (36326644284154459/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8321 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013461360374810949/50000000000000000000 : ℝ) ≤ (2000132513249591/2000000000000000 : ℝ) ^ (8321/2048 : ℝ) := by
    have hpowers : (50013461360374810949/50000000000000000000 : ℝ)^2048 ≤ (2000132513249591/2000000000000000 : ℝ)^8321 := by
      have hnat : (50013461360374810949 : ℕ)^2048*2000000000000000^8321 ≤ 2000132513249591^8321*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013461360374810949 50000000000000000000 2000132513249591 2000000000000000 2048 8321 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000132513249591/2000000000000000 : ℝ)) (X := (50013461360374810949/50000000000000000000 : ℝ)) (by norm_num) 8321 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (3126555875145592669/3125000000000000000 : ℝ) ≤ (10001225173695441/10000000000000000 : ℝ) ^ (8321/2048 : ℝ) := by
    have hpowers : (3126555875145592669/3125000000000000000 : ℝ)^2048 ≤ (10001225173695441/10000000000000000 : ℝ)^8321 := by
      have hnat : (3126555875145592669 : ℕ)^2048*10000000000000000^8321 ≤ 10001225173695441^8321*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126555875145592669 3125000000000000000 10001225173695441 10000000000000000 2048 8321 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001225173695441/10000000000000000 : ℝ)) (X := (3126555875145592669/3125000000000000000 : ℝ)) (by norm_num) 8321 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036326644284154459/50000000000000000000 : ℝ) ≤ (10001787781142927/10000000000000000 : ℝ) ^ (8321/2048 : ℝ) := by
    have hpowers : (50036326644284154459/50000000000000000000 : ℝ)^2048 ≤ (10001787781142927/10000000000000000 : ℝ)^8321 := by
      have hnat : (50036326644284154459 : ℕ)^2048*10000000000000000^8321 ≤ 10001787781142927^8321*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036326644284154459 50000000000000000000 10001787781142927 10000000000000000 2048 8321 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001787781142927/10000000000000000 : ℝ)) (X := (50036326644284154459/50000000000000000000 : ℝ)) (by norm_num) 8321 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13461360374810949/100000000000000000000 : ℝ) ≤ ((3084949853336225133/3086000000000000000 : ℝ)+2*(281303723743/154300000000000 : ℝ)*(223/2000 : ℝ))^(8321/2048 : ℝ) := by
    rw [show (3084949853336225133/3086000000000000000 : ℝ)+2*(281303723743/154300000000000 : ℝ)*(223/2000 : ℝ)=(2000132513249591/2000000000000000 : ℝ) by norm_num, show 1+2*(13461360374810949/100000000000000000000 : ℝ)=(50013461360374810949/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36326644284154459/100000000000000000000 : ℝ)+(13461360374810949/100000000000000000000 : ℝ) ≤ ((3084949853336225133/3086000000000000000 : ℝ)+(281303723743/154300000000000 : ℝ)*((3559/25000 : ℝ)+(223/2000 : ℝ)))^(8321/2048 : ℝ) := by
    rw [show (3084949853336225133/3086000000000000000 : ℝ)+(281303723743/154300000000000 : ℝ)*((3559/25000 : ℝ)+(223/2000 : ℝ))=(10001225173695441/10000000000000000 : ℝ) by norm_num, show 1+(36326644284154459/100000000000000000000 : ℝ)+(13461360374810949/100000000000000000000 : ℝ)=(3126555875145592669/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36326644284154459/100000000000000000000 : ℝ) ≤ ((3084949853336225133/3086000000000000000 : ℝ)+2*(281303723743/154300000000000 : ℝ)*(3559/25000 : ℝ))^(8321/2048 : ℝ) := by
    rw [show (3084949853336225133/3086000000000000000 : ℝ)+2*(281303723743/154300000000000 : ℝ)*(3559/25000 : ℝ)=(10001787781142927/10000000000000000 : ℝ) by norm_num, show 1+2*(36326644284154459/100000000000000000000 : ℝ)=(50036326644284154459/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3084949853336225133/3086000000000000000 : ℝ)*(X 1 0+X 2 0)+(281303723743/154300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8321/2048 : ℝ)) (lo := (223/2000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (3084949853336225133/3086000000000000000 : ℝ)) (alpha := (281303723743/154300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3084949853336225133/3086000000000000000 : ℝ)*(X 0 1+X 2 1)+(281303723743/154300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8321/2048 : ℝ)) (lo := (223/2000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (3084949853336225133/3086000000000000000 : ℝ)) (alpha := (281303723743/154300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3084949853336225133/3086000000000000000 : ℝ)*(X 0 2+X 1 2)+(281303723743/154300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8321/2048 : ℝ)) (lo := (223/2000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (3084949853336225133/3086000000000000000 : ℝ)) (alpha := (281303723743/154300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-543236513/2500000000 : ℝ)*X 0 0+(2697630277/5000000000 : ℝ)*X 0 1+(5263647611/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672652077/5000000000 : ℝ)*X 1 0+(-1119867281/5000000000 : ℝ)*X 1 1+(657955941/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672652003/5000000000 : ℝ)*X 2 0+(1052729531/2000000000 : ℝ)*X 2 1+(-34995853/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((545800967/1250000000 : ℝ)*X 0 0+(169510813/400000000 : ℝ)*X 0 1+(4498943363/10000000000 : ℝ)*X 0 2+(545800967/1250000000 : ℝ)*X 1 0+(169510813/400000000 : ℝ)*X 1 1+(4498943363/10000000000 : ℝ)*X 1 2+(545800967/1250000000 : ℝ)*X 2 0+(169510813/400000000 : ℝ)*X 2 1+(4498943363/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-271618913/1250000000 : ℝ)*X 0 0+(1052797623/2000000000 : ℝ)*X 0 1+(5394918873/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((66399901/125000000 : ℝ)*X 1 0+(-2108463299/10000000000 : ℝ)*X 1 1+(5394918871/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((212479683/400000000 : ℝ)*X 2 0+(1348729717/2500000000 : ℝ)*X 2 1+(-527115827/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((873283701/2000000000 : ℝ)*X 0 0+(899653541/2000000000 : ℝ)*X 0 1+(4238448393/10000000000 : ℝ)*X 0 2+(873283701/2000000000 : ℝ)*X 1 0+(899653541/2000000000 : ℝ)*X 1 1+(4238448393/10000000000 : ℝ)*X 1 2+(873283701/2000000000 : ℝ)*X 2 0+(899653541/2000000000 : ℝ)*X 2 1+(4238448393/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1129_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (772053911256222266029593849/154300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1394184471/100000000000000 : ℝ)*(base19) + (988968871/100000000000000 : ℝ)*(base23) + (245605881/100000000000000 : ℝ)*(upper3) + (104148193/100000000000000 : ℝ)*(upper4) + (9612191/50000000000000 : ℝ)*(upper5) + (5713505716391551/100000000000000 : ℝ)*(major0) + (5713505716391551/100000000000000 : ℝ)*(major1) + (5713505716391551/100000000000000 : ℝ)*(major2) + (3799036759841379/50000000000000 : ℝ)*(sp0) + (7598098914666571/100000000000000 : ℝ)*(sp1) + (7598099319882171/100000000000000 : ℝ)*(sp2) + (3828892847079689/100000000000000 : ℝ)*(sp3) + (6697292071/25000000000000 : ℝ)*(sp4) + (18110066039/100000000000000 : ℝ)*(sp7) + (29913366852701/781250000000 : ℝ)*(f.failure) + (3799050154425521/50000000000000 : ℝ)*(f.sum) + (2076457963197/1928750000000000000000000000 : ℝ)*base65 + (2339775344480288717/308600000000000000000000000000000 : ℝ)*base68 + (405152994488511283/308600000000000000000000000000000 : ℝ)*base69 + (2973914312380888717/308600000000000000000000000000000 : ℝ)*base72 + (5275684819023/7715000000000000000000000000 : ℝ)*base73 + (38975305106288717/308600000000000000000000000000000 : ℝ)*base76 + (3160012793372088717/308600000000000000000000000000000 : ℝ)*base78 + (833192328467911283/308600000000000000000000000000000 : ℝ)*base79 + (10686617936963/7715000000000000000000000000 : ℝ)*base81 + (4711/625000000000000000 : ℝ)*base89 + (4711/625000000000000000 : ℝ)*base91 + (4711/625000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (803976831895479901784497101/77150000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (24814613/1250000000000 : ℝ)*(base19) + (2122441529/100000000000000 : ℝ)*(base23) + (211733329/100000000000000 : ℝ)*(upper3) + (33938937/50000000000000 : ℝ)*(lower4) + (218252519/100000000000000 : ℝ)*(upper5) + (2871612871112501/50000000000000 : ℝ)*(major0) + (2871612871112501/50000000000000 : ℝ)*(major1) + (2871612871112501/50000000000000 : ℝ)*(major2) + (13348793007/25000000000000 : ℝ)*(sp1) + (56055100713/100000000000000 : ℝ)*(sp2) + (1527524655618243/20000000000000 : ℝ)*(sp4) + (7637567897750147/100000000000000 : ℝ)*(sp5) + (7637565100548973/100000000000000 : ℝ)*(sp6) + (240551741187097/6250000000000 : ℝ)*(sp7) + (240551741187097/6250000000000 : ℝ)*(f.failure) + (1527524655618243/20000000000000 : ℝ)*(f.sum) + (11846245619257/3857500000000000000000000000 : ℝ)*base66 + (458742743076047633/154300000000000000000000000000000 : ℝ)*base67 + (380664667768247633/154300000000000000000000000000000 : ℝ)*base69 + (216778328346052367/154300000000000000000000000000000 : ℝ)*base72 + (10059824476279/7715000000000000000000000000 : ℝ)*base74 + (482068312673552367/154300000000000000000000000000000 : ℝ)*base76 + (2072739702225647633/154300000000000000000000000000000 : ℝ)*base77 + (1273278424303847633/154300000000000000000000000000000 : ℝ)*base79 + (11965557153027/3857500000000000000000000000 : ℝ)*base82 + (1817/5000000000000000000 : ℝ)*base89 + (1817/5000000000000000000 : ℝ)*base91 + (1817/5000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1129_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1193761/800000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (223/2000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (353/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3521/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1129_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1129_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1193761/800000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16541/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9011/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (353/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3521/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1129_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1129_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1129_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8321/2048 : ℝ) ≤ p) (hpb : p ≤ (4161/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1193761/800000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16541/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9011/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (353/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3521/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1129_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
