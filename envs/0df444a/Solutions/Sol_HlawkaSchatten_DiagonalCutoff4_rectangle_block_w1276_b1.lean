-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1276_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:20:42.24576+00:00
-- url     : https://prove2.me/submissions/23c68dd3-8171-4ff7-927f-68c5453a9626

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
theorem support_rectangle_w1276_s3_0 (p : ℝ) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-524951969/2500000000 : ℝ)*x 0 + (2718264589/5000000000 : ℝ)*x 1 + (5223619619/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (524951969/2500000000 : ℝ)^1059 ≤ (6383478055221/50000000000000 : ℝ)^803 := by
    have hnat : (524951969 : ℕ)^1059*50000000000000^803 ≤ 6383478055221^803*2500000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524951969 2500000000 6383478055221 50000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2718264589/5000000000 : ℝ)^1059 ≤ (44765259047677/100000000000000 : ℝ)^803 := by
    have hnat : (2718264589 : ℕ)^1059*100000000000000^803 ≤ 44765259047677^803*5000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718264589 5000000000 44765259047677 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5223619619/10000000000 : ℝ)^1059 ≤ (4246778483247/10000000000000 : ℝ)^803 := by
    have hnat : (5223619619 : ℕ)^1059*10000000000000^803 ≤ 4246778483247^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5223619619 10000000000 4246778483247 10000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1059/256 : ℝ)) 1059 803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-524951969/2500000000 : ℝ), (2718264589/5000000000 : ℝ), (5223619619/10000000000 : ℝ)] ![(6383478055221/50000000000000 : ℝ), (44765259047677/100000000000000 : ℝ), (4246778483247/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-524951969/2500000000 : ℝ)|^1059 ≤ (6383478055221/50000000000000 : ℝ)^803
        have hw : |(-524951969/2500000000 : ℝ)|=(524951969/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2718264589/5000000000 : ℝ)|^1059 ≤ (44765259047677/100000000000000 : ℝ)^803
        have hw : |(2718264589/5000000000 : ℝ)|=(2718264589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5223619619/10000000000 : ℝ)|^1059 ≤ (4246778483247/10000000000000 : ℝ)^803
        have hw : |(5223619619/10000000000 : ℝ)|=(5223619619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1276_s3_1 (p : ℝ) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1338794201/2500000000 : ℝ)*x 0 + (-2208827161/10000000000 : ℝ)*x 1 + (5223619521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338794201/2500000000 : ℝ)^1059 ≤ (43883947797737/100000000000000 : ℝ)^803 := by
    have hnat : (1338794201 : ℕ)^1059*100000000000000^803 ≤ 43883947797737^803*2500000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338794201 2500000000 43883947797737 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2208827161/10000000000 : ℝ)^1059 ≤ (13648268400757/100000000000000 : ℝ)^803 := by
    have hnat : (2208827161 : ℕ)^1059*100000000000000^803 ≤ 13648268400757^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2208827161 10000000000 13648268400757 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5223619521/10000000000 : ℝ)^1059 ≤ (42467783781731/100000000000000 : ℝ)^803 := by
    have hnat : (5223619521 : ℕ)^1059*100000000000000^803 ≤ 42467783781731^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5223619521 10000000000 42467783781731 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1059/256 : ℝ)) 1059 803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338794201/2500000000 : ℝ), (-2208827161/10000000000 : ℝ), (5223619521/10000000000 : ℝ)] ![(43883947797737/100000000000000 : ℝ), (13648268400757/100000000000000 : ℝ), (42467783781731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338794201/2500000000 : ℝ)|^1059 ≤ (43883947797737/100000000000000 : ℝ)^803
        have hw : |(1338794201/2500000000 : ℝ)|=(1338794201/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2208827161/10000000000 : ℝ)|^1059 ≤ (13648268400757/100000000000000 : ℝ)^803
        have hw : |(-2208827161/10000000000 : ℝ)|=(2208827161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5223619521/10000000000 : ℝ)|^1059 ≤ (42467783781731/100000000000000 : ℝ)^803
        have hw : |(5223619521/10000000000 : ℝ)|=(5223619521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1276_s3_2 (p : ℝ) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2677588369/5000000000 : ℝ)*x 0 + (652952493/1250000000 : ℝ)*x 1 + (-2208826693/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677588369/5000000000 : ℝ)^1059 ≤ (43883947084463/100000000000000 : ℝ)^803 := by
    have hnat : (2677588369 : ℕ)^1059*100000000000000^803 ≤ 43883947084463^803*5000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677588369 5000000000 43883947084463 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (652952493/1250000000 : ℝ)^1059 ≤ (42467788317061/100000000000000 : ℝ)^803 := by
    have hnat : (652952493 : ℕ)^1059*100000000000000^803 ≤ 42467788317061^803*1250000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652952493 1250000000 42467788317061 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2208826693/10000000000 : ℝ)^1059 ≤ (1706033073387/12500000000000 : ℝ)^803 := by
    have hnat : (2208826693 : ℕ)^1059*12500000000000^803 ≤ 1706033073387^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2208826693 10000000000 1706033073387 12500000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1059/256 : ℝ)) 1059 803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677588369/5000000000 : ℝ), (652952493/1250000000 : ℝ), (-2208826693/10000000000 : ℝ)] ![(43883947084463/100000000000000 : ℝ), (42467788317061/100000000000000 : ℝ), (1706033073387/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677588369/5000000000 : ℝ)|^1059 ≤ (43883947084463/100000000000000 : ℝ)^803
        have hw : |(2677588369/5000000000 : ℝ)|=(2677588369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(652952493/1250000000 : ℝ)|^1059 ≤ (42467788317061/100000000000000 : ℝ)^803
        have hw : |(652952493/1250000000 : ℝ)|=(652952493/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2208826693/10000000000 : ℝ)|^1059 ≤ (1706033073387/12500000000000 : ℝ)^803
        have hw : |(-2208826693/10000000000 : ℝ)|=(2208826693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1276_s3_3 (p : ℝ) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4342623387/10000000000 : ℝ)*x 0 + (4130409537/10000000000 : ℝ)*x 1 + (1141328709/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4342623387/10000000000 : ℝ)^1059 ≤ (1040197858581/3125000000000 : ℝ)^803 := by
    have hnat : (4342623387 : ℕ)^1059*3125000000000^803 ≤ 1040197858581^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4342623387 10000000000 1040197858581 3125000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4130409537/10000000000 : ℝ)^1059 ≤ (7789507627517/25000000000000 : ℝ)^803 := by
    have hnat : (4130409537 : ℕ)^1059*25000000000000^803 ≤ 7789507627517^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4130409537 10000000000 7789507627517 25000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1141328709/2500000000 : ℝ)^1059 ≤ (4444454751019/12500000000000 : ℝ)^803 := by
    have hnat : (1141328709 : ℕ)^1059*12500000000000^803 ≤ 4444454751019^803*2500000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1141328709 2500000000 4444454751019 12500000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1059/256 : ℝ)) 1059 803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4342623387/10000000000 : ℝ), (4130409537/10000000000 : ℝ), (1141328709/2500000000 : ℝ)] ![(1040197858581/3125000000000 : ℝ), (7789507627517/25000000000000 : ℝ), (4444454751019/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4342623387/10000000000 : ℝ)|^1059 ≤ (1040197858581/3125000000000 : ℝ)^803
        have hw : |(4342623387/10000000000 : ℝ)|=(4342623387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4130409537/10000000000 : ℝ)|^1059 ≤ (7789507627517/25000000000000 : ℝ)^803
        have hw : |(4130409537/10000000000 : ℝ)|=(4130409537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1141328709/2500000000 : ℝ)|^1059 ≤ (4444454751019/12500000000000 : ℝ)^803
        have hw : |(1141328709/2500000000 : ℝ)|=(1141328709/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1276_s3_4 (p : ℝ) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-524957777/2500000000 : ℝ)*x 0 + (2612273871/5000000000 : ℝ)*x 1 + (2717797797/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (524957777/2500000000 : ℝ)^1059 ≤ (2553428478891/20000000000000 : ℝ)^803 := by
    have hnat : (524957777 : ℕ)^1059*20000000000000^803 ≤ 2553428478891^803*2500000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524957777 2500000000 2553428478891 20000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2612273871/5000000000 : ℝ)^1059 ≤ (21238868140641/50000000000000 : ℝ)^803 := by
    have hnat : (2612273871 : ℕ)^1059*50000000000000^803 ≤ 21238868140641^803*5000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2612273871 5000000000 21238868140641 50000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2717797797/5000000000 : ℝ)^1059 ≤ (44755121304031/100000000000000 : ℝ)^803 := by
    have hnat : (2717797797 : ℕ)^1059*100000000000000^803 ≤ 44755121304031^803*5000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717797797 5000000000 44755121304031 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1059/256 : ℝ)) 1059 803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-524957777/2500000000 : ℝ), (2612273871/5000000000 : ℝ), (2717797797/5000000000 : ℝ)] ![(2553428478891/20000000000000 : ℝ), (21238868140641/50000000000000 : ℝ), (44755121304031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-524957777/2500000000 : ℝ)|^1059 ≤ (2553428478891/20000000000000 : ℝ)^803
        have hw : |(-524957777/2500000000 : ℝ)|=(524957777/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2612273871/5000000000 : ℝ)|^1059 ≤ (21238868140641/50000000000000 : ℝ)^803
        have hw : |(2612273871/5000000000 : ℝ)|=(2612273871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2717797797/5000000000 : ℝ)|^1059 ≤ (44755121304031/100000000000000 : ℝ)^803
        have hw : |(2717797797/5000000000 : ℝ)|=(2717797797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1276_s3_5 (p : ℝ) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1325192977/2500000000 : ℝ)*x 0 + (-249606463/1250000000 : ℝ)*x 1 + (2717797933/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325192977/2500000000 : ℝ)^1059 ≤ (10824234696229/25000000000000 : ℝ)^803 := by
    have hnat : (1325192977 : ℕ)^1059*25000000000000^803 ≤ 10824234696229^803*2500000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325192977 2500000000 10824234696229 25000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (249606463/1250000000 : ℝ)^1059 ≤ (11947936940851/100000000000000 : ℝ)^803 := by
    have hnat : (249606463 : ℕ)^1059*100000000000000^803 ≤ 11947936940851^803*1250000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249606463 1250000000 11947936940851 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2717797933/5000000000 : ℝ)^1059 ≤ (8951024851517/20000000000000 : ℝ)^803 := by
    have hnat : (2717797933 : ℕ)^1059*20000000000000^803 ≤ 8951024851517^803*5000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717797933 5000000000 8951024851517 20000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1059/256 : ℝ)) 1059 803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1325192977/2500000000 : ℝ), (-249606463/1250000000 : ℝ), (2717797933/5000000000 : ℝ)] ![(10824234696229/25000000000000 : ℝ), (11947936940851/100000000000000 : ℝ), (8951024851517/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1325192977/2500000000 : ℝ)|^1059 ≤ (10824234696229/25000000000000 : ℝ)^803
        have hw : |(1325192977/2500000000 : ℝ)|=(1325192977/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-249606463/1250000000 : ℝ)|^1059 ≤ (11947936940851/100000000000000 : ℝ)^803
        have hw : |(-249606463/1250000000 : ℝ)|=(249606463/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2717797933/5000000000 : ℝ)|^1059 ≤ (8951024851517/20000000000000 : ℝ)^803
        have hw : |(2717797933/5000000000 : ℝ)|=(2717797933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1276_s3_6 (p : ℝ) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2650386479/5000000000 : ℝ)*x 0 + (108711899/200000000 : ℝ)*x 1 + (-1996851531/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2650386479/5000000000 : ℝ)^1059 ≤ (10824237523893/25000000000000 : ℝ)^803 := by
    have hnat : (2650386479 : ℕ)^1059*25000000000000^803 ≤ 10824237523893^803*5000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2650386479 5000000000 10824237523893 25000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (108711899/200000000 : ℝ)^1059 ≤ (22377557155529/50000000000000 : ℝ)^803 := by
    have hnat : (108711899 : ℕ)^1059*50000000000000^803 ≤ 22377557155529^803*200000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108711899 200000000 22377557155529 50000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1996851531/10000000000 : ℝ)^1059 ≤ (11947935575723/100000000000000 : ℝ)^803 := by
    have hnat : (1996851531 : ℕ)^1059*100000000000000^803 ≤ 11947935575723^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1996851531 10000000000 11947935575723 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1059/256 : ℝ)) 1059 803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2650386479/5000000000 : ℝ), (108711899/200000000 : ℝ), (-1996851531/10000000000 : ℝ)] ![(10824237523893/25000000000000 : ℝ), (22377557155529/50000000000000 : ℝ), (11947935575723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2650386479/5000000000 : ℝ)|^1059 ≤ (10824237523893/25000000000000 : ℝ)^803
        have hw : |(2650386479/5000000000 : ℝ)|=(2650386479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(108711899/200000000 : ℝ)|^1059 ≤ (22377557155529/50000000000000 : ℝ)^803
        have hw : |(108711899/200000000 : ℝ)|=(108711899/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1996851531/10000000000 : ℝ)|^1059 ≤ (11947935575723/100000000000000 : ℝ)^803
        have hw : |(-1996851531/10000000000 : ℝ)|=(1996851531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1276_s3_7 (p : ℝ) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4342672937/10000000000 : ℝ)*x 0 + (4563418511/10000000000 : ℝ)*x 1 + (2066158371/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4342672937/10000000000 : ℝ)^1059 ≤ (33286832360289/100000000000000 : ℝ)^803 := by
    have hnat : (4342672937 : ℕ)^1059*100000000000000^803 ≤ 33286832360289^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4342672937 10000000000 33286832360289 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4563418511/10000000000 : ℝ)^1059 ≤ (8884040475093/25000000000000 : ℝ)^803 := by
    have hnat : (4563418511 : ℕ)^1059*25000000000000^803 ≤ 8884040475093^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4563418511 10000000000 8884040475093 25000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2066158371/5000000000 : ℝ)^1059 ≤ (15588502861017/50000000000000 : ℝ)^803 := by
    have hnat : (2066158371 : ℕ)^1059*50000000000000^803 ≤ 15588502861017^803*5000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2066158371 5000000000 15588502861017 50000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1059/256 : ℝ)) 1059 803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4342672937/10000000000 : ℝ), (4563418511/10000000000 : ℝ), (2066158371/5000000000 : ℝ)] ![(33286832360289/100000000000000 : ℝ), (8884040475093/25000000000000 : ℝ), (15588502861017/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4342672937/10000000000 : ℝ)|^1059 ≤ (33286832360289/100000000000000 : ℝ)^803
        have hw : |(4342672937/10000000000 : ℝ)|=(4342672937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4563418511/10000000000 : ℝ)|^1059 ≤ (8884040475093/25000000000000 : ℝ)^803
        have hw : |(4563418511/10000000000 : ℝ)|=(4563418511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2066158371/5000000000 : ℝ)|^1059 ≤ (15588502861017/50000000000000 : ℝ)^803
        have hw : |(2066158371/5000000000 : ℝ)|=(2066158371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1276_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152133963/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16393/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1877/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (2117/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (943/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16393/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1877/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16393/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1877/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16393/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1877/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16393/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1877/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16393/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1877/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16393/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1877/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
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
  have hpowlo : (1877/20000 : ℝ) ^ (4235/1024 : ℝ) ≤ (5626691298614319/100000000000000000000 : ℝ) := by
    have hpowers : (1877/20000 : ℝ)^4235 ≤ (5626691298614319/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1877 : ℕ)^4235*100000000000000000000^1024 ≤ 5626691298614319^1024*20000^4235 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1877 20000 5626691298614319 100000000000000000000 4235 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1877/20000 : ℝ)) (X := (5626691298614319/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4235 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16393/100000 : ℝ) ^ (4235/1024 : ℝ) ≤ (28248785336078831/50000000000000000000 : ℝ) := by
    have hpowers : (16393/100000 : ℝ)^4235 ≤ (28248785336078831/50000000000000000000 : ℝ)^1024 := by
      have hnat : (16393 : ℕ)^4235*50000000000000000000^1024 ≤ 28248785336078831^1024*100000^4235 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16393 100000 28248785336078831 50000000000000000000 4235 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16393/100000 : ℝ)) (X := (28248785336078831/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4235 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005626691298614319/50000000000000000000 : ℝ) ≤ (2500068022268001/2500000000000000 : ℝ) ^ (4235/1024 : ℝ) := by
    have hpowers : (50005626691298614319/50000000000000000000 : ℝ)^1024 ≤ (2500068022268001/2500000000000000 : ℝ)^4235 := by
      have hnat : (50005626691298614319 : ℕ)^1024*2500000000000000^4235 ≤ 2500068022268001^4235*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005626691298614319 50000000000000000000 2500068022268001 2500000000000000 1024 4235 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500068022268001/2500000000000000 : ℝ)) (X := (50005626691298614319/50000000000000000000 : ℝ)) (by norm_num) 4235 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100062124261970771981/100000000000000000000 : ℝ) ≤ (1250187722158741/1250000000000000 : ℝ) ^ (4235/1024 : ℝ) := by
    have hpowers : (100062124261970771981/100000000000000000000 : ℝ)^1024 ≤ (1250187722158741/1250000000000000 : ℝ)^4235 := by
      have hnat : (100062124261970771981 : ℕ)^1024*1250000000000000^4235 ≤ 1250187722158741^4235*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100062124261970771981 100000000000000000000 1250187722158741 1250000000000000 1024 4235 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250187722158741/1250000000000000 : ℝ)) (X := (100062124261970771981/100000000000000000000 : ℝ)) (by norm_num) 4235 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25028248785336078831/25000000000000000000 : ℝ) ≤ (2500682866366963/2500000000000000 : ℝ) ^ (4235/1024 : ℝ) := by
    have hpowers : (25028248785336078831/25000000000000000000 : ℝ)^1024 ≤ (2500682866366963/2500000000000000 : ℝ)^4235 := by
      have hnat : (25028248785336078831 : ℕ)^1024*2500000000000000^4235 ≤ 2500682866366963^4235*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25028248785336078831 25000000000000000000 2500682866366963 2500000000000000 1024 4235 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500682866366963/2500000000000000 : ℝ)) (X := (25028248785336078831/25000000000000000000 : ℝ)) (by norm_num) 4235 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5626691298614319/100000000000000000000 : ℝ) ≤ ((8757353194092696319/8760000000000000000 : ℝ)+2*(307422049481/175200000000000 : ℝ)*(1877/20000 : ℝ))^(4235/1024 : ℝ) := by
    rw [show (8757353194092696319/8760000000000000000 : ℝ)+2*(307422049481/175200000000000 : ℝ)*(1877/20000 : ℝ)=(2500068022268001/2500000000000000 : ℝ) by norm_num, show 1+2*(5626691298614319/100000000000000000000 : ℝ)=(50005626691298614319/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(28248785336078831/50000000000000000000 : ℝ)+(5626691298614319/100000000000000000000 : ℝ) ≤ ((8757353194092696319/8760000000000000000 : ℝ)+(307422049481/175200000000000 : ℝ)*((16393/100000 : ℝ)+(1877/20000 : ℝ)))^(4235/1024 : ℝ) := by
    rw [show (8757353194092696319/8760000000000000000 : ℝ)+(307422049481/175200000000000 : ℝ)*((16393/100000 : ℝ)+(1877/20000 : ℝ))=(1250187722158741/1250000000000000 : ℝ) by norm_num, show 1+(28248785336078831/50000000000000000000 : ℝ)+(5626691298614319/100000000000000000000 : ℝ)=(100062124261970771981/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(28248785336078831/50000000000000000000 : ℝ) ≤ ((8757353194092696319/8760000000000000000 : ℝ)+2*(307422049481/175200000000000 : ℝ)*(16393/100000 : ℝ))^(4235/1024 : ℝ) := by
    rw [show (8757353194092696319/8760000000000000000 : ℝ)+2*(307422049481/175200000000000 : ℝ)*(16393/100000 : ℝ)=(2500682866366963/2500000000000000 : ℝ) by norm_num, show 1+2*(28248785336078831/50000000000000000000 : ℝ)=(25028248785336078831/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8757353194092696319/8760000000000000000 : ℝ)*(X 1 0+X 2 0)+(307422049481/175200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4235/1024 : ℝ)) (lo := (1877/20000 : ℝ)) (hi := (16393/100000 : ℝ)) (c := (8757353194092696319/8760000000000000000 : ℝ)) (alpha := (307422049481/175200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8757353194092696319/8760000000000000000 : ℝ)*(X 0 1+X 2 1)+(307422049481/175200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4235/1024 : ℝ)) (lo := (1877/20000 : ℝ)) (hi := (16393/100000 : ℝ)) (c := (8757353194092696319/8760000000000000000 : ℝ)) (alpha := (307422049481/175200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8757353194092696319/8760000000000000000 : ℝ)*(X 0 2+X 1 2)+(307422049481/175200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4235/1024 : ℝ)) (lo := (1877/20000 : ℝ)) (hi := (16393/100000 : ℝ)) (c := (8757353194092696319/8760000000000000000 : ℝ)) (alpha := (307422049481/175200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-524951969/2500000000 : ℝ)*X 0 0+(2718264589/5000000000 : ℝ)*X 0 1+(5223619619/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1276_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338794201/2500000000 : ℝ)*X 1 0+(-2208827161/10000000000 : ℝ)*X 1 1+(5223619521/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1276_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2677588369/5000000000 : ℝ)*X 2 0+(652952493/1250000000 : ℝ)*X 2 1+(-2208826693/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1276_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4342623387/10000000000 : ℝ)*X 0 0+(4130409537/10000000000 : ℝ)*X 0 1+(1141328709/2500000000 : ℝ)*X 0 2+(4342623387/10000000000 : ℝ)*X 1 0+(4130409537/10000000000 : ℝ)*X 1 1+(1141328709/2500000000 : ℝ)*X 1 2+(4342623387/10000000000 : ℝ)*X 2 0+(4130409537/10000000000 : ℝ)*X 2 1+(1141328709/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1276_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-524957777/2500000000 : ℝ)*X 0 0+(2612273871/5000000000 : ℝ)*X 0 1+(2717797797/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1276_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1325192977/2500000000 : ℝ)*X 1 0+(-249606463/1250000000 : ℝ)*X 1 1+(2717797933/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1276_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2650386479/5000000000 : ℝ)*X 2 0+(108711899/200000000 : ℝ)*X 2 1+(-1996851531/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1276_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4342672937/10000000000 : ℝ)*X 0 0+(4563418511/10000000000 : ℝ)*X 0 1+(2066158371/5000000000 : ℝ)*X 0 2+(4342672937/10000000000 : ℝ)*X 1 0+(4563418511/10000000000 : ℝ)*X 1 1+(2066158371/5000000000 : ℝ)*X 1 2+(4342672937/10000000000 : ℝ)*X 2 0+(4563418511/10000000000 : ℝ)*X 2 1+(2066158371/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1276_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (458493638650468087615215479/73000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7284729/625000000000 : ℝ)*(base19) + (227497747/20000000000000 : ℝ)*(base23) + (16477829/100000000000000 : ℝ)*(upper4) + (177913267/100000000000000 : ℝ)*(upper5) + (3498129435300641/100000000000000 : ℝ)*(major0) + (3498129435300641/100000000000000 : ℝ)*(major1) + (1749064717650321/50000000000000 : ℝ)*(major2) + (293553386363573/6250000000000 : ℝ)*(sp0) + (4696877107903629/100000000000000 : ℝ)*(sp1) + (4696883099846067/100000000000000 : ℝ)*(sp2) + (574840946022143/25000000000000 : ℝ)*(sp3) + (15027758817/50000000000000 : ℝ)*(sp4) + (1490968633/25000000000000 : ℝ)*(sp5) + (5319910037/50000000000000 : ℝ)*(sp7) + (1149687211954323/50000000000000 : ℝ)*(f.failure) + (2348442118667401/50000000000000 : ℝ)*(f.sum) + (101846932442117/17520000000000000000000000000 : ℝ)*base66 + (12430252082140859521/876000000000000000000000000000000 : ℝ)*base68 + (2185137870825106601/438000000000000000000000000000000 : ℝ)*base70 + (8938978753804859521/876000000000000000000000000000000 : ℝ)*base72 + (101651306206997/17520000000000000000000000000 : ℝ)*base74 + (1004595888320893399/438000000000000000000000000000000 : ℝ)*base75 + (7402709166702909521/876000000000000000000000000000000 : ℝ)*base78 + (11273491311030909521/876000000000000000000000000000000 : ℝ)*base80 + (1016139003119/8760000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (82972049/5000000000000000000000 : ℝ)*base89 + (82972049/5000000000000000000000 : ℝ)*base91 + (32972049/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2048746461455737814039/730000000000000000000000000 : ℝ) := by norm_num
    linear_combination (78914531/50000000000000 : ℝ)*(base15) + (415254797/100000000000000 : ℝ)*(lower2) + (1699191/20000000000000 : ℝ)*(upper3) + (29290129/100000000000000 : ℝ)*(lower4) + (44122199/100000000000000 : ℝ)*(upper5) + (882240680261329/25000000000000 : ℝ)*(major0) + (882240680261329/25000000000000 : ℝ)*(major1) + (882240680261329/25000000000000 : ℝ)*(major2) + (5240057019/100000000000000 : ℝ)*(sp0) + (3436055149/50000000000000 : ℝ)*(sp1) + (4738278490362203/100000000000000 : ℝ)*(sp4) + (2369138350239931/50000000000000 : ℝ)*(sp5) + (2369141865209611/50000000000000 : ℝ)*(sp6) + (2319641618121337/100000000000000 : ℝ)*(sp7) + (2319641618121337/100000000000000 : ℝ)*(f.failure) + (2369141865209611/50000000000000 : ℝ)*(f.sum) + (48366891779941/2190000000000000000000000000 : ℝ)*base66 + (325555066083797951/219000000000000000000000000000000 : ℝ)*base67 + (342493085774202049/219000000000000000000000000000000 : ℝ)*base70 + (528187916685797951/219000000000000000000000000000000 : ℝ)*base71 + (6586304785859/2190000000000000000000000000 : ℝ)*base73 + (338855146907202049/219000000000000000000000000000000 : ℝ)*base76 + (5821181494286202049/219000000000000000000000000000000 : ℝ)*base78 + (355528962735797951/219000000000000000000000000000000 : ℝ)*base79 + (2398640606431/2190000000000000000000000000 : ℝ)*base82 + (12668531/10000000000000000000000 : ℝ)*base89 + (12668531/10000000000000000000000 : ℝ)*base91 + (12668531/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1276_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152133963/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16393/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1877/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2117/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (943/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1276_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1276_s4_0 (p : ℝ) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2101908291/10000000000 : ℝ)*x 0 + (5420187697/10000000000 : ℝ)*x 1 + (5238584731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2101908291/10000000000 : ℝ)^1059 ≤ (12783800782383/100000000000000 : ℝ)^803 := by
    have hnat : (2101908291 : ℕ)^1059*100000000000000^803 ≤ 12783800782383^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2101908291 10000000000 12783800782383 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5420187697/10000000000 : ℝ)^1059 ≤ (44587887920423/100000000000000 : ℝ)^803 := by
    have hnat : (5420187697 : ℕ)^1059*100000000000000^803 ≤ 44587887920423^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420187697 10000000000 44587887920423 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5238584731/10000000000 : ℝ)^1059 ≤ (42628311283993/100000000000000 : ℝ)^803 := by
    have hnat : (5238584731 : ℕ)^1059*100000000000000^803 ≤ 42628311283993^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5238584731 10000000000 42628311283993 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1059/256 : ℝ)) 1059 803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2101908291/10000000000 : ℝ), (5420187697/10000000000 : ℝ), (5238584731/10000000000 : ℝ)] ![(12783800782383/100000000000000 : ℝ), (44587887920423/100000000000000 : ℝ), (42628311283993/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2101908291/10000000000 : ℝ)|^1059 ≤ (12783800782383/100000000000000 : ℝ)^803
        have hw : |(-2101908291/10000000000 : ℝ)|=(2101908291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5420187697/10000000000 : ℝ)|^1059 ≤ (44587887920423/100000000000000 : ℝ)^803
        have hw : |(5420187697/10000000000 : ℝ)|=(5420187697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5238584731/10000000000 : ℝ)|^1059 ≤ (42628311283993/100000000000000 : ℝ)^803
        have hw : |(5238584731/10000000000 : ℝ)|=(5238584731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1276_s4_1 (p : ℝ) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1337764269/2500000000 : ℝ)*x 0 + (-1097288043/5000000000 : ℝ)*x 1 + (5238584723/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337764269/2500000000 : ℝ)^1059 ≤ (43839430626019/100000000000000 : ℝ)^803 := by
    have hnat : (1337764269 : ℕ)^1059*100000000000000^803 ≤ 43839430626019^803*2500000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337764269 2500000000 43839430626019 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1097288043/5000000000 : ℝ)^1059 ≤ (13532258160233/100000000000000 : ℝ)^803 := by
    have hnat : (1097288043 : ℕ)^1059*100000000000000^803 ≤ 13532258160233^803*5000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097288043 5000000000 13532258160233 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5238584723/10000000000 : ℝ)^1059 ≤ (2131415559907/5000000000000 : ℝ)^803 := by
    have hnat : (5238584723 : ℕ)^1059*5000000000000^803 ≤ 2131415559907^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5238584723 10000000000 2131415559907 5000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1059/256 : ℝ)) 1059 803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337764269/2500000000 : ℝ), (-1097288043/5000000000 : ℝ), (5238584723/10000000000 : ℝ)] ![(43839430626019/100000000000000 : ℝ), (13532258160233/100000000000000 : ℝ), (2131415559907/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337764269/2500000000 : ℝ)|^1059 ≤ (43839430626019/100000000000000 : ℝ)^803
        have hw : |(1337764269/2500000000 : ℝ)|=(1337764269/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1097288043/5000000000 : ℝ)|^1059 ≤ (13532258160233/100000000000000 : ℝ)^803
        have hw : |(-1097288043/5000000000 : ℝ)|=(1097288043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5238584723/10000000000 : ℝ)|^1059 ≤ (2131415559907/5000000000000 : ℝ)^803
        have hw : |(5238584723/10000000000 : ℝ)|=(5238584723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1276_s4_2 (p : ℝ) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1337764267/2500000000 : ℝ)*x 0 + (65482309/125000000 : ℝ)*x 1 + (-21945761/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337764267/2500000000 : ℝ)^1059 ≤ (43839430539583/100000000000000 : ℝ)^803 := by
    have hnat : (1337764267 : ℕ)^1059*100000000000000^803 ≤ 43839430539583^803*2500000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337764267 2500000000 43839430539583 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (65482309/125000000 : ℝ)^1059 ≤ (8525662233189/20000000000000 : ℝ)^803 := by
    have hnat : (65482309 : ℕ)^1059*20000000000000^803 ≤ 8525662233189^803*125000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65482309 125000000 8525662233189 20000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21945761/100000000 : ℝ)^1059 ≤ (13532258274081/100000000000000 : ℝ)^803 := by
    have hnat : (21945761 : ℕ)^1059*100000000000000^803 ≤ 13532258274081^803*100000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21945761 100000000 13532258274081 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1059/256 : ℝ)) 1059 803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337764267/2500000000 : ℝ), (65482309/125000000 : ℝ), (-21945761/100000000 : ℝ)] ![(43839430539583/100000000000000 : ℝ), (8525662233189/20000000000000 : ℝ), (13532258274081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337764267/2500000000 : ℝ)|^1059 ≤ (43839430539583/100000000000000 : ℝ)^803
        have hw : |(1337764267/2500000000 : ℝ)|=(1337764267/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(65482309/125000000 : ℝ)|^1059 ≤ (8525662233189/20000000000000 : ℝ)^803
        have hw : |(65482309/125000000 : ℝ)|=(65482309/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-21945761/100000000 : ℝ)|^1059 ≤ (13532258274081/100000000000000 : ℝ)^803
        have hw : |(-21945761/100000000 : ℝ)|=(21945761/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1276_s4_3 (p : ℝ) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ)) (x : Fin 3 → ℝ) :
    (542986189/1250000000 : ℝ)*x 0 + (4162223509/10000000000 : ℝ)*x 1 + (2266590081/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (542986189/1250000000 : ℝ)^1059 ≤ (33299130913971/100000000000000 : ℝ)^803 := by
    have hnat : (542986189 : ℕ)^1059*100000000000000^803 ≤ 33299130913971^803*1250000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542986189 1250000000 33299130913971 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4162223509/10000000000 : ℝ)^1059 ≤ (31474919502539/100000000000000 : ℝ)^803 := by
    have hnat : (4162223509 : ℕ)^1059*100000000000000^803 ≤ 31474919502539^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4162223509 10000000000 31474919502539 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2266590081/5000000000 : ℝ)^1059 ≤ (17612974785057/50000000000000 : ℝ)^803 := by
    have hnat : (2266590081 : ℕ)^1059*50000000000000^803 ≤ 17612974785057^803*5000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2266590081 5000000000 17612974785057 50000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1059/256 : ℝ)) 1059 803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(542986189/1250000000 : ℝ), (4162223509/10000000000 : ℝ), (2266590081/5000000000 : ℝ)] ![(33299130913971/100000000000000 : ℝ), (31474919502539/100000000000000 : ℝ), (17612974785057/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(542986189/1250000000 : ℝ)|^1059 ≤ (33299130913971/100000000000000 : ℝ)^803
        have hw : |(542986189/1250000000 : ℝ)|=(542986189/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4162223509/10000000000 : ℝ)|^1059 ≤ (31474919502539/100000000000000 : ℝ)^803
        have hw : |(4162223509/10000000000 : ℝ)|=(4162223509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2266590081/5000000000 : ℝ)|^1059 ≤ (17612974785057/50000000000000 : ℝ)^803
        have hw : |(2266590081/5000000000 : ℝ)|=(2266590081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1276_s4_4 (p : ℝ) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-262740371/1250000000 : ℝ)*x 0 + (261963027/500000000 : ℝ)*x 1 + (677438539/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (262740371/1250000000 : ℝ)^1059 ≤ (798994906639/6250000000000 : ℝ)^803 := by
    have hnat : (262740371 : ℕ)^1059*6250000000000^803 ≤ 798994906639^803*1250000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262740371 1250000000 798994906639 6250000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (261963027/500000000 : ℝ)^1059 ≤ (21317781973279/50000000000000 : ℝ)^803 := by
    have hnat : (261963027 : ℕ)^1059*50000000000000^803 ≤ 21317781973279^803*500000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261963027 500000000 21317781973279 50000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (677438539/1250000000 : ℝ)^1059 ≤ (11145129383467/25000000000000 : ℝ)^803 := by
    have hnat : (677438539 : ℕ)^1059*25000000000000^803 ≤ 11145129383467^803*1250000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677438539 1250000000 11145129383467 25000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1059/256 : ℝ)) 1059 803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-262740371/1250000000 : ℝ), (261963027/500000000 : ℝ), (677438539/1250000000 : ℝ)] ![(798994906639/6250000000000 : ℝ), (21317781973279/50000000000000 : ℝ), (11145129383467/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-262740371/1250000000 : ℝ)|^1059 ≤ (798994906639/6250000000000 : ℝ)^803
        have hw : |(-262740371/1250000000 : ℝ)|=(262740371/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(261963027/500000000 : ℝ)|^1059 ≤ (21317781973279/50000000000000 : ℝ)^803
        have hw : |(261963027/500000000 : ℝ)|=(261963027/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(677438539/1250000000 : ℝ)|^1059 ≤ (11145129383467/25000000000000 : ℝ)^803
        have hw : |(677438539/1250000000 : ℝ)|=(677438539/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1276_s4_5 (p : ℝ) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2652328457/5000000000 : ℝ)*x 0 + (-503413131/2500000000 : ℝ)*x 1 + (5419508403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652328457/5000000000 : ℝ)^1059 ≤ (21669396582299/50000000000000 : ℝ)^803 := by
    have hnat : (2652328457 : ℕ)^1059*50000000000000^803 ≤ 21669396582299^803*5000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652328457 5000000000 21669396582299 50000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (503413131/2500000000 : ℝ)^1059 ≤ (6040344147691/50000000000000 : ℝ)^803 := by
    have hnat : (503413131 : ℕ)^1059*50000000000000^803 ≤ 6040344147691^803*2500000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      503413131 2500000000 6040344147691 50000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5419508403/10000000000 : ℝ)^1059 ≤ (44580518521073/100000000000000 : ℝ)^803 := by
    have hnat : (5419508403 : ℕ)^1059*100000000000000^803 ≤ 44580518521073^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419508403 10000000000 44580518521073 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1059/256 : ℝ)) 1059 803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652328457/5000000000 : ℝ), (-503413131/2500000000 : ℝ), (5419508403/10000000000 : ℝ)] ![(21669396582299/50000000000000 : ℝ), (6040344147691/50000000000000 : ℝ), (44580518521073/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652328457/5000000000 : ℝ)|^1059 ≤ (21669396582299/50000000000000 : ℝ)^803
        have hw : |(2652328457/5000000000 : ℝ)|=(2652328457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-503413131/2500000000 : ℝ)|^1059 ≤ (6040344147691/50000000000000 : ℝ)^803
        have hw : |(-503413131/2500000000 : ℝ)|=(503413131/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5419508403/10000000000 : ℝ)|^1059 ≤ (44580518521073/100000000000000 : ℝ)^803
        have hw : |(5419508403/10000000000 : ℝ)|=(5419508403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1276_s4_6 (p : ℝ) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1060931361/2000000000 : ℝ)*x 0 + (2709754129/5000000000 : ℝ)*x 1 + (-251706609/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060931361/2000000000 : ℝ)^1059 ≤ (4333879199017/10000000000000 : ℝ)^803 := by
    have hnat : (1060931361 : ℕ)^1059*10000000000000^803 ≤ 4333879199017^803*2000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060931361 2000000000 4333879199017 10000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2709754129/5000000000 : ℝ)^1059 ≤ (8916103389611/20000000000000 : ℝ)^803 := by
    have hnat : (2709754129 : ℕ)^1059*20000000000000^803 ≤ 8916103389611^803*5000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709754129 5000000000 8916103389611 20000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (251706609/1250000000 : ℝ)^1059 ≤ (12080691048767/100000000000000 : ℝ)^803 := by
    have hnat : (251706609 : ℕ)^1059*100000000000000^803 ≤ 12080691048767^803*1250000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      251706609 1250000000 12080691048767 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1059/256 : ℝ)) 1059 803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060931361/2000000000 : ℝ), (2709754129/5000000000 : ℝ), (-251706609/1250000000 : ℝ)] ![(4333879199017/10000000000000 : ℝ), (8916103389611/20000000000000 : ℝ), (12080691048767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060931361/2000000000 : ℝ)|^1059 ≤ (4333879199017/10000000000000 : ℝ)^803
        have hw : |(1060931361/2000000000 : ℝ)|=(1060931361/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2709754129/5000000000 : ℝ)|^1059 ≤ (8916103389611/20000000000000 : ℝ)^803
        have hw : |(2709754129/5000000000 : ℝ)|=(2709754129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-251706609/1250000000 : ℝ)|^1059 ≤ (12080691048767/100000000000000 : ℝ)^803
        have hw : |(-251706609/1250000000 : ℝ)|=(251706609/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1276_s4_7 (p : ℝ) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ)) (x : Fin 3 → ℝ) :
    (542989959/1250000000 : ℝ)*x 0 + (2265899697/5000000000 : ℝ)*x 1 + (4163611659/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (542989959/1250000000 : ℝ)^1059 ≤ (6659887164049/20000000000000 : ℝ)^803 := by
    have hnat : (542989959 : ℕ)^1059*20000000000000^803 ≤ 6659887164049^803*1250000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542989959 1250000000 6659887164049 20000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2265899697/5000000000 : ℝ)^1059 ≤ (35211800113243/100000000000000 : ℝ)^803 := by
    have hnat : (2265899697 : ℕ)^1059*100000000000000^803 ≤ 35211800113243^803*5000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2265899697 5000000000 35211800113243 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4163611659/10000000000 : ℝ)^1059 ≤ (15744382030799/50000000000000 : ℝ)^803 := by
    have hnat : (4163611659 : ℕ)^1059*50000000000000^803 ≤ 15744382030799^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4163611659 10000000000 15744382030799 50000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1059/256 : ℝ)) 1059 803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(542989959/1250000000 : ℝ), (2265899697/5000000000 : ℝ), (4163611659/10000000000 : ℝ)] ![(6659887164049/20000000000000 : ℝ), (35211800113243/100000000000000 : ℝ), (15744382030799/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(542989959/1250000000 : ℝ)|^1059 ≤ (6659887164049/20000000000000 : ℝ)^803
        have hw : |(542989959/1250000000 : ℝ)|=(542989959/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2265899697/5000000000 : ℝ)|^1059 ≤ (35211800113243/100000000000000 : ℝ)^803
        have hw : |(2265899697/5000000000 : ℝ)|=(2265899697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4163611659/10000000000 : ℝ)|^1059 ≤ (15744382030799/50000000000000 : ℝ)^803
        have hw : |(4163611659/10000000000 : ℝ)|=(4163611659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1276_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152133963/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (943/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2117/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (2181/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3687/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (943/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2117/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (943/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2117/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (943/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2117/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (943/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2117/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (943/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2117/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (943/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2117/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2117/20000 : ℝ) ^ (4235/1024 : ℝ) ≤ (231373098318861/2500000000000000000 : ℝ) := by
    have hpowers : (2117/20000 : ℝ)^4235 ≤ (231373098318861/2500000000000000000 : ℝ)^1024 := by
      have hnat : (2117 : ℕ)^4235*2500000000000000000^1024 ≤ 231373098318861^1024*20000^4235 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2117 20000 231373098318861 2500000000000000000 4235 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2117/20000 : ℝ)) (X := (231373098318861/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4235 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (943/6250 : ℝ) ^ (4235/1024 : ℝ) ≤ (40089659578018449/100000000000000000000 : ℝ) := by
    have hpowers : (943/6250 : ℝ)^4235 ≤ (40089659578018449/100000000000000000000 : ℝ)^1024 := by
      have hnat : (943 : ℕ)^4235*100000000000000000000^1024 ≤ 40089659578018449^1024*6250^4235 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        943 6250 40089659578018449 100000000000000000000 4235 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (943/6250 : ℝ)) (X := (40089659578018449/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4235 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1250231373098318861/1250000000000000000 : ℝ) ≤ (5000223763333237/5000000000000000 : ℝ) ^ (4235/1024 : ℝ) := by
    have hpowers : (1250231373098318861/1250000000000000000 : ℝ)^1024 ≤ (5000223763333237/5000000000000000 : ℝ)^4235 := by
      have hnat : (1250231373098318861 : ℕ)^1024*5000000000000000^4235 ≤ 5000223763333237^4235*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250231373098318861 1250000000000000000 5000223763333237 5000000000000000 1024 4235 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000223763333237/5000000000000000 : ℝ)) (X := (1250231373098318861/1250000000000000000 : ℝ)) (by norm_num) 4235 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100049344583510772889/100000000000000000000 : ℝ) ≤ (10001192902101157/10000000000000000 : ℝ) ^ (4235/1024 : ℝ) := by
    have hpowers : (100049344583510772889/100000000000000000000 : ℝ)^1024 ≤ (10001192902101157/10000000000000000 : ℝ)^4235 := by
      have hnat : (100049344583510772889 : ℕ)^1024*10000000000000000^4235 ≤ 10001192902101157^4235*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100049344583510772889 100000000000000000000 10001192902101157 10000000000000000 1024 4235 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001192902101157/10000000000000000 : ℝ)) (X := (100049344583510772889/100000000000000000000 : ℝ)) (by norm_num) 4235 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50040089659578018449/50000000000000000000 : ℝ) ≤ (62512114234599/62500000000000 : ℝ) ^ (4235/1024 : ℝ) := by
    have hpowers : (50040089659578018449/50000000000000000000 : ℝ)^1024 ≤ (62512114234599/62500000000000 : ℝ)^4235 := by
      have hnat : (50040089659578018449 : ℕ)^1024*62500000000000^4235 ≤ 62512114234599^4235*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50040089659578018449 50000000000000000000 62512114234599 62500000000000 1024 4235 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (62512114234599/62500000000000 : ℝ)) (X := (50040089659578018449/50000000000000000000 : ℝ)) (by norm_num) 4235 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(231373098318861/2500000000000000000 : ℝ) ≤ ((87922335184818151/87949218750000000 : ℝ)+2*(745375434683/450300000000000 : ℝ)*(2117/20000 : ℝ))^(4235/1024 : ℝ) := by
    rw [show (87922335184818151/87949218750000000 : ℝ)+2*(745375434683/450300000000000 : ℝ)*(2117/20000 : ℝ)=(5000223763333237/5000000000000000 : ℝ) by norm_num, show 1+2*(231373098318861/2500000000000000000 : ℝ)=(1250231373098318861/1250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(40089659578018449/100000000000000000000 : ℝ)+(231373098318861/2500000000000000000 : ℝ) ≤ ((87922335184818151/87949218750000000 : ℝ)+(745375434683/450300000000000 : ℝ)*((943/6250 : ℝ)+(2117/20000 : ℝ)))^(4235/1024 : ℝ) := by
    rw [show (87922335184818151/87949218750000000 : ℝ)+(745375434683/450300000000000 : ℝ)*((943/6250 : ℝ)+(2117/20000 : ℝ))=(10001192902101157/10000000000000000 : ℝ) by norm_num, show 1+(40089659578018449/100000000000000000000 : ℝ)+(231373098318861/2500000000000000000 : ℝ)=(100049344583510772889/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(40089659578018449/100000000000000000000 : ℝ) ≤ ((87922335184818151/87949218750000000 : ℝ)+2*(745375434683/450300000000000 : ℝ)*(943/6250 : ℝ))^(4235/1024 : ℝ) := by
    rw [show (87922335184818151/87949218750000000 : ℝ)+2*(745375434683/450300000000000 : ℝ)*(943/6250 : ℝ)=(62512114234599/62500000000000 : ℝ) by norm_num, show 1+2*(40089659578018449/100000000000000000000 : ℝ)=(50040089659578018449/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (87922335184818151/87949218750000000 : ℝ)*(X 1 0+X 2 0)+(745375434683/450300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4235/1024 : ℝ)) (lo := (2117/20000 : ℝ)) (hi := (943/6250 : ℝ)) (c := (87922335184818151/87949218750000000 : ℝ)) (alpha := (745375434683/450300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (87922335184818151/87949218750000000 : ℝ)*(X 0 1+X 2 1)+(745375434683/450300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4235/1024 : ℝ)) (lo := (2117/20000 : ℝ)) (hi := (943/6250 : ℝ)) (c := (87922335184818151/87949218750000000 : ℝ)) (alpha := (745375434683/450300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (87922335184818151/87949218750000000 : ℝ)*(X 0 2+X 1 2)+(745375434683/450300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4235/1024 : ℝ)) (lo := (2117/20000 : ℝ)) (hi := (943/6250 : ℝ)) (c := (87922335184818151/87949218750000000 : ℝ)) (alpha := (745375434683/450300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2101908291/10000000000 : ℝ)*X 0 0+(5420187697/10000000000 : ℝ)*X 0 1+(5238584731/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1276_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337764269/2500000000 : ℝ)*X 1 0+(-1097288043/5000000000 : ℝ)*X 1 1+(5238584723/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1276_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337764267/2500000000 : ℝ)*X 2 0+(65482309/125000000 : ℝ)*X 2 1+(-21945761/100000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1276_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((542986189/1250000000 : ℝ)*X 0 0+(4162223509/10000000000 : ℝ)*X 0 1+(2266590081/5000000000 : ℝ)*X 0 2+(542986189/1250000000 : ℝ)*X 1 0+(4162223509/10000000000 : ℝ)*X 1 1+(2266590081/5000000000 : ℝ)*X 1 2+(542986189/1250000000 : ℝ)*X 2 0+(4162223509/10000000000 : ℝ)*X 2 1+(2266590081/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1276_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-262740371/1250000000 : ℝ)*X 0 0+(261963027/500000000 : ℝ)*X 0 1+(677438539/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1276_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652328457/5000000000 : ℝ)*X 1 0+(-503413131/2500000000 : ℝ)*X 1 1+(5419508403/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1276_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1060931361/2000000000 : ℝ)*X 2 0+(2709754129/5000000000 : ℝ)*X 2 1+(-251706609/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1276_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((542989959/1250000000 : ℝ)*X 0 0+(2265899697/5000000000 : ℝ)*X 0 1+(4163611659/10000000000 : ℝ)*X 0 2+(542989959/1250000000 : ℝ)*X 1 0+(2265899697/5000000000 : ℝ)*X 1 1+(4163611659/10000000000 : ℝ)*X 1 2+(542989959/1250000000 : ℝ)*X 2 0+(2265899697/5000000000 : ℝ)*X 2 1+(4163611659/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1276_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (82811071600756108625939799/23453125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (731484999/100000000000000 : ℝ)*(base19) + (136846283/20000000000000 : ℝ)*(base23) + (20880427/100000000000000 : ℝ)*(lower2) + (24245733/25000000000000 : ℝ)*(upper3) + (24925607/50000000000000 : ℝ)*(upper5) + (1025286701057811/25000000000000 : ℝ)*(major0) + (1025286701057811/25000000000000 : ℝ)*(major1) + (820229360846249/20000000000000 : ℝ)*(major2) + (550653280411277/10000000000000 : ℝ)*(sp0) + (344159107462241/6250000000000 : ℝ)*(sp1) + (34415911041559/625000000000 : ℝ)*(sp2) + (53914789547831/2000000000000 : ℝ)*(sp3) + (2729353617/20000000000000 : ℝ)*(sp4) + (1512498559/20000000000000 : ℝ)*(sp7) + (539149407976869/20000000000000 : ℝ)*(f.failure) + (1101309290176171/20000000000000 : ℝ)*(f.sum) + (239821226978713/45030000000000000000000000000 : ℝ)*base66 + (2537156621784733121/140718750000000000000000000000000 : ℝ)*base68 + (54790053497899583/14071875000000000000000000000000 : ℝ)*base70 + (1987282926265295621/140718750000000000000000000000000 : ℝ)*base72 + (115758221740933/45030000000000000000000000000 : ℝ)*base74 + (146442574599443333/14071875000000000000000000000000 : ℝ)*base76 + (35593547308723333/11726562500000000000000000000000 : ℝ)*base78 + (37517545087995417/11726562500000000000000000000000 : ℝ)*base79 + (13836011145641/7505000000000000000000000000 : ℝ)*base82 + (13301847/2000000000000000000000 : ℝ)*base89 + (13301847/2000000000000000000000 : ℝ)*base91 + (6698153/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (36897637471038028487400303/2931640625000000000000000000000 : ℝ) := by norm_num
    linear_combination (919274999/50000000000000 : ℝ)*(base19) + (1879784891/100000000000000 : ℝ)*(base23) + (16390507/10000000000000 : ℝ)*(upper3) + (26614177/20000000000000 : ℝ)*(lower4) + (40386649/12500000000000 : ℝ)*(upper5) + (1032990280320483/25000000000000 : ℝ)*(major0) + (1032990280320483/25000000000000 : ℝ)*(major1) + (1032990280320483/25000000000000 : ℝ)*(major2) + (40278159579/100000000000000 : ℝ)*(sp1) + (29346047587/100000000000000 : ℝ)*(sp2) + (5547920057348469/100000000000000 : ℝ)*(sp4) + (1386969485159723/25000000000000 : ℝ)*(sp5) + (5547888831515991/100000000000000 : ℝ)*(sp6) + (679000441420489/25000000000000 : ℝ)*(sp7) + (679000441420489/25000000000000 : ℝ)*(f.failure) + (5547920057348469/100000000000000 : ℝ)*(f.sum) + (236083949087/1876250000000000000000000000 : ℝ)*base66 + (124399667408799899/11726562500000000000000000000000 : ℝ)*base68 + (205943267904174899/11726562500000000000000000000000 : ℝ)*base70 + (94044531633799899/11726562500000000000000000000000 : ℝ)*base72 + (7942798833229/3752500000000000000000000000 : ℝ)*base74 + (108453446656240423/23453125000000000000000000000000 : ℝ)*base76 + (303359610171959173/23453125000000000000000000000000 : ℝ)*base78 + (6622756321890247/1465820312500000000000000000000 : ℝ)*base79 + (11137989003727/1876250000000000000000000000 : ℝ)*base82 + (40967907/2500000000000000000000 : ℝ)*base89 + (40967907/2500000000000000000000 : ℝ)*base91 + (40967907/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1276_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152133963/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (943/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2117/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2181/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3687/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1276_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1276_s5_0 (p : ℝ) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2102306031/10000000000 : ℝ)*x 0 + (5416808179/10000000000 : ℝ)*x 1 + (1310425811/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2102306031/10000000000 : ℝ)^1059 ≤ (6393495568703/50000000000000 : ℝ)^803 := by
    have hnat : (2102306031 : ℕ)^1059*50000000000000^803 ≤ 6393495568703^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2102306031 10000000000 6393495568703 50000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5416808179/10000000000 : ℝ)^1059 ≤ (44551227741399/100000000000000 : ℝ)^803 := by
    have hnat : (5416808179 : ℕ)^1059*100000000000000^803 ≤ 44551227741399^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416808179 10000000000 44551227741399 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310425811/2500000000 : ℝ)^1059 ≤ (21330890550301/50000000000000 : ℝ)^803 := by
    have hnat : (1310425811 : ℕ)^1059*50000000000000^803 ≤ 21330890550301^803*2500000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310425811 2500000000 21330890550301 50000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1059/256 : ℝ)) 1059 803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2102306031/10000000000 : ℝ), (5416808179/10000000000 : ℝ), (1310425811/2500000000 : ℝ)] ![(6393495568703/50000000000000 : ℝ), (44551227741399/100000000000000 : ℝ), (21330890550301/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2102306031/10000000000 : ℝ)|^1059 ≤ (6393495568703/50000000000000 : ℝ)^803
        have hw : |(-2102306031/10000000000 : ℝ)|=(2102306031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5416808179/10000000000 : ℝ)|^1059 ≤ (44551227741399/100000000000000 : ℝ)^803
        have hw : |(5416808179/10000000000 : ℝ)|=(5416808179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310425811/2500000000 : ℝ)|^1059 ≤ (21330890550301/50000000000000 : ℝ)^803
        have hw : |(1310425811/2500000000 : ℝ)|=(1310425811/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1276_s5_1 (p : ℝ) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5350203377/10000000000 : ℝ)*x 0 + (-2191593823/10000000000 : ℝ)*x 1 + (209668131/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350203377/10000000000 : ℝ)^1059 ≤ (43830207047181/100000000000000 : ℝ)^803 := by
    have hnat : (5350203377 : ℕ)^1059*100000000000000^803 ≤ 43830207047181^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350203377 10000000000 43830207047181 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2191593823/10000000000 : ℝ)^1059 ≤ (6754005751501/50000000000000 : ℝ)^803 := by
    have hnat : (2191593823 : ℕ)^1059*50000000000000^803 ≤ 6754005751501^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2191593823 10000000000 6754005751501 50000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (209668131/400000000 : ℝ)^1059 ≤ (8532356286669/20000000000000 : ℝ)^803 := by
    have hnat : (209668131 : ℕ)^1059*20000000000000^803 ≤ 8532356286669^803*400000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209668131 400000000 8532356286669 20000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1059/256 : ℝ)) 1059 803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350203377/10000000000 : ℝ), (-2191593823/10000000000 : ℝ), (209668131/400000000 : ℝ)] ![(43830207047181/100000000000000 : ℝ), (6754005751501/50000000000000 : ℝ), (8532356286669/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350203377/10000000000 : ℝ)|^1059 ≤ (43830207047181/100000000000000 : ℝ)^803
        have hw : |(5350203377/10000000000 : ℝ)|=(5350203377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2191593823/10000000000 : ℝ)|^1059 ≤ (6754005751501/50000000000000 : ℝ)^803
        have hw : |(-2191593823/10000000000 : ℝ)|=(2191593823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(209668131/400000000 : ℝ)|^1059 ≤ (8532356286669/20000000000000 : ℝ)^803
        have hw : |(209668131/400000000 : ℝ)|=(209668131/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1276_s5_2 (p : ℝ) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1070040691/2000000000 : ℝ)*x 0 + (2620851649/5000000000 : ℝ)*x 1 + (-219159369/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070040691/2000000000 : ℝ)^1059 ≤ (43830207889891/100000000000000 : ℝ)^803 := by
    have hnat : (1070040691 : ℕ)^1059*100000000000000^803 ≤ 43830207889891^803*2000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070040691 2000000000 43830207889891 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2620851649/5000000000 : ℝ)^1059 ≤ (42661781680219/100000000000000 : ℝ)^803 := by
    have hnat : (2620851649 : ℕ)^1059*100000000000000^803 ≤ 42661781680219^803*5000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620851649 5000000000 42661781680219 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (219159369/1000000000 : ℝ)^1059 ≤ (3377002605477/25000000000000 : ℝ)^803 := by
    have hnat : (219159369 : ℕ)^1059*25000000000000^803 ≤ 3377002605477^803*1000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219159369 1000000000 3377002605477 25000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1059/256 : ℝ)) 1059 803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070040691/2000000000 : ℝ), (2620851649/5000000000 : ℝ), (-219159369/1000000000 : ℝ)] ![(43830207889891/100000000000000 : ℝ), (42661781680219/100000000000000 : ℝ), (3377002605477/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070040691/2000000000 : ℝ)|^1059 ≤ (43830207889891/100000000000000 : ℝ)^803
        have hw : |(1070040691/2000000000 : ℝ)|=(1070040691/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2620851649/5000000000 : ℝ)|^1059 ≤ (42661781680219/100000000000000 : ℝ)^803
        have hw : |(2620851649/5000000000 : ℝ)|=(2620851649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-219159369/1000000000 : ℝ)|^1059 ≤ (3377002605477/25000000000000 : ℝ)^803
        have hw : |(-219159369/1000000000 : ℝ)|=(219159369/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1276_s5_3 (p : ℝ) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4344127671/10000000000 : ℝ)*x 0 + (1042207369/2500000000 : ℝ)*x 1 + (1131628359/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4344127671/10000000000 : ℝ)^1059 ≤ (8325384657601/25000000000000 : ℝ)^803 := by
    have hnat : (4344127671 : ℕ)^1059*25000000000000^803 ≤ 8325384657601^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4344127671 10000000000 8325384657601 25000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1042207369/2500000000 : ℝ)^1059 ≤ (3942602067001/12500000000000 : ℝ)^803 := by
    have hnat : (1042207369 : ℕ)^1059*12500000000000^803 ≤ 3942602067001^803*2500000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042207369 2500000000 3942602067001 12500000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1131628359/2500000000 : ℝ)^1059 ≤ (35157644821869/100000000000000 : ℝ)^803 := by
    have hnat : (1131628359 : ℕ)^1059*100000000000000^803 ≤ 35157644821869^803*2500000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1131628359 2500000000 35157644821869 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1059/256 : ℝ)) 1059 803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4344127671/10000000000 : ℝ), (1042207369/2500000000 : ℝ), (1131628359/2500000000 : ℝ)] ![(8325384657601/25000000000000 : ℝ), (3942602067001/12500000000000 : ℝ), (35157644821869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4344127671/10000000000 : ℝ)|^1059 ≤ (8325384657601/25000000000000 : ℝ)^803
        have hw : |(4344127671/10000000000 : ℝ)|=(4344127671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1042207369/2500000000 : ℝ)|^1059 ≤ (3942602067001/12500000000000 : ℝ)^803
        have hw : |(1042207369/2500000000 : ℝ)|=(1042207369/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1131628359/2500000000 : ℝ)|^1059 ≤ (35157644821869/100000000000000 : ℝ)^803
        have hw : |(1131628359/2500000000 : ℝ)|=(1131628359/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1276_s5_4 (p : ℝ) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1051159483/5000000000 : ℝ)*x 0 + (5242331677/10000000000 : ℝ)*x 1 + (2708088353/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051159483/5000000000 : ℝ)^1059 ≤ (2557418978991/20000000000000 : ℝ)^803 := by
    have hnat : (1051159483 : ℕ)^1059*20000000000000^803 ≤ 2557418978991^803*5000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051159483 5000000000 2557418978991 20000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242331677/10000000000 : ℝ)^1059 ≤ (10667131650551/25000000000000 : ℝ)^803 := by
    have hnat : (5242331677 : ℕ)^1059*25000000000000^803 ≤ 10667131650551^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242331677 10000000000 10667131650551 25000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2708088353/5000000000 : ℝ)^1059 ≤ (556804731077/1250000000000 : ℝ)^803 := by
    have hnat : (2708088353 : ℕ)^1059*1250000000000^803 ≤ 556804731077^803*5000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708088353 5000000000 556804731077 1250000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1059/256 : ℝ)) 1059 803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1051159483/5000000000 : ℝ), (5242331677/10000000000 : ℝ), (2708088353/5000000000 : ℝ)] ![(2557418978991/20000000000000 : ℝ), (10667131650551/25000000000000 : ℝ), (556804731077/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1051159483/5000000000 : ℝ)|^1059 ≤ (2557418978991/20000000000000 : ℝ)^803
        have hw : |(-1051159483/5000000000 : ℝ)|=(1051159483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242331677/10000000000 : ℝ)|^1059 ≤ (10667131650551/25000000000000 : ℝ)^803
        have hw : |(5242331677/10000000000 : ℝ)|=(5242331677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2708088353/5000000000 : ℝ)|^1059 ≤ (556804731077/1250000000000 : ℝ)^803
        have hw : |(2708088353/5000000000 : ℝ)|=(2708088353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1276_s5_5 (p : ℝ) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5305463797/10000000000 : ℝ)*x 0 + (-8068481/40000000 : ℝ)*x 1 + (1354044217/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305463797/10000000000 : ℝ)^1059 ≤ (21673743596183/50000000000000 : ℝ)^803 := by
    have hnat : (5305463797 : ℕ)^1059*50000000000000^803 ≤ 21673743596183^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305463797 10000000000 21673743596183 50000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8068481/40000000 : ℝ)^1059 ≤ (12108132553283/100000000000000 : ℝ)^803 := by
    have hnat : (8068481 : ℕ)^1059*100000000000000^803 ≤ 12108132553283^803*40000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8068481 40000000 12108132553283 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1354044217/2500000000 : ℝ)^1059 ≤ (5568047530407/12500000000000 : ℝ)^803 := by
    have hnat : (1354044217 : ℕ)^1059*12500000000000^803 ≤ 5568047530407^803*2500000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354044217 2500000000 5568047530407 12500000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1059/256 : ℝ)) 1059 803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305463797/10000000000 : ℝ), (-8068481/40000000 : ℝ), (1354044217/2500000000 : ℝ)] ![(21673743596183/50000000000000 : ℝ), (12108132553283/100000000000000 : ℝ), (5568047530407/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305463797/10000000000 : ℝ)|^1059 ≤ (21673743596183/50000000000000 : ℝ)^803
        have hw : |(5305463797/10000000000 : ℝ)|=(5305463797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-8068481/40000000 : ℝ)|^1059 ≤ (12108132553283/100000000000000 : ℝ)^803
        have hw : |(-8068481/40000000 : ℝ)|=(8068481/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1354044217/2500000000 : ℝ)|^1059 ≤ (5568047530407/12500000000000 : ℝ)^803
        have hw : |(1354044217/2500000000 : ℝ)|=(1354044217/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1276_s5_6 (p : ℝ) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5305464167/10000000000 : ℝ)*x 0 + (5416176511/10000000000 : ℝ)*x 1 + (-504280059/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305464167/10000000000 : ℝ)^1059 ≤ (866949823583/2000000000000 : ℝ)^803 := by
    have hnat : (5305464167 : ℕ)^1059*2000000000000^803 ≤ 866949823583^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305464167 10000000000 866949823583 2000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5416176511/10000000000 : ℝ)^1059 ≤ (44544376371137/100000000000000 : ℝ)^803 := by
    have hnat : (5416176511 : ℕ)^1059*100000000000000^803 ≤ 44544376371137^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416176511 10000000000 44544376371137 100000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (504280059/2500000000 : ℝ)^1059 ≤ (6054066221227/50000000000000 : ℝ)^803 := by
    have hnat : (504280059 : ℕ)^1059*50000000000000^803 ≤ 6054066221227^803*2500000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      504280059 2500000000 6054066221227 50000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1059/256 : ℝ)) 1059 803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305464167/10000000000 : ℝ), (5416176511/10000000000 : ℝ), (-504280059/2500000000 : ℝ)] ![(866949823583/2000000000000 : ℝ), (44544376371137/100000000000000 : ℝ), (6054066221227/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305464167/10000000000 : ℝ)|^1059 ≤ (866949823583/2000000000000 : ℝ)^803
        have hw : |(5305464167/10000000000 : ℝ)|=(5305464167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5416176511/10000000000 : ℝ)|^1059 ≤ (44544376371137/100000000000000 : ℝ)^803
        have hw : |(5416176511/10000000000 : ℝ)|=(5416176511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-504280059/2500000000 : ℝ)|^1059 ≤ (6054066221227/50000000000000 : ℝ)^803
        have hw : |(-504280059/2500000000 : ℝ)|=(504280059/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1276_s5_7 (p : ℝ) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4344154137/10000000000 : ℝ)*x 0 + (141413427/312500000 : ℝ)*x 1 + (834024089/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4344154137/10000000000 : ℝ)^1059 ≤ (6660361239273/20000000000000 : ℝ)^803 := by
    have hnat : (4344154137 : ℕ)^1059*20000000000000^803 ≤ 6660361239273^803*10000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4344154137 10000000000 6660361239273 20000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (141413427/312500000 : ℝ)^1059 ≤ (17572247730577/50000000000000 : ℝ)^803 := by
    have hnat : (141413427 : ℕ)^1059*50000000000000^803 ≤ 17572247730577^803*312500000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      141413427 312500000 17572247730577 50000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (834024089/2000000000 : ℝ)^1059 ≤ (7888424583361/25000000000000 : ℝ)^803 := by
    have hnat : (834024089 : ℕ)^1059*25000000000000^803 ≤ 7888424583361^803*2000000000^1059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      834024089 2000000000 7888424583361 25000000000000 1059 803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1059/256 : ℝ)) 1059 803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4344154137/10000000000 : ℝ), (141413427/312500000 : ℝ), (834024089/2000000000 : ℝ)] ![(6660361239273/20000000000000 : ℝ), (17572247730577/50000000000000 : ℝ), (7888424583361/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4344154137/10000000000 : ℝ)|^1059 ≤ (6660361239273/20000000000000 : ℝ)^803
        have hw : |(4344154137/10000000000 : ℝ)|=(4344154137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(141413427/312500000 : ℝ)|^1059 ≤ (17572247730577/50000000000000 : ℝ)^803
        have hw : |(141413427/312500000 : ℝ)|=(141413427/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(834024089/2000000000 : ℝ)|^1059 ≤ (7888424583361/25000000000000 : ℝ)^803
        have hw : |(834024089/2000000000 : ℝ)|=(834024089/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1276_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152133963/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3687/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2181/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (10971/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14677/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3687/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2181/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3687/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2181/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3687/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2181/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3687/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2181/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3687/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2181/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3687/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2181/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2181/20000 : ℝ) ^ (4235/1024 : ℝ) ≤ (261702512153923/2500000000000000000 : ℝ) := by
    have hpowers : (2181/20000 : ℝ)^4235 ≤ (261702512153923/2500000000000000000 : ℝ)^1024 := by
      have hnat : (2181 : ℕ)^4235*2500000000000000000^1024 ≤ 261702512153923^1024*20000^4235 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2181 20000 261702512153923 2500000000000000000 4235 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2181/20000 : ℝ)) (X := (261702512153923/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4235 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3687/25000 : ℝ) ^ (4235/1024 : ℝ) ≤ (7296667020789833/20000000000000000000 : ℝ) := by
    have hpowers : (3687/25000 : ℝ)^4235 ≤ (7296667020789833/20000000000000000000 : ℝ)^1024 := by
      have hnat : (3687 : ℕ)^4235*20000000000000000000^1024 ≤ 7296667020789833^1024*25000^4235 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3687 25000 7296667020789833 20000000000000000000 4235 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3687/25000 : ℝ)) (X := (7296667020789833/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4235 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1250261702512153923/1250000000000000000 : ℝ) ≤ (2500126546448781/2500000000000000 : ℝ) ^ (4235/1024 : ℝ) := by
    have hpowers : (1250261702512153923/1250000000000000000 : ℝ)^1024 ≤ (2500126546448781/2500000000000000 : ℝ)^4235 := by
      have hnat : (1250261702512153923 : ℕ)^1024*2500000000000000^4235 ≤ 2500126546448781^4235*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250261702512153923 1250000000000000000 2500126546448781 2500000000000000 1024 4235 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500126546448781/2500000000000000 : ℝ)) (X := (1250261702512153923/1250000000000000000 : ℝ)) (by norm_num) 4235 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009390287118021217/20000000000000000000 : ℝ) ≤ (10001135058199449/10000000000000000 : ℝ) ^ (4235/1024 : ℝ) := by
    have hpowers : (20009390287118021217/20000000000000000000 : ℝ)^1024 ≤ (10001135058199449/10000000000000000 : ℝ)^4235 := by
      have hnat : (20009390287118021217 : ℕ)^1024*10000000000000000^4235 ≤ 10001135058199449^4235*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009390287118021217 20000000000000000000 10001135058199449 10000000000000000 1024 4235 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001135058199449/10000000000000000 : ℝ)) (X := (20009390287118021217/20000000000000000000 : ℝ)) (by norm_num) 4235 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10007296667020789833/10000000000000000000 : ℝ) ≤ (5000881965301887/5000000000000000 : ℝ) ^ (4235/1024 : ℝ) := by
    have hpowers : (10007296667020789833/10000000000000000000 : ℝ)^1024 ≤ (5000881965301887/5000000000000000 : ℝ)^4235 := by
      have hnat : (10007296667020789833 : ℕ)^1024*5000000000000000^4235 ≤ 5000881965301887^4235*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10007296667020789833 10000000000000000000 5000881965301887 5000000000000000 1024 4235 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000881965301887/5000000000000000 : ℝ)) (X := (10007296667020789833/10000000000000000000 : ℝ)) (by norm_num) 4235 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(261702512153923/2500000000000000000 : ℝ) ≤ ((2134346086937351849/2135000000000000000 : ℝ)+2*(8384965391/5124000000000 : ℝ)*(2181/20000 : ℝ))^(4235/1024 : ℝ) := by
    rw [show (2134346086937351849/2135000000000000000 : ℝ)+2*(8384965391/5124000000000 : ℝ)*(2181/20000 : ℝ)=(2500126546448781/2500000000000000 : ℝ) by norm_num, show 1+2*(261702512153923/2500000000000000000 : ℝ)=(1250261702512153923/1250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7296667020789833/20000000000000000000 : ℝ)+(261702512153923/2500000000000000000 : ℝ) ≤ ((2134346086937351849/2135000000000000000 : ℝ)+(8384965391/5124000000000 : ℝ)*((3687/25000 : ℝ)+(2181/20000 : ℝ)))^(4235/1024 : ℝ) := by
    rw [show (2134346086937351849/2135000000000000000 : ℝ)+(8384965391/5124000000000 : ℝ)*((3687/25000 : ℝ)+(2181/20000 : ℝ))=(10001135058199449/10000000000000000 : ℝ) by norm_num, show 1+(7296667020789833/20000000000000000000 : ℝ)+(261702512153923/2500000000000000000 : ℝ)=(20009390287118021217/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7296667020789833/20000000000000000000 : ℝ) ≤ ((2134346086937351849/2135000000000000000 : ℝ)+2*(8384965391/5124000000000 : ℝ)*(3687/25000 : ℝ))^(4235/1024 : ℝ) := by
    rw [show (2134346086937351849/2135000000000000000 : ℝ)+2*(8384965391/5124000000000 : ℝ)*(3687/25000 : ℝ)=(5000881965301887/5000000000000000 : ℝ) by norm_num, show 1+2*(7296667020789833/20000000000000000000 : ℝ)=(10007296667020789833/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2134346086937351849/2135000000000000000 : ℝ)*(X 1 0+X 2 0)+(8384965391/5124000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4235/1024 : ℝ)) (lo := (2181/20000 : ℝ)) (hi := (3687/25000 : ℝ)) (c := (2134346086937351849/2135000000000000000 : ℝ)) (alpha := (8384965391/5124000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2134346086937351849/2135000000000000000 : ℝ)*(X 0 1+X 2 1)+(8384965391/5124000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4235/1024 : ℝ)) (lo := (2181/20000 : ℝ)) (hi := (3687/25000 : ℝ)) (c := (2134346086937351849/2135000000000000000 : ℝ)) (alpha := (8384965391/5124000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2134346086937351849/2135000000000000000 : ℝ)*(X 0 2+X 1 2)+(8384965391/5124000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4235/1024 : ℝ)) (lo := (2181/20000 : ℝ)) (hi := (3687/25000 : ℝ)) (c := (2134346086937351849/2135000000000000000 : ℝ)) (alpha := (8384965391/5124000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2102306031/10000000000 : ℝ)*X 0 0+(5416808179/10000000000 : ℝ)*X 0 1+(1310425811/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1276_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350203377/10000000000 : ℝ)*X 1 0+(-2191593823/10000000000 : ℝ)*X 1 1+(209668131/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1276_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1070040691/2000000000 : ℝ)*X 2 0+(2620851649/5000000000 : ℝ)*X 2 1+(-219159369/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1276_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4344127671/10000000000 : ℝ)*X 0 0+(1042207369/2500000000 : ℝ)*X 0 1+(1131628359/2500000000 : ℝ)*X 0 2+(4344127671/10000000000 : ℝ)*X 1 0+(1042207369/2500000000 : ℝ)*X 1 1+(1131628359/2500000000 : ℝ)*X 1 2+(4344127671/10000000000 : ℝ)*X 2 0+(1042207369/2500000000 : ℝ)*X 2 1+(1131628359/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1276_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1051159483/5000000000 : ℝ)*X 0 0+(5242331677/10000000000 : ℝ)*X 0 1+(2708088353/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1276_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305463797/10000000000 : ℝ)*X 1 0+(-8068481/40000000 : ℝ)*X 1 1+(1354044217/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1276_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305464167/10000000000 : ℝ)*X 2 0+(5416176511/10000000000 : ℝ)*X 2 1+(-504280059/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1276_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4344154137/10000000000 : ℝ)*X 0 0+(141413427/312500000 : ℝ)*X 0 1+(834024089/2000000000 : ℝ)*X 0 2+(4344154137/10000000000 : ℝ)*X 1 0+(141413427/312500000 : ℝ)*X 1 1+(834024089/2000000000 : ℝ)*X 1 2+(4344154137/10000000000 : ℝ)*X 2 0+(141413427/312500000 : ℝ)*X 2 1+(834024089/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1276_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10970070393521273968222319/1334375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (234778523/12500000000000 : ℝ)*(base19) + (45922313/2500000000000 : ℝ)*(base23) + (66660643/100000000000000 : ℝ)*(lower2) + (288015351/100000000000000 : ℝ)*(upper3) + (91836789/25000000000000 : ℝ)*(upper5) + (2126682611967081/50000000000000 : ℝ)*(major0) + (2126682611967081/50000000000000 : ℝ)*(major1) + (1063341305983541/25000000000000 : ℝ)*(major2) + (5710891888591303/100000000000000 : ℝ)*(sp0) + (1142185148204969/20000000000000 : ℝ)*(sp1) + (571092578236051/10000000000000 : ℝ)*(sp2) + (2795783468054441/100000000000000 : ℝ)*(sp3) + (17865330863/50000000000000 : ℝ)*(sp4) + (9543261587/50000000000000 : ℝ)*(sp7) + (559160510915523/20000000000000 : ℝ)*(f.failure) + (571092761925303/10000000000000 : ℝ)*(f.sum) + (444224322863/51240000000000000000000000 : ℝ)*base66 + (1225465070132801693/320250000000000000000000000000000 : ℝ)*base68 + (989564617788292309/53375000000000000000000000000000 : ℝ)*base69 + (4332694257273551693/320250000000000000000000000000000 : ℝ)*base72 + (1193861941/40031250000000000000000000 : ℝ)*base74 + (346896211069667309/53375000000000000000000000000000 : ℝ)*base75 + (138157201634931033/15250000000000000000000000000000 : ℝ)*base78 + (397892588288181033/15250000000000000000000000000000 : ℝ)*base80 + (5788692293/7625000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (32207649/2000000000000000000000 : ℝ)*base89 + (32207649/2000000000000000000000 : ℝ)*base91 + (7792351/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (106902256710839520051303673/13343750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (525109581/50000000000000 : ℝ)*(base19) + (1616583487/100000000000000 : ℝ)*(base23) + (53992411/50000000000000 : ℝ)*(upper3) + (38813607/50000000000000 : ℝ)*(lower4) + (213454181/100000000000000 : ℝ)*(upper5) + (535518092023759/12500000000000 : ℝ)*(major0) + (535518092023759/12500000000000 : ℝ)*(major1) + (535518092023759/12500000000000 : ℝ)*(major2) + (1069740321/4000000000000 : ℝ)*(sp1) + (2898376301/10000000000000 : ℝ)*(sp2) + (719031850335781/12500000000000 : ℝ)*(sp4) + (5752227008959061/100000000000000 : ℝ)*(sp5) + (23008896809359/400000000000 : ℝ)*(sp6) + (1408017201323439/50000000000000 : ℝ)*(sp7) + (1408017201323439/50000000000000 : ℝ)*(f.failure) + (719031850335781/12500000000000 : ℝ)*(f.sum) + (1332128551499/640500000000000000000000000 : ℝ)*base66 + (113771083472501261/11437500000000000000000000000000 : ℝ)*base68 + (21080358630626261/11437500000000000000000000000000 : ℝ)*base70 + (2214082630001261/11437500000000000000000000000000 : ℝ)*base72 + (8097643517167/1281000000000000000000000000 : ℝ)*base74 + (157579415099688761/11437500000000000000000000000000 : ℝ)*base76 + (52506088325373739/11437500000000000000000000000000 : ℝ)*base77 + (108387012519873739/11437500000000000000000000000000 : ℝ)*base79 + (123063212777/25620000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (19858757/5000000000000000000000 : ℝ)*base89 + (19858757/5000000000000000000000 : ℝ)*base91 + (19858757/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1276_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152133963/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3687/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2181/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10971/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14677/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1276_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1276_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152133963/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16393/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1877/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10971/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14677/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1276_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1276_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1276_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4235/1024 : ℝ) ≤ p) (hpb : p ≤ (1059/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152133963/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16393/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1877/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10971/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14677/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1276_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
