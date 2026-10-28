-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1102_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:01:38.787894+00:00
-- url     : https://prove2.me/submissions/e3ab64e8-cbf1-4730-967d-65e93e8ebc92

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
theorem support_rectangle_w1102_box_0 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2057930743/10000000000 : ℝ)*x 0 + (2688437453/5000000000 : ℝ)*x 1 + (1344218739/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2057930743/10000000000 : ℝ)^8295 ≤ (3063992611293/25000000000000 : ℝ)^6247 := by
    have hnat : (2057930743 : ℕ)^8295*25000000000000^6247 ≤ 3063992611293^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2057930743 10000000000 3063992611293 25000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2688437453/5000000000 : ℝ)^8295 ≤ (43872014500631/100000000000000 : ℝ)^6247 := by
    have hnat : (2688437453 : ℕ)^8295*100000000000000^6247 ≤ 43872014500631^6247*5000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688437453 5000000000 43872014500631 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1344218739/2500000000 : ℝ)^8295 ≤ (10968003760587/25000000000000 : ℝ)^6247 := by
    have hnat : (1344218739 : ℕ)^8295*25000000000000^6247 ≤ 10968003760587^6247*2500000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344218739 2500000000 10968003760587 25000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2057930743/10000000000 : ℝ), (2688437453/5000000000 : ℝ), (1344218739/2500000000 : ℝ)] ![(3063992611293/25000000000000 : ℝ), (43872014500631/100000000000000 : ℝ), (10968003760587/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2057930743/10000000000 : ℝ)|^8295 ≤ (3063992611293/25000000000000 : ℝ)^6247
        have hw : |(-2057930743/10000000000 : ℝ)|=(2057930743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2688437453/5000000000 : ℝ)|^8295 ≤ (43872014500631/100000000000000 : ℝ)^6247
        have hw : |(2688437453/5000000000 : ℝ)|=(2688437453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1344218739/2500000000 : ℝ)|^8295 ≤ (10968003760587/25000000000000 : ℝ)^6247
        have hw : |(1344218739/2500000000 : ℝ)|=(1344218739/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_box_1 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (661948979/1250000000 : ℝ)*x 0 + (-1084031027/5000000000 : ℝ)*x 1 + (2688437479/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661948979/1250000000 : ℝ)^8295 ≤ (4299355557497/10000000000000 : ℝ)^6247 := by
    have hnat : (661948979 : ℕ)^8295*10000000000000^6247 ≤ 4299355557497^6247*1250000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661948979 1250000000 4299355557497 10000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1084031027/5000000000 : ℝ)^8295 ≤ (6567214673989/50000000000000 : ℝ)^6247 := by
    have hnat : (1084031027 : ℕ)^8295*50000000000000^6247 ≤ 6567214673989^6247*5000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084031027 5000000000 6567214673989 50000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2688437479/5000000000 : ℝ)^8295 ≤ (2742000941501/6250000000000 : ℝ)^6247 := by
    have hnat : (2688437479 : ℕ)^8295*6250000000000^6247 ≤ 2742000941501^6247*5000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688437479 5000000000 2742000941501 6250000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661948979/1250000000 : ℝ), (-1084031027/5000000000 : ℝ), (2688437479/5000000000 : ℝ)] ![(4299355557497/10000000000000 : ℝ), (6567214673989/50000000000000 : ℝ), (2742000941501/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661948979/1250000000 : ℝ)|^8295 ≤ (4299355557497/10000000000000 : ℝ)^6247
        have hw : |(661948979/1250000000 : ℝ)|=(661948979/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1084031027/5000000000 : ℝ)|^8295 ≤ (6567214673989/50000000000000 : ℝ)^6247
        have hw : |(-1084031027/5000000000 : ℝ)|=(1084031027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2688437479/5000000000 : ℝ)|^8295 ≤ (2742000941501/6250000000000 : ℝ)^6247
        have hw : |(2688437479/5000000000 : ℝ)|=(2688437479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_box_2 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5295591571/10000000000 : ℝ)*x 0 + (5376874933/10000000000 : ℝ)*x 1 + (-2168062437/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295591571/10000000000 : ℝ)^8295 ≤ (42993552761293/100000000000000 : ℝ)^6247 := by
    have hnat : (5295591571 : ℕ)^8295*100000000000000^6247 ≤ 42993552761293^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295591571 10000000000 42993552761293 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5376874933/10000000000 : ℝ)^8295 ≤ (21936007396579/50000000000000 : ℝ)^6247 := by
    have hnat : (5376874933 : ℕ)^8295*50000000000000^6247 ≤ 21936007396579^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376874933 10000000000 21936007396579 50000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2168062437/10000000000 : ℝ)^8295 ≤ (6567216214459/50000000000000 : ℝ)^6247 := by
    have hnat : (2168062437 : ℕ)^8295*50000000000000^6247 ≤ 6567216214459^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2168062437 10000000000 6567216214459 50000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295591571/10000000000 : ℝ), (5376874933/10000000000 : ℝ), (-2168062437/10000000000 : ℝ)] ![(42993552761293/100000000000000 : ℝ), (21936007396579/50000000000000 : ℝ), (6567216214459/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295591571/10000000000 : ℝ)|^8295 ≤ (42993552761293/100000000000000 : ℝ)^6247
        have hw : |(5295591571/10000000000 : ℝ)|=(5295591571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5376874933/10000000000 : ℝ)|^8295 ≤ (21936007396579/50000000000000 : ℝ)^6247
        have hw : |(5376874933/10000000000 : ℝ)|=(5376874933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2168062437/10000000000 : ℝ)|^8295 ≤ (6567216214459/50000000000000 : ℝ)^6247
        have hw : |(-2168062437/10000000000 : ℝ)|=(2168062437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_box_3 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4478324691/10000000000 : ℝ)*x 0 + (539810707/1250000000 : ℝ)*x 1 + (2159242971/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4478324691/10000000000 : ℝ)^8295 ≤ (34414243669529/100000000000000 : ℝ)^6247 := by
    have hnat : (4478324691 : ℕ)^8295*100000000000000^6247 ≤ 34414243669529^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4478324691 10000000000 34414243669529 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539810707/1250000000 : ℝ)^8295 ≤ (32792876715381/100000000000000 : ℝ)^6247 := by
    have hnat : (539810707 : ℕ)^8295*100000000000000^6247 ≤ 32792876715381^6247*1250000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539810707 1250000000 32792876715381 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2159242971/5000000000 : ℝ)^8295 ≤ (1639643979957/5000000000000 : ℝ)^6247 := by
    have hnat : (2159242971 : ℕ)^8295*5000000000000^6247 ≤ 1639643979957^6247*5000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2159242971 5000000000 1639643979957 5000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4478324691/10000000000 : ℝ), (539810707/1250000000 : ℝ), (2159242971/5000000000 : ℝ)] ![(34414243669529/100000000000000 : ℝ), (32792876715381/100000000000000 : ℝ), (1639643979957/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4478324691/10000000000 : ℝ)|^8295 ≤ (34414243669529/100000000000000 : ℝ)^6247
        have hw : |(4478324691/10000000000 : ℝ)|=(4478324691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539810707/1250000000 : ℝ)|^8295 ≤ (32792876715381/100000000000000 : ℝ)^6247
        have hw : |(539810707/1250000000 : ℝ)|=(539810707/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2159242971/5000000000 : ℝ)|^8295 ≤ (1639643979957/5000000000000 : ℝ)^6247
        have hw : |(2159242971/5000000000 : ℝ)|=(2159242971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_box_4 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1157892149/5000000000 : ℝ)*x 0 + (5280607391/10000000000 : ℝ)*x 1 + (1320151823/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1157892149/5000000000 : ℝ)^8295 ≤ (7167907824949/50000000000000 : ℝ)^6247 := by
    have hnat : (1157892149 : ℕ)^8295*50000000000000^6247 ≤ 7167907824949^6247*5000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1157892149 5000000000 7167907824949 50000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5280607391/10000000000 : ℝ)^8295 ≤ (8566418540217/20000000000000 : ℝ)^6247 := by
    have hnat : (5280607391 : ℕ)^8295*20000000000000^6247 ≤ 8566418540217^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280607391 10000000000 8566418540217 20000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1320151823/2500000000 : ℝ)^8295 ≤ (42832091634819/100000000000000 : ℝ)^6247 := by
    have hnat : (1320151823 : ℕ)^8295*100000000000000^6247 ≤ 42832091634819^6247*2500000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320151823 2500000000 42832091634819 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1157892149/5000000000 : ℝ), (5280607391/10000000000 : ℝ), (1320151823/2500000000 : ℝ)] ![(7167907824949/50000000000000 : ℝ), (8566418540217/20000000000000 : ℝ), (42832091634819/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1157892149/5000000000 : ℝ)|^8295 ≤ (7167907824949/50000000000000 : ℝ)^6247
        have hw : |(-1157892149/5000000000 : ℝ)|=(1157892149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5280607391/10000000000 : ℝ)|^8295 ≤ (8566418540217/20000000000000 : ℝ)^6247
        have hw : |(5280607391/10000000000 : ℝ)|=(5280607391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1320151823/2500000000 : ℝ)|^8295 ≤ (42832091634819/100000000000000 : ℝ)^6247
        have hw : |(1320151823/2500000000 : ℝ)|=(1320151823/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_box_5 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5363665907/10000000000 : ℝ)*x 0 + (-110290481/500000000 : ℝ)*x 1 + (2640303849/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5363665907/10000000000 : ℝ)^8295 ≤ (43728961352703/100000000000000 : ℝ)^6247 := by
    have hnat : (5363665907 : ℕ)^8295*100000000000000^6247 ≤ 43728961352703^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363665907 10000000000 43728961352703 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (110290481/500000000 : ℝ)^8295 ≤ (6719471314579/50000000000000 : ℝ)^6247 := by
    have hnat : (110290481 : ℕ)^8295*50000000000000^6247 ≤ 6719471314579^6247*500000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110290481 500000000 6719471314579 50000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2640303849/5000000000 : ℝ)^8295 ≤ (21416048003793/50000000000000 : ℝ)^6247 := by
    have hnat : (2640303849 : ℕ)^8295*50000000000000^6247 ≤ 21416048003793^6247*5000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640303849 5000000000 21416048003793 50000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5363665907/10000000000 : ℝ), (-110290481/500000000 : ℝ), (2640303849/5000000000 : ℝ)] ![(43728961352703/100000000000000 : ℝ), (6719471314579/50000000000000 : ℝ), (21416048003793/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5363665907/10000000000 : ℝ)|^8295 ≤ (43728961352703/100000000000000 : ℝ)^6247
        have hw : |(5363665907/10000000000 : ℝ)|=(5363665907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-110290481/500000000 : ℝ)|^8295 ≤ (6719471314579/50000000000000 : ℝ)^6247
        have hw : |(-110290481/500000000 : ℝ)|=(110290481/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2640303849/5000000000 : ℝ)|^8295 ≤ (21416048003793/50000000000000 : ℝ)^6247
        have hw : |(2640303849/5000000000 : ℝ)|=(2640303849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_box_6 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1072733321/2000000000 : ℝ)*x 0 + (5280606851/10000000000 : ℝ)*x 1 + (-2205809813/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072733321/2000000000 : ℝ)^8295 ≤ (43728968908979/100000000000000 : ℝ)^6247 := by
    have hnat : (1072733321 : ℕ)^8295*100000000000000^6247 ≤ 43728968908979^6247*2000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072733321 2000000000 43728968908979 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5280606851/10000000000 : ℝ)^8295 ≤ (4283208688509/10000000000000 : ℝ)^6247 := by
    have hnat : (5280606851 : ℕ)^8295*10000000000000^6247 ≤ 4283208688509^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280606851 10000000000 4283208688509 10000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2205809813/10000000000 : ℝ)^8295 ≤ (1679868023813/12500000000000 : ℝ)^6247 := by
    have hnat : (2205809813 : ℕ)^8295*12500000000000^6247 ≤ 1679868023813^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2205809813 10000000000 1679868023813 12500000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1072733321/2000000000 : ℝ), (5280606851/10000000000 : ℝ), (-2205809813/10000000000 : ℝ)] ![(43728968908979/100000000000000 : ℝ), (4283208688509/10000000000000 : ℝ), (1679868023813/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1072733321/2000000000 : ℝ)|^8295 ≤ (43728968908979/100000000000000 : ℝ)^6247
        have hw : |(1072733321/2000000000 : ℝ)|=(1072733321/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5280606851/10000000000 : ℝ)|^8295 ≤ (4283208688509/10000000000000 : ℝ)^6247
        have hw : |(5280606851/10000000000 : ℝ)|=(5280606851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2205809813/10000000000 : ℝ)|^8295 ≤ (1679868023813/12500000000000 : ℝ)^6247
        have hw : |(-2205809813/10000000000 : ℝ)|=(2205809813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_box_7 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1065503489/2500000000 : ℝ)*x 0 + (553327501/1250000000 : ℝ)*x 1 + (4426620009/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1065503489/2500000000 : ℝ)^8295 ≤ (8056173141533/25000000000000 : ℝ)^6247 := by
    have hnat : (1065503489 : ℕ)^8295*25000000000000^6247 ≤ 8056173141533^6247*2500000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065503489 2500000000 8056173141533 25000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (553327501/1250000000 : ℝ)^8295 ≤ (529494589087/1562500000000 : ℝ)^6247 := by
    have hnat : (553327501 : ℕ)^8295*1562500000000^6247 ≤ 529494589087^6247*1250000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      553327501 1250000000 529494589087 1562500000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4426620009/10000000000 : ℝ)^8295 ≤ (33887653711733/100000000000000 : ℝ)^6247 := by
    have hnat : (4426620009 : ℕ)^8295*100000000000000^6247 ≤ 33887653711733^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4426620009 10000000000 33887653711733 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1065503489/2500000000 : ℝ), (553327501/1250000000 : ℝ), (4426620009/10000000000 : ℝ)] ![(8056173141533/25000000000000 : ℝ), (529494589087/1562500000000 : ℝ), (33887653711733/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1065503489/2500000000 : ℝ)|^8295 ≤ (8056173141533/25000000000000 : ℝ)^6247
        have hw : |(1065503489/2500000000 : ℝ)|=(1065503489/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(553327501/1250000000 : ℝ)|^8295 ≤ (529494589087/1562500000000 : ℝ)^6247
        have hw : |(553327501/1250000000 : ℝ)|=(553327501/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4426620009/10000000000 : ℝ)|^8295 ≤ (33887653711733/100000000000000 : ℝ)^6247
        have hw : |(4426620009/10000000000 : ℝ)|=(4426620009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_box_8 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2261910491/10000000000 : ℝ)*x 0 + (521521377/1000000000 : ℝ)*x 1 + (2693240161/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2261910491/10000000000 : ℝ)^8295 ≤ (13894673236561/100000000000000 : ℝ)^6247 := by
    have hnat : (2261910491 : ℕ)^8295*100000000000000^6247 ≤ 13894673236561^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2261910491 10000000000 13894673236561 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (521521377/1000000000 : ℝ)^8295 ≤ (8425842684577/20000000000000 : ℝ)^6247 := by
    have hnat : (521521377 : ℕ)^8295*20000000000000^6247 ≤ 8425842684577^6247*1000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521521377 1000000000 8425842684577 20000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2693240161/5000000000 : ℝ)^8295 ≤ (43976113321811/100000000000000 : ℝ)^6247 := by
    have hnat : (2693240161 : ℕ)^8295*100000000000000^6247 ≤ 43976113321811^6247*5000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693240161 5000000000 43976113321811 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2261910491/10000000000 : ℝ), (521521377/1000000000 : ℝ), (2693240161/5000000000 : ℝ)] ![(13894673236561/100000000000000 : ℝ), (8425842684577/20000000000000 : ℝ), (43976113321811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2261910491/10000000000 : ℝ)|^8295 ≤ (13894673236561/100000000000000 : ℝ)^6247
        have hw : |(-2261910491/10000000000 : ℝ)|=(2261910491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(521521377/1000000000 : ℝ)|^8295 ≤ (8425842684577/20000000000000 : ℝ)^6247
        have hw : |(521521377/1000000000 : ℝ)|=(521521377/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2693240161/5000000000 : ℝ)|^8295 ≤ (43976113321811/100000000000000 : ℝ)^6247
        have hw : |(2693240161/5000000000 : ℝ)|=(2693240161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_box_9 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5288795747/10000000000 : ℝ)*x 0 + (-2164226129/10000000000 : ℝ)*x 1 + (5386480207/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288795747/10000000000 : ℝ)^8295 ≤ (21460153333909/50000000000000 : ℝ)^6247 := by
    have hnat : (5288795747 : ℕ)^8295*50000000000000^6247 ≤ 21460153333909^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288795747 10000000000 21460153333909 50000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2164226129/10000000000 : ℝ)^8295 ≤ (13103581244431/100000000000000 : ℝ)^6247 := by
    have hnat : (2164226129 : ℕ)^8295*100000000000000^6247 ≤ 13103581244431^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2164226129 10000000000 13103581244431 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5386480207/10000000000 : ℝ)^8295 ≤ (10994028018783/25000000000000 : ℝ)^6247 := by
    have hnat : (5386480207 : ℕ)^8295*25000000000000^6247 ≤ 10994028018783^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386480207 10000000000 10994028018783 25000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288795747/10000000000 : ℝ), (-2164226129/10000000000 : ℝ), (5386480207/10000000000 : ℝ)] ![(21460153333909/50000000000000 : ℝ), (13103581244431/100000000000000 : ℝ), (10994028018783/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288795747/10000000000 : ℝ)|^8295 ≤ (21460153333909/50000000000000 : ℝ)^6247
        have hw : |(5288795747/10000000000 : ℝ)|=(5288795747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2164226129/10000000000 : ℝ)|^8295 ≤ (13103581244431/100000000000000 : ℝ)^6247
        have hw : |(-2164226129/10000000000 : ℝ)|=(2164226129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5386480207/10000000000 : ℝ)|^8295 ≤ (10994028018783/25000000000000 : ℝ)^6247
        have hw : |(5386480207/10000000000 : ℝ)|=(5386480207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_box_10 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5288795863/10000000000 : ℝ)*x 0 + (5386480297/10000000000 : ℝ)*x 1 + (-2164225853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288795863/10000000000 : ℝ)^8295 ≤ (8584061583563/20000000000000 : ℝ)^6247 := by
    have hnat : (5288795863 : ℕ)^8295*20000000000000^6247 ≤ 8584061583563^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288795863 10000000000 8584061583563 20000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5386480297/10000000000 : ℝ)^8295 ≤ (21988056525397/50000000000000 : ℝ)^6247 := by
    have hnat : (5386480297 : ℕ)^8295*50000000000000^6247 ≤ 21988056525397^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386480297 10000000000 21988056525397 50000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2164225853/10000000000 : ℝ)^8295 ≤ (13103579025513/100000000000000 : ℝ)^6247 := by
    have hnat : (2164225853 : ℕ)^8295*100000000000000^6247 ≤ 13103579025513^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2164225853 10000000000 13103579025513 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288795863/10000000000 : ℝ), (5386480297/10000000000 : ℝ), (-2164225853/10000000000 : ℝ)] ![(8584061583563/20000000000000 : ℝ), (21988056525397/50000000000000 : ℝ), (13103579025513/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288795863/10000000000 : ℝ)|^8295 ≤ (8584061583563/20000000000000 : ℝ)^6247
        have hw : |(5288795863/10000000000 : ℝ)|=(5288795863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5386480297/10000000000 : ℝ)|^8295 ≤ (21988056525397/50000000000000 : ℝ)^6247
        have hw : |(5386480297/10000000000 : ℝ)|=(5386480297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2164225853/10000000000 : ℝ)|^8295 ≤ (13103579025513/100000000000000 : ℝ)^6247
        have hw : |(-2164225853/10000000000 : ℝ)|=(2164225853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_box_11 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (70306791/156250000 : ℝ)*x 0 + (4307690179/10000000000 : ℝ)*x 1 + (1076922601/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (70306791/156250000 : ℝ)^8295 ≤ (8657964548417/25000000000000 : ℝ)^6247 := by
    have hnat : (70306791 : ℕ)^8295*25000000000000^6247 ≤ 8657964548417^6247*156250000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70306791 156250000 8657964548417 25000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4307690179/10000000000 : ℝ)^8295 ≤ (32684069759731/100000000000000 : ℝ)^6247 := by
    have hnat : (4307690179 : ℕ)^8295*100000000000000^6247 ≤ 32684069759731^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4307690179 10000000000 32684069759731 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1076922601/2500000000 : ℝ)^8295 ≤ (16342036013281/50000000000000 : ℝ)^6247 := by
    have hnat : (1076922601 : ℕ)^8295*50000000000000^6247 ≤ 16342036013281^6247*2500000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076922601 2500000000 16342036013281 50000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(70306791/156250000 : ℝ), (4307690179/10000000000 : ℝ), (1076922601/2500000000 : ℝ)] ![(8657964548417/25000000000000 : ℝ), (32684069759731/100000000000000 : ℝ), (16342036013281/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(70306791/156250000 : ℝ)|^8295 ≤ (8657964548417/25000000000000 : ℝ)^6247
        have hw : |(70306791/156250000 : ℝ)|=(70306791/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4307690179/10000000000 : ℝ)|^8295 ≤ (32684069759731/100000000000000 : ℝ)^6247
        have hw : |(4307690179/10000000000 : ℝ)|=(4307690179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1076922601/2500000000 : ℝ)|^8295 ≤ (16342036013281/50000000000000 : ℝ)^6247
        have hw : |(1076922601/2500000000 : ℝ)|=(1076922601/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_box_12 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-264018637/1250000000 : ℝ)*x 0 + (340060053/625000000 : ℝ)*x 1 + (2636293809/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (264018637/1250000000 : ℝ)^8295 ≤ (507462609039/4000000000000 : ℝ)^6247 := by
    have hnat : (264018637 : ℕ)^8295*4000000000000^6247 ≤ 507462609039^6247*1250000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264018637 1250000000 507462609039 4000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (340060053/625000000 : ℝ)^8295 ≤ (8913539282179/20000000000000 : ℝ)^6247 := by
    have hnat : (340060053 : ℕ)^8295*20000000000000^6247 ≤ 8913539282179^6247*625000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340060053 625000000 8913539282179 20000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2636293809/5000000000 : ℝ)^8295 ≤ (8549147670669/20000000000000 : ℝ)^6247 := by
    have hnat : (2636293809 : ℕ)^8295*20000000000000^6247 ≤ 8549147670669^6247*5000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636293809 5000000000 8549147670669 20000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-264018637/1250000000 : ℝ), (340060053/625000000 : ℝ), (2636293809/5000000000 : ℝ)] ![(507462609039/4000000000000 : ℝ), (8913539282179/20000000000000 : ℝ), (8549147670669/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-264018637/1250000000 : ℝ)|^8295 ≤ (507462609039/4000000000000 : ℝ)^6247
        have hw : |(-264018637/1250000000 : ℝ)|=(264018637/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(340060053/625000000 : ℝ)|^8295 ≤ (8913539282179/20000000000000 : ℝ)^6247
        have hw : |(340060053/625000000 : ℝ)|=(340060053/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2636293809/5000000000 : ℝ)|^8295 ≤ (8549147670669/20000000000000 : ℝ)^6247
        have hw : |(2636293809/5000000000 : ℝ)|=(2636293809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_box_13 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1073867043/2000000000 : ℝ)*x 0 + (-220889581/1000000000 : ℝ)*x 1 + (2636293841/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073867043/2000000000 : ℝ)^8295 ≤ (43790345694163/100000000000000 : ℝ)^6247 := by
    have hnat : (1073867043 : ℕ)^8295*100000000000000^6247 ≤ 43790345694163^6247*2000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073867043 2000000000 43790345694163 100000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (220889581/1000000000 : ℝ)^8295 ≤ (3365978813269/25000000000000 : ℝ)^6247 := by
    have hnat : (220889581 : ℕ)^8295*25000000000000^6247 ≤ 3365978813269^6247*1000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220889581 1000000000 3365978813269 25000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2636293841/5000000000 : ℝ)^8295 ≤ (8549147808461/20000000000000 : ℝ)^6247 := by
    have hnat : (2636293841 : ℕ)^8295*20000000000000^6247 ≤ 8549147808461^6247*5000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636293841 5000000000 8549147808461 20000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073867043/2000000000 : ℝ), (-220889581/1000000000 : ℝ), (2636293841/5000000000 : ℝ)] ![(43790345694163/100000000000000 : ℝ), (3365978813269/25000000000000 : ℝ), (8549147808461/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073867043/2000000000 : ℝ)|^8295 ≤ (43790345694163/100000000000000 : ℝ)^6247
        have hw : |(1073867043/2000000000 : ℝ)|=(1073867043/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-220889581/1000000000 : ℝ)|^8295 ≤ (3365978813269/25000000000000 : ℝ)^6247
        have hw : |(-220889581/1000000000 : ℝ)|=(220889581/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2636293841/5000000000 : ℝ)|^8295 ≤ (8549147808461/20000000000000 : ℝ)^6247
        have hw : |(2636293841/5000000000 : ℝ)|=(2636293841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_box_14 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5369335089/10000000000 : ℝ)*x 0 + (2636293673/5000000000 : ℝ)*x 1 + (-88355857/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369335089/10000000000 : ℝ)^8295 ≤ (684224130151/1562500000000 : ℝ)^6247 := by
    have hnat : (5369335089 : ℕ)^8295*1562500000000^6247 ≤ 684224130151^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369335089 10000000000 684224130151 1562500000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2636293673/5000000000 : ℝ)^8295 ≤ (21372867712633/50000000000000 : ℝ)^6247 := by
    have hnat : (2636293673 : ℕ)^8295*50000000000000^6247 ≤ 21372867712633^6247*5000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636293673 5000000000 21372867712633 50000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (88355857/400000000 : ℝ)^8295 ≤ (1682990028829/12500000000000 : ℝ)^6247 := by
    have hnat : (88355857 : ℕ)^8295*12500000000000^6247 ≤ 1682990028829^6247*400000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88355857 400000000 1682990028829 12500000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369335089/10000000000 : ℝ), (2636293673/5000000000 : ℝ), (-88355857/400000000 : ℝ)] ![(684224130151/1562500000000 : ℝ), (21372867712633/50000000000000 : ℝ), (1682990028829/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369335089/10000000000 : ℝ)|^8295 ≤ (684224130151/1562500000000 : ℝ)^6247
        have hw : |(5369335089/10000000000 : ℝ)|=(5369335089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2636293673/5000000000 : ℝ)|^8295 ≤ (21372867712633/50000000000000 : ℝ)^6247
        have hw : |(2636293673/5000000000 : ℝ)|=(2636293673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-88355857/400000000 : ℝ)|^8295 ≤ (1682990028829/12500000000000 : ℝ)^6247
        have hw : |(-88355857/400000000 : ℝ)|=(88355857/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1102_box_15 (p : ℝ) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4243762437/10000000000 : ℝ)*x 0 + (4435623871/10000000000 : ℝ)*x 1 + (4435623659/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4243762437/10000000000 : ℝ)^8295 ≤ (6408316471561/20000000000000 : ℝ)^6247 := by
    have hnat : (4243762437 : ℕ)^8295*20000000000000^6247 ≤ 6408316471561^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4243762437 10000000000 6408316471561 20000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4435623871/10000000000 : ℝ)^8295 ≤ (8494802473889/25000000000000 : ℝ)^6247 := by
    have hnat : (4435623871 : ℕ)^8295*25000000000000^6247 ≤ 8494802473889^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4435623871 10000000000 8494802473889 25000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4435623659/10000000000 : ℝ)^8295 ≤ (16989603869553/50000000000000 : ℝ)^6247 := by
    have hnat : (4435623659 : ℕ)^8295*50000000000000^6247 ≤ 16989603869553^6247*10000000000^8295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4435623659 10000000000 16989603869553 50000000000000 8295 6247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8295/2048 : ℝ)) 8295 6247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4243762437/10000000000 : ℝ), (4435623871/10000000000 : ℝ), (4435623659/10000000000 : ℝ)] ![(6408316471561/20000000000000 : ℝ), (8494802473889/25000000000000 : ℝ), (16989603869553/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4243762437/10000000000 : ℝ)|^8295 ≤ (6408316471561/20000000000000 : ℝ)^6247
        have hw : |(4243762437/10000000000 : ℝ)|=(4243762437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4435623871/10000000000 : ℝ)|^8295 ≤ (8494802473889/25000000000000 : ℝ)^6247
        have hw : |(4435623871/10000000000 : ℝ)|=(4435623871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4435623659/10000000000 : ℝ)|^8295 ≤ (16989603869553/50000000000000 : ℝ)^6247
        have hw : |(4435623659/10000000000 : ℝ)|=(4435623659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1102_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148693861/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (561/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11301/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62227/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(14817/25000 : ℝ) ∧ (15937/20000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (41517/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (561/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11301/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (561/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11301/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (561/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11301/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (561/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11301/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (561/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11301/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (561/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11301/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11301/100000 : ℝ) ^ (4147/1024 : ℝ) ≤ (1829019326682201/12500000000000000000 : ℝ) := by
    have hpowers : (11301/100000 : ℝ)^4147 ≤ (1829019326682201/12500000000000000000 : ℝ)^1024 := by
      have hnat : (11301 : ℕ)^4147*12500000000000000000^1024 ≤ 1829019326682201^1024*100000^4147 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11301 100000 1829019326682201 12500000000000000000 4147 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11301/100000 : ℝ)) (X := (1829019326682201/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4147 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (561/4000 : ℝ) ^ (4147/1024 : ℝ) ≤ (3508514241646697/10000000000000000000 : ℝ) := by
    have hpowers : (561/4000 : ℝ)^4147 ≤ (3508514241646697/10000000000000000000 : ℝ)^1024 := by
      have hnat : (561 : ℕ)^4147*10000000000000000000^1024 ≤ 3508514241646697^1024*4000^4147 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        561 4000 3508514241646697 10000000000000000000 4147 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (561/4000 : ℝ)) (X := (3508514241646697/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4147 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251829019326682201/6250000000000000000 : ℝ) ≤ (1000072253077301/1000000000000000 : ℝ) ^ (4147/1024 : ℝ) := by
    have hpowers : (6251829019326682201/6250000000000000000 : ℝ)^1024 ≤ (1000072253077301/1000000000000000 : ℝ)^4147 := by
      have hnat : (6251829019326682201 : ℕ)^1024*1000000000000000^4147 ≤ 1000072253077301^4147*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251829019326682201 6250000000000000000 1000072253077301 1000000000000000 1024 4147 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000072253077301/1000000000000000 : ℝ)) (X := (6251829019326682201/6250000000000000000 : ℝ)) (by norm_num) 4147 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024858648514962289/50000000000000000000 : ℝ) ≤ (1000122741703081/1000000000000000 : ℝ) ^ (4147/1024 : ℝ) := by
    have hpowers : (50024858648514962289/50000000000000000000 : ℝ)^1024 ≤ (1000122741703081/1000000000000000 : ℝ)^4147 := by
      have hnat : (50024858648514962289 : ℕ)^1024*1000000000000000^4147 ≤ 1000122741703081^4147*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024858648514962289 50000000000000000000 1000122741703081 1000000000000000 1024 4147 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000122741703081/1000000000000000 : ℝ)) (X := (50024858648514962289/50000000000000000000 : ℝ)) (by norm_num) 4147 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003508514241646697/5000000000000000000 : ℝ) ≤ (1000173230328861/1000000000000000 : ℝ) ^ (4147/1024 : ℝ) := by
    have hpowers : (5003508514241646697/5000000000000000000 : ℝ)^1024 ≤ (1000173230328861/1000000000000000 : ℝ)^4147 := by
      have hnat : (5003508514241646697 : ℕ)^1024*1000000000000000^4147 ≤ 1000173230328861^4147*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003508514241646697 5000000000000000000 1000173230328861 1000000000000000 1024 4147 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000173230328861/1000000000000000 : ℝ)) (X := (5003508514241646697/5000000000000000000 : ℝ)) (by norm_num) 4147 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1829019326682201/12500000000000000000 : ℝ) ≤ ((226921306121890697/227000000000000000 : ℝ)+2*(2524431289/1362000000000 : ℝ)*(11301/100000 : ℝ))^(4147/1024 : ℝ) := by
    rw [show (226921306121890697/227000000000000000 : ℝ)+2*(2524431289/1362000000000 : ℝ)*(11301/100000 : ℝ)=(1000072253077301/1000000000000000 : ℝ) by norm_num, show 1+2*(1829019326682201/12500000000000000000 : ℝ)=(6251829019326682201/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3508514241646697/10000000000000000000 : ℝ)+(1829019326682201/12500000000000000000 : ℝ) ≤ ((226921306121890697/227000000000000000 : ℝ)+(2524431289/1362000000000 : ℝ)*((561/4000 : ℝ)+(11301/100000 : ℝ)))^(4147/1024 : ℝ) := by
    rw [show (226921306121890697/227000000000000000 : ℝ)+(2524431289/1362000000000 : ℝ)*((561/4000 : ℝ)+(11301/100000 : ℝ))=(1000122741703081/1000000000000000 : ℝ) by norm_num, show 1+(3508514241646697/10000000000000000000 : ℝ)+(1829019326682201/12500000000000000000 : ℝ)=(50024858648514962289/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3508514241646697/10000000000000000000 : ℝ) ≤ ((226921306121890697/227000000000000000 : ℝ)+2*(2524431289/1362000000000 : ℝ)*(561/4000 : ℝ))^(4147/1024 : ℝ) := by
    rw [show (226921306121890697/227000000000000000 : ℝ)+2*(2524431289/1362000000000 : ℝ)*(561/4000 : ℝ)=(1000173230328861/1000000000000000 : ℝ) by norm_num, show 1+2*(3508514241646697/10000000000000000000 : ℝ)=(5003508514241646697/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (226921306121890697/227000000000000000 : ℝ)*(X 1 0+X 2 0)+(2524431289/1362000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4147/1024 : ℝ)) (lo := (11301/100000 : ℝ)) (hi := (561/4000 : ℝ)) (c := (226921306121890697/227000000000000000 : ℝ)) (alpha := (2524431289/1362000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (226921306121890697/227000000000000000 : ℝ)*(X 0 1+X 2 1)+(2524431289/1362000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4147/1024 : ℝ)) (lo := (11301/100000 : ℝ)) (hi := (561/4000 : ℝ)) (c := (226921306121890697/227000000000000000 : ℝ)) (alpha := (2524431289/1362000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (226921306121890697/227000000000000000 : ℝ)*(X 0 2+X 1 2)+(2524431289/1362000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4147/1024 : ℝ)) (lo := (11301/100000 : ℝ)) (hi := (561/4000 : ℝ)) (c := (226921306121890697/227000000000000000 : ℝ)) (alpha := (2524431289/1362000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2057930743/10000000000 : ℝ)*X 0 0+(2688437453/5000000000 : ℝ)*X 0 1+(1344218739/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((661948979/1250000000 : ℝ)*X 1 0+(-1084031027/5000000000 : ℝ)*X 1 1+(2688437479/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5295591571/10000000000 : ℝ)*X 2 0+(5376874933/10000000000 : ℝ)*X 2 1+(-2168062437/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4478324691/10000000000 : ℝ)*X 0 0+(539810707/1250000000 : ℝ)*X 0 1+(2159242971/5000000000 : ℝ)*X 0 2+(4478324691/10000000000 : ℝ)*X 1 0+(539810707/1250000000 : ℝ)*X 1 1+(2159242971/5000000000 : ℝ)*X 1 2+(4478324691/10000000000 : ℝ)*X 2 0+(539810707/1250000000 : ℝ)*X 2 1+(2159242971/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1157892149/5000000000 : ℝ)*X 0 0+(5280607391/10000000000 : ℝ)*X 0 1+(1320151823/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5363665907/10000000000 : ℝ)*X 1 0+(-110290481/500000000 : ℝ)*X 1 1+(2640303849/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1072733321/2000000000 : ℝ)*X 2 0+(5280606851/10000000000 : ℝ)*X 2 1+(-2205809813/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1065503489/2500000000 : ℝ)*X 0 0+(553327501/1250000000 : ℝ)*X 0 1+(4426620009/10000000000 : ℝ)*X 0 2+(1065503489/2500000000 : ℝ)*X 1 0+(553327501/1250000000 : ℝ)*X 1 1+(4426620009/10000000000 : ℝ)*X 1 2+(1065503489/2500000000 : ℝ)*X 2 0+(553327501/1250000000 : ℝ)*X 2 1+(4426620009/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2261910491/10000000000 : ℝ)*X 0 0+(521521377/1000000000 : ℝ)*X 0 1+(2693240161/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5288795747/10000000000 : ℝ)*X 1 0+(-2164226129/10000000000 : ℝ)*X 1 1+(5386480207/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5288795863/10000000000 : ℝ)*X 2 0+(5386480297/10000000000 : ℝ)*X 2 1+(-2164225853/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((70306791/156250000 : ℝ)*X 0 0+(4307690179/10000000000 : ℝ)*X 0 1+(1076922601/2500000000 : ℝ)*X 0 2+(70306791/156250000 : ℝ)*X 1 0+(4307690179/10000000000 : ℝ)*X 1 1+(1076922601/2500000000 : ℝ)*X 1 2+(70306791/156250000 : ℝ)*X 2 0+(4307690179/10000000000 : ℝ)*X 2 1+(1076922601/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-264018637/1250000000 : ℝ)*X 0 0+(340060053/625000000 : ℝ)*X 0 1+(2636293809/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1073867043/2000000000 : ℝ)*X 1 0+(-220889581/1000000000 : ℝ)*X 1 1+(2636293841/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5369335089/10000000000 : ℝ)*X 2 0+(2636293673/5000000000 : ℝ)*X 2 1+(-88355857/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4243762437/10000000000 : ℝ)*X 0 0+(4435623871/10000000000 : ℝ)*X 0 1+(4435623659/10000000000 : ℝ)*X 0 2+(4243762437/10000000000 : ℝ)*X 1 0+(4435623871/10000000000 : ℝ)*X 1 1+(4435623659/10000000000 : ℝ)*X 1 2+(4243762437/10000000000 : ℝ)*X 2 0+(4435623871/10000000000 : ℝ)*X 2 1+(4435623659/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1102_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62227/100000 : ℝ) ≤ (-3531244590705236035393965581607/5675000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9684993/20000000000000 : ℝ)*(lower1) + (26568587/25000000000000 : ℝ)*(lower2) + (6726711/50000000000000 : ℝ)*(lower4) + (1943425802611677/50000000000000 : ℝ)*(major0) + (1943425802611677/50000000000000 : ℝ)*(major1) + (1943425802611677/50000000000000 : ℝ)*(major2) + (266189937/1000000000000 : ℝ)*(sp2) + (5180445125597561/100000000000000 : ℝ)*(sp4) + (5180294262062879/100000000000000 : ℝ)*(sp5) + (2590211049217417/50000000000000 : ℝ)*(sp6) + (130696629256137/5000000000000 : ℝ)*(sp7) + (1795915487/50000000000000 : ℝ)*(sp8) + (19306920707/12500000000000 : ℝ)*(sp13) + (63432657277/100000000000000 : ℝ)*(sp15) + (1306998008890009/50000000000000 : ℝ)*(f.failure) + (2590224358714267/50000000000000 : ℝ)*(f.sum) + (206146307541/227000000000000000000000000 : ℝ)*base65 + (66636941973931131/11350000000000000000000000000000 : ℝ)*base68 + (12597357442681131/11350000000000000000000000000000 : ℝ)*base70 + (74913683379668869/11350000000000000000000000000000 : ℝ)*base71 + (595808657751/227000000000000000000000000 : ℝ)*base73 + (21863699900418869/11350000000000000000000000000000 : ℝ)*base75 + (96800126990718869/11350000000000000000000000000000 : ℝ)*base77 + (58361918917018869/11350000000000000000000000000000 : ℝ)*base79 + (192631444227/227000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (62534749/5000000000000000000000 : ℝ)*base89 + (62534749/5000000000000000000000 : ℝ)*base91 + (62534749/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (14817/25000 : ℝ) ≤ (1681793931006485893445232211607/2837500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3852597/100000000000000 : ℝ)*(lower0) + (2756329/2000000000000 : ℝ)*(upper2) + (45333643/50000000000000 : ℝ)*(lower4) + (69167919/100000000000000 : ℝ)*(lower5) + (1975182451266677/50000000000000 : ℝ)*(major0) + (1975182451266677/50000000000000 : ℝ)*(major1) + (1975182451266677/50000000000000 : ℝ)*(major2) + (653031312749513/12500000000000 : ℝ)*(sp0) + (5224249361003231/100000000000000 : ℝ)*(sp1) + (2612131447429747/50000000000000 : ℝ)*(sp2) + (332088018094491/12500000000000 : ℝ)*(sp3) + (1691732033/12500000000000 : ℝ)*(sp5) + (3004276261/50000000000000 : ℝ)*(sp7) + (1239286339/10000000000000 : ℝ)*(sp12) + (53134203066169/2000000000000 : ℝ)*(f.failure) + (2612131447429747/50000000000000 : ℝ)*(f.sum) + (250775341937/170250000000000000000000000 : ℝ)*base66 + (198511587982688393/34050000000000000000000000000000 : ℝ)*base68 + (364709754774188393/34050000000000000000000000000000 : ℝ)*base70 + (495092741372288393/34050000000000000000000000000000 : ℝ)*base72 + (101546556307/68100000000000000000000000 : ℝ)*base73 + (519236592714488393/34050000000000000000000000000000 : ℝ)*base76 + (249637338349988393/34050000000000000000000000000000 : ℝ)*base78 + (14786364297411607/34050000000000000000000000000000 : ℝ)*base79 + (347791948223/85125000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (911491/200000000000000000000 : ℝ)*base90 + (911491/200000000000000000000 : ℝ)*base92 + (911491/200000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (15937/20000 : ℝ) ≤ (4522253222578888592810441219337/5675000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14345571/25000000000000 : ℝ)*(upper0) + (19981989/100000000000000 : ℝ)*(lower1) + (56410613/50000000000000 : ℝ)*(lower3) + (134728767/100000000000000 : ℝ)*(upper4) + (2209235051086707/50000000000000 : ℝ)*(major0) + (2209235051086707/50000000000000 : ℝ)*(major1) + (2209235051086707/50000000000000 : ℝ)*(major2) + (13374140733/50000000000000 : ℝ)*(sp1) + (2506770279/2000000000000 : ℝ)*(sp2) + (46430522547/50000000000000 : ℝ)*(sp3) + (5838856241296987/100000000000000 : ℝ)*(sp8) + (36492684331347/625000000000 : ℝ)*(sp9) + (5838730902783037/100000000000000 : ℝ)*(sp10) + (118857146994121/4000000000000 : ℝ)*(sp11) + (1485760767949059/50000000000000 : ℝ)*(f.failure) + (5838856241296987/100000000000000 : ℝ)*(f.sum) + (492829017879/227000000000000000000000000 : ℝ)*base66 + (40861373319985221/11350000000000000000000000000000 : ℝ)*base68 + (61883915199535221/11350000000000000000000000000000 : ℝ)*base70 + (53132419331064779/11350000000000000000000000000000 : ℝ)*base71 + (32860061469/45400000000000000000000000 : ℝ)*base74 + (16869748067564779/11350000000000000000000000000000 : ℝ)*base75 + (23939894468085221/11350000000000000000000000000000 : ℝ)*base78 + (32124442381135221/11350000000000000000000000000000 : ℝ)*base80 + (1279480719879/227000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (65973201/5000000000000000000000 : ℝ)*base90 + (65973201/5000000000000000000000 : ℝ)*base92 + (65973201/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-41517/50000 : ℝ) ≤ (-942412378480924911712267240099/1135000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (59806589/25000000000000 : ℝ)*(lower0) + (5475981/20000000000000 : ℝ)*(upper3) + (372573171/100000000000000 : ℝ)*(lower4) + (445320300590911/10000000000000 : ℝ)*(major0) + (445320300590911/10000000000000 : ℝ)*(major1) + (445320300590911/10000000000000 : ℝ)*(major2) + (16120553993/100000000000000 : ℝ)*(sp0) + (196366156607/100000000000000 : ℝ)*(sp5) + (45103024263/6250000000000 : ℝ)*(sp6) + (86044844227/50000000000000 : ℝ)*(sp7) + (5939186997643021/100000000000000 : ℝ)*(sp12) + (742375844005051/12500000000000 : ℝ)*(sp13) + (5938481469808807/100000000000000 : ℝ)*(sp14) + (2994708113139227/100000000000000 : ℝ)*(sp15) + (2994880202827681/100000000000000 : ℝ)*(f.failure) + (1187840623639403/20000000000000 : ℝ)*(f.sum) + (59656929013/170250000000000000000000000 : ℝ)*base65 + (69858303590314901/6810000000000000000000000000000 : ℝ)*base67 + (18042755928814901/6810000000000000000000000000000 : ℝ)*base69 + (32742032700055099/6810000000000000000000000000000 : ℝ)*base72 + (35889174442651/681000000000000000000000000 : ℝ)*base73 + (47800421348545099/6810000000000000000000000000000 : ℝ)*base76 + (15755559553195099/6810000000000000000000000000000 : ℝ)*base78 + (201034832482525099/6810000000000000000000000000000 : ℝ)*base80 + (15820819123/6810000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (5566341/10000000000000000000000 : ℝ)*base89 + (5566341/10000000000000000000000 : ℝ)*base91 + (5566341/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1102_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148693861/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (561/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11301/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62227/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14817/25000 : ℝ) else (15937/20000 : ℝ) ≤ X j i ∧ X j i ≤ (41517/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1102_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1102_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148693861/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (561/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11301/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62227/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14817/25000 : ℝ) else (15937/20000 : ℝ) ≤ X j i ∧ X j i ≤ (41517/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1102_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4147/1024 : ℝ) ≤ p) (hpb : p ≤ (8295/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148693861/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (561/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11301/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62227/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14817/25000 : ℝ) else (15937/20000 : ℝ) ≤ X j i ∧ X j i ≤ (41517/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1102_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
