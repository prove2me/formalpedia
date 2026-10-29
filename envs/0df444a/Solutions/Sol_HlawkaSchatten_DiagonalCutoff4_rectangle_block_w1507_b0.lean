-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1507_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:54:18.532529+00:00
-- url     : https://prove2.me/submissions/2bd489ee-a559-441f-a1a1-5a82675d262b

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
theorem support_rectangle_w1507_s0_0 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-338229967/2000000000 : ℝ)*x 0 + (5916688583/10000000000 : ℝ)*x 1 + (1213293183/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (338229967/2000000000 : ℝ)^4511 ≤ (5017626911561/50000000000000 : ℝ)^3487 := by
    have hnat : (338229967 : ℕ)^4511*50000000000000^3487 ≤ 5017626911561^3487*2000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338229967 2000000000 5017626911561 50000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5916688583/10000000000 : ℝ)^4511 ≤ (50716216871857/100000000000000 : ℝ)^3487 := by
    have hnat : (5916688583 : ℕ)^4511*100000000000000^3487 ≤ 50716216871857^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5916688583 10000000000 50716216871857 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1213293183/2500000000 : ℝ)^4511 ≤ (39248529296101/100000000000000 : ℝ)^3487 := by
    have hnat : (1213293183 : ℕ)^4511*100000000000000^3487 ≤ 39248529296101^3487*2500000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1213293183 2500000000 39248529296101 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-338229967/2000000000 : ℝ), (5916688583/10000000000 : ℝ), (1213293183/2500000000 : ℝ)] ![(5017626911561/50000000000000 : ℝ), (50716216871857/100000000000000 : ℝ), (39248529296101/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-338229967/2000000000 : ℝ)|^4511 ≤ (5017626911561/50000000000000 : ℝ)^3487
        have hw : |(-338229967/2000000000 : ℝ)|=(338229967/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5916688583/10000000000 : ℝ)|^4511 ≤ (50716216871857/100000000000000 : ℝ)^3487
        have hw : |(5916688583/10000000000 : ℝ)|=(5916688583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1213293183/2500000000 : ℝ)|^4511 ≤ (39248529296101/100000000000000 : ℝ)^3487
        have hw : |(1213293183/2500000000 : ℝ)|=(1213293183/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_s0_1 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2739534501/5000000000 : ℝ)*x 0 + (-1143827917/5000000000 : ℝ)*x 1 + (2426586341/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2739534501/5000000000 : ℝ)^4511 ≤ (11479285057791/25000000000000 : ℝ)^3487 := by
    have hnat : (2739534501 : ℕ)^4511*25000000000000^3487 ≤ 11479285057791^3487*5000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2739534501 5000000000 11479285057791 25000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1143827917/5000000000 : ℝ)^4511 ≤ (14834330973537/100000000000000 : ℝ)^3487 := by
    have hnat : (1143827917 : ℕ)^4511*100000000000000^3487 ≤ 14834330973537^3487*5000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1143827917 5000000000 14834330973537 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2426586341/5000000000 : ℝ)^4511 ≤ (9812132193249/25000000000000 : ℝ)^3487 := by
    have hnat : (2426586341 : ℕ)^4511*25000000000000^3487 ≤ 9812132193249^3487*5000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2426586341 5000000000 9812132193249 25000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2739534501/5000000000 : ℝ), (-1143827917/5000000000 : ℝ), (2426586341/5000000000 : ℝ)] ![(11479285057791/25000000000000 : ℝ), (14834330973537/100000000000000 : ℝ), (9812132193249/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2739534501/5000000000 : ℝ)|^4511 ≤ (11479285057791/25000000000000 : ℝ)^3487
        have hw : |(2739534501/5000000000 : ℝ)|=(2739534501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1143827917/5000000000 : ℝ)|^4511 ≤ (14834330973537/100000000000000 : ℝ)^3487
        have hw : |(-1143827917/5000000000 : ℝ)|=(1143827917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2426586341/5000000000 : ℝ)|^4511 ≤ (9812132193249/25000000000000 : ℝ)^3487
        have hw : |(2426586341/5000000000 : ℝ)|=(2426586341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_s0_2 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2739534521/5000000000 : ℝ)*x 0 + (485317269/1000000000 : ℝ)*x 1 + (-2287655773/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2739534521/5000000000 : ℝ)^4511 ≤ (45917140664823/100000000000000 : ℝ)^3487 := by
    have hnat : (2739534521 : ℕ)^4511*100000000000000^3487 ≤ 45917140664823^3487*5000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2739534521 5000000000 45917140664823 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (485317269/1000000000 : ℝ)^4511 ≤ (39248528856693/100000000000000 : ℝ)^3487 := by
    have hnat : (485317269 : ℕ)^4511*100000000000000^3487 ≤ 39248528856693^3487*1000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      485317269 1000000000 39248528856693 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2287655773/10000000000 : ℝ)^4511 ≤ (7417165230911/50000000000000 : ℝ)^3487 := by
    have hnat : (2287655773 : ℕ)^4511*50000000000000^3487 ≤ 7417165230911^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2287655773 10000000000 7417165230911 50000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2739534521/5000000000 : ℝ), (485317269/1000000000 : ℝ), (-2287655773/10000000000 : ℝ)] ![(45917140664823/100000000000000 : ℝ), (39248528856693/100000000000000 : ℝ), (7417165230911/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2739534521/5000000000 : ℝ)|^4511 ≤ (45917140664823/100000000000000 : ℝ)^3487
        have hw : |(2739534521/5000000000 : ℝ)|=(2739534521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(485317269/1000000000 : ℝ)|^4511 ≤ (39248528856693/100000000000000 : ℝ)^3487
        have hw : |(485317269/1000000000 : ℝ)|=(485317269/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2287655773/10000000000 : ℝ)|^4511 ≤ (7417165230911/50000000000000 : ℝ)^3487
        have hw : |(-2287655773/10000000000 : ℝ)|=(2287655773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_s0_3 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (829298929/2000000000 : ℝ)*x 0 + (1545619933/5000000000 : ℝ)*x 1 + (2747179259/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (829298929/2000000000 : ℝ)^4511 ≤ (32019055150851/100000000000000 : ℝ)^3487 := by
    have hnat : (829298929 : ℕ)^4511*100000000000000^3487 ≤ 32019055150851^3487*2000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      829298929 2000000000 32019055150851 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1545619933/5000000000 : ℝ)^4511 ≤ (10948987802513/50000000000000 : ℝ)^3487 := by
    have hnat : (1545619933 : ℕ)^4511*50000000000000^3487 ≤ 10948987802513^3487*5000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1545619933 5000000000 10948987802513 50000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2747179259/5000000000 : ℝ)^4511 ≤ (4608296922771/10000000000000 : ℝ)^3487 := by
    have hnat : (2747179259 : ℕ)^4511*10000000000000^3487 ≤ 4608296922771^3487*5000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2747179259 5000000000 4608296922771 10000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(829298929/2000000000 : ℝ), (1545619933/5000000000 : ℝ), (2747179259/5000000000 : ℝ)] ![(32019055150851/100000000000000 : ℝ), (10948987802513/50000000000000 : ℝ), (4608296922771/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(829298929/2000000000 : ℝ)|^4511 ≤ (32019055150851/100000000000000 : ℝ)^3487
        have hw : |(829298929/2000000000 : ℝ)|=(829298929/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1545619933/5000000000 : ℝ)|^4511 ≤ (10948987802513/50000000000000 : ℝ)^3487
        have hw : |(1545619933/5000000000 : ℝ)|=(1545619933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2747179259/5000000000 : ℝ)|^4511 ≤ (4608296922771/10000000000000 : ℝ)^3487
        have hw : |(2747179259/5000000000 : ℝ)|=(2747179259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_s0_4 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-847356601/5000000000 : ℝ)*x 0 + (1220081449/2500000000 : ℝ)*x 1 + (5888562137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (847356601/5000000000 : ℝ)^4511 ≤ (5031308357157/50000000000000 : ℝ)^3487 := by
    have hnat : (847356601 : ℕ)^4511*50000000000000^3487 ≤ 5031308357157^3487*5000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      847356601 5000000000 5031308357157 50000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1220081449/2500000000 : ℝ)^4511 ≤ (7906568040871/20000000000000 : ℝ)^3487 := by
    have hnat : (1220081449 : ℕ)^4511*20000000000000^3487 ≤ 7906568040871^3487*2500000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1220081449 2500000000 7906568040871 20000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5888562137/10000000000 : ℝ)^4511 ≤ (25202271536303/50000000000000 : ℝ)^3487 := by
    have hnat : (5888562137 : ℕ)^4511*50000000000000^3487 ≤ 25202271536303^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5888562137 10000000000 25202271536303 50000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-847356601/5000000000 : ℝ), (1220081449/2500000000 : ℝ), (5888562137/10000000000 : ℝ)] ![(5031308357157/50000000000000 : ℝ), (7906568040871/20000000000000 : ℝ), (25202271536303/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-847356601/5000000000 : ℝ)|^4511 ≤ (5031308357157/50000000000000 : ℝ)^3487
        have hw : |(-847356601/5000000000 : ℝ)|=(847356601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1220081449/2500000000 : ℝ)|^4511 ≤ (7906568040871/20000000000000 : ℝ)^3487
        have hw : |(1220081449/2500000000 : ℝ)|=(1220081449/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5888562137/10000000000 : ℝ)|^4511 ≤ (25202271536303/50000000000000 : ℝ)^3487
        have hw : |(5888562137/10000000000 : ℝ)|=(5888562137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_s0_5 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2594264017/5000000000 : ℝ)*x 0 + (-626133171/5000000000 : ℝ)*x 1 + (1177712437/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2594264017/5000000000 : ℝ)^4511 ≤ (8558416426101/20000000000000 : ℝ)^3487 := by
    have hnat : (2594264017 : ℕ)^4511*20000000000000^3487 ≤ 8558416426101^3487*5000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2594264017 5000000000 8558416426101 20000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (626133171/5000000000 : ℝ)^4511 ≤ (3401687123583/50000000000000 : ℝ)^3487 := by
    have hnat : (626133171 : ℕ)^4511*50000000000000^3487 ≤ 3401687123583^3487*5000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      626133171 5000000000 3401687123583 50000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1177712437/2000000000 : ℝ)^4511 ≤ (5040454360413/10000000000000 : ℝ)^3487 := by
    have hnat : (1177712437 : ℕ)^4511*10000000000000^3487 ≤ 5040454360413^3487*2000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1177712437 2000000000 5040454360413 10000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2594264017/5000000000 : ℝ), (-626133171/5000000000 : ℝ), (1177712437/2000000000 : ℝ)] ![(8558416426101/20000000000000 : ℝ), (3401687123583/50000000000000 : ℝ), (5040454360413/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2594264017/5000000000 : ℝ)|^4511 ≤ (8558416426101/20000000000000 : ℝ)^3487
        have hw : |(2594264017/5000000000 : ℝ)|=(2594264017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-626133171/5000000000 : ℝ)|^4511 ≤ (3401687123583/50000000000000 : ℝ)^3487
        have hw : |(-626133171/5000000000 : ℝ)|=(626133171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1177712437/2000000000 : ℝ)|^4511 ≤ (5040454360413/10000000000000 : ℝ)^3487
        have hw : |(1177712437/2000000000 : ℝ)|=(1177712437/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_s0_6 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5188528031/10000000000 : ℝ)*x 0 + (588856219/1000000000 : ℝ)*x 1 + (-62613317/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5188528031/10000000000 : ℝ)^4511 ≤ (42792082098497/100000000000000 : ℝ)^3487 := by
    have hnat : (5188528031 : ℕ)^4511*100000000000000^3487 ≤ 42792082098497^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5188528031 10000000000 42792082098497 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (588856219/1000000000 : ℝ)^4511 ≤ (50404543659497/100000000000000 : ℝ)^3487 := by
    have hnat : (588856219 : ℕ)^4511*100000000000000^3487 ≤ 50404543659497^3487*1000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      588856219 1000000000 50404543659497 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (62613317/500000000 : ℝ)^4511 ≤ (6803374233109/100000000000000 : ℝ)^3487 := by
    have hnat : (62613317 : ℕ)^4511*100000000000000^3487 ≤ 6803374233109^3487*500000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62613317 500000000 6803374233109 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5188528031/10000000000 : ℝ), (588856219/1000000000 : ℝ), (-62613317/500000000 : ℝ)] ![(42792082098497/100000000000000 : ℝ), (50404543659497/100000000000000 : ℝ), (6803374233109/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5188528031/10000000000 : ℝ)|^4511 ≤ (42792082098497/100000000000000 : ℝ)^3487
        have hw : |(5188528031/10000000000 : ℝ)|=(5188528031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(588856219/1000000000 : ℝ)|^4511 ≤ (50404543659497/100000000000000 : ℝ)^3487
        have hw : |(588856219/1000000000 : ℝ)|=(588856219/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-62613317/500000000 : ℝ)|^4511 ≤ (6803374233109/100000000000000 : ℝ)^3487
        have hw : |(-62613317/500000000 : ℝ)|=(62613317/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_s0_7 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4154546481/10000000000 : ℝ)*x 0 + (2716501693/5000000000 : ℝ)*x 1 + (157739723/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4154546481/10000000000 : ℝ)^4511 ≤ (8024878182293/25000000000000 : ℝ)^3487 := by
    have hnat : (4154546481 : ℕ)^4511*25000000000000^3487 ≤ 8024878182293^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4154546481 10000000000 8024878182293 25000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2716501693/5000000000 : ℝ)^4511 ≤ (45418338106981/100000000000000 : ℝ)^3487 := by
    have hnat : (2716501693 : ℕ)^4511*100000000000000^3487 ≤ 45418338106981^3487*5000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716501693 5000000000 45418338106981 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (157739723/500000000 : ℝ)^4511 ≤ (22482149149327/100000000000000 : ℝ)^3487 := by
    have hnat : (157739723 : ℕ)^4511*100000000000000^3487 ≤ 22482149149327^3487*500000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      157739723 500000000 22482149149327 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4154546481/10000000000 : ℝ), (2716501693/5000000000 : ℝ), (157739723/500000000 : ℝ)] ![(8024878182293/25000000000000 : ℝ), (45418338106981/100000000000000 : ℝ), (22482149149327/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4154546481/10000000000 : ℝ)|^4511 ≤ (8024878182293/25000000000000 : ℝ)^3487
        have hw : |(4154546481/10000000000 : ℝ)|=(4154546481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2716501693/5000000000 : ℝ)|^4511 ≤ (45418338106981/100000000000000 : ℝ)^3487
        have hw : |(2716501693/5000000000 : ℝ)|=(2716501693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(157739723/500000000 : ℝ)|^4511 ≤ (22482149149327/100000000000000 : ℝ)^3487
        have hw : |(157739723/500000000 : ℝ)|=(157739723/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1507_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162979907/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (2763/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (25549/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4509/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4509 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4509*1^1024 ≤ 0^1024*1^4509 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4509 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4509 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4509/1024 : ℝ) ≤ (1769060463672762733/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4509 ≤ (1769060463672762733/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4509*100000000000000000000^1024 ≤ 1769060463672762733^1024*5^4509 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1769060463672762733 100000000000000000000 4509 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1769060463672762733/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4509 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4509/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4509 := by
      have hnat : (1 : ℕ)^1024*1^4509 ≤ 1^4509*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4509 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4509 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101769060463672762733/100000000000000000000 : ℝ) ≤ (1254987972221231/1250000000000000 : ℝ) ^ (4509/1024 : ℝ) := by
    have hpowers : (101769060463672762733/100000000000000000000 : ℝ)^1024 ≤ (1254987972221231/1250000000000000 : ℝ)^4509 := by
      have hnat : (101769060463672762733 : ℕ)^1024*1250000000000000^4509 ≤ 1254987972221231^4509*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101769060463672762733 100000000000000000000 1254987972221231 1250000000000000 1024 4509 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1254987972221231/1250000000000000 : ℝ)) (X := (101769060463672762733/100000000000000000000 : ℝ)) (by norm_num) 4509 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51769060463672762733/50000000000000000000 : ℝ) ≤ (629987972221231/625000000000000 : ℝ) ^ (4509/1024 : ℝ) := by
    have hpowers : (51769060463672762733/50000000000000000000 : ℝ)^1024 ≤ (629987972221231/625000000000000 : ℝ)^4509 := by
      have hnat : (51769060463672762733 : ℕ)^1024*625000000000000^4509 ≤ 629987972221231^4509*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51769060463672762733 50000000000000000000 629987972221231 625000000000000 1024 4509 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (629987972221231/625000000000000 : ℝ)) (X := (51769060463672762733/50000000000000000000 : ℝ)) (by norm_num) 4509 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(4987972221231/500000000000000 : ℝ)*(0 : ℝ))^(4509/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(4987972221231/500000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1769060463672762733/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(4987972221231/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4509/1024 : ℝ) := by
    rw [show (1 : ℝ)+(4987972221231/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(1254987972221231/1250000000000000 : ℝ) by norm_num, show 1+(1769060463672762733/100000000000000000000 : ℝ)+(0 : ℝ)=(101769060463672762733/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1769060463672762733/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(4987972221231/500000000000000 : ℝ)*(2/5 : ℝ))^(4509/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(4987972221231/500000000000000 : ℝ)*(2/5 : ℝ)=(629987972221231/625000000000000 : ℝ) by norm_num, show 1+2*(1769060463672762733/100000000000000000000 : ℝ)=(51769060463672762733/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(4987972221231/500000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4509/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (4987972221231/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(4987972221231/500000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4509/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (4987972221231/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(4987972221231/500000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4509/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (4987972221231/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-338229967/2000000000 : ℝ)*X 0 0+(5916688583/10000000000 : ℝ)*X 0 1+(1213293183/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2739534501/5000000000 : ℝ)*X 1 0+(-1143827917/5000000000 : ℝ)*X 1 1+(2426586341/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2739534521/5000000000 : ℝ)*X 2 0+(485317269/1000000000 : ℝ)*X 2 1+(-2287655773/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((829298929/2000000000 : ℝ)*X 0 0+(1545619933/5000000000 : ℝ)*X 0 1+(2747179259/5000000000 : ℝ)*X 0 2+(829298929/2000000000 : ℝ)*X 1 0+(1545619933/5000000000 : ℝ)*X 1 1+(2747179259/5000000000 : ℝ)*X 1 2+(829298929/2000000000 : ℝ)*X 2 0+(1545619933/5000000000 : ℝ)*X 2 1+(2747179259/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-847356601/5000000000 : ℝ)*X 0 0+(1220081449/2500000000 : ℝ)*X 0 1+(5888562137/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2594264017/5000000000 : ℝ)*X 1 0+(-626133171/5000000000 : ℝ)*X 1 1+(1177712437/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5188528031/10000000000 : ℝ)*X 2 0+(588856219/1000000000 : ℝ)*X 2 1+(-62613317/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4154546481/10000000000 : ℝ)*X 0 0+(2716501693/5000000000 : ℝ)*X 0 1+(157739723/500000000 : ℝ)*X 0 2+(4154546481/10000000000 : ℝ)*X 1 0+(2716501693/5000000000 : ℝ)*X 1 1+(157739723/500000000 : ℝ)*X 1 2+(4154546481/10000000000 : ℝ)*X 2 0+(2716501693/5000000000 : ℝ)*X 2 1+(157739723/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8777647815022496821119/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (28432713/100000000000000 : ℝ)*(base1) + (404756857/50000000000000 : ℝ)*(base19) + (408189127/50000000000000 : ℝ)*(base23) + (47186257/50000000000000 : ℝ)*(upper3) + (113691477/100000000000000 : ℝ)*(upper5) + (67820580899783/10000000000000 : ℝ)*(major0) + (67820580899783/10000000000000 : ℝ)*(major1) + (67820580899783/10000000000000 : ℝ)*(major2) + (940280115955483/100000000000000 : ℝ)*(sp0) + (940282211880237/100000000000000 : ℝ)*(sp1) + (470141102507849/50000000000000 : ℝ)*(sp2) + (208063593009259/50000000000000 : ℝ)*(sp3) + (1466935591/50000000000000 : ℝ)*(sp4) + (1265115167/100000000000000 : ℝ)*(sp7) + (208064239783199/50000000000000 : ℝ)*(f.failure) + (29383844418561/3125000000000 : ℝ)*(f.sum) + (2236567527127/2500000000000000000000000000 : ℝ)*base66 + (6180661662127/5000000000000000000000000000 : ℝ)*base68 + (5469432722873/5000000000000000000000000000 : ℝ)*base69 + (9540481337873/5000000000000000000000000000 : ℝ)*base71 + (3567987587127/2500000000000000000000000000 : ℝ)*base74 + (22059632002873/5000000000000000000000000000 : ℝ)*base75 + (17223057872127/5000000000000000000000000000 : ℝ)*base78 + (18665292457127/5000000000000000000000000000 : ℝ)*base80 + (7574899417873/2500000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (26817507/5000000000000000000000 : ℝ)*base90 + (26817507/5000000000000000000000 : ℝ)*base92 + (26817507/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8924399781540870134757/1562500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1281550453/100000000000000 : ℝ)*(base19) + (645714483/50000000000000 : ℝ)*(base23) + (75806351/100000000000000 : ℝ)*(base32) + (193181023/100000000000000 : ℝ)*(upper3) + (34687413/25000000000000 : ℝ)*(upper5) + (357692987004827/50000000000000 : ℝ)*(major0) + (357692987004827/50000000000000 : ℝ)*(major1) + (357692987004827/50000000000000 : ℝ)*(major2) + (817280023/25000000000000 : ℝ)*(sp1) + (863943219/25000000000000 : ℝ)*(sp2) + (991830548756799/100000000000000 : ℝ)*(sp4) + (495912999043127/50000000000000 : ℝ)*(sp5) + (991825801554957/100000000000000 : ℝ)*(sp6) + (438941133068957/100000000000000 : ℝ)*(sp7) + (438941208875309/100000000000000 : ℝ)*(f.failure) + (991830548756799/100000000000000 : ℝ)*(f.sum) + (17122284894537/12500000000000000000000000000 : ℝ)*base65 + (222084523732037/25000000000000000000000000000 : ℝ)*base67 + (15708533192963/25000000000000000000000000000 : ℝ)*base70 + (39240830457037/25000000000000000000000000000 : ℝ)*base71 + (128836298807037/12500000000000000000000000000 : ℝ)*base73 + (99001339967963/25000000000000000000000000000 : ℝ)*base76 + (45871539482037/25000000000000000000000000000 : ℝ)*base77 + (78255892082037/25000000000000000000000000000 : ℝ)*base79 + (17247437732037/12500000000000000000000000000 : ℝ)*base81 + (35416263/10000000000000000000000 : ℝ)*base89 + (35416263/10000000000000000000000 : ℝ)*base91 + (35416263/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1507_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162979907/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2763/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (25549/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1507_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1507_s1_0 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1846204659/10000000000 : ℝ)*x 0 + (1393464287/2500000000 : ℝ)*x 1 + (101927391/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1846204659/10000000000 : ℝ)^4511 ≤ (5620616973429/50000000000000 : ℝ)^3487 := by
    have hnat : (1846204659 : ℕ)^4511*50000000000000^3487 ≤ 5620616973429^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1846204659 10000000000 5620616973429 50000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1393464287/2500000000 : ℝ)^4511 ≤ (46947384744977/100000000000000 : ℝ)^3487 := by
    have hnat : (1393464287 : ℕ)^4511*100000000000000^3487 ≤ 46947384744977^3487*2500000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1393464287 2500000000 46947384744977 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (101927391/200000000 : ℝ)^4511 ≤ (4181138129917/10000000000000 : ℝ)^3487 := by
    have hnat : (101927391 : ℕ)^4511*10000000000000^3487 ≤ 4181138129917^3487*200000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      101927391 200000000 4181138129917 10000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1846204659/10000000000 : ℝ), (1393464287/2500000000 : ℝ), (101927391/200000000 : ℝ)] ![(5620616973429/50000000000000 : ℝ), (46947384744977/100000000000000 : ℝ), (4181138129917/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1846204659/10000000000 : ℝ)|^4511 ≤ (5620616973429/50000000000000 : ℝ)^3487
        have hw : |(-1846204659/10000000000 : ℝ)|=(1846204659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1393464287/2500000000 : ℝ)|^4511 ≤ (46947384744977/100000000000000 : ℝ)^3487
        have hw : |(1393464287/2500000000 : ℝ)|=(1393464287/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(101927391/200000000 : ℝ)|^4511 ≤ (4181138129917/10000000000000 : ℝ)^3487
        have hw : |(101927391/200000000 : ℝ)|=(101927391/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_s1_1 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (673441963/1250000000 : ℝ)*x 0 + (-419558293/2000000000 : ℝ)*x 1 + (637046031/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (673441963/1250000000 : ℝ)^4511 ≤ (44927226824411/100000000000000 : ℝ)^3487 := by
    have hnat : (673441963 : ℕ)^4511*100000000000000^3487 ≤ 44927226824411^3487*1250000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673441963 1250000000 44927226824411 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (419558293/2000000000 : ℝ)^4511 ≤ (3315351421301/25000000000000 : ℝ)^3487 := by
    have hnat : (419558293 : ℕ)^4511*25000000000000^3487 ≤ 3315351421301^3487*2000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419558293 2000000000 3315351421301 25000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (637046031/1250000000 : ℝ)^4511 ≤ (1672454699221/4000000000000 : ℝ)^3487 := by
    have hnat : (637046031 : ℕ)^4511*4000000000000^3487 ≤ 1672454699221^3487*1250000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      637046031 1250000000 1672454699221 4000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(673441963/1250000000 : ℝ), (-419558293/2000000000 : ℝ), (637046031/1250000000 : ℝ)] ![(44927226824411/100000000000000 : ℝ), (3315351421301/25000000000000 : ℝ), (1672454699221/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(673441963/1250000000 : ℝ)|^4511 ≤ (44927226824411/100000000000000 : ℝ)^3487
        have hw : |(673441963/1250000000 : ℝ)|=(673441963/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-419558293/2000000000 : ℝ)|^4511 ≤ (3315351421301/25000000000000 : ℝ)^3487
        have hw : |(-419558293/2000000000 : ℝ)|=(419558293/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(637046031/1250000000 : ℝ)|^4511 ≤ (1672454699221/4000000000000 : ℝ)^3487
        have hw : |(637046031/1250000000 : ℝ)|=(637046031/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_s1_2 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (53875351/100000000 : ℝ)*x 0 + (2548184443/5000000000 : ℝ)*x 1 + (-1048895717/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53875351/100000000 : ℝ)^4511 ≤ (11231805077117/25000000000000 : ℝ)^3487 := by
    have hnat : (53875351 : ℕ)^4511*25000000000000^3487 ≤ 11231805077117^3487*100000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53875351 100000000 11231805077117 25000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2548184443/5000000000 : ℝ)^4511 ≤ (41811374251873/100000000000000 : ℝ)^3487 := by
    have hnat : (2548184443 : ℕ)^4511*100000000000000^3487 ≤ 41811374251873^3487*5000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2548184443 5000000000 41811374251873 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048895717/5000000000 : ℝ)^4511 ≤ (6630702715843/50000000000000 : ℝ)^3487 := by
    have hnat : (1048895717 : ℕ)^4511*50000000000000^3487 ≤ 6630702715843^3487*5000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048895717 5000000000 6630702715843 50000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53875351/100000000 : ℝ), (2548184443/5000000000 : ℝ), (-1048895717/5000000000 : ℝ)] ![(11231805077117/25000000000000 : ℝ), (41811374251873/100000000000000 : ℝ), (6630702715843/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53875351/100000000 : ℝ)|^4511 ≤ (11231805077117/25000000000000 : ℝ)^3487
        have hw : |(53875351/100000000 : ℝ)|=(53875351/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2548184443/5000000000 : ℝ)|^4511 ≤ (41811374251873/100000000000000 : ℝ)^3487
        have hw : |(2548184443/5000000000 : ℝ)|=(2548184443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1048895717/5000000000 : ℝ)|^4511 ≤ (6630702715843/50000000000000 : ℝ)^3487
        have hw : |(-1048895717/5000000000 : ℝ)|=(1048895717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_s1_3 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2125718047/5000000000 : ℝ)*x 0 + (3740987301/10000000000 : ℝ)*x 1 + (4819919851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2125718047/5000000000 : ℝ)^4511 ≤ (33071251373093/100000000000000 : ℝ)^3487 := by
    have hnat : (2125718047 : ℕ)^4511*100000000000000^3487 ≤ 33071251373093^3487*5000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125718047 5000000000 33071251373093 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3740987301/10000000000 : ℝ)^4511 ≤ (2802776343271/10000000000000 : ℝ)^3487 := by
    have hnat : (3740987301 : ℕ)^4511*10000000000000^3487 ≤ 2802776343271^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3740987301 10000000000 2802776343271 10000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4819919851/10000000000 : ℝ)^4511 ≤ (38900985176073/100000000000000 : ℝ)^3487 := by
    have hnat : (4819919851 : ℕ)^4511*100000000000000^3487 ≤ 38900985176073^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4819919851 10000000000 38900985176073 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2125718047/5000000000 : ℝ), (3740987301/10000000000 : ℝ), (4819919851/10000000000 : ℝ)] ![(33071251373093/100000000000000 : ℝ), (2802776343271/10000000000000 : ℝ), (38900985176073/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2125718047/5000000000 : ℝ)|^4511 ≤ (33071251373093/100000000000000 : ℝ)^3487
        have hw : |(2125718047/5000000000 : ℝ)|=(2125718047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3740987301/10000000000 : ℝ)|^4511 ≤ (2802776343271/10000000000000 : ℝ)^3487
        have hw : |(3740987301/10000000000 : ℝ)|=(3740987301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4819919851/10000000000 : ℝ)|^4511 ≤ (38900985176073/100000000000000 : ℝ)^3487
        have hw : |(4819919851/10000000000 : ℝ)|=(4819919851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_s1_4 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-923258197/5000000000 : ℝ)*x 0 + (5101746593/10000000000 : ℝ)*x 1 + (5568392721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (923258197/5000000000 : ℝ)^4511 ≤ (11243689511411/100000000000000 : ℝ)^3487 := by
    have hnat : (923258197 : ℕ)^4511*100000000000000^3487 ≤ 11243689511411^3487*5000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      923258197 5000000000 11243689511411 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5101746593/10000000000 : ℝ)^4511 ≤ (41868458839593/100000000000000 : ℝ)^3487 := by
    have hnat : (5101746593 : ℕ)^4511*100000000000000^3487 ≤ 41868458839593^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5101746593 10000000000 41868458839593 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5568392721/10000000000 : ℝ)^4511 ≤ (2344392581933/5000000000000 : ℝ)^3487 := by
    have hnat : (5568392721 : ℕ)^4511*5000000000000^3487 ≤ 2344392581933^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5568392721 10000000000 2344392581933 5000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-923258197/5000000000 : ℝ), (5101746593/10000000000 : ℝ), (5568392721/10000000000 : ℝ)] ![(11243689511411/100000000000000 : ℝ), (41868458839593/100000000000000 : ℝ), (2344392581933/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-923258197/5000000000 : ℝ)|^4511 ≤ (11243689511411/100000000000000 : ℝ)^3487
        have hw : |(-923258197/5000000000 : ℝ)|=(923258197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5101746593/10000000000 : ℝ)|^4511 ≤ (41868458839593/100000000000000 : ℝ)^3487
        have hw : |(5101746593/10000000000 : ℝ)|=(5101746593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5568392721/10000000000 : ℝ)|^4511 ≤ (2344392581933/5000000000000 : ℝ)^3487
        have hw : |(5568392721/10000000000 : ℝ)|=(5568392721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_s1_5 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5261843647/10000000000 : ℝ)*x 0 + (-1625766927/10000000000 : ℝ)*x 1 + (69604911/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5261843647/10000000000 : ℝ)^4511 ≤ (43575933561313/100000000000000 : ℝ)^3487 := by
    have hnat : (5261843647 : ℕ)^4511*100000000000000^3487 ≤ 43575933561313^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261843647 10000000000 43575933561313 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1625766927/10000000000 : ℝ)^4511 ≤ (9536213052689/100000000000000 : ℝ)^3487 := by
    have hnat : (1625766927 : ℕ)^4511*100000000000000^3487 ≤ 9536213052689^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1625766927 10000000000 9536213052689 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (69604911/125000000 : ℝ)^4511 ≤ (46887853370663/100000000000000 : ℝ)^3487 := by
    have hnat : (69604911 : ℕ)^4511*100000000000000^3487 ≤ 46887853370663^3487*125000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69604911 125000000 46887853370663 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5261843647/10000000000 : ℝ), (-1625766927/10000000000 : ℝ), (69604911/125000000 : ℝ)] ![(43575933561313/100000000000000 : ℝ), (9536213052689/100000000000000 : ℝ), (46887853370663/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5261843647/10000000000 : ℝ)|^4511 ≤ (43575933561313/100000000000000 : ℝ)^3487
        have hw : |(5261843647/10000000000 : ℝ)|=(5261843647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1625766927/10000000000 : ℝ)|^4511 ≤ (9536213052689/100000000000000 : ℝ)^3487
        have hw : |(-1625766927/10000000000 : ℝ)|=(1625766927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(69604911/125000000 : ℝ)|^4511 ≤ (46887853370663/100000000000000 : ℝ)^3487
        have hw : |(69604911/125000000 : ℝ)|=(69604911/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_s1_6 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5261843471/10000000000 : ℝ)*x 0 + (1113678589/2000000000 : ℝ)*x 1 + (-1625767083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5261843471/10000000000 : ℝ)^4511 ≤ (8715186335149/20000000000000 : ℝ)^3487 := by
    have hnat : (5261843471 : ℕ)^4511*20000000000000^3487 ≤ 8715186335149^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261843471 10000000000 8715186335149 20000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1113678589/2000000000 : ℝ)^4511 ≤ (23443927039357/50000000000000 : ℝ)^3487 := by
    have hnat : (1113678589 : ℕ)^4511*50000000000000^3487 ≤ 23443927039357^3487*2000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1113678589 2000000000 23443927039357 50000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1625767083/10000000000 : ℝ)^4511 ≤ (9536214236447/100000000000000 : ℝ)^3487 := by
    have hnat : (1625767083 : ℕ)^4511*100000000000000^3487 ≤ 9536214236447^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1625767083 10000000000 9536214236447 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5261843471/10000000000 : ℝ), (1113678589/2000000000 : ℝ), (-1625767083/10000000000 : ℝ)] ![(8715186335149/20000000000000 : ℝ), (23443927039357/50000000000000 : ℝ), (9536214236447/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5261843471/10000000000 : ℝ)|^4511 ≤ (8715186335149/20000000000000 : ℝ)^3487
        have hw : |(5261843471/10000000000 : ℝ)|=(5261843471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1113678589/2000000000 : ℝ)|^4511 ≤ (23443927039357/50000000000000 : ℝ)^3487
        have hw : |(1113678589/2000000000 : ℝ)|=(1113678589/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1625767083/10000000000 : ℝ)|^4511 ≤ (9536214236447/100000000000000 : ℝ)^3487
        have hw : |(-1625767083/10000000000 : ℝ)|=(1625767083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_s1_7 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (531517479/1250000000 : ℝ)*x 0 + (4807769169/10000000000 : ℝ)*x 1 + (1876667583/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531517479/1250000000 : ℝ)^4511 ≤ (33078333397353/100000000000000 : ℝ)^3487 := by
    have hnat : (531517479 : ℕ)^4511*100000000000000^3487 ≤ 33078333397353^3487*1250000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531517479 1250000000 33078333397353 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4807769169/10000000000 : ℝ)^4511 ≤ (38774167018811/100000000000000 : ℝ)^3487 := by
    have hnat : (4807769169 : ℕ)^4511*100000000000000^3487 ≤ 38774167018811^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4807769169 10000000000 38774167018811 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1876667583/5000000000 : ℝ)^4511 ≤ (1759218722821/6250000000000 : ℝ)^3487 := by
    have hnat : (1876667583 : ℕ)^4511*6250000000000^3487 ≤ 1759218722821^3487*5000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1876667583 5000000000 1759218722821 6250000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531517479/1250000000 : ℝ), (4807769169/10000000000 : ℝ), (1876667583/5000000000 : ℝ)] ![(33078333397353/100000000000000 : ℝ), (38774167018811/100000000000000 : ℝ), (1759218722821/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531517479/1250000000 : ℝ)|^4511 ≤ (33078333397353/100000000000000 : ℝ)^3487
        have hw : |(531517479/1250000000 : ℝ)|=(531517479/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4807769169/10000000000 : ℝ)|^4511 ≤ (38774167018811/100000000000000 : ℝ)^3487
        have hw : |(4807769169/10000000000 : ℝ)|=(4807769169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1876667583/5000000000 : ℝ)|^4511 ≤ (1759218722821/6250000000000 : ℝ)^3487
        have hw : |(1876667583/5000000000 : ℝ)|=(1876667583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1507_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162979907/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (25549/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2763/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (8289/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (18387/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (25549/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2763/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (25549/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2763/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (25549/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2763/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (25549/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2763/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (25549/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2763/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (25549/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2763/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2763/100000 : ℝ) ^ (4509/1024 : ℝ) ≤ (1713210802387/12500000000000000000 : ℝ) := by
    have hpowers : (2763/100000 : ℝ)^4509 ≤ (1713210802387/12500000000000000000 : ℝ)^1024 := by
      have hnat : (2763 : ℕ)^4509*12500000000000000000^1024 ≤ 1713210802387^1024*100000^4509 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2763 100000 1713210802387 12500000000000000000 4509 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2763/100000 : ℝ)) (X := (1713210802387/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4509 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (25549/100000 : ℝ) ^ (4509/1024 : ℝ) ≤ (245740922318672943/100000000000000000000 : ℝ) := by
    have hpowers : (25549/100000 : ℝ)^4509 ≤ (245740922318672943/100000000000000000000 : ℝ)^1024 := by
      have hnat : (25549 : ℕ)^4509*100000000000000000000^1024 ≤ 245740922318672943^1024*100000^4509 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25549 100000 245740922318672943 100000000000000000000 4509 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (25549/100000 : ℝ)) (X := (245740922318672943/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4509 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250001713210802387/6250000000000000000 : ℝ) ≤ (125000007781449/125000000000000 : ℝ) ^ (4509/1024 : ℝ) := by
    have hpowers : (6250001713210802387/6250000000000000000 : ℝ)^1024 ≤ (125000007781449/125000000000000 : ℝ)^4509 := by
      have hnat : (6250001713210802387 : ℕ)^1024*125000000000000^4509 ≤ 125000007781449^4509*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250001713210802387 6250000000000000000 125000007781449 125000000000000 1024 4509 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125000007781449/125000000000000 : ℝ)) (X := (6250001713210802387/6250000000000000000 : ℝ)) (by norm_num) 4509 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100245754628005092039/100000000000000000000 : ℝ) ≤ (10005575828047961/10000000000000000 : ℝ) ^ (4509/1024 : ℝ) := by
    have hpowers : (100245754628005092039/100000000000000000000 : ℝ)^1024 ≤ (10005575828047961/10000000000000000 : ℝ)^4509 := by
      have hnat : (100245754628005092039 : ℕ)^1024*10000000000000000^4509 ≤ 10005575828047961^4509*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100245754628005092039 100000000000000000000 10005575828047961 10000000000000000 1024 4509 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10005575828047961/10000000000000000 : ℝ)) (X := (100245754628005092039/100000000000000000000 : ℝ)) (by norm_num) 4509 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50245740922318672943/50000000000000000000 : ℝ) ≤ (5005575516790001/5000000000000000 : ℝ) ^ (4509/1024 : ℝ) := by
    have hpowers : (50245740922318672943/50000000000000000000 : ℝ)^1024 ≤ (5005575516790001/5000000000000000 : ℝ)^4509 := by
      have hnat : (50245740922318672943 : ℕ)^1024*5000000000000000^4509 ≤ 5005575516790001^4509*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50245740922318672943 50000000000000000000 5005575516790001 5000000000000000 1024 4509 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5005575516790001/5000000000000000 : ℝ)) (X := (50245740922318672943/50000000000000000000 : ℝ)) (by norm_num) 4509 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1713210802387/12500000000000000000 : ℝ) ≤ ((113914602799438847277/113930000000000000000 : ℝ)+2*(5575205532041/2278600000000000 : ℝ)*(2763/100000 : ℝ))^(4509/1024 : ℝ) := by
    rw [show (113914602799438847277/113930000000000000000 : ℝ)+2*(5575205532041/2278600000000000 : ℝ)*(2763/100000 : ℝ)=(125000007781449/125000000000000 : ℝ) by norm_num, show 1+2*(1713210802387/12500000000000000000 : ℝ)=(6250001713210802387/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(245740922318672943/100000000000000000000 : ℝ)+(1713210802387/12500000000000000000 : ℝ) ≤ ((113914602799438847277/113930000000000000000 : ℝ)+(5575205532041/2278600000000000 : ℝ)*((25549/100000 : ℝ)+(2763/100000 : ℝ)))^(4509/1024 : ℝ) := by
    rw [show (113914602799438847277/113930000000000000000 : ℝ)+(5575205532041/2278600000000000 : ℝ)*((25549/100000 : ℝ)+(2763/100000 : ℝ))=(10005575828047961/10000000000000000 : ℝ) by norm_num, show 1+(245740922318672943/100000000000000000000 : ℝ)+(1713210802387/12500000000000000000 : ℝ)=(100245754628005092039/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(245740922318672943/100000000000000000000 : ℝ) ≤ ((113914602799438847277/113930000000000000000 : ℝ)+2*(5575205532041/2278600000000000 : ℝ)*(25549/100000 : ℝ))^(4509/1024 : ℝ) := by
    rw [show (113914602799438847277/113930000000000000000 : ℝ)+2*(5575205532041/2278600000000000 : ℝ)*(25549/100000 : ℝ)=(5005575516790001/5000000000000000 : ℝ) by norm_num, show 1+2*(245740922318672943/100000000000000000000 : ℝ)=(50245740922318672943/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (113914602799438847277/113930000000000000000 : ℝ)*(X 1 0+X 2 0)+(5575205532041/2278600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4509/1024 : ℝ)) (lo := (2763/100000 : ℝ)) (hi := (25549/100000 : ℝ)) (c := (113914602799438847277/113930000000000000000 : ℝ)) (alpha := (5575205532041/2278600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (113914602799438847277/113930000000000000000 : ℝ)*(X 0 1+X 2 1)+(5575205532041/2278600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4509/1024 : ℝ)) (lo := (2763/100000 : ℝ)) (hi := (25549/100000 : ℝ)) (c := (113914602799438847277/113930000000000000000 : ℝ)) (alpha := (5575205532041/2278600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (113914602799438847277/113930000000000000000 : ℝ)*(X 0 2+X 1 2)+(5575205532041/2278600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4509/1024 : ℝ)) (lo := (2763/100000 : ℝ)) (hi := (25549/100000 : ℝ)) (c := (113914602799438847277/113930000000000000000 : ℝ)) (alpha := (5575205532041/2278600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1846204659/10000000000 : ℝ)*X 0 0+(1393464287/2500000000 : ℝ)*X 0 1+(101927391/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((673441963/1250000000 : ℝ)*X 1 0+(-419558293/2000000000 : ℝ)*X 1 1+(637046031/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((53875351/100000000 : ℝ)*X 2 0+(2548184443/5000000000 : ℝ)*X 2 1+(-1048895717/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2125718047/5000000000 : ℝ)*X 0 0+(3740987301/10000000000 : ℝ)*X 0 1+(4819919851/10000000000 : ℝ)*X 0 2+(2125718047/5000000000 : ℝ)*X 1 0+(3740987301/10000000000 : ℝ)*X 1 1+(4819919851/10000000000 : ℝ)*X 1 2+(2125718047/5000000000 : ℝ)*X 2 0+(3740987301/10000000000 : ℝ)*X 2 1+(4819919851/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-923258197/5000000000 : ℝ)*X 0 0+(5101746593/10000000000 : ℝ)*X 0 1+(5568392721/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5261843647/10000000000 : ℝ)*X 1 0+(-1625766927/10000000000 : ℝ)*X 1 1+(69604911/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5261843471/10000000000 : ℝ)*X 2 0+(1113678589/2000000000 : ℝ)*X 2 1+(-1625767083/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((531517479/1250000000 : ℝ)*X 0 0+(4807769169/10000000000 : ℝ)*X 0 1+(1876667583/5000000000 : ℝ)*X 0 2+(531517479/1250000000 : ℝ)*X 1 0+(4807769169/10000000000 : ℝ)*X 1 1+(1876667583/5000000000 : ℝ)*X 1 2+(531517479/1250000000 : ℝ)*X 2 0+(4807769169/10000000000 : ℝ)*X 2 1+(1876667583/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1426473491627011613530343877/569650000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (672523/100000000000000 : ℝ)*(base1) + (139192707/25000000000000 : ℝ)*(base19) + (65323091/50000000000000 : ℝ)*(base23) + (38889087/50000000000000 : ℝ)*(lower2) + (9120899/20000000000000 : ℝ)*(upper5) + (302113868099733/20000000000000 : ℝ)*(major0) + (302113868099733/20000000000000 : ℝ)*(major1) + (302113868099733/20000000000000 : ℝ)*(major2) + (2094294689459677/100000000000000 : ℝ)*(sp0) + (1047147066008163/50000000000000 : ℝ)*(sp1) + (2094292545070633/100000000000000 : ℝ)*(sp2) + (37073723953961/4000000000000 : ℝ)*(sp3) + (2013070339/100000000000000 : ℝ)*(sp6) + (809217867/100000000000000 : ℝ)*(sp7) + (115855488592427/12500000000000 : ℝ)*(f.failure) + (1047147344393577/50000000000000 : ℝ)*(f.sum) + (103332061996033/22786000000000000000000000000 : ℝ)*base66 + (15392746241265727041/2278600000000000000000000000000000 : ℝ)*base67 + (4072555935249927041/2278600000000000000000000000000000 : ℝ)*base69 + (8497258419081327041/2278600000000000000000000000000000 : ℝ)*base71 + (4963896046613/4557200000000000000000000000 : ℝ)*base73 + (3552165853907127041/2278600000000000000000000000000000 : ℝ)*base75 + (5394439888932327041/2278600000000000000000000000000000 : ℝ)*base77 + (5719991185098472959/2278600000000000000000000000000000 : ℝ)*base80 + (4103021939723/4557200000000000000000000000 : ℝ)*base82 + (864289/1250000000000000000000 : ℝ)*base89 + (864289/1250000000000000000000 : ℝ)*base91 + (864289/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6298137467494944716396019093/1424125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (870648033/100000000000000 : ℝ)*(base19) + (867635449/100000000000000 : ℝ)*(base23) + (27351941/20000000000000 : ℝ)*(upper3) + (29011841/100000000000000 : ℝ)*(lower4) + (35219839/100000000000000 : ℝ)*(upper5) + (386415776545603/25000000000000 : ℝ)*(major0) + (386415776545603/25000000000000 : ℝ)*(major1) + (386415776545603/25000000000000 : ℝ)*(major2) + (1499657943/25000000000000 : ℝ)*(sp1) + (3282514481/50000000000000 : ℝ)*(sp2) + (2142949584293823/100000000000000 : ℝ)*(sp4) + (1071471357507009/50000000000000 : ℝ)*(sp5) + (535735537907353/25000000000000 : ℝ)*(sp6) + (474188240327813/50000000000000 : ℝ)*(sp7) + (474188240327813/50000000000000 : ℝ)*(f.failure) + (2142949584293823/100000000000000 : ℝ)*(f.sum) + (74854319259651/14241250000000000000000000000 : ℝ)*base66 + (11419480333213226969/2848250000000000000000000000000000 : ℝ)*base68 + (6691640042502273031/2848250000000000000000000000000000 : ℝ)*base69 + (18915037949030476969/2848250000000000000000000000000000 : ℝ)*base72 + (95504320725037/28482500000000000000000000000 : ℝ)*base74 + (3052417024050023031/2848250000000000000000000000000000 : ℝ)*base75 + (18651016903123976969/2848250000000000000000000000000000 : ℝ)*base78 + (5323597672905476969/2848250000000000000000000000000000 : ℝ)*base80 + (112195734899933/28482500000000000000000000000 : ℝ)*base81 + (12253391/5000000000000000000000 : ℝ)*base89 + (12253391/5000000000000000000000 : ℝ)*base91 + (12253391/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1507_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162979907/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (25549/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2763/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8289/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (18387/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1507_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1507_s2_0 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-935652087/5000000000 : ℝ)*x 0 + (272976689/500000000 : ℝ)*x 1 + (2597221699/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (935652087/5000000000 : ℝ)^4511 ≤ (2859833395181/25000000000000 : ℝ)^3487 := by
    have hnat : (935652087 : ℕ)^4511*25000000000000^3487 ≤ 2859833395181^3487*5000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      935652087 5000000000 2859833395181 25000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (272976689/500000000 : ℝ)^4511 ≤ (22852730150879/50000000000000 : ℝ)^3487 := by
    have hnat : (272976689 : ℕ)^4511*50000000000000^3487 ≤ 22852730150879^3487*500000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272976689 500000000 22852730150879 50000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2597221699/5000000000 : ℝ)^4511 ≤ (10713801524219/25000000000000 : ℝ)^3487 := by
    have hnat : (2597221699 : ℕ)^4511*25000000000000^3487 ≤ 10713801524219^3487*5000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2597221699 5000000000 10713801524219 25000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-935652087/5000000000 : ℝ), (272976689/500000000 : ℝ), (2597221699/5000000000 : ℝ)] ![(2859833395181/25000000000000 : ℝ), (22852730150879/50000000000000 : ℝ), (10713801524219/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-935652087/5000000000 : ℝ)|^4511 ≤ (2859833395181/25000000000000 : ℝ)^3487
        have hw : |(-935652087/5000000000 : ℝ)|=(935652087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(272976689/500000000 : ℝ)|^4511 ≤ (22852730150879/50000000000000 : ℝ)^3487
        have hw : |(272976689/500000000 : ℝ)|=(272976689/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2597221699/5000000000 : ℝ)|^4511 ≤ (10713801524219/25000000000000 : ℝ)^3487
        have hw : |(2597221699/5000000000 : ℝ)|=(2597221699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_s2_1 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1339632979/2500000000 : ℝ)*x 0 + (-501952037/2500000000 : ℝ)*x 1 + (2597222121/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1339632979/2500000000 : ℝ)^4511 ≤ (8922916408323/20000000000000 : ℝ)^3487 := by
    have hnat : (1339632979 : ℕ)^4511*20000000000000^3487 ≤ 8922916408323^3487*2500000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1339632979 2500000000 8922916408323 20000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (501952037/2500000000 : ℝ)^4511 ≤ (2506040568157/20000000000000 : ℝ)^3487 := by
    have hnat : (501952037 : ℕ)^4511*20000000000000^3487 ≤ 2506040568157^3487*2500000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      501952037 2500000000 2506040568157 20000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2597222121/5000000000 : ℝ)^4511 ≤ (21427607552433/50000000000000 : ℝ)^3487 := by
    have hnat : (2597222121 : ℕ)^4511*50000000000000^3487 ≤ 21427607552433^3487*5000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2597222121 5000000000 21427607552433 50000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1339632979/2500000000 : ℝ), (-501952037/2500000000 : ℝ), (2597222121/5000000000 : ℝ)] ![(8922916408323/20000000000000 : ℝ), (2506040568157/20000000000000 : ℝ), (21427607552433/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1339632979/2500000000 : ℝ)|^4511 ≤ (8922916408323/20000000000000 : ℝ)^3487
        have hw : |(1339632979/2500000000 : ℝ)|=(1339632979/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-501952037/2500000000 : ℝ)|^4511 ≤ (2506040568157/20000000000000 : ℝ)^3487
        have hw : |(-501952037/2500000000 : ℝ)|=(501952037/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2597222121/5000000000 : ℝ)|^4511 ≤ (21427607552433/50000000000000 : ℝ)^3487
        have hw : |(2597222121/5000000000 : ℝ)|=(2597222121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_s2_2 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1339633207/2500000000 : ℝ)*x 0 + (5194443633/10000000000 : ℝ)*x 1 + (-250975967/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1339633207/2500000000 : ℝ)^4511 ≤ (22307295932337/50000000000000 : ℝ)^3487 := by
    have hnat : (1339633207 : ℕ)^4511*50000000000000^3487 ≤ 22307295932337^3487*2500000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1339633207 2500000000 22307295932337 50000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5194443633/10000000000 : ℝ)^4511 ≤ (1714208344201/4000000000000 : ℝ)^3487 := by
    have hnat : (5194443633 : ℕ)^4511*4000000000000^3487 ≤ 1714208344201^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5194443633 10000000000 1714208344201 4000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (250975967/1250000000 : ℝ)^4511 ≤ (6265099757271/50000000000000 : ℝ)^3487 := by
    have hnat : (250975967 : ℕ)^4511*50000000000000^3487 ≤ 6265099757271^3487*1250000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      250975967 1250000000 6265099757271 50000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1339633207/2500000000 : ℝ), (5194443633/10000000000 : ℝ), (-250975967/1250000000 : ℝ)] ![(22307295932337/50000000000000 : ℝ), (1714208344201/4000000000000 : ℝ), (6265099757271/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1339633207/2500000000 : ℝ)|^4511 ≤ (22307295932337/50000000000000 : ℝ)^3487
        have hw : |(1339633207/2500000000 : ℝ)|=(1339633207/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5194443633/10000000000 : ℝ)|^4511 ≤ (1714208344201/4000000000000 : ℝ)^3487
        have hw : |(5194443633/10000000000 : ℝ)|=(5194443633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-250975967/1250000000 : ℝ)|^4511 ≤ (6265099757271/50000000000000 : ℝ)^3487
        have hw : |(-250975967/1250000000 : ℝ)|=(250975967/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_s2_3 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2134718683/5000000000 : ℝ)*x 0 + (3978885283/10000000000 : ℝ)*x 1 + (2288941933/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2134718683/5000000000 : ℝ)^4511 ≤ (33252514178927/100000000000000 : ℝ)^3487 := by
    have hnat : (2134718683 : ℕ)^4511*100000000000000^3487 ≤ 33252514178927^3487*5000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2134718683 5000000000 33252514178927 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3978885283/10000000000 : ℝ)^4511 ≤ (30354737807973/100000000000000 : ℝ)^3487 := by
    have hnat : (3978885283 : ℕ)^4511*100000000000000^3487 ≤ 30354737807973^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3978885283 10000000000 30354737807973 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2288941933/5000000000 : ℝ)^4511 ≤ (1819637399629/5000000000000 : ℝ)^3487 := by
    have hnat : (2288941933 : ℕ)^4511*5000000000000^3487 ≤ 1819637399629^3487*5000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2288941933 5000000000 1819637399629 5000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2134718683/5000000000 : ℝ), (3978885283/10000000000 : ℝ), (2288941933/5000000000 : ℝ)] ![(33252514178927/100000000000000 : ℝ), (30354737807973/100000000000000 : ℝ), (1819637399629/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2134718683/5000000000 : ℝ)|^4511 ≤ (33252514178927/100000000000000 : ℝ)^3487
        have hw : |(2134718683/5000000000 : ℝ)|=(2134718683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3978885283/10000000000 : ℝ)|^4511 ≤ (30354737807973/100000000000000 : ℝ)^3487
        have hw : |(3978885283/10000000000 : ℝ)|=(3978885283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2288941933/5000000000 : ℝ)|^4511 ≤ (1819637399629/5000000000000 : ℝ)^3487
        have hw : |(2288941933/5000000000 : ℝ)|=(2288941933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_s2_4 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-467839137/2500000000 : ℝ)*x 0 + (129902771/250000000 : ℝ)*x 1 + (5457852137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (467839137/2500000000 : ℝ)^4511 ≤ (5719873883043/50000000000000 : ℝ)^3487 := by
    have hnat : (467839137 : ℕ)^4511*50000000000000^3487 ≤ 5719873883043^3487*2500000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      467839137 2500000000 5719873883043 50000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (129902771/250000000 : ℝ)^4511 ≤ (21436501750329/50000000000000 : ℝ)^3487 := by
    have hnat : (129902771 : ℕ)^4511*50000000000000^3487 ≤ 21436501750329^3487*250000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129902771 250000000 21436501750329 50000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5457852137/10000000000 : ℝ)^4511 ≤ (22843624362061/50000000000000 : ℝ)^3487 := by
    have hnat : (5457852137 : ℕ)^4511*50000000000000^3487 ≤ 22843624362061^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5457852137 10000000000 22843624362061 50000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-467839137/2500000000 : ℝ), (129902771/250000000 : ℝ), (5457852137/10000000000 : ℝ)] ![(5719873883043/50000000000000 : ℝ), (21436501750329/50000000000000 : ℝ), (22843624362061/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-467839137/2500000000 : ℝ)|^4511 ≤ (5719873883043/50000000000000 : ℝ)^3487
        have hw : |(-467839137/2500000000 : ℝ)|=(467839137/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(129902771/250000000 : ℝ)|^4511 ≤ (21436501750329/50000000000000 : ℝ)^3487
        have hw : |(129902771/250000000 : ℝ)|=(129902771/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5457852137/10000000000 : ℝ)|^4511 ≤ (22843624362061/50000000000000 : ℝ)^3487
        have hw : |(5457852137/10000000000 : ℝ)|=(5457852137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_s2_5 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5288976241/10000000000 : ℝ)*x 0 + (-69775977/400000000 : ℝ)*x 1 + (5457853057/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288976241/10000000000 : ℝ)^4511 ≤ (43866837266397/100000000000000 : ℝ)^3487 := by
    have hnat : (5288976241 : ℕ)^4511*100000000000000^3487 ≤ 43866837266397^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288976241 10000000000 43866837266397 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (69775977/400000000 : ℝ)^4511 ≤ (10445904031469/100000000000000 : ℝ)^3487 := by
    have hnat : (69775977 : ℕ)^4511*100000000000000^3487 ≤ 10445904031469^3487*400000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69775977 400000000 10445904031469 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5457853057/10000000000 : ℝ)^4511 ≤ (9137451737387/20000000000000 : ℝ)^3487 := by
    have hnat : (5457853057 : ℕ)^4511*20000000000000^3487 ≤ 9137451737387^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5457853057 10000000000 9137451737387 20000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288976241/10000000000 : ℝ), (-69775977/400000000 : ℝ), (5457853057/10000000000 : ℝ)] ![(43866837266397/100000000000000 : ℝ), (10445904031469/100000000000000 : ℝ), (9137451737387/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288976241/10000000000 : ℝ)|^4511 ≤ (43866837266397/100000000000000 : ℝ)^3487
        have hw : |(5288976241/10000000000 : ℝ)|=(5288976241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-69775977/400000000 : ℝ)|^4511 ≤ (10445904031469/100000000000000 : ℝ)^3487
        have hw : |(-69775977/400000000 : ℝ)|=(69775977/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5457853057/10000000000 : ℝ)|^4511 ≤ (9137451737387/20000000000000 : ℝ)^3487
        have hw : |(5457853057/10000000000 : ℝ)|=(5457853057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_s2_6 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (165280517/312500000 : ℝ)*x 0 + (5457852417/10000000000 : ℝ)*x 1 + (-17443999/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165280517/312500000 : ℝ)^4511 ≤ (43866840517481/100000000000000 : ℝ)^3487 := by
    have hnat : (165280517 : ℕ)^4511*100000000000000^3487 ≤ 43866840517481^3487*312500000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165280517 312500000 43866840517481 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5457852417/10000000000 : ℝ)^4511 ≤ (45687251756283/100000000000000 : ℝ)^3487 := by
    have hnat : (5457852417 : ℕ)^4511*100000000000000^3487 ≤ 45687251756283^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5457852417 10000000000 45687251756283 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (17443999/100000000 : ℝ)^4511 ≤ (2611476927797/25000000000000 : ℝ)^3487 := by
    have hnat : (17443999 : ℕ)^4511*25000000000000^3487 ≤ 2611476927797^3487*100000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17443999 100000000 2611476927797 25000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165280517/312500000 : ℝ), (5457852417/10000000000 : ℝ), (-17443999/100000000 : ℝ)] ![(43866840517481/100000000000000 : ℝ), (45687251756283/100000000000000 : ℝ), (2611476927797/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165280517/312500000 : ℝ)|^4511 ≤ (43866840517481/100000000000000 : ℝ)^3487
        have hw : |(165280517/312500000 : ℝ)|=(165280517/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5457852417/10000000000 : ℝ)|^4511 ≤ (45687251756283/100000000000000 : ℝ)^3487
        have hw : |(5457852417/10000000000 : ℝ)|=(5457852417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-17443999/100000000 : ℝ)|^4511 ≤ (2611476927797/25000000000000 : ℝ)^3487
        have hw : |(-17443999/100000000 : ℝ)|=(17443999/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1507_s2_7 (p : ℝ) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1067389783/2500000000 : ℝ)*x 0 + (4574118173/10000000000 : ℝ)*x 1 + (3982683973/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1067389783/2500000000 : ℝ)^4511 ≤ (8313435265079/25000000000000 : ℝ)^3487 := by
    have hnat : (1067389783 : ℕ)^4511*25000000000000^3487 ≤ 8313435265079^3487*2500000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1067389783 2500000000 8313435265079 25000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4574118173/10000000000 : ℝ)^4511 ≤ (36354025491371/100000000000000 : ℝ)^3487 := by
    have hnat : (4574118173 : ℕ)^4511*100000000000000^3487 ≤ 36354025491371^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4574118173 10000000000 36354025491371 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3982683973/10000000000 : ℝ)^4511 ≤ (30392233438687/100000000000000 : ℝ)^3487 := by
    have hnat : (3982683973 : ℕ)^4511*100000000000000^3487 ≤ 30392233438687^3487*10000000000^4511 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3982683973 10000000000 30392233438687 100000000000000 4511 3487 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4511/1024 : ℝ)) 4511 3487 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1067389783/2500000000 : ℝ), (4574118173/10000000000 : ℝ), (3982683973/10000000000 : ℝ)] ![(8313435265079/25000000000000 : ℝ), (36354025491371/100000000000000 : ℝ), (30392233438687/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1067389783/2500000000 : ℝ)|^4511 ≤ (8313435265079/25000000000000 : ℝ)^3487
        have hw : |(1067389783/2500000000 : ℝ)|=(1067389783/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4574118173/10000000000 : ℝ)|^4511 ≤ (36354025491371/100000000000000 : ℝ)^3487
        have hw : |(4574118173/10000000000 : ℝ)|=(4574118173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3982683973/10000000000 : ℝ)|^4511 ≤ (30392233438687/100000000000000 : ℝ)^3487
        have hw : |(3982683973/10000000000 : ℝ)|=(3982683973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1507_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162979907/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18387/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8289/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2081/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1001/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (18387/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8289/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (18387/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8289/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (18387/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8289/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (18387/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8289/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (18387/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8289/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (18387/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8289/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8289/100000 : ℝ) ^ (4509/1024 : ℝ) ≤ (864546800434747/50000000000000000000 : ℝ) := by
    have hpowers : (8289/100000 : ℝ)^4509 ≤ (864546800434747/50000000000000000000 : ℝ)^1024 := by
      have hnat : (8289 : ℕ)^4509*50000000000000000000^1024 ≤ 864546800434747^1024*100000^4509 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8289 100000 864546800434747 50000000000000000000 4509 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8289/100000 : ℝ)) (X := (864546800434747/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4509 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (18387/100000 : ℝ) ^ (4509/1024 : ℝ) ≤ (57730564081787211/100000000000000000000 : ℝ) := by
    have hpowers : (18387/100000 : ℝ)^4509 ≤ (57730564081787211/100000000000000000000 : ℝ)^1024 := by
      have hnat : (18387 : ℕ)^4509*100000000000000000000^1024 ≤ 57730564081787211^1024*100000^4509 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18387 100000 57730564081787211 100000000000000000000 4509 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18387/100000 : ℝ)) (X := (57730564081787211/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4509 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000864546800434747/25000000000000000000 : ℝ) ≤ (10000078534849649/10000000000000000 : ℝ) ^ (4509/1024 : ℝ) := by
    have hpowers : (25000864546800434747/25000000000000000000 : ℝ)^1024 ≤ (10000078534849649/10000000000000000 : ℝ)^4509 := by
      have hnat : (25000864546800434747 : ℕ)^1024*10000000000000000^4509 ≤ 10000078534849649^4509*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000864546800434747 25000000000000000000 10000078534849649 10000000000000000 1024 4509 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000078534849649/10000000000000000 : ℝ)) (X := (25000864546800434747/25000000000000000000 : ℝ)) (by norm_num) 4509 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20011891931536531341/20000000000000000000 : ℝ) ≤ (50006750133483/50000000000000 : ℝ) ^ (4509/1024 : ℝ) := by
    have hpowers : (20011891931536531341/20000000000000000000 : ℝ)^1024 ≤ (50006750133483/50000000000000 : ℝ)^4509 := by
      have hnat : (20011891931536531341 : ℕ)^1024*50000000000000^4509 ≤ 50006750133483^4509*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20011891931536531341 20000000000000000000 50006750133483 50000000000000 1024 4509 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (50006750133483/50000000000000 : ℝ)) (X := (20011891931536531341/20000000000000000000 : ℝ)) (by norm_num) 4509 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50057730564081787211/50000000000000000000 : ℝ) ≤ (10002621518543551/10000000000000000 : ℝ) ^ (4509/1024 : ℝ) := by
    have hpowers : (50057730564081787211/50000000000000000000 : ℝ)^1024 ≤ (10002621518543551/10000000000000000 : ℝ)^4509 := by
      have hnat : (50057730564081787211 : ℕ)^1024*10000000000000000^4509 ≤ 10002621518543551^4509*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50057730564081787211 50000000000000000000 10002621518543551 10000000000000000 1024 4509 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002621518543551/10000000000000000 : ℝ)) (X := (50057730564081787211/50000000000000000000 : ℝ)) (by norm_num) 4509 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(864546800434747/50000000000000000000 : ℝ) ≤ ((934812169009935203/935000000000000000 : ℝ)+2*(1271491846951/1009800000000000 : ℝ)*(8289/100000 : ℝ))^(4509/1024 : ℝ) := by
    rw [show (934812169009935203/935000000000000000 : ℝ)+2*(1271491846951/1009800000000000 : ℝ)*(8289/100000 : ℝ)=(10000078534849649/10000000000000000 : ℝ) by norm_num, show 1+2*(864546800434747/50000000000000000000 : ℝ)=(25000864546800434747/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(57730564081787211/100000000000000000000 : ℝ)+(864546800434747/50000000000000000000 : ℝ) ≤ ((934812169009935203/935000000000000000 : ℝ)+(1271491846951/1009800000000000 : ℝ)*((18387/100000 : ℝ)+(8289/100000 : ℝ)))^(4509/1024 : ℝ) := by
    rw [show (934812169009935203/935000000000000000 : ℝ)+(1271491846951/1009800000000000 : ℝ)*((18387/100000 : ℝ)+(8289/100000 : ℝ))=(50006750133483/50000000000000 : ℝ) by norm_num, show 1+(57730564081787211/100000000000000000000 : ℝ)+(864546800434747/50000000000000000000 : ℝ)=(20011891931536531341/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(57730564081787211/100000000000000000000 : ℝ) ≤ ((934812169009935203/935000000000000000 : ℝ)+2*(1271491846951/1009800000000000 : ℝ)*(18387/100000 : ℝ))^(4509/1024 : ℝ) := by
    rw [show (934812169009935203/935000000000000000 : ℝ)+2*(1271491846951/1009800000000000 : ℝ)*(18387/100000 : ℝ)=(10002621518543551/10000000000000000 : ℝ) by norm_num, show 1+2*(57730564081787211/100000000000000000000 : ℝ)=(50057730564081787211/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (934812169009935203/935000000000000000 : ℝ)*(X 1 0+X 2 0)+(1271491846951/1009800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4509/1024 : ℝ)) (lo := (8289/100000 : ℝ)) (hi := (18387/100000 : ℝ)) (c := (934812169009935203/935000000000000000 : ℝ)) (alpha := (1271491846951/1009800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (934812169009935203/935000000000000000 : ℝ)*(X 0 1+X 2 1)+(1271491846951/1009800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4509/1024 : ℝ)) (lo := (8289/100000 : ℝ)) (hi := (18387/100000 : ℝ)) (c := (934812169009935203/935000000000000000 : ℝ)) (alpha := (1271491846951/1009800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (934812169009935203/935000000000000000 : ℝ)*(X 0 2+X 1 2)+(1271491846951/1009800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4509/1024 : ℝ)) (lo := (8289/100000 : ℝ)) (hi := (18387/100000 : ℝ)) (c := (934812169009935203/935000000000000000 : ℝ)) (alpha := (1271491846951/1009800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-935652087/5000000000 : ℝ)*X 0 0+(272976689/500000000 : ℝ)*X 0 1+(2597221699/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1339632979/2500000000 : ℝ)*X 1 0+(-501952037/2500000000 : ℝ)*X 1 1+(2597222121/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1339633207/2500000000 : ℝ)*X 2 0+(5194443633/10000000000 : ℝ)*X 2 1+(-250975967/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2134718683/5000000000 : ℝ)*X 0 0+(3978885283/10000000000 : ℝ)*X 0 1+(2288941933/5000000000 : ℝ)*X 0 2+(2134718683/5000000000 : ℝ)*X 1 0+(3978885283/10000000000 : ℝ)*X 1 1+(2288941933/5000000000 : ℝ)*X 1 2+(2134718683/5000000000 : ℝ)*X 2 0+(3978885283/10000000000 : ℝ)*X 2 1+(2288941933/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-467839137/2500000000 : ℝ)*X 0 0+(129902771/250000000 : ℝ)*X 0 1+(5457852137/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5288976241/10000000000 : ℝ)*X 1 0+(-69775977/400000000 : ℝ)*X 1 1+(5457853057/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((165280517/312500000 : ℝ)*X 2 0+(5457852417/10000000000 : ℝ)*X 2 1+(-17443999/100000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1067389783/2500000000 : ℝ)*X 0 0+(4574118173/10000000000 : ℝ)*X 0 1+(3982683973/10000000000 : ℝ)*X 0 2+(1067389783/2500000000 : ℝ)*X 1 0+(4574118173/10000000000 : ℝ)*X 1 1+(3982683973/10000000000 : ℝ)*X 1 2+(1067389783/2500000000 : ℝ)*X 2 0+(4574118173/10000000000 : ℝ)*X 2 1+(3982683973/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1507_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (341771559756729466955827/66406250000000000000000000000 : ℝ) := by norm_num
    linear_combination (1104538567/100000000000000 : ℝ)*(base19) + (690570561/50000000000000 : ℝ)*(base23) + (39944369/50000000000000 : ℝ)*(upper3) + (39163889/20000000000000 : ℝ)*(upper4) + (65966549/25000000000000 : ℝ)*(upper5) + (85028475038397/3125000000000 : ℝ)*(major0) + (85028475038397/3125000000000 : ℝ)*(major1) + (85028475038397/3125000000000 : ℝ)*(major2) + (1886158276939861/50000000000000 : ℝ)*(sp0) + (1886172327250107/50000000000000 : ℝ)*(sp1) + (1886172188948829/50000000000000 : ℝ)*(sp2) + (834732225178803/50000000000000 : ℝ)*(sp3) + (14602579529/50000000000000 : ℝ)*(sp4) + (3005376273/25000000000000 : ℝ)*(sp7) + (1669476471862697/100000000000000 : ℝ)*(f.failure) + (188617287951939/5000000000000 : ℝ)*(f.sum) + (48748895111/47812500000000000000000000 : ℝ)*base66 + (34613453789797721/2390625000000000000000000000000 : ℝ)*base68 + (32828637836047721/2390625000000000000000000000000 : ℝ)*base70 + (22938809516516471/2390625000000000000000000000000 : ℝ)*base72 + (1684130650243/382500000000000000000000000 : ℝ)*base74 + (24798254701016471/2390625000000000000000000000000 : ℝ)*base76 + (18801801397766471/2390625000000000000000000000000 : ℝ)*base78 + (29855425446078971/2390625000000000000000000000000 : ℝ)*base80 + (322521285701/47812500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (73829179/10000000000000000000000 : ℝ)*base89 + (73829179/10000000000000000000000 : ℝ)*base91 + (73829179/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (153025109268162381276469891/11687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (321781109/50000000000000 : ℝ)*(base19) + (57177241/3125000000000 : ℝ)*(base23) + (20728537/5000000000000 : ℝ)*(upper3) + (429389143/100000000000000 : ℝ)*(lower4) + (1377840461843001/50000000000000 : ℝ)*(major0) + (1377840461843001/50000000000000 : ℝ)*(major1) + (1377840461843001/50000000000000 : ℝ)*(major2) + (2175661691/25000000000000 : ℝ)*(sp1) + (5129319119/25000000000000 : ℝ)*(sp2) + (714752469/50000000000000 : ℝ)*(sp3) + (38205511911923/1000000000000 : ℝ)*(sp4) + (1910270922491659/50000000000000 : ℝ)*(sp5) + (238783052765257/6250000000000 : ℝ)*(sp6) + (1690808790239513/100000000000000 : ℝ)*(sp7) + (1690810219744451/100000000000000 : ℝ)*(f.failure) + (38205511911923/1000000000000 : ℝ)*(f.sum) + (619492537357/8415000000000000000000000000 : ℝ)*base65 + (525468762392252827/420750000000000000000000000000000 : ℝ)*base67 + (1966663509803247173/420750000000000000000000000000000 : ℝ)*base70 + (209891837820002827/420750000000000000000000000000000 : ℝ)*base71 + (7049082646601/4207500000000000000000000000 : ℝ)*base73 + (4114397988131252827/420750000000000000000000000000000 : ℝ)*base75 + (3127879091644502827/420750000000000000000000000000000 : ℝ)*base77 + (1399970704343252827/420750000000000000000000000000000 : ℝ)*base79 + (11214733803949/4207500000000000000000000000 : ℝ)*base82 + (12253943/10000000000000000000000 : ℝ)*base90 + (12253943/10000000000000000000000 : ℝ)*base92 + (12253943/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1507_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162979907/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18387/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8289/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2081/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1001/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1507_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1507_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162979907/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2081/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1001/6250 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1507_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1507_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1507_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4509/1024 : ℝ) ≤ p) (hpb : p ≤ (4511/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162979907/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2081/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1001/6250 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1507_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
