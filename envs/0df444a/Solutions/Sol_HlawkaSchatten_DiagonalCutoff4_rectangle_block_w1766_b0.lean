-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1766_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:29:48.360994+00:00
-- url     : https://prove2.me/submissions/b3fd2dce-f720-4da1-9118-d798362ad8c6

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
theorem support_rectangle_w1766_s0_0 (p : ℝ) (hpa : (6015/1024 : ℝ) ≤ p) (hpb : p ≤ (6031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-552239377/5000000000 : ℝ)*x 0 + (5584400431/10000000000 : ℝ)*x 1 + (2499945681/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (552239377/5000000000 : ℝ)^6031 ≤ (3519167687759/50000000000000 : ℝ)^5007 := by
    have hnat : (552239377 : ℕ)^6031*50000000000000^5007 ≤ 3519167687759^5007*5000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      552239377 5000000000 3519167687759 50000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5584400431/10000000000 : ℝ)^6031 ≤ (24785620715309/50000000000000 : ℝ)^5007 := by
    have hnat : (5584400431 : ℕ)^6031*50000000000000^5007 ≤ 24785620715309^5007*10000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5584400431 10000000000 24785620715309 50000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2499945681/5000000000 : ℝ)^6031 ≤ (21695211589703/50000000000000 : ℝ)^5007 := by
    have hnat : (2499945681 : ℕ)^6031*50000000000000^5007 ≤ 21695211589703^5007*5000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2499945681 5000000000 21695211589703 50000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6031/1024 : ℝ)) 6031 5007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-552239377/5000000000 : ℝ), (5584400431/10000000000 : ℝ), (2499945681/5000000000 : ℝ)] ![(3519167687759/50000000000000 : ℝ), (24785620715309/50000000000000 : ℝ), (21695211589703/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-552239377/5000000000 : ℝ)|^6031 ≤ (3519167687759/50000000000000 : ℝ)^5007
        have hw : |(-552239377/5000000000 : ℝ)|=(552239377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5584400431/10000000000 : ℝ)|^6031 ≤ (24785620715309/50000000000000 : ℝ)^5007
        have hw : |(5584400431/10000000000 : ℝ)|=(5584400431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2499945681/5000000000 : ℝ)|^6031 ≤ (21695211589703/50000000000000 : ℝ)^5007
        have hw : |(2499945681/5000000000 : ℝ)|=(2499945681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1766_s0_1 (p : ℝ) (hpa : (6015/1024 : ℝ) ≤ p) (hpb : p ≤ (6031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353915023/10000000000 : ℝ)*x 0 + (-1415792037/10000000000 : ℝ)*x 1 + (4999890873/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353915023/10000000000 : ℝ)^6031 ≤ (23558687019013/50000000000000 : ℝ)^5007 := by
    have hnat : (5353915023 : ℕ)^6031*50000000000000^5007 ≤ 23558687019013^5007*10000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353915023 10000000000 23558687019013 50000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1415792037/10000000000 : ℝ)^6031 ≤ (4746103942591/50000000000000 : ℝ)^5007 := by
    have hnat : (1415792037 : ℕ)^6031*50000000000000^5007 ≤ 4746103942591^5007*10000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1415792037 10000000000 4746103942591 50000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4999890873/10000000000 : ℝ)^6031 ≤ (43390418067841/100000000000000 : ℝ)^5007 := by
    have hnat : (4999890873 : ℕ)^6031*100000000000000^5007 ≤ 43390418067841^5007*10000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4999890873 10000000000 43390418067841 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6031/1024 : ℝ)) 6031 5007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353915023/10000000000 : ℝ), (-1415792037/10000000000 : ℝ), (4999890873/10000000000 : ℝ)] ![(23558687019013/50000000000000 : ℝ), (4746103942591/50000000000000 : ℝ), (43390418067841/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353915023/10000000000 : ℝ)|^6031 ≤ (23558687019013/50000000000000 : ℝ)^5007
        have hw : |(5353915023/10000000000 : ℝ)|=(5353915023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1415792037/10000000000 : ℝ)|^6031 ≤ (4746103942591/50000000000000 : ℝ)^5007
        have hw : |(-1415792037/10000000000 : ℝ)|=(1415792037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4999890873/10000000000 : ℝ)|^6031 ≤ (43390418067841/100000000000000 : ℝ)^5007
        have hw : |(4999890873/10000000000 : ℝ)|=(4999890873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1766_s0_2 (p : ℝ) (hpa : (6015/1024 : ℝ) ≤ p) (hpb : p ≤ (6031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676955849/5000000000 : ℝ)*x 0 + (1249973269/2500000000 : ℝ)*x 1 + (-1415793549/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676955849/5000000000 : ℝ)^6031 ≤ (11779334697943/25000000000000 : ℝ)^5007 := by
    have hnat : (2676955849 : ℕ)^6031*25000000000000^5007 ≤ 11779334697943^5007*5000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676955849 5000000000 11779334697943 25000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1249973269/2500000000 : ℝ)^6031 ≤ (21695220548009/50000000000000 : ℝ)^5007 := by
    have hnat : (1249973269 : ℕ)^6031*50000000000000^5007 ≤ 21695220548009^5007*2500000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1249973269 2500000000 21695220548009 50000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1415793549/10000000000 : ℝ)^6031 ≤ (9492220095623/100000000000000 : ℝ)^5007 := by
    have hnat : (1415793549 : ℕ)^6031*100000000000000^5007 ≤ 9492220095623^5007*10000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1415793549 10000000000 9492220095623 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6031/1024 : ℝ)) 6031 5007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676955849/5000000000 : ℝ), (1249973269/2500000000 : ℝ), (-1415793549/10000000000 : ℝ)] ![(11779334697943/25000000000000 : ℝ), (21695220548009/50000000000000 : ℝ), (9492220095623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676955849/5000000000 : ℝ)|^6031 ≤ (11779334697943/25000000000000 : ℝ)^5007
        have hw : |(2676955849/5000000000 : ℝ)|=(2676955849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1249973269/2500000000 : ℝ)|^6031 ≤ (21695220548009/50000000000000 : ℝ)^5007
        have hw : |(1249973269/2500000000 : ℝ)|=(1249973269/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1415793549/10000000000 : ℝ)|^6031 ≤ (9492220095623/100000000000000 : ℝ)^5007
        have hw : |(-1415793549/10000000000 : ℝ)|=(1415793549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1766_s0_3 (p : ℝ) (hpa : (6015/1024 : ℝ) ≤ p) (hpb : p ≤ (6031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3954476411/10000000000 : ℝ)*x 0 + (149903479/500000000 : ℝ)*x 1 + (5044324053/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3954476411/10000000000 : ℝ)^6031 ≤ (6542114954773/20000000000000 : ℝ)^5007 := by
    have hnat : (3954476411 : ℕ)^6031*20000000000000^5007 ≤ 6542114954773^5007*10000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3954476411 10000000000 6542114954773 20000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (149903479/500000000 : ℝ)^6031 ≤ (11717060819057/50000000000000 : ℝ)^5007 := by
    have hnat : (149903479 : ℕ)^6031*50000000000000^5007 ≤ 11717060819057^5007*500000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      149903479 500000000 11717060819057 50000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5044324053/10000000000 : ℝ)^6031 ≤ (8771060712981/20000000000000 : ℝ)^5007 := by
    have hnat : (5044324053 : ℕ)^6031*20000000000000^5007 ≤ 8771060712981^5007*10000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5044324053 10000000000 8771060712981 20000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6031/1024 : ℝ)) 6031 5007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3954476411/10000000000 : ℝ), (149903479/500000000 : ℝ), (5044324053/10000000000 : ℝ)] ![(6542114954773/20000000000000 : ℝ), (11717060819057/50000000000000 : ℝ), (8771060712981/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3954476411/10000000000 : ℝ)|^6031 ≤ (6542114954773/20000000000000 : ℝ)^5007
        have hw : |(3954476411/10000000000 : ℝ)|=(3954476411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(149903479/500000000 : ℝ)|^6031 ≤ (11717060819057/50000000000000 : ℝ)^5007
        have hw : |(149903479/500000000 : ℝ)|=(149903479/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5044324053/10000000000 : ℝ)|^6031 ≤ (8771060712981/20000000000000 : ℝ)^5007
        have hw : |(5044324053/10000000000 : ℝ)|=(5044324053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1766_s0_4 (p : ℝ) (hpa : (6015/1024 : ℝ) ≤ p) (hpb : p ≤ (6031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-138193791/1250000000 : ℝ)*x 0 + (5014412849/10000000000 : ℝ)*x 1 + (1113885187/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (138193791/1250000000 : ℝ)^6031 ≤ (7046561391879/100000000000000 : ℝ)^5007 := by
    have hnat : (138193791 : ℕ)^6031*100000000000000^5007 ≤ 7046561391879^5007*1250000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138193791 1250000000 7046561391879 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5014412849/10000000000 : ℝ)^6031 ≤ (21771131382233/50000000000000 : ℝ)^5007 := by
    have hnat : (5014412849 : ℕ)^6031*50000000000000^5007 ≤ 21771131382233^5007*10000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5014412849 10000000000 21771131382233 50000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1113885187/2000000000 : ℝ)^6031 ≤ (12352793957397/25000000000000 : ℝ)^5007 := by
    have hnat : (1113885187 : ℕ)^6031*25000000000000^5007 ≤ 12352793957397^5007*2000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1113885187 2000000000 12352793957397 25000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6031/1024 : ℝ)) 6031 5007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-138193791/1250000000 : ℝ), (5014412849/10000000000 : ℝ), (1113885187/2000000000 : ℝ)] ![(7046561391879/100000000000000 : ℝ), (21771131382233/50000000000000 : ℝ), (12352793957397/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-138193791/1250000000 : ℝ)|^6031 ≤ (7046561391879/100000000000000 : ℝ)^5007
        have hw : |(-138193791/1250000000 : ℝ)|=(138193791/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5014412849/10000000000 : ℝ)|^6031 ≤ (21771131382233/50000000000000 : ℝ)^5007
        have hw : |(5014412849/10000000000 : ℝ)|=(5014412849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1113885187/2000000000 : ℝ)|^6031 ≤ (12352793957397/25000000000000 : ℝ)^5007
        have hw : |(1113885187/2000000000 : ℝ)|=(1113885187/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1766_s0_5 (p : ℝ) (hpa : (6015/1024 : ℝ) ≤ p) (hpb : p ≤ (6031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2599582783/5000000000 : ℝ)*x 0 + (-169251793/2000000000 : ℝ)*x 1 + (5569425933/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2599582783/5000000000 : ℝ)^6031 ≤ (1137046435281/2500000000000 : ℝ)^5007 := by
    have hnat : (2599582783 : ℕ)^6031*2500000000000^5007 ≤ 1137046435281^5007*5000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2599582783 5000000000 1137046435281 2500000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169251793/2000000000 : ℝ)^6031 ≤ (2553483379737/50000000000000 : ℝ)^5007 := by
    have hnat : (169251793 : ℕ)^6031*50000000000000^5007 ≤ 2553483379737^5007*2000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169251793 2000000000 2553483379737 50000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5569425933/10000000000 : ℝ)^6031 ≤ (6176396976027/12500000000000 : ℝ)^5007 := by
    have hnat : (5569425933 : ℕ)^6031*12500000000000^5007 ≤ 6176396976027^5007*10000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5569425933 10000000000 6176396976027 12500000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6031/1024 : ℝ)) 6031 5007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2599582783/5000000000 : ℝ), (-169251793/2000000000 : ℝ), (5569425933/10000000000 : ℝ)] ![(1137046435281/2500000000000 : ℝ), (2553483379737/50000000000000 : ℝ), (6176396976027/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2599582783/5000000000 : ℝ)|^6031 ≤ (1137046435281/2500000000000 : ℝ)^5007
        have hw : |(2599582783/5000000000 : ℝ)|=(2599582783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-169251793/2000000000 : ℝ)|^6031 ≤ (2553483379737/50000000000000 : ℝ)^5007
        have hw : |(-169251793/2000000000 : ℝ)|=(169251793/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5569425933/10000000000 : ℝ)|^6031 ≤ (6176396976027/12500000000000 : ℝ)^5007
        have hw : |(5569425933/10000000000 : ℝ)|=(5569425933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1766_s0_6 (p : ℝ) (hpa : (6015/1024 : ℝ) ≤ p) (hpb : p ≤ (6031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1039833171/2000000000 : ℝ)*x 0 + (5569425883/10000000000 : ℝ)*x 1 + (-846258621/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1039833171/2000000000 : ℝ)^6031 ≤ (11370465114107/25000000000000 : ℝ)^5007 := by
    have hnat : (1039833171 : ℕ)^6031*25000000000000^5007 ≤ 11370465114107^5007*2000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039833171 2000000000 11370465114107 25000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5569425883/10000000000 : ℝ)^6031 ≤ (24705587636951/50000000000000 : ℝ)^5007 := by
    have hnat : (5569425883 : ℕ)^6031*50000000000000^5007 ≤ 24705587636951^5007*10000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5569425883 10000000000 24705587636951 50000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (846258621/10000000000 : ℝ)^6031 ≤ (1276741064739/25000000000000 : ℝ)^5007 := by
    have hnat : (846258621 : ℕ)^6031*25000000000000^5007 ≤ 1276741064739^5007*10000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      846258621 10000000000 1276741064739 25000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6031/1024 : ℝ)) 6031 5007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1039833171/2000000000 : ℝ), (5569425883/10000000000 : ℝ), (-846258621/10000000000 : ℝ)] ![(11370465114107/25000000000000 : ℝ), (24705587636951/50000000000000 : ℝ), (1276741064739/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1039833171/2000000000 : ℝ)|^6031 ≤ (11370465114107/25000000000000 : ℝ)^5007
        have hw : |(1039833171/2000000000 : ℝ)|=(1039833171/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5569425883/10000000000 : ℝ)|^6031 ≤ (24705587636951/50000000000000 : ℝ)^5007
        have hw : |(5569425883/10000000000 : ℝ)|=(5569425883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-846258621/10000000000 : ℝ)|^6031 ≤ (1276741064739/25000000000000 : ℝ)^5007
        have hw : |(-846258621/10000000000 : ℝ)|=(846258621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1766_s0_7 (p : ℝ) (hpa : (6015/1024 : ℝ) ≤ p) (hpb : p ≤ (6031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3958224637/10000000000 : ℝ)*x 0 + (1248372671/2500000000 : ℝ)*x 1 + (3050491567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3958224637/10000000000 : ℝ)^6031 ≤ (16373961878097/50000000000000 : ℝ)^5007 := by
    have hnat : (3958224637 : ℕ)^6031*50000000000000^5007 ≤ 16373961878097^5007*10000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3958224637 10000000000 16373961878097 50000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1248372671/2500000000 : ℝ)^6031 ≤ (43323525021417/100000000000000 : ℝ)^5007 := by
    have hnat : (1248372671 : ℕ)^6031*100000000000000^5007 ≤ 43323525021417^5007*2500000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1248372671 2500000000 43323525021417 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3050491567/10000000000 : ℝ)^6031 ≤ (11964275606509/50000000000000 : ℝ)^5007 := by
    have hnat : (3050491567 : ℕ)^6031*50000000000000^5007 ≤ 11964275606509^5007*10000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3050491567 10000000000 11964275606509 50000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6031/1024 : ℝ)) 6031 5007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3958224637/10000000000 : ℝ), (1248372671/2500000000 : ℝ), (3050491567/10000000000 : ℝ)] ![(16373961878097/50000000000000 : ℝ), (43323525021417/100000000000000 : ℝ), (11964275606509/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3958224637/10000000000 : ℝ)|^6031 ≤ (16373961878097/50000000000000 : ℝ)^5007
        have hw : |(3958224637/10000000000 : ℝ)|=(3958224637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1248372671/2500000000 : ℝ)|^6031 ≤ (43323525021417/100000000000000 : ℝ)^5007
        have hw : |(1248372671/2500000000 : ℝ)|=(1248372671/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3050491567/10000000000 : ℝ)|^6031 ≤ (11964275606509/50000000000000 : ℝ)^5007
        have hw : |(3050491567/10000000000 : ℝ)|=(3050491567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1766_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6015/1024 : ℝ) ≤ p) (hpb : p ≤ (6031/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11252043/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (3653/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9997/50000 : ℝ)*pair X 0 0 := by
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
  have base37 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 1 2+(1 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 2).2]
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
  have hpowlo : (0 : ℝ) ^ (6015/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^6015 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^6015*1^1024 ≤ 0^1024*1^6015 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 6015 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 6015 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (6015/1024 : ℝ) ≤ (91943505515175289/20000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^6015 ≤ (91943505515175289/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^6015*20000000000000000000^1024 ≤ 91943505515175289^1024*5^6015 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 91943505515175289 20000000000000000000 6015 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (91943505515175289/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 6015 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (6015/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^6015 := by
      have hnat : (1 : ℕ)^1024*1^6015 ≤ 1^6015*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 6015 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 6015 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20091943505515175289/20000000000000000000 : ℝ) ≤ (2501952848740977/2500000000000000 : ℝ) ^ (6015/1024 : ℝ) := by
    have hpowers : (20091943505515175289/20000000000000000000 : ℝ)^1024 ≤ (2501952848740977/2500000000000000 : ℝ)^6015 := by
      have hnat : (20091943505515175289 : ℕ)^1024*2500000000000000^6015 ≤ 2501952848740977^6015*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20091943505515175289 20000000000000000000 2501952848740977 2500000000000000 1024 6015 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2501952848740977/2500000000000000 : ℝ)) (X := (20091943505515175289/20000000000000000000 : ℝ)) (by norm_num) 6015 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10091943505515175289/10000000000000000000 : ℝ) ≤ (1251952848740977/1250000000000000 : ℝ) ^ (6015/1024 : ℝ) := by
    have hpowers : (10091943505515175289/10000000000000000000 : ℝ)^1024 ≤ (1251952848740977/1250000000000000 : ℝ)^6015 := by
      have hnat : (10091943505515175289 : ℕ)^1024*1250000000000000^6015 ≤ 1251952848740977^6015*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10091943505515175289 10000000000000000000 1251952848740977 1250000000000000 1024 6015 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1251952848740977/1250000000000000 : ℝ)) (X := (10091943505515175289/10000000000000000000 : ℝ)) (by norm_num) 6015 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(1952848740977/1000000000000000 : ℝ)*(0 : ℝ))^(6015/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(1952848740977/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(91943505515175289/20000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(1952848740977/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(6015/1024 : ℝ) := by
    rw [show (1 : ℝ)+(1952848740977/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2501952848740977/2500000000000000 : ℝ) by norm_num, show 1+(91943505515175289/20000000000000000000 : ℝ)+(0 : ℝ)=(20091943505515175289/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(91943505515175289/20000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(1952848740977/1000000000000000 : ℝ)*(2/5 : ℝ))^(6015/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(1952848740977/1000000000000000 : ℝ)*(2/5 : ℝ)=(1251952848740977/1250000000000000 : ℝ) by norm_num, show 1+2*(91943505515175289/20000000000000000000 : ℝ)=(10091943505515175289/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(1952848740977/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6015/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1952848740977/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(1952848740977/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6015/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1952848740977/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(1952848740977/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6015/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1952848740977/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-552239377/5000000000 : ℝ)*X 0 0+(5584400431/10000000000 : ℝ)*X 0 1+(2499945681/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1766_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5353915023/10000000000 : ℝ)*X 1 0+(-1415792037/10000000000 : ℝ)*X 1 1+(4999890873/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1766_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676955849/5000000000 : ℝ)*X 2 0+(1249973269/2500000000 : ℝ)*X 2 1+(-1415793549/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1766_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((3954476411/10000000000 : ℝ)*X 0 0+(149903479/500000000 : ℝ)*X 0 1+(5044324053/10000000000 : ℝ)*X 0 2+(3954476411/10000000000 : ℝ)*X 1 0+(149903479/500000000 : ℝ)*X 1 1+(5044324053/10000000000 : ℝ)*X 1 2+(3954476411/10000000000 : ℝ)*X 2 0+(149903479/500000000 : ℝ)*X 2 1+(5044324053/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1766_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-138193791/1250000000 : ℝ)*X 0 0+(5014412849/10000000000 : ℝ)*X 0 1+(1113885187/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1766_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2599582783/5000000000 : ℝ)*X 1 0+(-169251793/2000000000 : ℝ)*X 1 1+(5569425933/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1766_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1039833171/2000000000 : ℝ)*X 2 0+(5569425883/10000000000 : ℝ)*X 2 1+(-846258621/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1766_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3958224637/10000000000 : ℝ)*X 0 0+(1248372671/2500000000 : ℝ)*X 0 1+(3050491567/10000000000 : ℝ)*X 0 2+(3958224637/10000000000 : ℝ)*X 1 0+(1248372671/2500000000 : ℝ)*X 1 1+(3050491567/10000000000 : ℝ)*X 1 2+(3958224637/10000000000 : ℝ)*X 2 0+(1248372671/2500000000 : ℝ)*X 2 1+(3050491567/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1766_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (155888040874775744667579/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (435847457/100000000000000 : ℝ)*(base1) + (752227577/50000000000000 : ℝ)*(base19) + (20645379/6250000000000 : ℝ)*(base23) + (325311373/100000000000000 : ℝ)*(upper3) + (1099773314416597/100000000000000 : ℝ)*(major0) + (1099773314416597/100000000000000 : ℝ)*(major1) + (1099773314416597/100000000000000 : ℝ)*(major2) + (342169052784503/20000000000000 : ℝ)*(sp0) + (1710845524596179/100000000000000 : ℝ)*(sp1) + (427710709191567/25000000000000 : ℝ)*(sp2) + (97739609310621/20000000000000 : ℝ)*(sp3) + (88039051/4000000000000 : ℝ)*(sp4) + (3861959001/100000000000000 : ℝ)*(sp6) + (227382643/25000000000000 : ℝ)*(sp7) + (97739878386227/20000000000000 : ℝ)*(f.failure) + (1710847029051333/100000000000000 : ℝ)*(f.sum) + (128305022345269/50000000000000000000000000000 : ℝ)*base65 + (626714863995269/100000000000000000000000000000 : ℝ)*base67 + (313961878395269/100000000000000000000000000000 : ℝ)*base69 + (500524159195269/100000000000000000000000000000 : ℝ)*base71 + (144744196545269/50000000000000000000000000000 : ℝ)*base73 + (203735207195269/100000000000000000000000000000 : ℝ)*base75 + (561562478995269/100000000000000000000000000000 : ℝ)*base77 + (63012682895269/100000000000000000000000000000 : ℝ)*base79 + (38413815995269/50000000000000000000000000000 : ℝ)*base81 + (188239/100000000000000000000 : ℝ)*base90 + (188239/100000000000000000000 : ℝ)*base92 + (188239/100000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (70967934811098103090617/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2860989/2500000000000 : ℝ)*(base19) + (50749083/20000000000000 : ℝ)*(base23) + (14378733/12500000000000 : ℝ)*(base32) + (25983311/100000000000000 : ℝ)*(base37) + (4867117/12500000000000 : ℝ)*(upper3) + (579106815667369/50000000000000 : ℝ)*(major0) + (579106815667369/50000000000000 : ℝ)*(major1) + (579106815667369/50000000000000 : ℝ)*(major2) + (200268747/100000000000000 : ℝ)*(sp1) + (47367469/3125000000000 : ℝ)*(sp2) + (1801759017855083/100000000000000 : ℝ)*(sp4) + (225219837893347/12500000000000 : ℝ)*(sp5) + (90087862417533/5000000000000 : ℝ)*(sp6) + (514668009177301/100000000000000 : ℝ)*(sp7) + (128667037547619/25000000000000 : ℝ)*(f.failure) + (1801759017855083/100000000000000 : ℝ)*(f.sum) + (30136515745487/25000000000000000000000000000 : ℝ)*base66 + (38023404529513/50000000000000000000000000000 : ℝ)*base67 + (410835241520487/50000000000000000000000000000 : ℝ)*base70 + (134011365379513/50000000000000000000000000000 : ℝ)*base71 + (939063045487/25000000000000000000000000000 : ℝ)*base74 + (205855768220487/50000000000000000000000000000 : ℝ)*base76 + (65738058970487/50000000000000000000000000000 : ℝ)*base78 + (276383408479513/50000000000000000000000000000 : ℝ)*base79 + (176011363295487/25000000000000000000000000000 : ℝ)*base82 + (1035617/125000000000000000000 : ℝ)*base89 + (1035617/125000000000000000000 : ℝ)*base91 + (1035617/125000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1766_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6015/1024 : ℝ) ≤ p) (hpb : p ≤ (6031/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11252043/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3653/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9997/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1766_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1766_s1_0 (p : ℝ) (hpa : (6015/1024 : ℝ) ≤ p) (hpb : p ≤ (6031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1137994817/10000000000 : ℝ)*x 0 + (136948541/250000000 : ℝ)*x 1 + (5083741287/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1137994817/10000000000 : ℝ)^6031 ≤ (729639033443/10000000000000 : ℝ)^5007 := by
    have hnat : (1137994817 : ℕ)^6031*10000000000000^5007 ≤ 729639033443^5007*10000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1137994817 10000000000 729639033443 10000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (136948541/250000000 : ℝ)^6031 ≤ (189199994051/390625000000 : ℝ)^5007 := by
    have hnat : (136948541 : ℕ)^6031*390625000000^5007 ≤ 189199994051^5007*250000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136948541 250000000 189199994051 390625000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5083741287/10000000000 : ℝ)^6031 ≤ (44268411175079/100000000000000 : ℝ)^5007 := by
    have hnat : (5083741287 : ℕ)^6031*100000000000000^5007 ≤ 44268411175079^5007*10000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5083741287 10000000000 44268411175079 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6031/1024 : ℝ)) 6031 5007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1137994817/10000000000 : ℝ), (136948541/250000000 : ℝ), (5083741287/10000000000 : ℝ)] ![(729639033443/10000000000000 : ℝ), (189199994051/390625000000 : ℝ), (44268411175079/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1137994817/10000000000 : ℝ)|^6031 ≤ (729639033443/10000000000000 : ℝ)^5007
        have hw : |(-1137994817/10000000000 : ℝ)|=(1137994817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(136948541/250000000 : ℝ)|^6031 ≤ (189199994051/390625000000 : ℝ)^5007
        have hw : |(136948541/250000000 : ℝ)|=(136948541/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5083741287/10000000000 : ℝ)|^6031 ≤ (44268411175079/100000000000000 : ℝ)^5007
        have hw : |(5083741287/10000000000 : ℝ)|=(5083741287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1766_s1_1 (p : ℝ) (hpa : (6015/1024 : ℝ) ≤ p) (hpb : p ≤ (6031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5325685851/10000000000 : ℝ)*x 0 + (-1343725907/10000000000 : ℝ)*x 1 + (1016748213/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5325685851/10000000000 : ℝ)^6031 ≤ (23409147858157/50000000000000 : ℝ)^5007 := by
    have hnat : (5325685851 : ℕ)^6031*50000000000000^5007 ≤ 23409147858157^5007*10000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5325685851 10000000000 23409147858157 50000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1343725907/10000000000 : ℝ)^6031 ≤ (8913295425513/100000000000000 : ℝ)^5007 := by
    have hnat : (1343725907 : ℕ)^6031*100000000000000^5007 ≤ 8913295425513^5007*10000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343725907 10000000000 8913295425513 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1016748213/2000000000 : ℝ)^6031 ≤ (8853681769317/20000000000000 : ℝ)^5007 := by
    have hnat : (1016748213 : ℕ)^6031*20000000000000^5007 ≤ 8853681769317^5007*2000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1016748213 2000000000 8853681769317 20000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6031/1024 : ℝ)) 6031 5007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5325685851/10000000000 : ℝ), (-1343725907/10000000000 : ℝ), (1016748213/2000000000 : ℝ)] ![(23409147858157/50000000000000 : ℝ), (8913295425513/100000000000000 : ℝ), (8853681769317/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5325685851/10000000000 : ℝ)|^6031 ≤ (23409147858157/50000000000000 : ℝ)^5007
        have hw : |(5325685851/10000000000 : ℝ)|=(5325685851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1343725907/10000000000 : ℝ)|^6031 ≤ (8913295425513/100000000000000 : ℝ)^5007
        have hw : |(-1343725907/10000000000 : ℝ)|=(1343725907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1016748213/2000000000 : ℝ)|^6031 ≤ (8853681769317/20000000000000 : ℝ)^5007
        have hw : |(1016748213/2000000000 : ℝ)|=(1016748213/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1766_s1_2 (p : ℝ) (hpa : (6015/1024 : ℝ) ≤ p) (hpb : p ≤ (6031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5325685437/10000000000 : ℝ)*x 0 + (5083741463/10000000000 : ℝ)*x 1 + (-335931483/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5325685437/10000000000 : ℝ)^6031 ≤ (46818291332499/100000000000000 : ℝ)^5007 := by
    have hnat : (5325685437 : ℕ)^6031*100000000000000^5007 ≤ 46818291332499^5007*10000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5325685437 10000000000 46818291332499 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5083741463/10000000000 : ℝ)^6031 ≤ (44268413021093/100000000000000 : ℝ)^5007 := by
    have hnat : (5083741463 : ℕ)^6031*100000000000000^5007 ≤ 44268413021093^5007*10000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5083741463 10000000000 44268413021093 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (335931483/2500000000 : ℝ)^6031 ≤ (8913295625259/100000000000000 : ℝ)^5007 := by
    have hnat : (335931483 : ℕ)^6031*100000000000000^5007 ≤ 8913295625259^5007*2500000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335931483 2500000000 8913295625259 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6031/1024 : ℝ)) 6031 5007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5325685437/10000000000 : ℝ), (5083741463/10000000000 : ℝ), (-335931483/2500000000 : ℝ)] ![(46818291332499/100000000000000 : ℝ), (44268413021093/100000000000000 : ℝ), (8913295625259/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5325685437/10000000000 : ℝ)|^6031 ≤ (46818291332499/100000000000000 : ℝ)^5007
        have hw : |(5325685437/10000000000 : ℝ)|=(5325685437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5083741463/10000000000 : ℝ)|^6031 ≤ (44268413021093/100000000000000 : ℝ)^5007
        have hw : |(5083741463/10000000000 : ℝ)|=(5083741463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-335931483/2500000000 : ℝ)|^6031 ≤ (8913295625259/100000000000000 : ℝ)^5007
        have hw : |(-335931483/2500000000 : ℝ)|=(335931483/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1766_s1_3 (p : ℝ) (hpa : (6015/1024 : ℝ) ≤ p) (hpb : p ≤ (6031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (997156077/2500000000 : ℝ)*x 0 + (3328827713/10000000000 : ℝ)*x 1 + (4708850947/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (997156077/2500000000 : ℝ)^6031 ≤ (33051106304711/100000000000000 : ℝ)^5007 := by
    have hnat : (997156077 : ℕ)^6031*100000000000000^5007 ≤ 33051106304711^5007*2500000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      997156077 2500000000 33051106304711 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3328827713/10000000000 : ℝ)^6031 ≤ (13291174559731/50000000000000 : ℝ)^5007 := by
    have hnat : (3328827713 : ℕ)^6031*50000000000000^5007 ≤ 13291174559731^5007*10000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3328827713 10000000000 13291174559731 50000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4708850947/10000000000 : ℝ)^6031 ≤ (40366544564513/100000000000000 : ℝ)^5007 := by
    have hnat : (4708850947 : ℕ)^6031*100000000000000^5007 ≤ 40366544564513^5007*10000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4708850947 10000000000 40366544564513 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6031/1024 : ℝ)) 6031 5007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(997156077/2500000000 : ℝ), (3328827713/10000000000 : ℝ), (4708850947/10000000000 : ℝ)] ![(33051106304711/100000000000000 : ℝ), (13291174559731/50000000000000 : ℝ), (40366544564513/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(997156077/2500000000 : ℝ)|^6031 ≤ (33051106304711/100000000000000 : ℝ)^5007
        have hw : |(997156077/2500000000 : ℝ)|=(997156077/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3328827713/10000000000 : ℝ)|^6031 ≤ (13291174559731/50000000000000 : ℝ)^5007
        have hw : |(3328827713/10000000000 : ℝ)|=(3328827713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4708850947/10000000000 : ℝ)|^6031 ≤ (40366544564513/100000000000000 : ℝ)^5007
        have hw : |(4708850947/10000000000 : ℝ)|=(4708850947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1766_s1_4 (p : ℝ) (hpa : (6015/1024 : ℝ) ≤ p) (hpb : p ≤ (6031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1138322237/10000000000 : ℝ)*x 0 + (2545183533/5000000000 : ℝ)*x 1 + (5471177133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1138322237/10000000000 : ℝ)^6031 ≤ (3649459517751/50000000000000 : ℝ)^5007 := by
    have hnat : (1138322237 : ℕ)^6031*50000000000000^5007 ≤ 3649459517751^5007*10000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1138322237 10000000000 3649459517751 50000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2545183533/5000000000 : ℝ)^6031 ≤ (692779942701/1562500000000 : ℝ)^5007 := by
    have hnat : (2545183533 : ℕ)^6031*1562500000000^5007 ≤ 692779942701^5007*5000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2545183533 5000000000 692779942701 1562500000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5471177133/10000000000 : ℝ)^6031 ≤ (48363164613481/100000000000000 : ℝ)^5007 := by
    have hnat : (5471177133 : ℕ)^6031*100000000000000^5007 ≤ 48363164613481^5007*10000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5471177133 10000000000 48363164613481 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6031/1024 : ℝ)) 6031 5007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1138322237/10000000000 : ℝ), (2545183533/5000000000 : ℝ), (5471177133/10000000000 : ℝ)] ![(3649459517751/50000000000000 : ℝ), (692779942701/1562500000000 : ℝ), (48363164613481/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1138322237/10000000000 : ℝ)|^6031 ≤ (3649459517751/50000000000000 : ℝ)^5007
        have hw : |(-1138322237/10000000000 : ℝ)|=(1138322237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2545183533/5000000000 : ℝ)|^6031 ≤ (692779942701/1562500000000 : ℝ)^5007
        have hw : |(2545183533/5000000000 : ℝ)|=(2545183533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5471177133/10000000000 : ℝ)|^6031 ≤ (48363164613481/100000000000000 : ℝ)^5007
        have hw : |(5471177133/10000000000 : ℝ)|=(5471177133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1766_s1_5 (p : ℝ) (hpa : (6015/1024 : ℝ) ≤ p) (hpb : p ≤ (6031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1044346959/2000000000 : ℝ)*x 0 + (-38251599/400000000 : ℝ)*x 1 + (5471176891/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1044346959/2000000000 : ℝ)^6031 ≤ (45719774435767/100000000000000 : ℝ)^5007 := by
    have hnat : (1044346959 : ℕ)^6031*100000000000000^5007 ≤ 45719774435767^5007*2000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044346959 2000000000 45719774435767 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (38251599/400000000 : ℝ)^6031 ≤ (5917063505457/100000000000000 : ℝ)^5007 := by
    have hnat : (38251599 : ℕ)^6031*100000000000000^5007 ≤ 5917063505457^5007*400000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38251599 400000000 5917063505457 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5471176891/10000000000 : ℝ)^6031 ≤ (24181581018399/50000000000000 : ℝ)^5007 := by
    have hnat : (5471176891 : ℕ)^6031*50000000000000^5007 ≤ 24181581018399^5007*10000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5471176891 10000000000 24181581018399 50000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6031/1024 : ℝ)) 6031 5007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1044346959/2000000000 : ℝ), (-38251599/400000000 : ℝ), (5471176891/10000000000 : ℝ)] ![(45719774435767/100000000000000 : ℝ), (5917063505457/100000000000000 : ℝ), (24181581018399/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1044346959/2000000000 : ℝ)|^6031 ≤ (45719774435767/100000000000000 : ℝ)^5007
        have hw : |(1044346959/2000000000 : ℝ)|=(1044346959/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-38251599/400000000 : ℝ)|^6031 ≤ (5917063505457/100000000000000 : ℝ)^5007
        have hw : |(-38251599/400000000 : ℝ)|=(38251599/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5471176891/10000000000 : ℝ)|^6031 ≤ (24181581018399/50000000000000 : ℝ)^5007
        have hw : |(5471176891/10000000000 : ℝ)|=(5471176891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1766_s1_6 (p : ℝ) (hpa : (6015/1024 : ℝ) ≤ p) (hpb : p ≤ (6031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (522173489/1000000000 : ℝ)*x 0 + (5471176903/10000000000 : ℝ)*x 1 + (-29884057/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (522173489/1000000000 : ℝ)^6031 ≤ (11429943859417/25000000000000 : ℝ)^5007 := by
    have hnat : (522173489 : ℕ)^6031*25000000000000^5007 ≤ 11429943859417^5007*1000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522173489 1000000000 11429943859417 25000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5471176903/10000000000 : ℝ)^6031 ≤ (48363162164567/100000000000000 : ℝ)^5007 := by
    have hnat : (5471176903 : ℕ)^6031*100000000000000^5007 ≤ 48363162164567^5007*10000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5471176903 10000000000 48363162164567 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (29884057/312500000 : ℝ)^6031 ≤ (5917062380061/100000000000000 : ℝ)^5007 := by
    have hnat : (29884057 : ℕ)^6031*100000000000000^5007 ≤ 5917062380061^5007*312500000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      29884057 312500000 5917062380061 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6031/1024 : ℝ)) 6031 5007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(522173489/1000000000 : ℝ), (5471176903/10000000000 : ℝ), (-29884057/312500000 : ℝ)] ![(11429943859417/25000000000000 : ℝ), (48363162164567/100000000000000 : ℝ), (5917062380061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(522173489/1000000000 : ℝ)|^6031 ≤ (11429943859417/25000000000000 : ℝ)^5007
        have hw : |(522173489/1000000000 : ℝ)|=(522173489/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5471176903/10000000000 : ℝ)|^6031 ≤ (48363162164567/100000000000000 : ℝ)^5007
        have hw : |(5471176903/10000000000 : ℝ)|=(5471176903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-29884057/312500000 : ℝ)|^6031 ≤ (5917062380061/100000000000000 : ℝ)^5007
        have hw : |(-29884057/312500000 : ℝ)|=(29884057/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1766_s1_7 (p : ℝ) (hpa : (6015/1024 : ℝ) ≤ p) (hpb : p ≤ (6031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1994885353/5000000000 : ℝ)*x 0 + (4685655611/10000000000 : ℝ)*x 1 + (3352508677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1994885353/5000000000 : ℝ)^6031 ≤ (16531274426963/50000000000000 : ℝ)^5007 := by
    have hnat : (1994885353 : ℕ)^6031*50000000000000^5007 ≤ 16531274426963^5007*5000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1994885353 5000000000 16531274426963 50000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4685655611/10000000000 : ℝ)^6031 ≤ (20063578954469/50000000000000 : ℝ)^5007 := by
    have hnat : (4685655611 : ℕ)^6031*50000000000000^5007 ≤ 20063578954469^5007*10000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4685655611 10000000000 20063578954469 50000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3352508677/10000000000 : ℝ)^6031 ≤ (13405146613739/50000000000000 : ℝ)^5007 := by
    have hnat : (3352508677 : ℕ)^6031*50000000000000^5007 ≤ 13405146613739^5007*10000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3352508677 10000000000 13405146613739 50000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6031/1024 : ℝ)) 6031 5007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1994885353/5000000000 : ℝ), (4685655611/10000000000 : ℝ), (3352508677/10000000000 : ℝ)] ![(16531274426963/50000000000000 : ℝ), (20063578954469/50000000000000 : ℝ), (13405146613739/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1994885353/5000000000 : ℝ)|^6031 ≤ (16531274426963/50000000000000 : ℝ)^5007
        have hw : |(1994885353/5000000000 : ℝ)|=(1994885353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4685655611/10000000000 : ℝ)|^6031 ≤ (20063578954469/50000000000000 : ℝ)^5007
        have hw : |(4685655611/10000000000 : ℝ)|=(4685655611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3352508677/10000000000 : ℝ)|^6031 ≤ (13405146613739/50000000000000 : ℝ)^5007
        have hw : |(3352508677/10000000000 : ℝ)|=(3352508677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1766_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6015/1024 : ℝ) ≤ p) (hpb : p ≤ (6031/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11252043/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9997/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3653/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (4593/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8851/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9997/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3653/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9997/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3653/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9997/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3653/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9997/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3653/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9997/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3653/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9997/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3653/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3653/50000 : ℝ) ^ (6015/1024 : ℝ) ≤ (2643247009947/12500000000000000000 : ℝ) := by
    have hpowers : (3653/50000 : ℝ)^6015 ≤ (2643247009947/12500000000000000000 : ℝ)^1024 := by
      have hnat : (3653 : ℕ)^6015*12500000000000000000^1024 ≤ 2643247009947^1024*50000^6015 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3653 50000 2643247009947 12500000000000000000 6015 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3653/50000 : ℝ)) (X := (2643247009947/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 6015 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (9997/50000 : ℝ) ^ (6015/1024 : ℝ) ≤ (7824712344905459/100000000000000000000 : ℝ) := by
    have hpowers : (9997/50000 : ℝ)^6015 ≤ (7824712344905459/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9997 : ℕ)^6015*100000000000000000000^1024 ≤ 7824712344905459^1024*50000^6015 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9997 50000 7824712344905459 100000000000000000000 6015 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9997/50000 : ℝ)) (X := (7824712344905459/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 6015 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250002643247009947/6250000000000000000 : ℝ) ≤ (1250000089997821/1250000000000000 : ℝ) ^ (6015/1024 : ℝ) := by
    have hpowers : (6250002643247009947/6250000000000000000 : ℝ)^1024 ≤ (1250000089997821/1250000000000000 : ℝ)^6015 := by
      have hnat : (6250002643247009947 : ℕ)^1024*1250000000000000^6015 ≤ 1250000089997821^6015*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250002643247009947 6250000000000000000 1250000089997821 1250000000000000 1024 6015 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250000089997821/1250000000000000 : ℝ)) (X := (6250002643247009947/6250000000000000000 : ℝ)) (by norm_num) 6015 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20001569171664197007/20000000000000000000 : ℝ) ≤ (10000133564379293/10000000000000000 : ℝ) ^ (6015/1024 : ℝ) := by
    have hpowers : (20001569171664197007/20000000000000000000 : ℝ)^1024 ≤ (10000133564379293/10000000000000000 : ℝ)^6015 := by
      have hnat : (20001569171664197007 : ℕ)^1024*10000000000000000^6015 ≤ 10000133564379293^6015*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20001569171664197007 20000000000000000000 10000133564379293 10000000000000000 1024 6015 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000133564379293/10000000000000000 : ℝ)) (X := (20001569171664197007/20000000000000000000 : ℝ)) (by norm_num) 6015 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50007824712344905459/50000000000000000000 : ℝ) ≤ (5000133204388009/5000000000000000 : ℝ) ^ (6015/1024 : ℝ) := by
    have hpowers : (50007824712344905459/50000000000000000000 : ℝ)^1024 ≤ (5000133204388009/5000000000000000 : ℝ)^6015 := by
      have hnat : (50007824712344905459 : ℕ)^1024*5000000000000000^6015 ≤ 5000133204388009^6015*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50007824712344905459 50000000000000000000 5000133204388009 5000000000000000 1024 6015 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000133204388009/5000000000000000 : ℝ)) (X := (50007824712344905459/50000000000000000000 : ℝ)) (by norm_num) 6015 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2643247009947/12500000000000000000 : ℝ) ≤ ((2439962846400266867/2440000000000000000 : ℝ)+2*(5313775869/50752000000000 : ℝ)*(3653/50000 : ℝ))^(6015/1024 : ℝ) := by
    rw [show (2439962846400266867/2440000000000000000 : ℝ)+2*(5313775869/50752000000000 : ℝ)*(3653/50000 : ℝ)=(1250000089997821/1250000000000000 : ℝ) by norm_num, show 1+2*(2643247009947/12500000000000000000 : ℝ)=(6250002643247009947/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7824712344905459/100000000000000000000 : ℝ)+(2643247009947/12500000000000000000 : ℝ) ≤ ((2439962846400266867/2440000000000000000 : ℝ)+(5313775869/50752000000000 : ℝ)*((9997/50000 : ℝ)+(3653/50000 : ℝ)))^(6015/1024 : ℝ) := by
    rw [show (2439962846400266867/2440000000000000000 : ℝ)+(5313775869/50752000000000 : ℝ)*((9997/50000 : ℝ)+(3653/50000 : ℝ))=(10000133564379293/10000000000000000 : ℝ) by norm_num, show 1+(7824712344905459/100000000000000000000 : ℝ)+(2643247009947/12500000000000000000 : ℝ)=(20001569171664197007/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7824712344905459/100000000000000000000 : ℝ) ≤ ((2439962846400266867/2440000000000000000 : ℝ)+2*(5313775869/50752000000000 : ℝ)*(9997/50000 : ℝ))^(6015/1024 : ℝ) := by
    rw [show (2439962846400266867/2440000000000000000 : ℝ)+2*(5313775869/50752000000000 : ℝ)*(9997/50000 : ℝ)=(5000133204388009/5000000000000000 : ℝ) by norm_num, show 1+2*(7824712344905459/100000000000000000000 : ℝ)=(50007824712344905459/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2439962846400266867/2440000000000000000 : ℝ)*(X 1 0+X 2 0)+(5313775869/50752000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6015/1024 : ℝ)) (lo := (3653/50000 : ℝ)) (hi := (9997/50000 : ℝ)) (c := (2439962846400266867/2440000000000000000 : ℝ)) (alpha := (5313775869/50752000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2439962846400266867/2440000000000000000 : ℝ)*(X 0 1+X 2 1)+(5313775869/50752000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6015/1024 : ℝ)) (lo := (3653/50000 : ℝ)) (hi := (9997/50000 : ℝ)) (c := (2439962846400266867/2440000000000000000 : ℝ)) (alpha := (5313775869/50752000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2439962846400266867/2440000000000000000 : ℝ)*(X 0 2+X 1 2)+(5313775869/50752000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6015/1024 : ℝ)) (lo := (3653/50000 : ℝ)) (hi := (9997/50000 : ℝ)) (c := (2439962846400266867/2440000000000000000 : ℝ)) (alpha := (5313775869/50752000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1137994817/10000000000 : ℝ)*X 0 0+(136948541/250000000 : ℝ)*X 0 1+(5083741287/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1766_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5325685851/10000000000 : ℝ)*X 1 0+(-1343725907/10000000000 : ℝ)*X 1 1+(1016748213/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1766_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5325685437/10000000000 : ℝ)*X 2 0+(5083741463/10000000000 : ℝ)*X 2 1+(-335931483/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1766_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((997156077/2500000000 : ℝ)*X 0 0+(3328827713/10000000000 : ℝ)*X 0 1+(4708850947/10000000000 : ℝ)*X 0 2+(997156077/2500000000 : ℝ)*X 1 0+(3328827713/10000000000 : ℝ)*X 1 1+(4708850947/10000000000 : ℝ)*X 1 2+(997156077/2500000000 : ℝ)*X 2 0+(3328827713/10000000000 : ℝ)*X 2 1+(4708850947/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1766_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1138322237/10000000000 : ℝ)*X 0 0+(2545183533/5000000000 : ℝ)*X 0 1+(5471177133/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1766_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1044346959/2000000000 : ℝ)*X 1 0+(-38251599/400000000 : ℝ)*X 1 1+(5471176891/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1766_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((522173489/1000000000 : ℝ)*X 2 0+(5471176903/10000000000 : ℝ)*X 2 1+(-29884057/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1766_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1994885353/5000000000 : ℝ)*X 0 0+(4685655611/10000000000 : ℝ)*X 0 1+(3352508677/10000000000 : ℝ)*X 0 2+(1994885353/5000000000 : ℝ)*X 1 0+(4685655611/10000000000 : ℝ)*X 1 1+(3352508677/10000000000 : ℝ)*X 1 2+(1994885353/5000000000 : ℝ)*X 2 0+(4685655611/10000000000 : ℝ)*X 2 1+(3352508677/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1766_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3969753478042064952159/488000000000000000000000000 : ℝ) := by norm_num
    linear_combination (487633999/50000000000000 : ℝ)*(base19) + (88530059/12500000000000 : ℝ)*(base23) + (18593599/50000000000000 : ℝ)*(lower2) + (91122367/50000000000000 : ℝ)*(upper3) + (9497689/10000000000000 : ℝ)*(upper5) + (815356104107857/50000000000000 : ℝ)*(major0) + (815356104107857/50000000000000 : ℝ)*(major1) + (815356104107857/50000000000000 : ℝ)*(major2) + (3170985673247/125000000000 : ℝ)*(sp0) + (79274805664787/3125000000000 : ℝ)*(sp1) + (2536794048300709/100000000000000 : ℝ)*(sp2) + (181156808796581/25000000000000 : ℝ)*(sp3) + (3108971791/50000000000000 : ℝ)*(sp4) + (2153545889/100000000000000 : ℝ)*(sp7) + (181157347183053/25000000000000 : ℝ)*(f.failure) + (1268397378270591/50000000000000 : ℝ)*(f.sum) + (876891532709/488000000000000000000000000 : ℝ)*base65 + (610947263413900981/122000000000000000000000000000000 : ℝ)*base68 + (30298805138099019/122000000000000000000000000000000 : ℝ)*base69 + (22693325067900981/122000000000000000000000000000000 : ℝ)*base72 + (2968369376659/488000000000000000000000000 : ℝ)*base74 + (111523676049900981/122000000000000000000000000000000 : ℝ)*base76 + (499032934554099019/122000000000000000000000000000000 : ℝ)*base77 + (519667868276099019/122000000000000000000000000000000 : ℝ)*base79 + (947214696579/488000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (1272721/125000000000000000000 : ℝ)*base90 + (1272721/125000000000000000000 : ℝ)*base92 + (1272721/125000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1328633120055252087661613373/396500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (16463979/4000000000000 : ℝ)*(base19) + (278449277/50000000000000 : ℝ)*(base23) + (12585011/25000000000000 : ℝ)*(upper3) + (31256069/100000000000000 : ℝ)*(lower4) + (8673899/50000000000000 : ℝ)*(upper5) + (422010665213879/25000000000000 : ℝ)*(major0) + (422010665213879/25000000000000 : ℝ)*(major1) + (422010665213879/25000000000000 : ℝ)*(major2) + (1871725629/100000000000000 : ℝ)*(sp1) + (3763831533/100000000000000 : ℝ)*(sp2) + (2625980246473177/100000000000000 : ℝ)*(sp4) + (1312988981574037/50000000000000 : ℝ)*(sp5) + (262597592574309/10000000000000 : ℝ)*(sp6) + (46881560221317/6250000000000 : ℝ)*(sp7) + (46881560221317/6250000000000 : ℝ)*(f.failure) + (2625980246473177/100000000000000 : ℝ)*(f.sum) + (819739200379/3172000000000000000000000000 : ℝ)*base65 + (1709963700194087209/793000000000000000000000000000000 : ℝ)*base67 + (2882298991328912791/793000000000000000000000000000000 : ℝ)*base70 + (5292625390536912791/793000000000000000000000000000000 : ℝ)*base72 + (18375089281947/3172000000000000000000000000 : ℝ)*base73 + (1288919645217087209/793000000000000000000000000000000 : ℝ)*base75 + (2806692074247087209/793000000000000000000000000000000 : ℝ)*base77 + (3037751507163087209/793000000000000000000000000000000 : ℝ)*base79 + (6979739169161/3172000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (349369/31250000000000000000 : ℝ)*base90 + (349369/31250000000000000000 : ℝ)*base92 + (349369/31250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1766_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6015/1024 : ℝ) ≤ p) (hpb : p ≤ (6031/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11252043/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9997/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3653/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4593/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8851/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1766_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1766_s2_0 (p : ℝ) (hpa : (6015/1024 : ℝ) ≤ p) (hpb : p ≤ (6031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1138496517/10000000000 : ℝ)*x 0 + (1095264967/2000000000 : ℝ)*x 1 + (5085013473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1138496517/10000000000 : ℝ)^6031 ≤ (7300265079989/100000000000000 : ℝ)^5007 := by
    have hnat : (1138496517 : ℕ)^6031*100000000000000^5007 ≤ 7300265079989^5007*10000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1138496517 10000000000 7300265079989 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1095264967/2000000000 : ℝ)^6031 ≤ (24208989896553/50000000000000 : ℝ)^5007 := by
    have hnat : (1095264967 : ℕ)^6031*50000000000000^5007 ≤ 24208989896553^5007*2000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095264967 2000000000 24208989896553 50000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5085013473/10000000000 : ℝ)^6031 ≤ (44281755111239/100000000000000 : ℝ)^5007 := by
    have hnat : (5085013473 : ℕ)^6031*100000000000000^5007 ≤ 44281755111239^5007*10000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5085013473 10000000000 44281755111239 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6031/1024 : ℝ)) 6031 5007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1138496517/10000000000 : ℝ), (1095264967/2000000000 : ℝ), (5085013473/10000000000 : ℝ)] ![(7300265079989/100000000000000 : ℝ), (24208989896553/50000000000000 : ℝ), (44281755111239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1138496517/10000000000 : ℝ)|^6031 ≤ (7300265079989/100000000000000 : ℝ)^5007
        have hw : |(-1138496517/10000000000 : ℝ)|=(1138496517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1095264967/2000000000 : ℝ)|^6031 ≤ (24208989896553/50000000000000 : ℝ)^5007
        have hw : |(1095264967/2000000000 : ℝ)|=(1095264967/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5085013473/10000000000 : ℝ)|^6031 ≤ (44281755111239/100000000000000 : ℝ)^5007
        have hw : |(5085013473/10000000000 : ℝ)|=(5085013473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1766_s2_1 (p : ℝ) (hpa : (6015/1024 : ℝ) ≤ p) (hpb : p ≤ (6031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5325232471/10000000000 : ℝ)*x 0 + (-671328149/5000000000 : ℝ)*x 1 + (2542506729/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5325232471/10000000000 : ℝ)^6031 ≤ (46813494952171/100000000000000 : ℝ)^5007 := by
    have hnat : (5325232471 : ℕ)^6031*100000000000000^5007 ≤ 46813494952171^5007*10000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5325232471 10000000000 46813494952171 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (671328149/5000000000 : ℝ)^6031 ≤ (4452375045803/50000000000000 : ℝ)^5007 := by
    have hnat : (671328149 : ℕ)^6031*50000000000000^5007 ≤ 4452375045803^5007*5000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671328149 5000000000 4452375045803 50000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2542506729/5000000000 : ℝ)^6031 ≤ (44281754953901/100000000000000 : ℝ)^5007 := by
    have hnat : (2542506729 : ℕ)^6031*100000000000000^5007 ≤ 44281754953901^5007*5000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2542506729 5000000000 44281754953901 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6031/1024 : ℝ)) 6031 5007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5325232471/10000000000 : ℝ), (-671328149/5000000000 : ℝ), (2542506729/5000000000 : ℝ)] ![(46813494952171/100000000000000 : ℝ), (4452375045803/50000000000000 : ℝ), (44281754953901/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5325232471/10000000000 : ℝ)|^6031 ≤ (46813494952171/100000000000000 : ℝ)^5007
        have hw : |(5325232471/10000000000 : ℝ)|=(5325232471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-671328149/5000000000 : ℝ)|^6031 ≤ (4452375045803/50000000000000 : ℝ)^5007
        have hw : |(-671328149/5000000000 : ℝ)|=(671328149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2542506729/5000000000 : ℝ)|^6031 ≤ (44281754953901/100000000000000 : ℝ)^5007
        have hw : |(2542506729/5000000000 : ℝ)|=(2542506729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1766_s2_2 (p : ℝ) (hpa : (6015/1024 : ℝ) ≤ p) (hpb : p ≤ (6031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (532523239/1000000000 : ℝ)*x 0 + (1271253353/2500000000 : ℝ)*x 1 + (-83916029/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (532523239/1000000000 : ℝ)^6031 ≤ (46813494094483/100000000000000 : ℝ)^5007 := by
    have hnat : (532523239 : ℕ)^6031*100000000000000^5007 ≤ 46813494094483^5007*1000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      532523239 1000000000 46813494094483 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1271253353/2500000000 : ℝ)^6031 ≤ (8856350894279/20000000000000 : ℝ)^5007 := by
    have hnat : (1271253353 : ℕ)^6031*20000000000000^5007 ≤ 8856350894279^5007*2500000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1271253353 2500000000 8856350894279 20000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (83916029/625000000 : ℝ)^6031 ≤ (8904751417707/100000000000000 : ℝ)^5007 := by
    have hnat : (83916029 : ℕ)^6031*100000000000000^5007 ≤ 8904751417707^5007*625000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83916029 625000000 8904751417707 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6031/1024 : ℝ)) 6031 5007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(532523239/1000000000 : ℝ), (1271253353/2500000000 : ℝ), (-83916029/625000000 : ℝ)] ![(46813494094483/100000000000000 : ℝ), (8856350894279/20000000000000 : ℝ), (8904751417707/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(532523239/1000000000 : ℝ)|^6031 ≤ (46813494094483/100000000000000 : ℝ)^5007
        have hw : |(532523239/1000000000 : ℝ)|=(532523239/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1271253353/2500000000 : ℝ)|^6031 ≤ (8856350894279/20000000000000 : ℝ)^5007
        have hw : |(1271253353/2500000000 : ℝ)|=(1271253353/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-83916029/625000000 : ℝ)|^6031 ≤ (8904751417707/100000000000000 : ℝ)^5007
        have hw : |(-83916029/625000000 : ℝ)|=(83916029/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1766_s2_3 (p : ℝ) (hpa : (6015/1024 : ℝ) ≤ p) (hpb : p ≤ (6031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3989039049/10000000000 : ℝ)*x 0 + (3333855801/10000000000 : ℝ)*x 1 + (4703764961/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3989039049/10000000000 : ℝ)^6031 ≤ (4131905735487/12500000000000 : ℝ)^5007 := by
    have hnat : (3989039049 : ℕ)^6031*12500000000000^5007 ≤ 4131905735487^5007*10000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3989039049 10000000000 4131905735487 12500000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3333855801/10000000000 : ℝ)^6031 ≤ (26630719966599/100000000000000 : ℝ)^5007 := by
    have hnat : (3333855801 : ℕ)^6031*100000000000000^5007 ≤ 26630719966599^5007*10000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3333855801 10000000000 26630719966599 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4703764961/10000000000 : ℝ)^6031 ≤ (40314034137999/100000000000000 : ℝ)^5007 := by
    have hnat : (4703764961 : ℕ)^6031*100000000000000^5007 ≤ 40314034137999^5007*10000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4703764961 10000000000 40314034137999 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6031/1024 : ℝ)) 6031 5007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3989039049/10000000000 : ℝ), (3333855801/10000000000 : ℝ), (4703764961/10000000000 : ℝ)] ![(4131905735487/12500000000000 : ℝ), (26630719966599/100000000000000 : ℝ), (40314034137999/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3989039049/10000000000 : ℝ)|^6031 ≤ (4131905735487/12500000000000 : ℝ)^5007
        have hw : |(3989039049/10000000000 : ℝ)|=(3989039049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3333855801/10000000000 : ℝ)|^6031 ≤ (26630719966599/100000000000000 : ℝ)^5007
        have hw : |(3333855801/10000000000 : ℝ)|=(3333855801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4703764961/10000000000 : ℝ)|^6031 ≤ (40314034137999/100000000000000 : ℝ)^5007
        have hw : |(4703764961/10000000000 : ℝ)|=(4703764961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1766_s2_4 (p : ℝ) (hpa : (6015/1024 : ℝ) ≤ p) (hpb : p ≤ (6031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-569408443/5000000000 : ℝ)*x 0 + (1018308511/2000000000 : ℝ)*x 1 + (5469659971/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (569408443/5000000000 : ℝ)^6031 ≤ (146054790937/2000000000000 : ℝ)^5007 := by
    have hnat : (569408443 : ℕ)^6031*2000000000000^5007 ≤ 146054790937^5007*5000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      569408443 5000000000 146054790937 2000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1018308511/2000000000 : ℝ)^6031 ≤ (44350249276313/100000000000000 : ℝ)^5007 := by
    have hnat : (1018308511 : ℕ)^6031*100000000000000^5007 ≤ 44350249276313^5007*2000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1018308511 2000000000 44350249276313 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5469659971/10000000000 : ℝ)^6031 ≤ (4834701116269/10000000000000 : ℝ)^5007 := by
    have hnat : (5469659971 : ℕ)^6031*10000000000000^5007 ≤ 4834701116269^5007*10000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5469659971 10000000000 4834701116269 10000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6031/1024 : ℝ)) 6031 5007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-569408443/5000000000 : ℝ), (1018308511/2000000000 : ℝ), (5469659971/10000000000 : ℝ)] ![(146054790937/2000000000000 : ℝ), (44350249276313/100000000000000 : ℝ), (4834701116269/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-569408443/5000000000 : ℝ)|^6031 ≤ (146054790937/2000000000000 : ℝ)^5007
        have hw : |(-569408443/5000000000 : ℝ)|=(569408443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1018308511/2000000000 : ℝ)|^6031 ≤ (44350249276313/100000000000000 : ℝ)^5007
        have hw : |(1018308511/2000000000 : ℝ)|=(1018308511/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5469659971/10000000000 : ℝ)|^6031 ≤ (4834701116269/10000000000000 : ℝ)^5007
        have hw : |(5469659971/10000000000 : ℝ)|=(5469659971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1766_s2_5 (p : ℝ) (hpa : (6015/1024 : ℝ) ≤ p) (hpb : p ≤ (6031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (522205049/1000000000 : ℝ)*x 0 + (-958009947/10000000000 : ℝ)*x 1 + (5469659991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (522205049/1000000000 : ℝ)^6031 ≤ (45723103877307/100000000000000 : ℝ)^5007 := by
    have hnat : (522205049 : ℕ)^6031*100000000000000^5007 ≤ 45723103877307^5007*1000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522205049 1000000000 45723103877307 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (958009947/10000000000 : ℝ)^6031 ≤ (59298847319/1000000000000 : ℝ)^5007 := by
    have hnat : (958009947 : ℕ)^6031*1000000000000^5007 ≤ 59298847319^5007*10000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      958009947 10000000000 59298847319 1000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5469659991/10000000000 : ℝ)^6031 ≤ (48347011375627/100000000000000 : ℝ)^5007 := by
    have hnat : (5469659991 : ℕ)^6031*100000000000000^5007 ≤ 48347011375627^5007*10000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5469659991 10000000000 48347011375627 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6031/1024 : ℝ)) 6031 5007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(522205049/1000000000 : ℝ), (-958009947/10000000000 : ℝ), (5469659991/10000000000 : ℝ)] ![(45723103877307/100000000000000 : ℝ), (59298847319/1000000000000 : ℝ), (48347011375627/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(522205049/1000000000 : ℝ)|^6031 ≤ (45723103877307/100000000000000 : ℝ)^5007
        have hw : |(522205049/1000000000 : ℝ)|=(522205049/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-958009947/10000000000 : ℝ)|^6031 ≤ (59298847319/1000000000000 : ℝ)^5007
        have hw : |(-958009947/10000000000 : ℝ)|=(958009947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5469659991/10000000000 : ℝ)|^6031 ≤ (48347011375627/100000000000000 : ℝ)^5007
        have hw : |(5469659991/10000000000 : ℝ)|=(5469659991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1766_s2_6 (p : ℝ) (hpa : (6015/1024 : ℝ) ≤ p) (hpb : p ≤ (6031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5222050467/10000000000 : ℝ)*x 0 + (1093932003/2000000000 : ℝ)*x 1 + (-191601989/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5222050467/10000000000 : ℝ)^6031 ≤ (45723103634739/100000000000000 : ℝ)^5007 := by
    have hnat : (5222050467 : ℕ)^6031*100000000000000^5007 ≤ 45723103634739^5007*10000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5222050467 10000000000 45723103634739 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1093932003/2000000000 : ℝ)^6031 ≤ (3021688226947/6250000000000 : ℝ)^5007 := by
    have hnat : (1093932003 : ℕ)^6031*6250000000000^5007 ≤ 3021688226947^5007*2000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093932003 2000000000 3021688226947 6250000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (191601989/2000000000 : ℝ)^6031 ≤ (5929884716989/100000000000000 : ℝ)^5007 := by
    have hnat : (191601989 : ℕ)^6031*100000000000000^5007 ≤ 5929884716989^5007*2000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      191601989 2000000000 5929884716989 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6031/1024 : ℝ)) 6031 5007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5222050467/10000000000 : ℝ), (1093932003/2000000000 : ℝ), (-191601989/2000000000 : ℝ)] ![(45723103634739/100000000000000 : ℝ), (3021688226947/6250000000000 : ℝ), (5929884716989/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5222050467/10000000000 : ℝ)|^6031 ≤ (45723103634739/100000000000000 : ℝ)^5007
        have hw : |(5222050467/10000000000 : ℝ)|=(5222050467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1093932003/2000000000 : ℝ)|^6031 ≤ (3021688226947/6250000000000 : ℝ)^5007
        have hw : |(1093932003/2000000000 : ℝ)|=(1093932003/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-191601989/2000000000 : ℝ)|^6031 ≤ (5929884716989/100000000000000 : ℝ)^5007
        have hw : |(-191601989/2000000000 : ℝ)|=(191601989/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1766_s2_7 (p : ℝ) (hpa : (6015/1024 : ℝ) ≤ p) (hpb : p ≤ (6031/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1995080031/5000000000 : ℝ)*x 0 + (292556759/625000000 : ℝ)*x 1 + (3357187931/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1995080031/5000000000 : ℝ)^6031 ≤ (33066435288279/100000000000000 : ℝ)^5007 := by
    have hnat : (1995080031 : ℕ)^6031*100000000000000^5007 ≤ 33066435288279^5007*5000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1995080031 5000000000 33066435288279 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (292556759/625000000 : ℝ)^6031 ≤ (8015638334677/20000000000000 : ℝ)^5007 := by
    have hnat : (292556759 : ℕ)^6031*20000000000000^5007 ≤ 8015638334677^5007*625000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      292556759 625000000 8015638334677 20000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3357187931/10000000000 : ℝ)^6031 ≤ (26855373026161/100000000000000 : ℝ)^5007 := by
    have hnat : (3357187931 : ℕ)^6031*100000000000000^5007 ≤ 26855373026161^5007*10000000000^6031 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3357187931 10000000000 26855373026161 100000000000000 6031 5007 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6031/1024 : ℝ)) 6031 5007 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1995080031/5000000000 : ℝ), (292556759/625000000 : ℝ), (3357187931/10000000000 : ℝ)] ![(33066435288279/100000000000000 : ℝ), (8015638334677/20000000000000 : ℝ), (26855373026161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1995080031/5000000000 : ℝ)|^6031 ≤ (33066435288279/100000000000000 : ℝ)^5007
        have hw : |(1995080031/5000000000 : ℝ)|=(1995080031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(292556759/625000000 : ℝ)|^6031 ≤ (8015638334677/20000000000000 : ℝ)^5007
        have hw : |(292556759/625000000 : ℝ)|=(292556759/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3357187931/10000000000 : ℝ)|^6031 ≤ (26855373026161/100000000000000 : ℝ)^5007
        have hw : |(3357187931/10000000000 : ℝ)|=(3357187931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1766_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6015/1024 : ℝ) ≤ p) (hpb : p ≤ (6031/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11252043/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8851/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4593/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (4607/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4417/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8851/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4593/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8851/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4593/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8851/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4593/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8851/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4593/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8851/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4593/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8851/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4593/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4593/50000 : ℝ) ^ (6015/1024 : ℝ) ≤ (20291792930211/25000000000000000000 : ℝ) := by
    have hpowers : (4593/50000 : ℝ)^6015 ≤ (20291792930211/25000000000000000000 : ℝ)^1024 := by
      have hnat : (4593 : ℕ)^6015*25000000000000000000^1024 ≤ 20291792930211^1024*50000^6015 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4593 50000 20291792930211 25000000000000000000 6015 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4593/50000 : ℝ)) (X := (20291792930211/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 6015 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8851/50000 : ℝ) ^ (6015/1024 : ℝ) ≤ (3827062718863343/100000000000000000000 : ℝ) := by
    have hpowers : (8851/50000 : ℝ)^6015 ≤ (3827062718863343/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8851 : ℕ)^6015*100000000000000000000^1024 ≤ 3827062718863343^1024*50000^6015 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8851 50000 3827062718863343 100000000000000000000 6015 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8851/50000 : ℝ)) (X := (3827062718863343/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 6015 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500020291792930211/12500000000000000000 : ℝ) ≤ (5000001381797637/5000000000000000 : ℝ) ^ (6015/1024 : ℝ) := by
    have hpowers : (12500020291792930211/12500000000000000000 : ℝ)^1024 ≤ (5000001381797637/5000000000000000 : ℝ)^6015 := by
      have hnat : (12500020291792930211 : ℕ)^1024*5000000000000000^6015 ≤ 5000001381797637^6015*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500020291792930211 12500000000000000000 5000001381797637 5000000000000000 1024 6015 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000001381797637/5000000000000000 : ℝ)) (X := (12500020291792930211/12500000000000000000 : ℝ)) (by norm_num) 6015 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100003908229890584187/100000000000000000000 : ℝ) ≤ (2500016633260677/2500000000000000 : ℝ) ^ (6015/1024 : ℝ) := by
    have hpowers : (100003908229890584187/100000000000000000000 : ℝ)^1024 ≤ (2500016633260677/2500000000000000 : ℝ)^6015 := by
      have hnat : (100003908229890584187 : ℕ)^1024*2500000000000000^6015 ≤ 2500016633260677^6015*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100003908229890584187 100000000000000000000 2500016633260677 2500000000000000 1024 6015 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500016633260677/2500000000000000 : ℝ)) (X := (100003908229890584187/100000000000000000000 : ℝ)) (by norm_num) 6015 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50003827062718863343/50000000000000000000 : ℝ) ≤ (5000065151245071/5000000000000000 : ℝ) ^ (6015/1024 : ℝ) := by
    have hpowers : (50003827062718863343/50000000000000000000 : ℝ)^1024 ≤ (5000065151245071/5000000000000000 : ℝ)^6015 := by
      have hnat : (50003827062718863343 : ℕ)^1024*5000000000000000^6015 ≤ 5000065151245071^6015*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50003827062718863343 50000000000000000000 5000065151245071 5000000000000000 1024 6015 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000065151245071/5000000000000000 : ℝ)) (X := (50003827062718863343/50000000000000000000 : ℝ)) (by norm_num) 6015 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(20291792930211/25000000000000000000 : ℝ) ≤ ((332651765478473031/332656250000000000 : ℝ)+2*(31884723717/425800000000000 : ℝ)*(4593/50000 : ℝ))^(6015/1024 : ℝ) := by
    rw [show (332651765478473031/332656250000000000 : ℝ)+2*(31884723717/425800000000000 : ℝ)*(4593/50000 : ℝ)=(5000001381797637/5000000000000000 : ℝ) by norm_num, show 1+2*(20291792930211/25000000000000000000 : ℝ)=(12500020291792930211/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3827062718863343/100000000000000000000 : ℝ)+(20291792930211/25000000000000000000 : ℝ) ≤ ((332651765478473031/332656250000000000 : ℝ)+(31884723717/425800000000000 : ℝ)*((8851/50000 : ℝ)+(4593/50000 : ℝ)))^(6015/1024 : ℝ) := by
    rw [show (332651765478473031/332656250000000000 : ℝ)+(31884723717/425800000000000 : ℝ)*((8851/50000 : ℝ)+(4593/50000 : ℝ))=(2500016633260677/2500000000000000 : ℝ) by norm_num, show 1+(3827062718863343/100000000000000000000 : ℝ)+(20291792930211/25000000000000000000 : ℝ)=(100003908229890584187/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3827062718863343/100000000000000000000 : ℝ) ≤ ((332651765478473031/332656250000000000 : ℝ)+2*(31884723717/425800000000000 : ℝ)*(8851/50000 : ℝ))^(6015/1024 : ℝ) := by
    rw [show (332651765478473031/332656250000000000 : ℝ)+2*(31884723717/425800000000000 : ℝ)*(8851/50000 : ℝ)=(5000065151245071/5000000000000000 : ℝ) by norm_num, show 1+2*(3827062718863343/100000000000000000000 : ℝ)=(50003827062718863343/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (332651765478473031/332656250000000000 : ℝ)*(X 1 0+X 2 0)+(31884723717/425800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6015/1024 : ℝ)) (lo := (4593/50000 : ℝ)) (hi := (8851/50000 : ℝ)) (c := (332651765478473031/332656250000000000 : ℝ)) (alpha := (31884723717/425800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (332651765478473031/332656250000000000 : ℝ)*(X 0 1+X 2 1)+(31884723717/425800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6015/1024 : ℝ)) (lo := (4593/50000 : ℝ)) (hi := (8851/50000 : ℝ)) (c := (332651765478473031/332656250000000000 : ℝ)) (alpha := (31884723717/425800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (332651765478473031/332656250000000000 : ℝ)*(X 0 2+X 1 2)+(31884723717/425800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6015/1024 : ℝ)) (lo := (4593/50000 : ℝ)) (hi := (8851/50000 : ℝ)) (c := (332651765478473031/332656250000000000 : ℝ)) (alpha := (31884723717/425800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1138496517/10000000000 : ℝ)*X 0 0+(1095264967/2000000000 : ℝ)*X 0 1+(5085013473/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1766_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5325232471/10000000000 : ℝ)*X 1 0+(-671328149/5000000000 : ℝ)*X 1 1+(2542506729/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1766_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((532523239/1000000000 : ℝ)*X 2 0+(1271253353/2500000000 : ℝ)*X 2 1+(-83916029/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1766_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((3989039049/10000000000 : ℝ)*X 0 0+(3333855801/10000000000 : ℝ)*X 0 1+(4703764961/10000000000 : ℝ)*X 0 2+(3989039049/10000000000 : ℝ)*X 1 0+(3333855801/10000000000 : ℝ)*X 1 1+(4703764961/10000000000 : ℝ)*X 1 2+(3989039049/10000000000 : ℝ)*X 2 0+(3333855801/10000000000 : ℝ)*X 2 1+(4703764961/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1766_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-569408443/5000000000 : ℝ)*X 0 0+(1018308511/2000000000 : ℝ)*X 0 1+(5469659971/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1766_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((522205049/1000000000 : ℝ)*X 1 0+(-958009947/10000000000 : ℝ)*X 1 1+(5469659991/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1766_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5222050467/10000000000 : ℝ)*X 2 0+(1093932003/2000000000 : ℝ)*X 2 1+(-191601989/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1766_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1995080031/5000000000 : ℝ)*X 0 0+(292556759/625000000 : ℝ)*X 0 1+(3357187931/10000000000 : ℝ)*X 0 2+(1995080031/5000000000 : ℝ)*X 1 0+(292556759/625000000 : ℝ)*X 1 1+(3357187931/10000000000 : ℝ)*X 1 2+(1995080031/5000000000 : ℝ)*X 2 0+(292556759/625000000 : ℝ)*X 2 1+(3357187931/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1766_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18650259065686946530207377/1663281250000000000000000000000 : ℝ) := by norm_num
    linear_combination (809351883/50000000000000 : ℝ)*(base19) + (711385453/50000000000000 : ℝ)*(base23) + (83638977/100000000000000 : ℝ)*(lower2) + (168494833/50000000000000 : ℝ)*(upper3) + (32878601/25000000000000 : ℝ)*(upper5) + (164275926016961/10000000000000 : ℝ)*(major0) + (164275926016961/10000000000000 : ℝ)*(major1) + (164275926016961/10000000000000 : ℝ)*(major2) + (2555523661679017/100000000000000 : ℝ)*(sp0) + (638883466495101/25000000000000 : ℝ)*(sp1) + (159720878869579/6250000000000 : ℝ)*(sp2) + (729978465831319/100000000000000 : ℝ)*(sp3) + (369468911/3125000000000 : ℝ)*(sp4) + (419605933/10000000000000 : ℝ)*(sp7) + (729982661890649/100000000000000 : ℝ)*(f.failure) + (2555535484684169/100000000000000 : ℝ)*(f.sum) + (2986406705767/2129000000000000000000000000 : ℝ)*base65 + (91648046550768289/13306250000000000000000000000000 : ℝ)*base67 + (99035931658193289/13306250000000000000000000000000 : ℝ)*base69 + (84055410071087039/13306250000000000000000000000000 : ℝ)*base71 + (2516828841713/1064500000000000000000000000 : ℝ)*base74 + (42498796088500461/13306250000000000000000000000000 : ℝ)*base76 + (94794582713562039/13306250000000000000000000000000 : ℝ)*base77 + (12579360120962961/13306250000000000000000000000000 : ℝ)*base80 + (24873119219/53225000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (6154093/500000000000000000000 : ℝ)*base90 + (6154093/500000000000000000000 : ℝ)*base92 + (6154093/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (37004795919737098922798313/3326562500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1385810923/100000000000000 : ℝ)*(base19) + (1477006181/100000000000000 : ℝ)*(base23) + (15374833/4000000000000 : ℝ)*(lower1) + (3886531/1562500000000 : ℝ)*(upper3) + (21917341/50000000000000 : ℝ)*(lower4) + (223595001/100000000000000 : ℝ)*(upper5) + (85002853104757/5000000000000 : ℝ)*(major0) + (85002853104757/5000000000000 : ℝ)*(major1) + (85002853104757/5000000000000 : ℝ)*(major2) + (956628903/100000000000000 : ℝ)*(sp2) + (132233501274169/5000000000000 : ℝ)*(sp4) + (1322334319836229/50000000000000 : ℝ)*(sp5) + (2644667591848297/100000000000000 : ℝ)*(sp6) + (755443727905741/100000000000000 : ℝ)*(sp7) + (755443727905741/100000000000000 : ℝ)*(f.failure) + (132233501274169/5000000000000 : ℝ)*(f.sum) + (395297985837/106450000000000000000000000 : ℝ)*base65 + (66825743762524493/6653125000000000000000000000000 : ℝ)*base67 + (14558237486163809/3326562500000000000000000000000 : ℝ)*base69 + (82311359528830743/6653125000000000000000000000000 : ℝ)*base71 + (448488203461/133062500000000000000000000 : ℝ)*base73 + (7909282748887273/415820312500000000000000000000 : ℝ)*base75 + (3002108783288809/3326562500000000000000000000000 : ℝ)*base77 + (5491849923076309/3326562500000000000000000000000 : ℝ)*base79 + (545292059233/532250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (2321137/500000000000000000000 : ℝ)*base90 + (2321137/500000000000000000000 : ℝ)*base92 + (2321137/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1766_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6015/1024 : ℝ) ≤ p) (hpb : p ≤ (6031/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11252043/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8851/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4593/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4607/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4417/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1766_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1766_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6015/1024 : ℝ) ≤ p) (hpb : p ≤ (6031/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11252043/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4607/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4417/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1766_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1766_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1766_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (6015/1024 : ℝ) ≤ p) (hpb : p ≤ (6031/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11252043/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4607/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4417/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1766_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
