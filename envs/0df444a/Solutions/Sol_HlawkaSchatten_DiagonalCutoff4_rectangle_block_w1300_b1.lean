-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1300_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:36:07.116479+00:00
-- url     : https://prove2.me/submissions/3c04763f-1f33-43f2-a642-beeb4f93953e

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
theorem support_rectangle_w1300_s3_0 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-207857217/1000000000 : ℝ)*x 0 + (5432898711/10000000000 : ℝ)*x 1 + (1045334399/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (207857217/1000000000 : ℝ)^1065 ≤ (6321915252471/50000000000000 : ℝ)^809 := by
    have hnat : (207857217 : ℕ)^1065*50000000000000^809 ≤ 6321915252471^809*1000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207857217 1000000000 6321915252471 50000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5432898711/10000000000 : ℝ)^1065 ≤ (5598800726841/12500000000000 : ℝ)^809 := by
    have hnat : (5432898711 : ℕ)^1065*12500000000000^809 ≤ 5598800726841^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432898711 10000000000 5598800726841 12500000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1045334399/2000000000 : ℝ)^1065 ≤ (42565763664983/100000000000000 : ℝ)^809 := by
    have hnat : (1045334399 : ℕ)^1065*100000000000000^809 ≤ 42565763664983^809*2000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045334399 2000000000 42565763664983 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-207857217/1000000000 : ℝ), (5432898711/10000000000 : ℝ), (1045334399/2000000000 : ℝ)] ![(6321915252471/50000000000000 : ℝ), (5598800726841/12500000000000 : ℝ), (42565763664983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-207857217/1000000000 : ℝ)|^1065 ≤ (6321915252471/50000000000000 : ℝ)^809
        have hw : |(-207857217/1000000000 : ℝ)|=(207857217/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5432898711/10000000000 : ℝ)|^1065 ≤ (5598800726841/12500000000000 : ℝ)^809
        have hw : |(5432898711/10000000000 : ℝ)|=(5432898711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1045334399/2000000000 : ℝ)|^1065 ≤ (42565763664983/100000000000000 : ℝ)^809
        have hw : |(1045334399/2000000000 : ℝ)|=(1045334399/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_s3_1 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1070848799/2000000000 : ℝ)*x 0 + (-1092045439/5000000000 : ℝ)*x 1 + (522667213/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070848799/2000000000 : ℝ)^1065 ≤ (1757548755217/4000000000000 : ℝ)^809 := by
    have hnat : (1070848799 : ℕ)^1065*4000000000000^809 ≤ 1757548755217^809*2000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070848799 2000000000 1757548755217 4000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1092045439/5000000000 : ℝ)^1065 ≤ (2699103198731/20000000000000 : ℝ)^809 := by
    have hnat : (1092045439 : ℕ)^1065*20000000000000^809 ≤ 2699103198731^809*5000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092045439 5000000000 2699103198731 20000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (522667213/1000000000 : ℝ)^1065 ≤ (42565765112321/100000000000000 : ℝ)^809 := by
    have hnat : (522667213 : ℕ)^1065*100000000000000^809 ≤ 42565765112321^809*1000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522667213 1000000000 42565765112321 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070848799/2000000000 : ℝ), (-1092045439/5000000000 : ℝ), (522667213/1000000000 : ℝ)] ![(1757548755217/4000000000000 : ℝ), (2699103198731/20000000000000 : ℝ), (42565765112321/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070848799/2000000000 : ℝ)|^1065 ≤ (1757548755217/4000000000000 : ℝ)^809
        have hw : |(1070848799/2000000000 : ℝ)|=(1070848799/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1092045439/5000000000 : ℝ)|^1065 ≤ (2699103198731/20000000000000 : ℝ)^809
        have hw : |(-1092045439/5000000000 : ℝ)|=(1092045439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(522667213/1000000000 : ℝ)|^1065 ≤ (42565765112321/100000000000000 : ℝ)^809
        have hw : |(522667213/1000000000 : ℝ)|=(522667213/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_s3_2 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (107084881/200000000 : ℝ)*x 0 + (5226671849/10000000000 : ℝ)*x 1 + (-87363647/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107084881/200000000 : ℝ)^1065 ≤ (21969359737299/50000000000000 : ℝ)^809 := by
    have hnat : (107084881 : ℕ)^1065*50000000000000^809 ≤ 21969359737299^809*200000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107084881 200000000 21969359737299 50000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5226671849/10000000000 : ℝ)^1065 ≤ (42565762099713/100000000000000 : ℝ)^809 := by
    have hnat : (5226671849 : ℕ)^1065*100000000000000^809 ≤ 42565762099713^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5226671849 10000000000 42565762099713 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (87363647/400000000 : ℝ)^1065 ≤ (13495518409541/100000000000000 : ℝ)^809 := by
    have hnat : (87363647 : ℕ)^1065*100000000000000^809 ≤ 13495518409541^809*400000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87363647 400000000 13495518409541 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(107084881/200000000 : ℝ), (5226671849/10000000000 : ℝ), (-87363647/400000000 : ℝ)] ![(21969359737299/50000000000000 : ℝ), (42565762099713/100000000000000 : ℝ), (13495518409541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(107084881/200000000 : ℝ)|^1065 ≤ (21969359737299/50000000000000 : ℝ)^809
        have hw : |(107084881/200000000 : ℝ)|=(107084881/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5226671849/10000000000 : ℝ)|^1065 ≤ (42565762099713/100000000000000 : ℝ)^809
        have hw : |(5226671849/10000000000 : ℝ)|=(5226671849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-87363647/400000000 : ℝ)|^1065 ≤ (13495518409541/100000000000000 : ℝ)^809
        have hw : |(-87363647/400000000 : ℝ)|=(87363647/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_s3_3 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4336368633/10000000000 : ℝ)*x 0 + (1032189139/2500000000 : ℝ)*x 1 + (4553897711/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4336368633/10000000000 : ℝ)^1065 ≤ (33288819113939/100000000000000 : ℝ)^809 := by
    have hnat : (4336368633 : ℕ)^1065*100000000000000^809 ≤ 33288819113939^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4336368633 10000000000 33288819113939 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1032189139/2500000000 : ℝ)^1065 ≤ (31206790765063/100000000000000 : ℝ)^809 := by
    have hnat : (1032189139 : ℕ)^1065*100000000000000^809 ≤ 31206790765063^809*2500000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1032189139 2500000000 31206790765063 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4553897711/10000000000 : ℝ)^1065 ≤ (35504390111969/100000000000000 : ℝ)^809 := by
    have hnat : (4553897711 : ℕ)^1065*100000000000000^809 ≤ 35504390111969^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4553897711 10000000000 35504390111969 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4336368633/10000000000 : ℝ), (1032189139/2500000000 : ℝ), (4553897711/10000000000 : ℝ)] ![(33288819113939/100000000000000 : ℝ), (31206790765063/100000000000000 : ℝ), (35504390111969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4336368633/10000000000 : ℝ)|^1065 ≤ (33288819113939/100000000000000 : ℝ)^809
        have hw : |(4336368633/10000000000 : ℝ)|=(4336368633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1032189139/2500000000 : ℝ)|^1065 ≤ (31206790765063/100000000000000 : ℝ)^809
        have hw : |(1032189139/2500000000 : ℝ)|=(1032189139/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4553897711/10000000000 : ℝ)|^1065 ≤ (35504390111969/100000000000000 : ℝ)^809
        have hw : |(4553897711/10000000000 : ℝ)|=(4553897711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_s3_4 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2078594173/10000000000 : ℝ)*x 0 + (163361093/312500000 : ℝ)*x 1 + (1086402039/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2078594173/10000000000 : ℝ)^1065 ≤ (12644006701439/100000000000000 : ℝ)^809 := by
    have hnat : (2078594173 : ℕ)^1065*100000000000000^809 ≤ 12644006701439^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2078594173 10000000000 12644006701439 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (163361093/312500000 : ℝ)^1065 ≤ (42575230378519/100000000000000 : ℝ)^809 := by
    have hnat : (163361093 : ℕ)^1065*100000000000000^809 ≤ 42575230378519^809*312500000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163361093 312500000 42575230378519 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1086402039/2000000000 : ℝ)^1065 ≤ (44780762896373/100000000000000 : ℝ)^809 := by
    have hnat : (1086402039 : ℕ)^1065*100000000000000^809 ≤ 44780762896373^809*2000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086402039 2000000000 44780762896373 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2078594173/10000000000 : ℝ), (163361093/312500000 : ℝ), (1086402039/2000000000 : ℝ)] ![(12644006701439/100000000000000 : ℝ), (42575230378519/100000000000000 : ℝ), (44780762896373/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2078594173/10000000000 : ℝ)|^1065 ≤ (12644006701439/100000000000000 : ℝ)^809
        have hw : |(-2078594173/10000000000 : ℝ)|=(2078594173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(163361093/312500000 : ℝ)|^1065 ≤ (42575230378519/100000000000000 : ℝ)^809
        have hw : |(163361093/312500000 : ℝ)|=(163361093/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1086402039/2000000000 : ℝ)|^1065 ≤ (44780762896373/100000000000000 : ℝ)^809
        have hw : |(1086402039/2000000000 : ℝ)|=(1086402039/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_s3_5 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (662673511/1250000000 : ℝ)*x 0 + (-1978752699/10000000000 : ℝ)*x 1 + (5432010159/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (662673511/1250000000 : ℝ)^1065 ≤ (867372051749/2000000000000 : ℝ)^809 := by
    have hnat : (662673511 : ℕ)^1065*2000000000000^809 ≤ 867372051749^809*1250000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      662673511 1250000000 867372051749 2000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1978752699/10000000000 : ℝ)^1065 ≤ (2370126978599/20000000000000 : ℝ)^809 := by
    have hnat : (1978752699 : ℕ)^1065*20000000000000^809 ≤ 2370126978599^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1978752699 10000000000 2370126978599 20000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5432010159/10000000000 : ℝ)^1065 ≤ (44780762505681/100000000000000 : ℝ)^809 := by
    have hnat : (5432010159 : ℕ)^1065*100000000000000^809 ≤ 44780762505681^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432010159 10000000000 44780762505681 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(662673511/1250000000 : ℝ), (-1978752699/10000000000 : ℝ), (5432010159/10000000000 : ℝ)] ![(867372051749/2000000000000 : ℝ), (2370126978599/20000000000000 : ℝ), (44780762505681/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(662673511/1250000000 : ℝ)|^1065 ≤ (867372051749/2000000000000 : ℝ)^809
        have hw : |(662673511/1250000000 : ℝ)|=(662673511/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1978752699/10000000000 : ℝ)|^1065 ≤ (2370126978599/20000000000000 : ℝ)^809
        have hw : |(-1978752699/10000000000 : ℝ)|=(1978752699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5432010159/10000000000 : ℝ)|^1065 ≤ (44780762505681/100000000000000 : ℝ)^809
        have hw : |(5432010159/10000000000 : ℝ)|=(5432010159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_s3_6 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1325347043/2500000000 : ℝ)*x 0 + (5432010063/10000000000 : ℝ)*x 1 + (-1978752717/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325347043/2500000000 : ℝ)^1065 ≤ (4336860349207/10000000000000 : ℝ)^809 := by
    have hnat : (1325347043 : ℕ)^1065*10000000000000^809 ≤ 4336860349207^809*2500000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325347043 2500000000 4336860349207 10000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5432010063/10000000000 : ℝ)^1065 ≤ (11195190365959/25000000000000 : ℝ)^809 := by
    have hnat : (5432010063 : ℕ)^1065*25000000000000^809 ≤ 11195190365959^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432010063 10000000000 11195190365959 25000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1978752717/10000000000 : ℝ)^1065 ≤ (11850635034909/100000000000000 : ℝ)^809 := by
    have hnat : (1978752717 : ℕ)^1065*100000000000000^809 ≤ 11850635034909^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1978752717 10000000000 11850635034909 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1325347043/2500000000 : ℝ), (5432010063/10000000000 : ℝ), (-1978752717/10000000000 : ℝ)] ![(4336860349207/10000000000000 : ℝ), (11195190365959/25000000000000 : ℝ), (11850635034909/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1325347043/2500000000 : ℝ)|^1065 ≤ (4336860349207/10000000000000 : ℝ)^809
        have hw : |(1325347043/2500000000 : ℝ)|=(1325347043/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5432010063/10000000000 : ℝ)|^1065 ≤ (11195190365959/25000000000000 : ℝ)^809
        have hw : |(5432010063/10000000000 : ℝ)|=(5432010063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1978752717/10000000000 : ℝ)|^1065 ≤ (11850635034909/100000000000000 : ℝ)^809
        have hw : |(-1978752717/10000000000 : ℝ)|=(1978752717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_s3_7 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (542051703/1250000000 : ℝ)*x 0 + (569009653/1250000000 : ℝ)*x 1 + (1032647111/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (542051703/1250000000 : ℝ)^1065 ≤ (8322318446859/25000000000000 : ℝ)^809 := by
    have hnat : (542051703 : ℕ)^1065*25000000000000^809 ≤ 8322318446859^809*1250000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542051703 1250000000 8322318446859 25000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (569009653/1250000000 : ℝ)^1065 ≤ (35485706536921/100000000000000 : ℝ)^809 := by
    have hnat : (569009653 : ℕ)^1065*100000000000000^809 ≤ 35485706536921^809*1250000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      569009653 1250000000 35485706536921 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1032647111/2500000000 : ℝ)^1065 ≤ (3903127457387/12500000000000 : ℝ)^809 := by
    have hnat : (1032647111 : ℕ)^1065*12500000000000^809 ≤ 3903127457387^809*2500000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1032647111 2500000000 3903127457387 12500000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(542051703/1250000000 : ℝ), (569009653/1250000000 : ℝ), (1032647111/2500000000 : ℝ)] ![(8322318446859/25000000000000 : ℝ), (35485706536921/100000000000000 : ℝ), (3903127457387/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(542051703/1250000000 : ℝ)|^1065 ≤ (8322318446859/25000000000000 : ℝ)^809
        have hw : |(542051703/1250000000 : ℝ)|=(542051703/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(569009653/1250000000 : ℝ)|^1065 ≤ (35485706536921/100000000000000 : ℝ)^809
        have hw : |(569009653/1250000000 : ℝ)|=(569009653/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1032647111/2500000000 : ℝ)|^1065 ≤ (3903127457387/12500000000000 : ℝ)^809
        have hw : |(1032647111/2500000000 : ℝ)|=(1032647111/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1300_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153076077/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16281/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9563/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10693/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (941/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16281/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9563/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16281/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9563/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16281/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9563/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16281/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9563/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16281/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9563/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16281/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9563/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9563/100000 : ℝ) ^ (4259/1024 : ℝ) ≤ (5755829482286537/100000000000000000000 : ℝ) := by
    have hpowers : (9563/100000 : ℝ)^4259 ≤ (5755829482286537/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9563 : ℕ)^4259*100000000000000000000^1024 ≤ 5755829482286537^1024*100000^4259 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9563 100000 5755829482286537 100000000000000000000 4259 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9563/100000 : ℝ)) (X := (5755829482286537/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4259 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16281/100000 : ℝ) ^ (4259/1024 : ℝ) ≤ (52630796828568193/100000000000000000000 : ℝ) := by
    have hpowers : (16281/100000 : ℝ)^4259 ≤ (52630796828568193/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16281 : ℕ)^4259*100000000000000000000^1024 ≤ 52630796828568193^1024*100000^4259 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16281 100000 52630796828568193 100000000000000000000 4259 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16281/100000 : ℝ)) (X := (52630796828568193/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4259 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005755829482286537/50000000000000000000 : ℝ) ≤ (5000138382524683/5000000000000000 : ℝ) ^ (4259/1024 : ℝ) := by
    have hpowers : (50005755829482286537/50000000000000000000 : ℝ)^1024 ≤ (5000138382524683/5000000000000000 : ℝ)^4259 := by
      have hnat : (50005755829482286537 : ℕ)^1024*5000000000000000^4259 ≤ 5000138382524683^4259*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005755829482286537 50000000000000000000 5000138382524683 5000000000000000 1024 4259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000138382524683/5000000000000000 : ℝ)) (X := (50005755829482286537/50000000000000000000 : ℝ)) (by norm_num) 4259 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10005838662631085473/10000000000000000000 : ℝ) ≤ (10001403490310581/10000000000000000 : ℝ) ^ (4259/1024 : ℝ) := by
    have hpowers : (10005838662631085473/10000000000000000000 : ℝ)^1024 ≤ (10001403490310581/10000000000000000 : ℝ)^4259 := by
      have hnat : (10005838662631085473 : ℕ)^1024*10000000000000000^4259 ≤ 10001403490310581^4259*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005838662631085473 10000000000000000000 10001403490310581 10000000000000000 1024 4259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001403490310581/10000000000000000 : ℝ)) (X := (10005838662631085473/10000000000000000000 : ℝ)) (by norm_num) 4259 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50052630796828568193/50000000000000000000 : ℝ) ≤ (2500632553892949/2500000000000000 : ℝ) ^ (4259/1024 : ℝ) := by
    have hpowers : (50052630796828568193/50000000000000000000 : ℝ)^1024 ≤ (2500632553892949/2500000000000000 : ℝ)^4259 := by
      have hnat : (50052630796828568193 : ℕ)^1024*2500000000000000^4259 ≤ 2500632553892949^4259*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50052630796828568193 50000000000000000000 2500632553892949 2500000000000000 1024 4259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500632553892949/2500000000000000 : ℝ)) (X := (50052630796828568193/50000000000000000000 : ℝ)) (by norm_num) 4259 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5755829482286537/100000000000000000000 : ℝ) ≤ ((33580154780127821349/33590000000000000000 : ℝ)+2*(225345052243/134360000000000 : ℝ)*(9563/100000 : ℝ))^(4259/1024 : ℝ) := by
    rw [show (33580154780127821349/33590000000000000000 : ℝ)+2*(225345052243/134360000000000 : ℝ)*(9563/100000 : ℝ)=(5000138382524683/5000000000000000 : ℝ) by norm_num, show 1+2*(5755829482286537/100000000000000000000 : ℝ)=(50005755829482286537/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(52630796828568193/100000000000000000000 : ℝ)+(5755829482286537/100000000000000000000 : ℝ) ≤ ((33580154780127821349/33590000000000000000 : ℝ)+(225345052243/134360000000000 : ℝ)*((16281/100000 : ℝ)+(9563/100000 : ℝ)))^(4259/1024 : ℝ) := by
    rw [show (33580154780127821349/33590000000000000000 : ℝ)+(225345052243/134360000000000 : ℝ)*((16281/100000 : ℝ)+(9563/100000 : ℝ))=(10001403490310581/10000000000000000 : ℝ) by norm_num, show 1+(52630796828568193/100000000000000000000 : ℝ)+(5755829482286537/100000000000000000000 : ℝ)=(10005838662631085473/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(52630796828568193/100000000000000000000 : ℝ) ≤ ((33580154780127821349/33590000000000000000 : ℝ)+2*(225345052243/134360000000000 : ℝ)*(16281/100000 : ℝ))^(4259/1024 : ℝ) := by
    rw [show (33580154780127821349/33590000000000000000 : ℝ)+2*(225345052243/134360000000000 : ℝ)*(16281/100000 : ℝ)=(2500632553892949/2500000000000000 : ℝ) by norm_num, show 1+2*(52630796828568193/100000000000000000000 : ℝ)=(50052630796828568193/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (33580154780127821349/33590000000000000000 : ℝ)*(X 1 0+X 2 0)+(225345052243/134360000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4259/1024 : ℝ)) (lo := (9563/100000 : ℝ)) (hi := (16281/100000 : ℝ)) (c := (33580154780127821349/33590000000000000000 : ℝ)) (alpha := (225345052243/134360000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (33580154780127821349/33590000000000000000 : ℝ)*(X 0 1+X 2 1)+(225345052243/134360000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4259/1024 : ℝ)) (lo := (9563/100000 : ℝ)) (hi := (16281/100000 : ℝ)) (c := (33580154780127821349/33590000000000000000 : ℝ)) (alpha := (225345052243/134360000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (33580154780127821349/33590000000000000000 : ℝ)*(X 0 2+X 1 2)+(225345052243/134360000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4259/1024 : ℝ)) (lo := (9563/100000 : ℝ)) (hi := (16281/100000 : ℝ)) (c := (33580154780127821349/33590000000000000000 : ℝ)) (alpha := (225345052243/134360000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-207857217/1000000000 : ℝ)*X 0 0+(5432898711/10000000000 : ℝ)*X 0 1+(1045334399/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1070848799/2000000000 : ℝ)*X 1 0+(-1092045439/5000000000 : ℝ)*X 1 1+(522667213/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((107084881/200000000 : ℝ)*X 2 0+(5226671849/10000000000 : ℝ)*X 2 1+(-87363647/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4336368633/10000000000 : ℝ)*X 0 0+(1032189139/2500000000 : ℝ)*X 0 1+(4553897711/10000000000 : ℝ)*X 0 2+(4336368633/10000000000 : ℝ)*X 1 0+(1032189139/2500000000 : ℝ)*X 1 1+(4553897711/10000000000 : ℝ)*X 1 2+(4336368633/10000000000 : ℝ)*X 2 0+(1032189139/2500000000 : ℝ)*X 2 1+(4553897711/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2078594173/10000000000 : ℝ)*X 0 0+(163361093/312500000 : ℝ)*X 0 1+(1086402039/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((662673511/1250000000 : ℝ)*X 1 0+(-1978752699/10000000000 : ℝ)*X 1 1+(5432010159/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1325347043/2500000000 : ℝ)*X 2 0+(5432010063/10000000000 : ℝ)*X 2 1+(-1978752717/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((542051703/1250000000 : ℝ)*X 0 0+(569009653/1250000000 : ℝ)*X 0 1+(1032647111/2500000000 : ℝ)*X 0 2+(542051703/1250000000 : ℝ)*X 1 0+(569009653/1250000000 : ℝ)*X 1 1+(1032647111/2500000000 : ℝ)*X 1 2+(542051703/1250000000 : ℝ)*X 2 0+(569009653/1250000000 : ℝ)*X 2 1+(1032647111/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2627612295970690871205768027/419875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (616187289/50000000000000 : ℝ)*(base19) + (1248743943/100000000000000 : ℝ)*(base23) + (6585643/10000000000000 : ℝ)*(lower2) + (159566683/50000000000000 : ℝ)*(upper3) + (47951087/100000000000000 : ℝ)*(lower4) + (900157040025659/25000000000000 : ℝ)*(major0) + (900157040025659/25000000000000 : ℝ)*(major1) + (900157040025659/25000000000000 : ℝ)*(major2) + (4849057666768803/100000000000000 : ℝ)*(sp0) + (2424536364291133/50000000000000 : ℝ)*(sp1) + (4849072712212901/100000000000000 : ℝ)*(sp2) + (1176084447157053/50000000000000 : ℝ)*(sp3) + (16294188041/100000000000000 : ℝ)*(sp4) + (13256331573/100000000000000 : ℝ)*(sp7) + (29402276883071/1250000000000 : ℝ)*(f.failure) + (1212268490239211/25000000000000 : ℝ)*(f.sum) + (2240461938401/3359000000000000000000000000 : ℝ)*base65 + (3267384825241493991/839750000000000000000000000000000 : ℝ)*base67 + (7106741541731743991/839750000000000000000000000000000 : ℝ)*base69 + (1785267551207756009/839750000000000000000000000000000 : ℝ)*base72 + (1021992598693/1679500000000000000000000000 : ℝ)*base74 + (5951584296881743991/839750000000000000000000000000000 : ℝ)*base75 + (2481925113687243991/839750000000000000000000000000000 : ℝ)*base77 + (2769048042508506009/839750000000000000000000000000000 : ℝ)*base80 + (13990865165297/3359000000000000000000000000 : ℝ)*base81 + (1392467/125000000000000000000 : ℝ)*base89 + (1392467/125000000000000000000 : ℝ)*base91 + (1392467/125000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3212748772206083991979660239/419875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (368429719/20000000000000 : ℝ)*(base19) + (1996735351/100000000000000 : ℝ)*(base23) + (38003811/20000000000000 : ℝ)*(upper3) + (7316747/20000000000000 : ℝ)*(lower4) + (40072733/20000000000000 : ℝ)*(upper5) + (1815897318013463/50000000000000 : ℝ)*(major0) + (1815897318013463/50000000000000 : ℝ)*(major1) + (1815897318013463/50000000000000 : ℝ)*(major2) + (15434666127/50000000000000 : ℝ)*(sp1) + (31679841403/100000000000000 : ℝ)*(sp2) + (611380843052657/12500000000000 : ℝ)*(sp4) + (2445507016470203/50000000000000 : ℝ)*(sp5) + (2445506533922251/50000000000000 : ℝ)*(sp6) + (593135568144153/25000000000000 : ℝ)*(sp7) + (593135568144153/25000000000000 : ℝ)*(f.failure) + (611380843052657/12500000000000 : ℝ)*(f.sum) + (22311348752109/3359000000000000000000000000 : ℝ)*base65 + (5924625761270071587/1679500000000000000000000000000000 : ℝ)*base67 + (6696517290597928413/1679500000000000000000000000000000 : ℝ)*base70 + (20025026888611071587/1679500000000000000000000000000000 : ℝ)*base71 + (1898407549729/3359000000000000000000000000 : ℝ)*base74 + (13862644191009071587/1679500000000000000000000000000000 : ℝ)*base75 + (12009052125149071587/1679500000000000000000000000000000 : ℝ)*base77 + (3598488169668571587/1679500000000000000000000000000000 : ℝ)*base79 + (2099271812469/1679500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (38272219/2500000000000000000000 : ℝ)*base90 + (38272219/2500000000000000000000 : ℝ)*base92 + (38272219/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1300_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153076077/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16281/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9563/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10693/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (941/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1300_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1300_s4_0 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2080410517/10000000000 : ℝ)*x 0 + (5418319601/10000000000 : ℝ)*x 1 + (1310011437/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2080410517/10000000000 : ℝ)^1065 ≤ (6329276863973/50000000000000 : ℝ)^809 := by
    have hnat : (2080410517 : ℕ)^1065*50000000000000^809 ≤ 6329276863973^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2080410517 10000000000 6329276863973 50000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5418319601/10000000000 : ℝ)^1065 ≤ (22316122126887/50000000000000 : ℝ)^809 := by
    have hnat : (5418319601 : ℕ)^1065*50000000000000^809 ≤ 22316122126887^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5418319601 10000000000 22316122126887 50000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310011437/2500000000 : ℝ)^1065 ≤ (8541840401057/20000000000000 : ℝ)^809 := by
    have hnat : (1310011437 : ℕ)^1065*20000000000000^809 ≤ 8541840401057^809*2500000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310011437 2500000000 8541840401057 20000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2080410517/10000000000 : ℝ), (5418319601/10000000000 : ℝ), (1310011437/2500000000 : ℝ)] ![(6329276863973/50000000000000 : ℝ), (22316122126887/50000000000000 : ℝ), (8541840401057/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2080410517/10000000000 : ℝ)|^1065 ≤ (6329276863973/50000000000000 : ℝ)^809
        have hw : |(-2080410517/10000000000 : ℝ)|=(2080410517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5418319601/10000000000 : ℝ)|^1065 ≤ (22316122126887/50000000000000 : ℝ)^809
        have hw : |(5418319601/10000000000 : ℝ)|=(5418319601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310011437/2500000000 : ℝ)|^1065 ≤ (8541840401057/20000000000000 : ℝ)^809
        have hw : |(1310011437/2500000000 : ℝ)|=(1310011437/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_s4_1 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2675276871/5000000000 : ℝ)*x 0 + (-2171345339/10000000000 : ℝ)*x 1 + (1048009247/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675276871/5000000000 : ℝ)^1065 ≤ (21949428439939/50000000000000 : ℝ)^809 := by
    have hnat : (2675276871 : ℕ)^1065*50000000000000^809 ≤ 21949428439939^809*5000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675276871 5000000000 21949428439939 50000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2171345339/10000000000 : ℝ)^1065 ≤ (6695967941383/50000000000000 : ℝ)^809 := by
    have hnat : (2171345339 : ℕ)^1065*50000000000000^809 ≤ 6695967941383^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2171345339 10000000000 6695967941383 50000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048009247/2000000000 : ℝ)^1065 ≤ (42709207230647/100000000000000 : ℝ)^809 := by
    have hnat : (1048009247 : ℕ)^1065*100000000000000^809 ≤ 42709207230647^809*2000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048009247 2000000000 42709207230647 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675276871/5000000000 : ℝ), (-2171345339/10000000000 : ℝ), (1048009247/2000000000 : ℝ)] ![(21949428439939/50000000000000 : ℝ), (6695967941383/50000000000000 : ℝ), (42709207230647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675276871/5000000000 : ℝ)|^1065 ≤ (21949428439939/50000000000000 : ℝ)^809
        have hw : |(2675276871/5000000000 : ℝ)|=(2675276871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2171345339/10000000000 : ℝ)|^1065 ≤ (6695967941383/50000000000000 : ℝ)^809
        have hw : |(-2171345339/10000000000 : ℝ)|=(2171345339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048009247/2000000000 : ℝ)|^1065 ≤ (42709207230647/100000000000000 : ℝ)^809
        have hw : |(1048009247/2000000000 : ℝ)|=(1048009247/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_s4_2 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5350553951/10000000000 : ℝ)*x 0 + (5240046179/10000000000 : ℝ)*x 1 + (-2171345133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350553951/10000000000 : ℝ)^1065 ≤ (43898859137243/100000000000000 : ℝ)^809 := by
    have hnat : (5350553951 : ℕ)^1065*100000000000000^809 ≤ 43898859137243^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350553951 10000000000 43898859137243 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5240046179/10000000000 : ℝ)^1065 ≤ (5338650828723/12500000000000 : ℝ)^809 := by
    have hnat : (5240046179 : ℕ)^1065*12500000000000^809 ≤ 5338650828723^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240046179 10000000000 5338650828723 12500000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2171345133/10000000000 : ℝ)^1065 ≤ (13391934210201/100000000000000 : ℝ)^809 := by
    have hnat : (2171345133 : ℕ)^1065*100000000000000^809 ≤ 13391934210201^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2171345133 10000000000 13391934210201 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350553951/10000000000 : ℝ), (5240046179/10000000000 : ℝ), (-2171345133/10000000000 : ℝ)] ![(43898859137243/100000000000000 : ℝ), (5338650828723/12500000000000 : ℝ), (13391934210201/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350553951/10000000000 : ℝ)|^1065 ≤ (43898859137243/100000000000000 : ℝ)^809
        have hw : |(5350553951/10000000000 : ℝ)|=(5350553951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5240046179/10000000000 : ℝ)|^1065 ≤ (5338650828723/12500000000000 : ℝ)^809
        have hw : |(5240046179/10000000000 : ℝ)|=(5240046179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2171345133/10000000000 : ℝ)|^1065 ≤ (13391934210201/100000000000000 : ℝ)^809
        have hw : |(-2171345133/10000000000 : ℝ)|=(2171345133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_s4_3 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (67773141/156250000 : ℝ)*x 0 + (2078715131/5000000000 : ℝ)*x 1 + (2262472311/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (67773141/156250000 : ℝ)^1065 ≤ (33300061237989/100000000000000 : ℝ)^809 := by
    have hnat : (67773141 : ℕ)^1065*100000000000000^809 ≤ 33300061237989^809*156250000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67773141 156250000 33300061237989 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2078715131/5000000000 : ℝ)^1065 ≤ (31492412296677/100000000000000 : ℝ)^809 := by
    have hnat : (2078715131 : ℕ)^1065*100000000000000^809 ≤ 31492412296677^809*5000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2078715131 5000000000 31492412296677 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2262472311/5000000000 : ℝ)^1065 ≤ (7041505289141/20000000000000 : ℝ)^809 := by
    have hnat : (2262472311 : ℕ)^1065*20000000000000^809 ≤ 7041505289141^809*5000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2262472311 5000000000 7041505289141 20000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(67773141/156250000 : ℝ), (2078715131/5000000000 : ℝ), (2262472311/5000000000 : ℝ)] ![(33300061237989/100000000000000 : ℝ), (31492412296677/100000000000000 : ℝ), (7041505289141/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(67773141/156250000 : ℝ)|^1065 ≤ (33300061237989/100000000000000 : ℝ)^809
        have hw : |(67773141/156250000 : ℝ)|=(67773141/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2078715131/5000000000 : ℝ)|^1065 ≤ (31492412296677/100000000000000 : ℝ)^809
        have hw : |(2078715131/5000000000 : ℝ)|=(2078715131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2262472311/5000000000 : ℝ)|^1065 ≤ (7041505289141/20000000000000 : ℝ)^809
        have hw : |(2262472311/5000000000 : ℝ)|=(2262472311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_s4_4 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1040212279/5000000000 : ℝ)*x 0 + (5240706687/10000000000 : ℝ)*x 1 + (216706209/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1040212279/5000000000 : ℝ)^1065 ≤ (12658666197413/100000000000000 : ℝ)^809 := by
    have hnat : (1040212279 : ℕ)^1065*100000000000000^809 ≤ 12658666197413^809*5000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040212279 5000000000 12658666197413 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5240706687/10000000000 : ℝ)^1065 ≤ (42716293822121/100000000000000 : ℝ)^809 := by
    have hnat : (5240706687 : ℕ)^1065*100000000000000^809 ≤ 42716293822121^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240706687 10000000000 42716293822121 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216706209/400000000 : ℝ)^1065 ≤ (44625039971801/100000000000000 : ℝ)^809 := by
    have hnat : (216706209 : ℕ)^1065*100000000000000^809 ≤ 44625039971801^809*400000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216706209 400000000 44625039971801 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1040212279/5000000000 : ℝ), (5240706687/10000000000 : ℝ), (216706209/400000000 : ℝ)] ![(12658666197413/100000000000000 : ℝ), (42716293822121/100000000000000 : ℝ), (44625039971801/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1040212279/5000000000 : ℝ)|^1065 ≤ (12658666197413/100000000000000 : ℝ)^809
        have hw : |(-1040212279/5000000000 : ℝ)|=(1040212279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5240706687/10000000000 : ℝ)|^1065 ≤ (42716293822121/100000000000000 : ℝ)^809
        have hw : |(5240706687/10000000000 : ℝ)|=(5240706687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216706209/400000000 : ℝ)|^1065 ≤ (44625039971801/100000000000000 : ℝ)^809
        have hw : |(216706209/400000000 : ℝ)|=(216706209/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_s4_5 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1326216403/2500000000 : ℝ)*x 0 + (-1993735827/10000000000 : ℝ)*x 1 + (84650861/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326216403/2500000000 : ℝ)^1065 ≤ (8681211384959/20000000000000 : ℝ)^809 := by
    have hnat : (1326216403 : ℕ)^1065*20000000000000^809 ≤ 8681211384959^809*2500000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326216403 2500000000 8681211384959 20000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1993735827/10000000000 : ℝ)^1065 ≤ (1496113049507/12500000000000 : ℝ)^809 := by
    have hnat : (1993735827 : ℕ)^1065*12500000000000^809 ≤ 1496113049507^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1993735827 10000000000 1496113049507 12500000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84650861/156250000 : ℝ)^1065 ≤ (44625038659741/100000000000000 : ℝ)^809 := by
    have hnat : (84650861 : ℕ)^1065*100000000000000^809 ≤ 44625038659741^809*156250000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84650861 156250000 44625038659741 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326216403/2500000000 : ℝ), (-1993735827/10000000000 : ℝ), (84650861/156250000 : ℝ)] ![(8681211384959/20000000000000 : ℝ), (1496113049507/12500000000000 : ℝ), (44625038659741/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326216403/2500000000 : ℝ)|^1065 ≤ (8681211384959/20000000000000 : ℝ)^809
        have hw : |(1326216403/2500000000 : ℝ)|=(1326216403/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1993735827/10000000000 : ℝ)|^1065 ≤ (1496113049507/12500000000000 : ℝ)^809
        have hw : |(-1993735827/10000000000 : ℝ)|=(1993735827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84650861/156250000 : ℝ)|^1065 ≤ (44625038659741/100000000000000 : ℝ)^809
        have hw : |(84650861/156250000 : ℝ)|=(84650861/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_s4_6 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5304865297/10000000000 : ℝ)*x 0 + (5417655453/10000000000 : ℝ)*x 1 + (-1993735777/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304865297/10000000000 : ℝ)^1065 ≤ (21703026765883/50000000000000 : ℝ)^809 := by
    have hnat : (5304865297 : ℕ)^1065*50000000000000^809 ≤ 21703026765883^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304865297 10000000000 21703026765883 50000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5417655453/10000000000 : ℝ)^1065 ≤ (2789065152757/6250000000000 : ℝ)^809 := by
    have hnat : (5417655453 : ℕ)^1065*6250000000000^809 ≤ 2789065152757^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417655453 10000000000 2789065152757 6250000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1993735777/10000000000 : ℝ)^1065 ≤ (11968904000909/100000000000000 : ℝ)^809 := by
    have hnat : (1993735777 : ℕ)^1065*100000000000000^809 ≤ 11968904000909^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1993735777 10000000000 11968904000909 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304865297/10000000000 : ℝ), (5417655453/10000000000 : ℝ), (-1993735777/10000000000 : ℝ)] ![(21703026765883/50000000000000 : ℝ), (2789065152757/6250000000000 : ℝ), (11968904000909/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304865297/10000000000 : ℝ)|^1065 ≤ (21703026765883/50000000000000 : ℝ)^809
        have hw : |(5304865297/10000000000 : ℝ)|=(5304865297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5417655453/10000000000 : ℝ)|^1065 ≤ (2789065152757/6250000000000 : ℝ)^809
        have hw : |(5417655453/10000000000 : ℝ)|=(5417655453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1993735777/10000000000 : ℝ)|^1065 ≤ (11968904000909/100000000000000 : ℝ)^809
        have hw : |(-1993735777/10000000000 : ℝ)|=(1993735777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_s4_7 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4337509903/10000000000 : ℝ)*x 0 + (4523583087/10000000000 : ℝ)*x 1 + (4158799379/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4337509903/10000000000 : ℝ)^1065 ≤ (33300353109119/100000000000000 : ℝ)^809 := by
    have hnat : (4337509903 : ℕ)^1065*100000000000000^809 ≤ 33300353109119^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4337509903 10000000000 33300353109119 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4523583087/10000000000 : ℝ)^1065 ≤ (1407743241201/4000000000000 : ℝ)^809 := by
    have hnat : (4523583087 : ℕ)^1065*4000000000000^809 ≤ 1407743241201^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4523583087 10000000000 1407743241201 4000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4158799379/10000000000 : ℝ)^1065 ≤ (6301213167111/20000000000000 : ℝ)^809 := by
    have hnat : (4158799379 : ℕ)^1065*20000000000000^809 ≤ 6301213167111^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4158799379 10000000000 6301213167111 20000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4337509903/10000000000 : ℝ), (4523583087/10000000000 : ℝ), (4158799379/10000000000 : ℝ)] ![(33300353109119/100000000000000 : ℝ), (1407743241201/4000000000000 : ℝ), (6301213167111/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4337509903/10000000000 : ℝ)|^1065 ≤ (33300353109119/100000000000000 : ℝ)^809
        have hw : |(4337509903/10000000000 : ℝ)|=(4337509903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4523583087/10000000000 : ℝ)|^1065 ≤ (1407743241201/4000000000000 : ℝ)^809
        have hw : |(4523583087/10000000000 : ℝ)|=(4523583087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4158799379/10000000000 : ℝ)|^1065 ≤ (6301213167111/20000000000000 : ℝ)^809
        have hw : |(4158799379/10000000000 : ℝ)|=(4158799379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1300_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153076077/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (941/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10693/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10979/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14751/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (941/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10693/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (941/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10693/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (941/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10693/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (941/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10693/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (941/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10693/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (941/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10693/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10693/100000 : ℝ) ^ (4259/1024 : ℝ) ≤ (4579527213066243/50000000000000000000 : ℝ) := by
    have hpowers : (10693/100000 : ℝ)^4259 ≤ (4579527213066243/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10693 : ℕ)^4259*50000000000000000000^1024 ≤ 4579527213066243^1024*100000^4259 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10693 100000 4579527213066243 50000000000000000000 4259 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10693/100000 : ℝ)) (X := (4579527213066243/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4259 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (941/6250 : ℝ) ^ (4259/1024 : ℝ) ≤ (38014256116317251/100000000000000000000 : ℝ) := by
    have hpowers : (941/6250 : ℝ)^4259 ≤ (38014256116317251/100000000000000000000 : ℝ)^1024 := by
      have hnat : (941 : ℕ)^4259*100000000000000000000^1024 ≤ 38014256116317251^1024*6250^4259 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        941 6250 38014256116317251 100000000000000000000 4259 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (941/6250 : ℝ)) (X := (38014256116317251/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4259 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004579527213066243/25000000000000000000 : ℝ) ≤ (2500110098841529/2500000000000000 : ℝ) ^ (4259/1024 : ℝ) := by
    have hpowers : (25004579527213066243/25000000000000000000 : ℝ)^1024 ≤ (2500110098841529/2500000000000000 : ℝ)^4259 := by
      have hnat : (25004579527213066243 : ℕ)^1024*2500000000000000^4259 ≤ 2500110098841529^4259*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004579527213066243 25000000000000000000 2500110098841529 2500000000000000 1024 4259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500110098841529/2500000000000000 : ℝ)) (X := (25004579527213066243/25000000000000000000 : ℝ)) (by norm_num) 4259 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047173310542449737/100000000000000000000 : ℝ) ≤ (10001133994321239/10000000000000000 : ℝ) ^ (4259/1024 : ℝ) := by
    have hpowers : (100047173310542449737/100000000000000000000 : ℝ)^1024 ≤ (10001133994321239/10000000000000000 : ℝ)^4259 := by
      have hnat : (100047173310542449737 : ℕ)^1024*10000000000000000^4259 ≤ 10001133994321239^4259*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047173310542449737 100000000000000000000 10001133994321239 10000000000000000 1024 4259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001133994321239/10000000000000000 : ℝ)) (X := (100047173310542449737/100000000000000000000 : ℝ)) (by norm_num) 4259 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50038014256116317251/50000000000000000000 : ℝ) ≤ (5000913796638181/5000000000000000 : ℝ) ^ (4259/1024 : ℝ) := by
    have hpowers : (50038014256116317251/50000000000000000000 : ℝ)^1024 ≤ (5000913796638181/5000000000000000 : ℝ)^4259 := by
      have hnat : (50038014256116317251 : ℕ)^1024*5000000000000000^4259 ≤ 5000913796638181^4259*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50038014256116317251 50000000000000000000 5000913796638181 5000000000000000 1024 4259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000913796638181/5000000000000000 : ℝ)) (X := (50038014256116317251/50000000000000000000 : ℝ)) (by norm_num) 4259 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4579527213066243/50000000000000000000 : ℝ) ≤ ((4361708813772810363/4363000000000000000 : ℝ)+2*(693598955123/436300000000000 : ℝ)*(10693/100000 : ℝ))^(4259/1024 : ℝ) := by
    rw [show (4361708813772810363/4363000000000000000 : ℝ)+2*(693598955123/436300000000000 : ℝ)*(10693/100000 : ℝ)=(2500110098841529/2500000000000000 : ℝ) by norm_num, show 1+2*(4579527213066243/50000000000000000000 : ℝ)=(25004579527213066243/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(38014256116317251/100000000000000000000 : ℝ)+(4579527213066243/50000000000000000000 : ℝ) ≤ ((4361708813772810363/4363000000000000000 : ℝ)+(693598955123/436300000000000 : ℝ)*((941/6250 : ℝ)+(10693/100000 : ℝ)))^(4259/1024 : ℝ) := by
    rw [show (4361708813772810363/4363000000000000000 : ℝ)+(693598955123/436300000000000 : ℝ)*((941/6250 : ℝ)+(10693/100000 : ℝ))=(10001133994321239/10000000000000000 : ℝ) by norm_num, show 1+(38014256116317251/100000000000000000000 : ℝ)+(4579527213066243/50000000000000000000 : ℝ)=(100047173310542449737/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(38014256116317251/100000000000000000000 : ℝ) ≤ ((4361708813772810363/4363000000000000000 : ℝ)+2*(693598955123/436300000000000 : ℝ)*(941/6250 : ℝ))^(4259/1024 : ℝ) := by
    rw [show (4361708813772810363/4363000000000000000 : ℝ)+2*(693598955123/436300000000000 : ℝ)*(941/6250 : ℝ)=(5000913796638181/5000000000000000 : ℝ) by norm_num, show 1+2*(38014256116317251/100000000000000000000 : ℝ)=(50038014256116317251/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4361708813772810363/4363000000000000000 : ℝ)*(X 1 0+X 2 0)+(693598955123/436300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4259/1024 : ℝ)) (lo := (10693/100000 : ℝ)) (hi := (941/6250 : ℝ)) (c := (4361708813772810363/4363000000000000000 : ℝ)) (alpha := (693598955123/436300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4361708813772810363/4363000000000000000 : ℝ)*(X 0 1+X 2 1)+(693598955123/436300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4259/1024 : ℝ)) (lo := (10693/100000 : ℝ)) (hi := (941/6250 : ℝ)) (c := (4361708813772810363/4363000000000000000 : ℝ)) (alpha := (693598955123/436300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4361708813772810363/4363000000000000000 : ℝ)*(X 0 2+X 1 2)+(693598955123/436300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4259/1024 : ℝ)) (lo := (10693/100000 : ℝ)) (hi := (941/6250 : ℝ)) (c := (4361708813772810363/4363000000000000000 : ℝ)) (alpha := (693598955123/436300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2080410517/10000000000 : ℝ)*X 0 0+(5418319601/10000000000 : ℝ)*X 0 1+(1310011437/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675276871/5000000000 : ℝ)*X 1 0+(-2171345339/10000000000 : ℝ)*X 1 1+(1048009247/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350553951/10000000000 : ℝ)*X 2 0+(5240046179/10000000000 : ℝ)*X 2 1+(-2171345133/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((67773141/156250000 : ℝ)*X 0 0+(2078715131/5000000000 : ℝ)*X 0 1+(2262472311/5000000000 : ℝ)*X 0 2+(67773141/156250000 : ℝ)*X 1 0+(2078715131/5000000000 : ℝ)*X 1 1+(2262472311/5000000000 : ℝ)*X 1 2+(67773141/156250000 : ℝ)*X 2 0+(2078715131/5000000000 : ℝ)*X 2 1+(2262472311/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1040212279/5000000000 : ℝ)*X 0 0+(5240706687/10000000000 : ℝ)*X 0 1+(216706209/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326216403/2500000000 : ℝ)*X 1 0+(-1993735827/10000000000 : ℝ)*X 1 1+(84650861/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5304865297/10000000000 : ℝ)*X 2 0+(5417655453/10000000000 : ℝ)*X 2 1+(-1993735777/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4337509903/10000000000 : ℝ)*X 0 0+(4523583087/10000000000 : ℝ)*X 0 1+(4158799379/10000000000 : ℝ)*X 0 2+(4337509903/10000000000 : ℝ)*X 1 0+(4523583087/10000000000 : ℝ)*X 1 1+(4158799379/10000000000 : ℝ)*X 1 2+(4337509903/10000000000 : ℝ)*X 2 0+(4523583087/10000000000 : ℝ)*X 2 1+(4158799379/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (26298969483232663037558253/6817187500000000000000000000000 : ℝ) := by norm_num
    linear_combination (409664311/100000000000000 : ℝ)*(base19) + (283840223/50000000000000 : ℝ)*(base23) + (32688779/100000000000000 : ℝ)*(lower2) + (14134243/50000000000000 : ℝ)*(upper3) + (260376587/100000000000000 : ℝ)*(upper5) + (32540546273513/781250000000 : ℝ)*(major0) + (32540546273513/781250000000 : ℝ)*(major1) + (32540546273513/781250000000 : ℝ)*(major2) + (2804680784124991/50000000000000 : ℝ)*(sp0) + (5609385926799313/100000000000000 : ℝ)*(sp1) + (2804692884391589/50000000000000 : ℝ)*(sp2) + (544197769859889/20000000000000 : ℝ)*(sp3) + (12384106821/50000000000000 : ℝ)*(sp4) + (1132916189/25000000000000 : ℝ)*(sp7) + (1360496690482101/50000000000000 : ℝ)*(f.failure) + (701173292057953/12500000000000 : ℝ)*(f.sum) + (40709420222499/10907500000000000000000000000 : ℝ)*base66 + (7329697977619813/6817187500000000000000000000000 : ℝ)*base67 + (6651312773842707/426074218750000000000000000000 : ℝ)*base70 + (32904499620513563/6817187500000000000000000000000 : ℝ)*base71 + (77712753035847/21815000000000000000000000000 : ℝ)*base73 + (133878261020925999/13634375000000000000000000000000 : ℝ)*base76 + (57457709489823937/6817187500000000000000000000000 : ℝ)*base78 + (77956844836376031/3408593750000000000000000000000 : ℝ)*base80 + (1293193446029/681718750000000000000000000 : ℝ)*base82 + (59797777/5000000000000000000000 : ℝ)*base89 + (59797777/5000000000000000000000 : ℝ)*base91 + (59797777/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (40536838632166014164656821/21815000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (180391457/25000000000000 : ℝ)*(base19) + (400834181/100000000000000 : ℝ)*(base23) + (49786977/100000000000000 : ℝ)*(upper3) + (70891/12500000000000 : ℝ)*(lower4) + (419635442469189/10000000000000 : ℝ)*(major0) + (419635442469189/10000000000000 : ℝ)*(major1) + (419635442469189/10000000000000 : ℝ)*(major2) + (11963251529/100000000000000 : ℝ)*(sp1) + (3390591331/25000000000000 : ℝ)*(sp2) + (2098301/200000000000 : ℝ)*(sp3) + (1412839143565331/25000000000000 : ℝ)*(sp4) + (5651343889443967/100000000000000 : ℝ)*(sp5) + (2825671305530909/50000000000000 : ℝ)*(sp6) + (548270232806327/20000000000000 : ℝ)*(sp7) + (342669026647767/12500000000000 : ℝ)*(f.failure) + (1412839143565331/25000000000000 : ℝ)*(f.sum) + (676301214479/174520000000000000000000000 : ℝ)*base65 + (68276561153914393/43630000000000000000000000000000 : ℝ)*base68 + (101431946321074393/43630000000000000000000000000000 : ℝ)*base70 + (46145937109134393/43630000000000000000000000000000 : ℝ)*base72 + (51496850921/4363000000000000000000000000 : ℝ)*base74 + (99249703869364393/43630000000000000000000000000000 : ℝ)*base76 + (366323760555625607/43630000000000000000000000000000 : ℝ)*base77 + (461225104794025607/43630000000000000000000000000000 : ℝ)*base79 + (5787829862213/4363000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (8170059/1250000000000000000000 : ℝ)*base89 + (8170059/1250000000000000000000 : ℝ)*base91 + (8170059/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1300_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153076077/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (941/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10693/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10979/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14751/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1300_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1300_s5_0 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1040375267/5000000000 : ℝ)*x 0 + (676928957/1250000000 : ℝ)*x 1 + (327669383/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1040375267/5000000000 : ℝ)^1065 ≤ (3165319339309/25000000000000 : ℝ)^809 := by
    have hnat : (1040375267 : ℕ)^1065*25000000000000^809 ≤ 3165319339309^809*5000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040375267 5000000000 3165319339309 25000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (676928957/1250000000 : ℝ)^1065 ≤ (4460093033069/10000000000000 : ℝ)^809 := by
    have hnat : (676928957 : ℕ)^1065*10000000000000^809 ≤ 4460093033069^809*1250000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676928957 1250000000 4460093033069 10000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (327669383/625000000 : ℝ)^1065 ≤ (5342224036929/12500000000000 : ℝ)^809 := by
    have hnat : (327669383 : ℕ)^1065*12500000000000^809 ≤ 5342224036929^809*625000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327669383 625000000 5342224036929 12500000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1040375267/5000000000 : ℝ), (676928957/1250000000 : ℝ), (327669383/625000000 : ℝ)] ![(3165319339309/25000000000000 : ℝ), (4460093033069/10000000000000 : ℝ), (5342224036929/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1040375267/5000000000 : ℝ)|^1065 ≤ (3165319339309/25000000000000 : ℝ)^809
        have hw : |(-1040375267/5000000000 : ℝ)|=(1040375267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(676928957/1250000000 : ℝ)|^1065 ≤ (4460093033069/10000000000000 : ℝ)^809
        have hw : |(676928957/1250000000 : ℝ)|=(676928957/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(327669383/625000000 : ℝ)|^1065 ≤ (5342224036929/12500000000000 : ℝ)^809
        have hw : |(327669383/625000000 : ℝ)|=(327669383/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_s5_1 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5349820729/10000000000 : ℝ)*x 0 + (-1084399641/5000000000 : ℝ)*x 1 + (5242710137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349820729/10000000000 : ℝ)^1065 ≤ (8778187986239/20000000000000 : ℝ)^809 := by
    have hnat : (5349820729 : ℕ)^1065*20000000000000^809 ≤ 8778187986239^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349820729 10000000000 8778187986239 20000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1084399641/5000000000 : ℝ)^1065 ≤ (6685633831571/50000000000000 : ℝ)^809 := by
    have hnat : (1084399641 : ℕ)^1065*50000000000000^809 ≤ 6685633831571^809*5000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084399641 5000000000 6685633831571 50000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242710137/10000000000 : ℝ)^1065 ≤ (8547558478403/20000000000000 : ℝ)^809 := by
    have hnat : (5242710137 : ℕ)^1065*20000000000000^809 ≤ 8547558478403^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242710137 10000000000 8547558478403 20000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349820729/10000000000 : ℝ), (-1084399641/5000000000 : ℝ), (5242710137/10000000000 : ℝ)] ![(8778187986239/20000000000000 : ℝ), (6685633831571/50000000000000 : ℝ), (8547558478403/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349820729/10000000000 : ℝ)|^1065 ≤ (8778187986239/20000000000000 : ℝ)^809
        have hw : |(5349820729/10000000000 : ℝ)|=(5349820729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1084399641/5000000000 : ℝ)|^1065 ≤ (6685633831571/50000000000000 : ℝ)^809
        have hw : |(-1084399641/5000000000 : ℝ)|=(1084399641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242710137/10000000000 : ℝ)|^1065 ≤ (8547558478403/20000000000000 : ℝ)^809
        have hw : |(5242710137/10000000000 : ℝ)|=(5242710137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_s5_2 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5349820667/10000000000 : ℝ)*x 0 + (2621355061/5000000000 : ℝ)*x 1 + (-271099923/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349820667/10000000000 : ℝ)^1065 ≤ (1755637570463/4000000000000 : ℝ)^809 := by
    have hnat : (5349820667 : ℕ)^1065*4000000000000^809 ≤ 1755637570463^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349820667 10000000000 1755637570463 4000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621355061/5000000000 : ℝ)^1065 ≤ (10684448057761/25000000000000 : ℝ)^809 := by
    have hnat : (2621355061 : ℕ)^1065*25000000000000^809 ≤ 10684448057761^809*5000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621355061 5000000000 10684448057761 25000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (271099923/1250000000 : ℝ)^1065 ≤ (13371268490997/100000000000000 : ℝ)^809 := by
    have hnat : (271099923 : ℕ)^1065*100000000000000^809 ≤ 13371268490997^809*1250000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271099923 1250000000 13371268490997 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349820667/10000000000 : ℝ), (2621355061/5000000000 : ℝ), (-271099923/1250000000 : ℝ)] ![(1755637570463/4000000000000 : ℝ), (10684448057761/25000000000000 : ℝ), (13371268490997/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349820667/10000000000 : ℝ)|^1065 ≤ (1755637570463/4000000000000 : ℝ)^809
        have hw : |(5349820667/10000000000 : ℝ)|=(5349820667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621355061/5000000000 : ℝ)|^1065 ≤ (10684448057761/25000000000000 : ℝ)^809
        have hw : |(2621355061/5000000000 : ℝ)|=(2621355061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-271099923/1250000000 : ℝ)|^1065 ≤ (13371268490997/100000000000000 : ℝ)^809
        have hw : |(-271099923/1250000000 : ℝ)|=(271099923/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_s5_3 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (271105153/625000000 : ℝ)*x 0 + (2081563797/5000000000 : ℝ)*x 1 + (1446143/3200000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (271105153/625000000 : ℝ)^1065 ≤ (33302096980931/100000000000000 : ℝ)^809 := by
    have hnat : (271105153 : ℕ)^1065*100000000000000^809 ≤ 33302096980931^809*625000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271105153 625000000 33302096980931 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2081563797/5000000000 : ℝ)^1065 ≤ (31549238376307/100000000000000 : ℝ)^809 := by
    have hnat : (2081563797 : ℕ)^1065*100000000000000^809 ≤ 31549238376307^809*5000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2081563797 5000000000 31549238376307 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1446143/3200000 : ℝ)^1065 ≤ (17574332314763/50000000000000 : ℝ)^809 := by
    have hnat : (1446143 : ℕ)^1065*50000000000000^809 ≤ 17574332314763^809*3200000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1446143 3200000 17574332314763 50000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(271105153/625000000 : ℝ), (2081563797/5000000000 : ℝ), (1446143/3200000 : ℝ)] ![(33302096980931/100000000000000 : ℝ), (31549238376307/100000000000000 : ℝ), (17574332314763/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(271105153/625000000 : ℝ)|^1065 ≤ (33302096980931/100000000000000 : ℝ)^809
        have hw : |(271105153/625000000 : ℝ)|=(271105153/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2081563797/5000000000 : ℝ)|^1065 ≤ (31549238376307/100000000000000 : ℝ)^809
        have hw : |(2081563797/5000000000 : ℝ)|=(2081563797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1446143/3200000 : ℝ)|^1065 ≤ (17574332314763/50000000000000 : ℝ)^809
        have hw : |(1446143/3200000 : ℝ)|=(1446143/3200000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_s5_4 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-416152687/2000000000 : ℝ)*x 0 + (5243330273/10000000000 : ℝ)*x 1 + (1082961657/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (416152687/2000000000 : ℝ)^1065 ≤ (12661380700553/100000000000000 : ℝ)^809 := by
    have hnat : (416152687 : ℕ)^1065*100000000000000^809 ≤ 12661380700553^809*2000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416152687 2000000000 12661380700553 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243330273/10000000000 : ℝ)^1065 ≤ (42744447458457/100000000000000 : ℝ)^809 := by
    have hnat : (5243330273 : ℕ)^1065*100000000000000^809 ≤ 42744447458457^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243330273 10000000000 42744447458457 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082961657/2000000000 : ℝ)^1065 ≤ (22297085913081/50000000000000 : ℝ)^809 := by
    have hnat : (1082961657 : ℕ)^1065*50000000000000^809 ≤ 22297085913081^809*2000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082961657 2000000000 22297085913081 50000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-416152687/2000000000 : ℝ), (5243330273/10000000000 : ℝ), (1082961657/2000000000 : ℝ)] ![(12661380700553/100000000000000 : ℝ), (42744447458457/100000000000000 : ℝ), (22297085913081/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-416152687/2000000000 : ℝ)|^1065 ≤ (12661380700553/100000000000000 : ℝ)^809
        have hw : |(-416152687/2000000000 : ℝ)|=(416152687/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243330273/10000000000 : ℝ)|^1065 ≤ (42744447458457/100000000000000 : ℝ)^809
        have hw : |(5243330273/10000000000 : ℝ)|=(5243330273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1082961657/2000000000 : ℝ)|^1065 ≤ (22297085913081/50000000000000 : ℝ)^809
        have hw : |(1082961657/2000000000 : ℝ)|=(1082961657/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_s5_5 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5305555087/10000000000 : ℝ)*x 0 + (-1996701091/10000000000 : ℝ)*x 1 + (1082961661/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305555087/10000000000 : ℝ)^1065 ≤ (10853370943001/25000000000000 : ℝ)^809 := by
    have hnat : (5305555087 : ℕ)^1065*25000000000000^809 ≤ 10853370943001^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305555087 10000000000 10853370943001 25000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1996701091/10000000000 : ℝ)^1065 ≤ (5996172084143/50000000000000 : ℝ)^809 := by
    have hnat : (1996701091 : ℕ)^1065*50000000000000^809 ≤ 5996172084143^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1996701091 10000000000 5996172084143 50000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082961661/2000000000 : ℝ)^1065 ≤ (8918834408599/20000000000000 : ℝ)^809 := by
    have hnat : (1082961661 : ℕ)^1065*20000000000000^809 ≤ 8918834408599^809*2000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082961661 2000000000 8918834408599 20000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305555087/10000000000 : ℝ), (-1996701091/10000000000 : ℝ), (1082961661/2000000000 : ℝ)] ![(10853370943001/25000000000000 : ℝ), (5996172084143/50000000000000 : ℝ), (8918834408599/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305555087/10000000000 : ℝ)|^1065 ≤ (10853370943001/25000000000000 : ℝ)^809
        have hw : |(5305555087/10000000000 : ℝ)|=(5305555087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1996701091/10000000000 : ℝ)|^1065 ≤ (5996172084143/50000000000000 : ℝ)^809
        have hw : |(-1996701091/10000000000 : ℝ)|=(1996701091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1082961661/2000000000 : ℝ)|^1065 ≤ (8918834408599/20000000000000 : ℝ)^809
        have hw : |(1082961661/2000000000 : ℝ)|=(1082961661/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_s5_6 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (530555509/1000000000 : ℝ)*x 0 + (1082961659/2000000000 : ℝ)*x 1 + (-998350551/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530555509/1000000000 : ℝ)^1065 ≤ (271334273777/625000000000 : ℝ)^809 := by
    have hnat : (530555509 : ℕ)^1065*625000000000^809 ≤ 271334273777^809*1000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530555509 1000000000 271334273777 625000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082961659/2000000000 : ℝ)^1065 ≤ (22297085967289/50000000000000 : ℝ)^809 := by
    have hnat : (1082961659 : ℕ)^1065*50000000000000^809 ≤ 22297085967289^809*2000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082961659 2000000000 22297085967289 50000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (998350551/5000000000 : ℝ)^1065 ≤ (11992344255259/100000000000000 : ℝ)^809 := by
    have hnat : (998350551 : ℕ)^1065*100000000000000^809 ≤ 11992344255259^809*5000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      998350551 5000000000 11992344255259 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530555509/1000000000 : ℝ), (1082961659/2000000000 : ℝ), (-998350551/5000000000 : ℝ)] ![(271334273777/625000000000 : ℝ), (22297085967289/50000000000000 : ℝ), (11992344255259/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530555509/1000000000 : ℝ)|^1065 ≤ (271334273777/625000000000 : ℝ)^809
        have hw : |(530555509/1000000000 : ℝ)|=(530555509/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1082961659/2000000000 : ℝ)|^1065 ≤ (22297085967289/50000000000000 : ℝ)^809
        have hw : |(1082961659/2000000000 : ℝ)|=(1082961659/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-998350551/5000000000 : ℝ)|^1065 ≤ (11992344255259/100000000000000 : ℝ)^809
        have hw : |(-998350551/5000000000 : ℝ)|=(998350551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_s5_7 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4337709051/10000000000 : ℝ)*x 0 + (4517918319/10000000000 : ℝ)*x 1 + (832882543/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4337709051/10000000000 : ℝ)^1065 ≤ (832559146329/2500000000000 : ℝ)^809 := by
    have hnat : (4337709051 : ℕ)^1065*2500000000000^809 ≤ 832559146329^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4337709051 10000000000 832559146329 2500000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4517918319/10000000000 : ℝ)^1065 ≤ (35135574348589/100000000000000 : ℝ)^809 := by
    have hnat : (4517918319 : ℕ)^1065*100000000000000^809 ≤ 35135574348589^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4517918319 10000000000 35135574348589 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (832882543/2000000000 : ℝ)^1065 ≤ (7890514944257/25000000000000 : ℝ)^809 := by
    have hnat : (832882543 : ℕ)^1065*25000000000000^809 ≤ 7890514944257^809*2000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      832882543 2000000000 7890514944257 25000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4337709051/10000000000 : ℝ), (4517918319/10000000000 : ℝ), (832882543/2000000000 : ℝ)] ![(832559146329/2500000000000 : ℝ), (35135574348589/100000000000000 : ℝ), (7890514944257/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4337709051/10000000000 : ℝ)|^1065 ≤ (832559146329/2500000000000 : ℝ)^809
        have hw : |(4337709051/10000000000 : ℝ)|=(4337709051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4517918319/10000000000 : ℝ)|^1065 ≤ (35135574348589/100000000000000 : ℝ)^809
        have hw : |(4517918319/10000000000 : ℝ)|=(4517918319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(832882543/2000000000 : ℝ)|^1065 ≤ (7890514944257/25000000000000 : ℝ)^809
        have hw : |(832882543/2000000000 : ℝ)|=(832882543/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1300_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153076077/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14751/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10979/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2759/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14691/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14751/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10979/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14751/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10979/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14751/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10979/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14751/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10979/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14751/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10979/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14751/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10979/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10979/100000 : ℝ) ^ (4259/1024 : ℝ) ≤ (5110909944128103/50000000000000000000 : ℝ) := by
    have hpowers : (10979/100000 : ℝ)^4259 ≤ (5110909944128103/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10979 : ℕ)^4259*50000000000000000000^1024 ≤ 5110909944128103^1024*100000^4259 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10979 100000 5110909944128103 50000000000000000000 4259 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10979/100000 : ℝ)) (X := (5110909944128103/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4259 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14751/100000 : ℝ) ^ (4259/1024 : ℝ) ≤ (34912352370365887/100000000000000000000 : ℝ) := by
    have hpowers : (14751/100000 : ℝ)^4259 ≤ (34912352370365887/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14751 : ℕ)^4259*100000000000000000000^1024 ≤ 34912352370365887^1024*100000^4259 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14751 100000 34912352370365887 100000000000000000000 4259 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14751/100000 : ℝ)) (X := (34912352370365887/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4259 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005110909944128103/25000000000000000000 : ℝ) ≤ (10000491492414957/10000000000000000 : ℝ) ^ (4259/1024 : ℝ) := by
    have hpowers : (25005110909944128103/25000000000000000000 : ℝ)^1024 ≤ (10000491492414957/10000000000000000 : ℝ)^4259 := by
      have hnat : (25005110909944128103 : ℕ)^1024*10000000000000000^4259 ≤ 10000491492414957^4259*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005110909944128103 25000000000000000000 10000491492414957 10000000000000000 1024 4259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000491492414957/10000000000000000 : ℝ)) (X := (25005110909944128103/25000000000000000000 : ℝ)) (by norm_num) 4259 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045134172258622093/100000000000000000000 : ℝ) ≤ (1250135623010851/1250000000000000 : ℝ) ^ (4259/1024 : ℝ) := by
    have hpowers : (100045134172258622093/100000000000000000000 : ℝ)^1024 ≤ (1250135623010851/1250000000000000 : ℝ)^4259 := by
      have hnat : (100045134172258622093 : ℕ)^1024*1250000000000000^4259 ≤ 1250135623010851^4259*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045134172258622093 100000000000000000000 1250135623010851 1250000000000000 1024 4259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250135623010851/1250000000000000 : ℝ)) (X := (100045134172258622093/100000000000000000000 : ℝ)) (by norm_num) 4259 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034912352370365887/50000000000000000000 : ℝ) ≤ (10001678475758659/10000000000000000 : ℝ) ^ (4259/1024 : ℝ) := by
    have hpowers : (50034912352370365887/50000000000000000000 : ℝ)^1024 ≤ (10001678475758659/10000000000000000 : ℝ)^4259 := by
      have hnat : (50034912352370365887 : ℕ)^1024*10000000000000000^4259 ≤ 10001678475758659^4259*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034912352370365887 50000000000000000000 10001678475758659 10000000000000000 1024 4259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001678475758659/10000000000000000 : ℝ)) (X := (50034912352370365887/50000000000000000000 : ℝ)) (by norm_num) 4259 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5110909944128103/50000000000000000000 : ℝ) ≤ ((18854411009629356773/18860000000000000000 : ℝ)+2*(593491671851/377200000000000 : ℝ)*(10979/100000 : ℝ))^(4259/1024 : ℝ) := by
    rw [show (18854411009629356773/18860000000000000000 : ℝ)+2*(593491671851/377200000000000 : ℝ)*(10979/100000 : ℝ)=(10000491492414957/10000000000000000 : ℝ) by norm_num, show 1+2*(5110909944128103/50000000000000000000 : ℝ)=(25005110909944128103/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34912352370365887/100000000000000000000 : ℝ)+(5110909944128103/50000000000000000000 : ℝ) ≤ ((18854411009629356773/18860000000000000000 : ℝ)+(593491671851/377200000000000 : ℝ)*((14751/100000 : ℝ)+(10979/100000 : ℝ)))^(4259/1024 : ℝ) := by
    rw [show (18854411009629356773/18860000000000000000 : ℝ)+(593491671851/377200000000000 : ℝ)*((14751/100000 : ℝ)+(10979/100000 : ℝ))=(1250135623010851/1250000000000000 : ℝ) by norm_num, show 1+(34912352370365887/100000000000000000000 : ℝ)+(5110909944128103/50000000000000000000 : ℝ)=(100045134172258622093/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34912352370365887/100000000000000000000 : ℝ) ≤ ((18854411009629356773/18860000000000000000 : ℝ)+2*(593491671851/377200000000000 : ℝ)*(14751/100000 : ℝ))^(4259/1024 : ℝ) := by
    rw [show (18854411009629356773/18860000000000000000 : ℝ)+2*(593491671851/377200000000000 : ℝ)*(14751/100000 : ℝ)=(10001678475758659/10000000000000000 : ℝ) by norm_num, show 1+2*(34912352370365887/100000000000000000000 : ℝ)=(50034912352370365887/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18854411009629356773/18860000000000000000 : ℝ)*(X 1 0+X 2 0)+(593491671851/377200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4259/1024 : ℝ)) (lo := (10979/100000 : ℝ)) (hi := (14751/100000 : ℝ)) (c := (18854411009629356773/18860000000000000000 : ℝ)) (alpha := (593491671851/377200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18854411009629356773/18860000000000000000 : ℝ)*(X 0 1+X 2 1)+(593491671851/377200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4259/1024 : ℝ)) (lo := (10979/100000 : ℝ)) (hi := (14751/100000 : ℝ)) (c := (18854411009629356773/18860000000000000000 : ℝ)) (alpha := (593491671851/377200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18854411009629356773/18860000000000000000 : ℝ)*(X 0 2+X 1 2)+(593491671851/377200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4259/1024 : ℝ)) (lo := (10979/100000 : ℝ)) (hi := (14751/100000 : ℝ)) (c := (18854411009629356773/18860000000000000000 : ℝ)) (alpha := (593491671851/377200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1040375267/5000000000 : ℝ)*X 0 0+(676928957/1250000000 : ℝ)*X 0 1+(327669383/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349820729/10000000000 : ℝ)*X 1 0+(-1084399641/5000000000 : ℝ)*X 1 1+(5242710137/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349820667/10000000000 : ℝ)*X 2 0+(2621355061/5000000000 : ℝ)*X 2 1+(-271099923/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((271105153/625000000 : ℝ)*X 0 0+(2081563797/5000000000 : ℝ)*X 0 1+(1446143/3200000 : ℝ)*X 0 2+(271105153/625000000 : ℝ)*X 1 0+(2081563797/5000000000 : ℝ)*X 1 1+(1446143/3200000 : ℝ)*X 1 2+(271105153/625000000 : ℝ)*X 2 0+(2081563797/5000000000 : ℝ)*X 2 1+(1446143/3200000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-416152687/2000000000 : ℝ)*X 0 0+(5243330273/10000000000 : ℝ)*X 0 1+(1082961657/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305555087/10000000000 : ℝ)*X 1 0+(-1996701091/10000000000 : ℝ)*X 1 1+(1082961661/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((530555509/1000000000 : ℝ)*X 2 0+(1082961659/2000000000 : ℝ)*X 2 1+(-998350551/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4337709051/10000000000 : ℝ)*X 0 0+(4517918319/10000000000 : ℝ)*X 0 1+(832882543/2000000000 : ℝ)*X 0 2+(4337709051/10000000000 : ℝ)*X 1 0+(4517918319/10000000000 : ℝ)*X 1 1+(832882543/2000000000 : ℝ)*X 1 2+(4337709051/10000000000 : ℝ)*X 2 0+(4517918319/10000000000 : ℝ)*X 2 1+(832882543/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1272893458427411139233837127/471500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (54929399/20000000000000 : ℝ)*(base19) + (59503607/25000000000000 : ℝ)*(base23) + (85697851/100000000000000 : ℝ)*(upper3) + (4786931/25000000000000 : ℝ)*(lower4) + (2149531080968567/50000000000000 : ℝ)*(major0) + (2149531080968567/50000000000000 : ℝ)*(major1) + (2149531080968567/50000000000000 : ℝ)*(major2) + (2894836613946193/50000000000000 : ℝ)*(sp0) + (115793517369301/2000000000000 : ℝ)*(sp1) + (289483763068439/5000000000000 : ℝ)*(sp2) + (1404222361156387/50000000000000 : ℝ)*(sp3) + (2915219659/100000000000000 : ℝ)*(sp4) + (643728837/100000000000000 : ℝ)*(sp6) + (673692101/20000000000000 : ℝ)*(sp7) + (1404224045386639/50000000000000 : ℝ)*(f.failure) + (1157935228622409/20000000000000 : ℝ)*(f.sum) + (51241789803223/9430000000000000000000000000 : ℝ)*base66 + (3783110236935404291/943000000000000000000000000000000 : ℝ)*base67 + (11842009384653404291/943000000000000000000000000000000 : ℝ)*base69 + (12287361841033595709/943000000000000000000000000000000 : ℝ)*base72 + (8876232634413/9430000000000000000000000000 : ℝ)*base74 + (2467786300392404291/943000000000000000000000000000000 : ℝ)*base75 + (14328167071946404291/943000000000000000000000000000000 : ℝ)*base77 + (944984215800595709/943000000000000000000000000000000 : ℝ)*base80 + (6972677083187/9430000000000000000000000000 : ℝ)*base81 + (53664797/5000000000000000000000 : ℝ)*base90 + (53664797/5000000000000000000000 : ℝ)*base92 + (53664797/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (84466338349076127233481303/14734375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (977869999/100000000000000 : ℝ)*(base19) + (535345929/50000000000000 : ℝ)*(base23) + (364553/312500000000 : ℝ)*(upper3) + (42249779/100000000000000 : ℝ)*(lower4) + (120647757/100000000000000 : ℝ)*(upper5) + (8457480526663/195312500000 : ℝ)*(major0) + (8457480526663/195312500000 : ℝ)*(major1) + (8457480526663/195312500000 : ℝ)*(major2) + (997623867/5000000000000 : ℝ)*(sp1) + (2113804971/10000000000000 : ℝ)*(sp2) + (5831650746297293/100000000000000 : ℝ)*(sp4) + (2915814907974977/50000000000000 : ℝ)*(sp5) + (233265141502229/4000000000000 : ℝ)*(sp6) + (2828809121918807/100000000000000 : ℝ)*(sp7) + (2828809121918807/100000000000000 : ℝ)*(f.failure) + (5831650746297293/100000000000000 : ℝ)*(f.sum) + (692977159333/2357500000000000000000000000 : ℝ)*base66 + (90175106542876127/7367187500000000000000000000000 : ℝ)*base68 + (63406630324001127/7367187500000000000000000000000 : ℝ)*base70 + (66941829729486629/14734375000000000000000000000000 : ℝ)*base72 + (41050019718121/4715000000000000000000000000 : ℝ)*base74 + (360425170889174129/14734375000000000000000000000000 : ℝ)*base76 + (80893072138330379/14734375000000000000000000000000 : ℝ)*base78 + (58591801369711501/3683593750000000000000000000000 : ℝ)*base80 + (8666412889539/4715000000000000000000000000 : ℝ)*base81 + (88080139/10000000000000000000000 : ℝ)*base89 + (88080139/10000000000000000000000 : ℝ)*base91 + (88080139/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1300_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153076077/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14751/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10979/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2759/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14691/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1300_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1300_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153076077/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16281/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9563/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2759/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14691/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1300_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1300_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1300_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153076077/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16281/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9563/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2759/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14691/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1300_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
