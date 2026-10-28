-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1135_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:29:10.347273+00:00
-- url     : https://prove2.me/submissions/27fee0d7-b5a5-4c3f-8eef-3d5b8309a1b4

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
theorem support_rectangle_w1135_s9_0 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2672385481/5000000000 : ℝ)*x 0 + (263283877/500000000 : ℝ)*x 1 + (-2234875267/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672385481/5000000000 : ℝ)^1041 ≤ (43571528238279/100000000000000 : ℝ)^785 := by
    have hnat : (2672385481 : ℕ)^1041*100000000000000^785 ≤ 43571528238279^785*5000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672385481 5000000000 43571528238279 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (263283877/500000000 : ℝ)^1041 ≤ (333738603409/781250000000 : ℝ)^785 := by
    have hnat : (263283877 : ℕ)^1041*781250000000^785 ≤ 333738603409^785*500000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263283877 500000000 333738603409 781250000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2234875267/10000000000 : ℝ)^1041 ≤ (6854965257181/50000000000000 : ℝ)^785 := by
    have hnat : (2234875267 : ℕ)^1041*50000000000000^785 ≤ 6854965257181^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2234875267 10000000000 6854965257181 50000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672385481/5000000000 : ℝ), (263283877/500000000 : ℝ), (-2234875267/10000000000 : ℝ)] ![(43571528238279/100000000000000 : ℝ), (333738603409/781250000000 : ℝ), (6854965257181/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672385481/5000000000 : ℝ)|^1041 ≤ (43571528238279/100000000000000 : ℝ)^785
        have hw : |(2672385481/5000000000 : ℝ)|=(2672385481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(263283877/500000000 : ℝ)|^1041 ≤ (333738603409/781250000000 : ℝ)^785
        have hw : |(263283877/500000000 : ℝ)|=(263283877/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2234875267/10000000000 : ℝ)|^1041 ≤ (6854965257181/50000000000000 : ℝ)^785
        have hw : |(-2234875267/10000000000 : ℝ)|=(2234875267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1135_s9_1 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2170243991/10000000000 : ℝ)*x 0 + (2632998659/5000000000 : ℝ)*x 1 + (5392786921/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2170243991/10000000000 : ℝ)^1041 ≤ (13186644090697/100000000000000 : ℝ)^785 := by
    have hnat : (2170243991 : ℕ)^1041*100000000000000^785 ≤ 13186644090697^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2170243991 10000000000 13186644090697 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632998659/5000000000 : ℝ)^1041 ≤ (8544396306943/20000000000000 : ℝ)^785 := by
    have hnat : (2632998659 : ℕ)^1041*20000000000000^785 ≤ 8544396306943^785*5000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632998659 5000000000 8544396306943 20000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392786921/10000000000 : ℝ)^1041 ≤ (11022843591263/25000000000000 : ℝ)^785 := by
    have hnat : (5392786921 : ℕ)^1041*25000000000000^785 ≤ 11022843591263^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392786921 10000000000 11022843591263 25000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2170243991/10000000000 : ℝ), (2632998659/5000000000 : ℝ), (5392786921/10000000000 : ℝ)] ![(13186644090697/100000000000000 : ℝ), (8544396306943/20000000000000 : ℝ), (11022843591263/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2170243991/10000000000 : ℝ)|^1041 ≤ (13186644090697/100000000000000 : ℝ)^785
        have hw : |(-2170243991/10000000000 : ℝ)|=(2170243991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632998659/5000000000 : ℝ)|^1041 ≤ (8544396306943/20000000000000 : ℝ)^785
        have hw : |(2632998659/5000000000 : ℝ)|=(2632998659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392786921/10000000000 : ℝ)|^1041 ≤ (11022843591263/25000000000000 : ℝ)^785
        have hw : |(5392786921/10000000000 : ℝ)|=(5392786921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1135_s9_2 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (664062847/1250000000 : ℝ)*x 0 + (-2107765651/10000000000 : ℝ)*x 1 + (1078557383/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664062847/1250000000 : ℝ)^1041 ≤ (43223029674963/100000000000000 : ℝ)^785 := by
    have hnat : (664062847 : ℕ)^1041*100000000000000^785 ≤ 43223029674963^785*1250000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664062847 1250000000 43223029674963 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2107765651/10000000000 : ℝ)^1041 ≤ (1585699500833/12500000000000 : ℝ)^785 := by
    have hnat : (2107765651 : ℕ)^1041*12500000000000^785 ≤ 1585699500833^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107765651 10000000000 1585699500833 12500000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078557383/2000000000 : ℝ)^1041 ≤ (22045687149999/50000000000000 : ℝ)^785 := by
    have hnat : (1078557383 : ℕ)^1041*50000000000000^785 ≤ 22045687149999^785*2000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078557383 2000000000 22045687149999 50000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664062847/1250000000 : ℝ), (-2107765651/10000000000 : ℝ), (1078557383/2000000000 : ℝ)] ![(43223029674963/100000000000000 : ℝ), (1585699500833/12500000000000 : ℝ), (22045687149999/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664062847/1250000000 : ℝ)|^1041 ≤ (43223029674963/100000000000000 : ℝ)^785
        have hw : |(664062847/1250000000 : ℝ)|=(664062847/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2107765651/10000000000 : ℝ)|^1041 ≤ (1585699500833/12500000000000 : ℝ)^785
        have hw : |(-2107765651/10000000000 : ℝ)|=(2107765651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078557383/2000000000 : ℝ)|^1041 ≤ (22045687149999/50000000000000 : ℝ)^785
        have hw : |(1078557383/2000000000 : ℝ)|=(1078557383/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1135_s9_3 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (265625143/500000000 : ℝ)*x 0 + (5392786901/10000000000 : ℝ)*x 1 + (-2107765557/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265625143/500000000 : ℝ)^1041 ≤ (5402878822659/12500000000000 : ℝ)^785 := by
    have hnat : (265625143 : ℕ)^1041*12500000000000^785 ≤ 5402878822659^785*500000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265625143 500000000 5402878822659 12500000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392786901/10000000000 : ℝ)^1041 ≤ (22045687074103/50000000000000 : ℝ)^785 := by
    have hnat : (5392786901 : ℕ)^1041*50000000000000^785 ≤ 22045687074103^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392786901 10000000000 22045687074103 50000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2107765557/10000000000 : ℝ)^1041 ≤ (12685595256429/100000000000000 : ℝ)^785 := by
    have hnat : (2107765557 : ℕ)^1041*100000000000000^785 ≤ 12685595256429^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107765557 10000000000 12685595256429 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265625143/500000000 : ℝ), (5392786901/10000000000 : ℝ), (-2107765557/10000000000 : ℝ)] ![(5402878822659/12500000000000 : ℝ), (22045687074103/50000000000000 : ℝ), (12685595256429/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265625143/500000000 : ℝ)|^1041 ≤ (5402878822659/12500000000000 : ℝ)^785
        have hw : |(265625143/500000000 : ℝ)|=(265625143/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392786901/10000000000 : ℝ)|^1041 ≤ (22045687074103/50000000000000 : ℝ)^785
        have hw : |(5392786901/10000000000 : ℝ)|=(5392786901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2107765557/10000000000 : ℝ)|^1041 ≤ (12685595256429/100000000000000 : ℝ)^785
        have hw : |(-2107765557/10000000000 : ℝ)|=(2107765557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1135_s9_4 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (873134519/2000000000 : ℝ)*x 0 + (1123360593/2500000000 : ℝ)*x 1 + (2120771991/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (873134519/2000000000 : ℝ)^1041 ≤ (520578945711/1562500000000 : ℝ)^785 := by
    have hnat : (873134519 : ℕ)^1041*1562500000000^785 ≤ 520578945711^785*2000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873134519 2000000000 520578945711 1562500000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1123360593/2500000000 : ℝ)^1041 ≤ (2163516309273/6250000000000 : ℝ)^785 := by
    have hnat : (1123360593 : ℕ)^1041*6250000000000^785 ≤ 2163516309273^785*2500000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123360593 2500000000 2163516309273 6250000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2120771991/5000000000 : ℝ)^1041 ≤ (16033343260087/50000000000000 : ℝ)^785 := by
    have hnat : (2120771991 : ℕ)^1041*50000000000000^785 ≤ 16033343260087^785*5000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2120771991 5000000000 16033343260087 50000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(873134519/2000000000 : ℝ), (1123360593/2500000000 : ℝ), (2120771991/5000000000 : ℝ)] ![(520578945711/1562500000000 : ℝ), (2163516309273/6250000000000 : ℝ), (16033343260087/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(873134519/2000000000 : ℝ)|^1041 ≤ (520578945711/1562500000000 : ℝ)^785
        have hw : |(873134519/2000000000 : ℝ)|=(873134519/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1123360593/2500000000 : ℝ)|^1041 ≤ (2163516309273/6250000000000 : ℝ)^785
        have hw : |(1123360593/2500000000 : ℝ)|=(1123360593/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2120771991/5000000000 : ℝ)|^1041 ≤ (16033343260087/50000000000000 : ℝ)^785
        have hw : |(2120771991/5000000000 : ℝ)|=(2120771991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1135_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37334287/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2809/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2269/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (2269/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3511/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2809/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2269/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2809/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2269/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2809/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2269/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2809/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2269/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2809/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2269/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2809/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2269/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2269/20000 : ℝ) ^ (8327/2048 : ℝ) ≤ (2870401373201317/20000000000000000000 : ℝ) := by
    have hpowers : (2269/20000 : ℝ)^8327 ≤ (2870401373201317/20000000000000000000 : ℝ)^2048 := by
      have hnat : (2269 : ℕ)^8327*20000000000000000000^2048 ≤ 2870401373201317^2048*20000^8327 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2269 20000 2870401373201317 20000000000000000000 8327 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2269/20000 : ℝ)) (X := (2870401373201317/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8327 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2809/20000 : ℝ) ^ (8327/2048 : ℝ) ≤ (8547386602430507/25000000000000000000 : ℝ) := by
    have hpowers : (2809/20000 : ℝ)^8327 ≤ (8547386602430507/25000000000000000000 : ℝ)^2048 := by
      have hnat : (2809 : ℕ)^8327*25000000000000000000^2048 ≤ 8547386602430507^2048*20000^8327 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2809 20000 8547386602430507 25000000000000000000 8327 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2809/20000 : ℝ)) (X := (8547386602430507/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8327 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002870401373201317/10000000000000000000 : ℝ) ≤ (10000705889987827/10000000000000000 : ℝ) ^ (8327/2048 : ℝ) := by
    have hpowers : (10002870401373201317/10000000000000000000 : ℝ)^2048 ≤ (10000705889987827/10000000000000000 : ℝ)^8327 := by
      have hnat : (10002870401373201317 : ℕ)^2048*10000000000000000^8327 ≤ 10000705889987827^8327*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002870401373201317 10000000000000000000 10000705889987827 10000000000000000 2048 8327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000705889987827/10000000000000000 : ℝ)) (X := (10002870401373201317/10000000000000000000 : ℝ)) (by norm_num) 8327 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048541553275728613/100000000000000000000 : ℝ) ≤ (1250149205764723/1250000000000000 : ℝ) ^ (8327/2048 : ℝ) := by
    have hpowers : (100048541553275728613/100000000000000000000 : ℝ)^2048 ≤ (1250149205764723/1250000000000000 : ℝ)^8327 := by
      have hnat : (100048541553275728613 : ℕ)^2048*1250000000000000^8327 ≤ 1250149205764723^8327*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048541553275728613 100000000000000000000 1250149205764723 1250000000000000 2048 8327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250149205764723/1250000000000000 : ℝ)) (X := (100048541553275728613/100000000000000000000 : ℝ)) (by norm_num) 8327 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508547386602430507/12500000000000000000 : ℝ) ≤ (10001681402247741/10000000000000000 : ℝ) ^ (8327/2048 : ℝ) := by
    have hpowers : (12508547386602430507/12500000000000000000 : ℝ)^2048 ≤ (10001681402247741/10000000000000000 : ℝ)^8327 := by
      have hnat : (12508547386602430507 : ℕ)^2048*10000000000000000^8327 ≤ 10001681402247741^8327*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508547386602430507 12500000000000000000 10001681402247741 10000000000000000 2048 8327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001681402247741/10000000000000000 : ℝ)) (X := (12508547386602430507/12500000000000000000 : ℝ)) (by norm_num) 8327 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2870401373201317/20000000000000000000 : ℝ) ≤ ((2699083871637840857/2700000000000000000 : ℝ)+2*(487756129957/270000000000000 : ℝ)*(2269/20000 : ℝ))^(8327/2048 : ℝ) := by
    rw [show (2699083871637840857/2700000000000000000 : ℝ)+2*(487756129957/270000000000000 : ℝ)*(2269/20000 : ℝ)=(10000705889987827/10000000000000000 : ℝ) by norm_num, show 1+2*(2870401373201317/20000000000000000000 : ℝ)=(10002870401373201317/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8547386602430507/25000000000000000000 : ℝ)+(2870401373201317/20000000000000000000 : ℝ) ≤ ((2699083871637840857/2700000000000000000 : ℝ)+(487756129957/270000000000000 : ℝ)*((2809/20000 : ℝ)+(2269/20000 : ℝ)))^(8327/2048 : ℝ) := by
    rw [show (2699083871637840857/2700000000000000000 : ℝ)+(487756129957/270000000000000 : ℝ)*((2809/20000 : ℝ)+(2269/20000 : ℝ))=(1250149205764723/1250000000000000 : ℝ) by norm_num, show 1+(8547386602430507/25000000000000000000 : ℝ)+(2870401373201317/20000000000000000000 : ℝ)=(100048541553275728613/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8547386602430507/25000000000000000000 : ℝ) ≤ ((2699083871637840857/2700000000000000000 : ℝ)+2*(487756129957/270000000000000 : ℝ)*(2809/20000 : ℝ))^(8327/2048 : ℝ) := by
    rw [show (2699083871637840857/2700000000000000000 : ℝ)+2*(487756129957/270000000000000 : ℝ)*(2809/20000 : ℝ)=(10001681402247741/10000000000000000 : ℝ) by norm_num, show 1+2*(8547386602430507/25000000000000000000 : ℝ)=(12508547386602430507/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2699083871637840857/2700000000000000000 : ℝ)*(X 1 0+X 2 0)+(487756129957/270000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8327/2048 : ℝ)) (lo := (2269/20000 : ℝ)) (hi := (2809/20000 : ℝ)) (c := (2699083871637840857/2700000000000000000 : ℝ)) (alpha := (487756129957/270000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2699083871637840857/2700000000000000000 : ℝ)*(X 0 1+X 2 1)+(487756129957/270000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8327/2048 : ℝ)) (lo := (2269/20000 : ℝ)) (hi := (2809/20000 : ℝ)) (c := (2699083871637840857/2700000000000000000 : ℝ)) (alpha := (487756129957/270000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2699083871637840857/2700000000000000000 : ℝ)*(X 0 2+X 1 2)+(487756129957/270000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8327/2048 : ℝ)) (lo := (2269/20000 : ℝ)) (hi := (2809/20000 : ℝ)) (c := (2699083871637840857/2700000000000000000 : ℝ)) (alpha := (487756129957/270000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((2672385481/5000000000 : ℝ)*X 2 0+(263283877/500000000 : ℝ)*X 2 1+(-2234875267/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_s9_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-2170243991/10000000000 : ℝ)*X 0 0+(2632998659/5000000000 : ℝ)*X 0 1+(5392786921/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_s9_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((664062847/1250000000 : ℝ)*X 1 0+(-2107765651/10000000000 : ℝ)*X 1 1+(1078557383/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_s9_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((265625143/500000000 : ℝ)*X 2 0+(5392786901/10000000000 : ℝ)*X 2 1+(-2107765557/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_s9_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((873134519/2000000000 : ℝ)*X 0 0+(1123360593/2500000000 : ℝ)*X 0 1+(2120771991/5000000000 : ℝ)*X 0 2+(873134519/2000000000 : ℝ)*X 1 0+(1123360593/2500000000 : ℝ)*X 1 1+(2120771991/5000000000 : ℝ)*X 1 2+(873134519/2000000000 : ℝ)*X 2 0+(1123360593/2500000000 : ℝ)*X 2 1+(2120771991/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_s9_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (19832136762552029248399363/4500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (399823467/50000000000000 : ℝ)*(base19) + (205793537/20000000000000 : ℝ)*(base23) + (242383259/100000000000000 : ℝ)*(lower1) + (15162361/12500000000000 : ℝ)*(upper3) + (13525323/50000000000000 : ℝ)*(lower4) + (108837141/100000000000000 : ℝ)*(upper5) + (592845471301541/10000000000000 : ℝ)*(major0) + (592845471301541/10000000000000 : ℝ)*(major1) + (592845471301541/10000000000000 : ℝ)*(major2) + (4419957341/50000000000000 : ℝ)*(sp0) + (7887063334957227/100000000000000 : ℝ)*(sp1) + (3943531267655147/50000000000000 : ℝ)*(sp2) + (394352673303743/5000000000000 : ℝ)*(sp3) + (1984922972084417/50000000000000 : ℝ)*(sp4) + (1984922972084417/50000000000000 : ℝ)*(f.failure) + (7887063334957227/100000000000000 : ℝ)*(f.sum) + (5059953145187/1350000000000000000000000000 : ℝ)*base65 + (300934670029307707/3000000000000000000000000000000 : ℝ)*base68 + (73438229107692293/3000000000000000000000000000000 : ℝ)*base69 + (484026556849307707/3000000000000000000000000000000 : ℝ)*base72 + (3295725489163/1350000000000000000000000000 : ℝ)*base74 + (154174304278692293/3000000000000000000000000000000 : ℝ)*base75 + (23757080530692293/3000000000000000000000000000000 : ℝ)*base77 + (9894328108692293/3000000000000000000000000000000 : ℝ)*base79 + (10118459033837/1350000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (12494321/1250000000000000000000 : ℝ)*base90 + (12494321/1250000000000000000000 : ℝ)*base92 + (12494321/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1135_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37334287/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2809/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2269/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2269/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3511/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1135_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1135_box_0 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2043121617/10000000000 : ℝ)*x 0 + (2688203801/5000000000 : ℝ)*x 1 + (2688203743/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2043121617/10000000000 : ℝ)^1041 ≤ (2434451099043/20000000000000 : ℝ)^785 := by
    have hnat : (2043121617 : ℕ)^1041*20000000000000^785 ≤ 2434451099043^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2043121617 10000000000 2434451099043 20000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2688203801/5000000000 : ℝ)^1041 ≤ (21956936436983/50000000000000 : ℝ)^785 := by
    have hnat : (2688203801 : ℕ)^1041*50000000000000^785 ≤ 21956936436983^785*5000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688203801 5000000000 21956936436983 50000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2688203743/5000000000 : ℝ)^1041 ≤ (21956935808753/50000000000000 : ℝ)^785 := by
    have hnat : (2688203743 : ℕ)^1041*50000000000000^785 ≤ 21956935808753^785*5000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688203743 5000000000 21956935808753 50000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2043121617/10000000000 : ℝ), (2688203801/5000000000 : ℝ), (2688203743/5000000000 : ℝ)] ![(2434451099043/20000000000000 : ℝ), (21956936436983/50000000000000 : ℝ), (21956935808753/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2043121617/10000000000 : ℝ)|^1041 ≤ (2434451099043/20000000000000 : ℝ)^785
        have hw : |(-2043121617/10000000000 : ℝ)|=(2043121617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2688203801/5000000000 : ℝ)|^1041 ≤ (21956936436983/50000000000000 : ℝ)^785
        have hw : |(2688203801/5000000000 : ℝ)|=(2688203801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2688203743/5000000000 : ℝ)|^1041 ≤ (21956935808753/50000000000000 : ℝ)^785
        have hw : |(2688203743/5000000000 : ℝ)|=(2688203743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1135_box_1 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2647959899/5000000000 : ℝ)*x 0 + (-215225927/1000000000 : ℝ)*x 1 + (2688203819/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647959899/5000000000 : ℝ)^1041 ≤ (269026253127/625000000000 : ℝ)^785 := by
    have hnat : (2647959899 : ℕ)^1041*625000000000^785 ≤ 269026253127^785*5000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647959899 5000000000 269026253127 625000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215225927/1000000000 : ℝ)^1041 ≤ (13041926219523/100000000000000 : ℝ)^785 := by
    have hnat : (215225927 : ℕ)^1041*100000000000000^785 ≤ 13041926219523^785*1000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215225927 1000000000 13041926219523 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2688203819/5000000000 : ℝ)^1041 ≤ (21956936631951/50000000000000 : ℝ)^785 := by
    have hnat : (2688203819 : ℕ)^1041*50000000000000^785 ≤ 21956936631951^785*5000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688203819 5000000000 21956936631951 50000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647959899/5000000000 : ℝ), (-215225927/1000000000 : ℝ), (2688203819/5000000000 : ℝ)] ![(269026253127/625000000000 : ℝ), (13041926219523/100000000000000 : ℝ), (21956936631951/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647959899/5000000000 : ℝ)|^1041 ≤ (269026253127/625000000000 : ℝ)^785
        have hw : |(2647959899/5000000000 : ℝ)|=(2647959899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-215225927/1000000000 : ℝ)|^1041 ≤ (13041926219523/100000000000000 : ℝ)^785
        have hw : |(-215225927/1000000000 : ℝ)|=(215225927/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2688203819/5000000000 : ℝ)|^1041 ≤ (21956936631951/50000000000000 : ℝ)^785
        have hw : |(2688203819/5000000000 : ℝ)|=(2688203819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1135_box_2 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (661990037/1250000000 : ℝ)*x 0 + (2688203733/5000000000 : ℝ)*x 1 + (-2152258833/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661990037/1250000000 : ℝ)^1041 ≤ (43044205867963/100000000000000 : ℝ)^785 := by
    have hnat : (661990037 : ℕ)^1041*100000000000000^785 ≤ 43044205867963^785*1250000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661990037 1250000000 43044205867963 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2688203733/5000000000 : ℝ)^1041 ≤ (351310971207/800000000000 : ℝ)^785 := by
    have hnat : (2688203733 : ℕ)^1041*800000000000^785 ≤ 351310971207^785*5000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688203733 5000000000 351310971207 800000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2152258833/10000000000 : ℝ)^1041 ≤ (6520961353943/50000000000000 : ℝ)^785 := by
    have hnat : (2152258833 : ℕ)^1041*50000000000000^785 ≤ 6520961353943^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2152258833 10000000000 6520961353943 50000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661990037/1250000000 : ℝ), (2688203733/5000000000 : ℝ), (-2152258833/10000000000 : ℝ)] ![(43044205867963/100000000000000 : ℝ), (351310971207/800000000000 : ℝ), (6520961353943/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661990037/1250000000 : ℝ)|^1041 ≤ (43044205867963/100000000000000 : ℝ)^785
        have hw : |(661990037/1250000000 : ℝ)|=(661990037/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2688203733/5000000000 : ℝ)|^1041 ≤ (351310971207/800000000000 : ℝ)^785
        have hw : |(2688203733/5000000000 : ℝ)|=(2688203733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2152258833/10000000000 : ℝ)|^1041 ≤ (6520961353943/50000000000000 : ℝ)^785
        have hw : |(-2152258833/10000000000 : ℝ)|=(2152258833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1135_box_3 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2236639287/5000000000 : ℝ)*x 0 + (539245953/1250000000 : ℝ)*x 1 + (431396739/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2236639287/5000000000 : ℝ)^1041 ≤ (3441041791197/10000000000000 : ℝ)^785 := by
    have hnat : (2236639287 : ℕ)^1041*10000000000000^785 ≤ 3441041791197^785*5000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2236639287 5000000000 3441041791197 10000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539245953/1250000000 : ℝ)^1041 ≤ (3279479221009/10000000000000 : ℝ)^785 := by
    have hnat : (539245953 : ℕ)^1041*10000000000000^785 ≤ 3279479221009^785*1250000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539245953 1250000000 3279479221009 10000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (431396739/1000000000 : ℝ)^1041 ≤ (16397394925553/50000000000000 : ℝ)^785 := by
    have hnat : (431396739 : ℕ)^1041*50000000000000^785 ≤ 16397394925553^785*1000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431396739 1000000000 16397394925553 50000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2236639287/5000000000 : ℝ), (539245953/1250000000 : ℝ), (431396739/1000000000 : ℝ)] ![(3441041791197/10000000000000 : ℝ), (3279479221009/10000000000000 : ℝ), (16397394925553/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2236639287/5000000000 : ℝ)|^1041 ≤ (3441041791197/10000000000000 : ℝ)^785
        have hw : |(2236639287/5000000000 : ℝ)|=(2236639287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539245953/1250000000 : ℝ)|^1041 ≤ (3279479221009/10000000000000 : ℝ)^785
        have hw : |(539245953/1250000000 : ℝ)|=(539245953/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(431396739/1000000000 : ℝ)|^1041 ≤ (16397394925553/50000000000000 : ℝ)^785
        have hw : |(431396739/1000000000 : ℝ)|=(431396739/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1135_box_4 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-287343389/1250000000 : ℝ)*x 0 + (2640526307/5000000000 : ℝ)*x 1 + (5281052663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (287343389/1250000000 : ℝ)^1041 ≤ (7115970290751/50000000000000 : ℝ)^785 := by
    have hnat : (287343389 : ℕ)^1041*50000000000000^785 ≤ 7115970290751^785*1250000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      287343389 1250000000 7115970290751 50000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2640526307/5000000000 : ℝ)^1041 ≤ (21442014717099/50000000000000 : ℝ)^785 := by
    have hnat : (2640526307 : ℕ)^1041*50000000000000^785 ≤ 21442014717099^785*5000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640526307 5000000000 21442014717099 50000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5281052663/10000000000 : ℝ)^1041 ≤ (335031484077/781250000000 : ℝ)^785 := by
    have hnat : (5281052663 : ℕ)^1041*781250000000^785 ≤ 335031484077^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281052663 10000000000 335031484077 781250000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-287343389/1250000000 : ℝ), (2640526307/5000000000 : ℝ), (5281052663/10000000000 : ℝ)] ![(7115970290751/50000000000000 : ℝ), (21442014717099/50000000000000 : ℝ), (335031484077/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-287343389/1250000000 : ℝ)|^1041 ≤ (7115970290751/50000000000000 : ℝ)^785
        have hw : |(-287343389/1250000000 : ℝ)|=(287343389/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2640526307/5000000000 : ℝ)|^1041 ≤ (21442014717099/50000000000000 : ℝ)^785
        have hw : |(2640526307/5000000000 : ℝ)|=(2640526307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5281052663/10000000000 : ℝ)|^1041 ≤ (335031484077/781250000000 : ℝ)^785
        have hw : |(5281052663/10000000000 : ℝ)|=(5281052663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1135_box_5 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (13408247/25000000 : ℝ)*x 0 + (-2189747971/10000000000 : ℝ)*x 1 + (5281052637/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13408247/25000000 : ℝ)^1041 ≤ (2735746294057/6250000000000 : ℝ)^785 := by
    have hnat : (13408247 : ℕ)^1041*6250000000000^785 ≤ 2735746294057^785*25000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13408247 25000000 2735746294057 6250000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2189747971/10000000000 : ℝ)^1041 ≤ (3336007396707/25000000000000 : ℝ)^785 := by
    have hnat : (2189747971 : ℕ)^1041*25000000000000^785 ≤ 3336007396707^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2189747971 10000000000 3336007396707 25000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5281052637/10000000000 : ℝ)^1041 ≤ (21442014840937/50000000000000 : ℝ)^785 := by
    have hnat : (5281052637 : ℕ)^1041*50000000000000^785 ≤ 21442014840937^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281052637 10000000000 21442014840937 50000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(13408247/25000000 : ℝ), (-2189747971/10000000000 : ℝ), (5281052637/10000000000 : ℝ)] ![(2735746294057/6250000000000 : ℝ), (3336007396707/25000000000000 : ℝ), (21442014840937/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(13408247/25000000 : ℝ)|^1041 ≤ (2735746294057/6250000000000 : ℝ)^785
        have hw : |(13408247/25000000 : ℝ)|=(13408247/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2189747971/10000000000 : ℝ)|^1041 ≤ (3336007396707/25000000000000 : ℝ)^785
        have hw : |(-2189747971/10000000000 : ℝ)|=(2189747971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5281052637/10000000000 : ℝ)|^1041 ≤ (21442014840937/50000000000000 : ℝ)^785
        have hw : |(5281052637/10000000000 : ℝ)|=(5281052637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1135_box_6 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2681649399/5000000000 : ℝ)*x 0 + (528105269/1000000000 : ℝ)*x 1 + (-437949581/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681649399/5000000000 : ℝ)^1041 ≤ (21885970341633/50000000000000 : ℝ)^785 := by
    have hnat : (2681649399 : ℕ)^1041*50000000000000^785 ≤ 21885970341633^785*5000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681649399 5000000000 21885970341633 50000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (528105269/1000000000 : ℝ)^1041 ≤ (21442015126303/50000000000000 : ℝ)^785 := by
    have hnat : (528105269 : ℕ)^1041*50000000000000^785 ≤ 21442015126303^785*1000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528105269 1000000000 21442015126303 50000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (437949581/2000000000 : ℝ)^1041 ≤ (13344029053471/100000000000000 : ℝ)^785 := by
    have hnat : (437949581 : ℕ)^1041*100000000000000^785 ≤ 13344029053471^785*2000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437949581 2000000000 13344029053471 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681649399/5000000000 : ℝ), (528105269/1000000000 : ℝ), (-437949581/2000000000 : ℝ)] ![(21885970341633/50000000000000 : ℝ), (21442015126303/50000000000000 : ℝ), (13344029053471/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681649399/5000000000 : ℝ)|^1041 ≤ (21885970341633/50000000000000 : ℝ)^785
        have hw : |(2681649399/5000000000 : ℝ)|=(2681649399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(528105269/1000000000 : ℝ)|^1041 ≤ (21442015126303/50000000000000 : ℝ)^785
        have hw : |(528105269/1000000000 : ℝ)|=(528105269/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-437949581/2000000000 : ℝ)|^1041 ≤ (13344029053471/100000000000000 : ℝ)^785
        have hw : |(-437949581/2000000000 : ℝ)|=(437949581/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1135_box_7 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (212884423/500000000 : ℝ)*x 0 + (110543543/250000000 : ℝ)*x 1 + (552717703/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212884423/500000000 : ℝ)^1041 ≤ (16114322635627/50000000000000 : ℝ)^785 := by
    have hnat : (212884423 : ℕ)^1041*50000000000000^785 ≤ 16114322635627^785*500000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212884423 500000000 16114322635627 50000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (110543543/250000000 : ℝ)^1041 ≤ (8471419461821/25000000000000 : ℝ)^785 := by
    have hnat : (110543543 : ℕ)^1041*25000000000000^785 ≤ 8471419461821^785*250000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110543543 250000000 8471419461821 25000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (552717703/1250000000 : ℝ)^1041 ≤ (33885676871677/100000000000000 : ℝ)^785 := by
    have hnat : (552717703 : ℕ)^1041*100000000000000^785 ≤ 33885676871677^785*1250000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      552717703 1250000000 33885676871677 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212884423/500000000 : ℝ), (110543543/250000000 : ℝ), (552717703/1250000000 : ℝ)] ![(16114322635627/50000000000000 : ℝ), (8471419461821/25000000000000 : ℝ), (33885676871677/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212884423/500000000 : ℝ)|^1041 ≤ (16114322635627/50000000000000 : ℝ)^785
        have hw : |(212884423/500000000 : ℝ)|=(212884423/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(110543543/250000000 : ℝ)|^1041 ≤ (8471419461821/25000000000000 : ℝ)^785
        have hw : |(110543543/250000000 : ℝ)|=(110543543/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(552717703/1250000000 : ℝ)|^1041 ≤ (33885676871677/100000000000000 : ℝ)^785
        have hw : |(552717703/1250000000 : ℝ)|=(552717703/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1135_box_8 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2245299951/10000000000 : ℝ)*x 0 + (2608107663/5000000000 : ℝ)*x 1 + (5386015349/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2245299951/10000000000 : ℝ)^1041 ≤ (6897400411857/50000000000000 : ℝ)^785 := by
    have hnat : (2245299951 : ℕ)^1041*50000000000000^785 ≤ 6897400411857^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245299951 10000000000 6897400411857 50000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2608107663/5000000000 : ℝ)^1041 ≤ (8437445836197/20000000000000 : ℝ)^785 := by
    have hnat : (2608107663 : ℕ)^1041*20000000000000^785 ≤ 8437445836197^785*5000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608107663 5000000000 8437445836197 20000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5386015349/10000000000 : ℝ)^1041 ≤ (44017969981753/100000000000000 : ℝ)^785 := by
    have hnat : (5386015349 : ℕ)^1041*100000000000000^785 ≤ 44017969981753^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386015349 10000000000 44017969981753 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2245299951/10000000000 : ℝ), (2608107663/5000000000 : ℝ), (5386015349/10000000000 : ℝ)] ![(6897400411857/50000000000000 : ℝ), (8437445836197/20000000000000 : ℝ), (44017969981753/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2245299951/10000000000 : ℝ)|^1041 ≤ (6897400411857/50000000000000 : ℝ)^785
        have hw : |(-2245299951/10000000000 : ℝ)|=(2245299951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2608107663/5000000000 : ℝ)|^1041 ≤ (8437445836197/20000000000000 : ℝ)^785
        have hw : |(2608107663/5000000000 : ℝ)|=(2608107663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5386015349/10000000000 : ℝ)|^1041 ≤ (44017969981753/100000000000000 : ℝ)^785
        have hw : |(5386015349/10000000000 : ℝ)|=(5386015349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1135_box_9 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5289127687/10000000000 : ℝ)*x 0 + (-214841239/1000000000 : ℝ)*x 1 + (215440613/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289127687/10000000000 : ℝ)^1041 ≤ (5371375965169/12500000000000 : ℝ)^785 := by
    have hnat : (5289127687 : ℕ)^1041*12500000000000^785 ≤ 5371375965169^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289127687 10000000000 5371375965169 12500000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (214841239/1000000000 : ℝ)^1041 ≤ (3252755634453/25000000000000 : ℝ)^785 := by
    have hnat : (214841239 : ℕ)^1041*25000000000000^785 ≤ 3252755634453^785*1000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214841239 1000000000 3252755634453 25000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215440613/400000000 : ℝ)^1041 ≤ (11004492430411/25000000000000 : ℝ)^785 := by
    have hnat : (215440613 : ℕ)^1041*25000000000000^785 ≤ 11004492430411^785*400000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215440613 400000000 11004492430411 25000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289127687/10000000000 : ℝ), (-214841239/1000000000 : ℝ), (215440613/400000000 : ℝ)] ![(5371375965169/12500000000000 : ℝ), (3252755634453/25000000000000 : ℝ), (11004492430411/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289127687/10000000000 : ℝ)|^1041 ≤ (5371375965169/12500000000000 : ℝ)^785
        have hw : |(5289127687/10000000000 : ℝ)|=(5289127687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-214841239/1000000000 : ℝ)|^1041 ≤ (3252755634453/25000000000000 : ℝ)^785
        have hw : |(-214841239/1000000000 : ℝ)|=(214841239/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(215440613/400000000 : ℝ)|^1041 ≤ (11004492430411/25000000000000 : ℝ)^785
        have hw : |(215440613/400000000 : ℝ)|=(215440613/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1135_box_10 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5289127683/10000000000 : ℝ)*x 0 + (269300769/500000000 : ℝ)*x 1 + (-2148412323/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289127683/10000000000 : ℝ)^1041 ≤ (42971007678257/100000000000000 : ℝ)^785 := by
    have hnat : (5289127683 : ℕ)^1041*100000000000000^785 ≤ 42971007678257^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289127683 10000000000 42971007678257 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269300769/500000000 : ℝ)^1041 ≤ (44017970317727/100000000000000 : ℝ)^785 := by
    have hnat : (269300769 : ℕ)^1041*100000000000000^785 ≤ 44017970317727^785*500000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269300769 500000000 44017970317727 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2148412323/10000000000 : ℝ)^1041 ≤ (13011021999729/100000000000000 : ℝ)^785 := by
    have hnat : (2148412323 : ℕ)^1041*100000000000000^785 ≤ 13011021999729^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2148412323 10000000000 13011021999729 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289127683/10000000000 : ℝ), (269300769/500000000 : ℝ), (-2148412323/10000000000 : ℝ)] ![(42971007678257/100000000000000 : ℝ), (44017970317727/100000000000000 : ℝ), (13011021999729/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289127683/10000000000 : ℝ)|^1041 ≤ (42971007678257/100000000000000 : ℝ)^785
        have hw : |(5289127683/10000000000 : ℝ)|=(5289127683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269300769/500000000 : ℝ)|^1041 ≤ (44017970317727/100000000000000 : ℝ)^785
        have hw : |(269300769/500000000 : ℝ)|=(269300769/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2148412323/10000000000 : ℝ)|^1041 ≤ (13011021999729/100000000000000 : ℝ)^785
        have hw : |(-2148412323/10000000000 : ℝ)|=(2148412323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1135_box_11 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4494727819/10000000000 : ℝ)*x 0 + (4303102279/10000000000 : ℝ)*x 1 + (1075775611/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4494727819/10000000000 : ℝ)^1041 ≤ (8657348430693/25000000000000 : ℝ)^785 := by
    have hnat : (4494727819 : ℕ)^1041*25000000000000^785 ≤ 8657348430693^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4494727819 10000000000 8657348430693 25000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4303102279/10000000000 : ℝ)^1041 ≤ (8171325574917/25000000000000 : ℝ)^785 := by
    have hnat : (4303102279 : ℕ)^1041*25000000000000^785 ≤ 8171325574917^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4303102279 10000000000 8171325574917 25000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1075775611/2500000000 : ℝ)^1041 ≤ (16342651980843/50000000000000 : ℝ)^785 := by
    have hnat : (1075775611 : ℕ)^1041*50000000000000^785 ≤ 16342651980843^785*2500000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075775611 2500000000 16342651980843 50000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4494727819/10000000000 : ℝ), (4303102279/10000000000 : ℝ), (1075775611/2500000000 : ℝ)] ![(8657348430693/25000000000000 : ℝ), (8171325574917/25000000000000 : ℝ), (16342651980843/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4494727819/10000000000 : ℝ)|^1041 ≤ (8657348430693/25000000000000 : ℝ)^785
        have hw : |(4494727819/10000000000 : ℝ)|=(4494727819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4303102279/10000000000 : ℝ)|^1041 ≤ (8171325574917/25000000000000 : ℝ)^785
        have hw : |(4303102279/10000000000 : ℝ)|=(4303102279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1075775611/2500000000 : ℝ)|^1041 ≤ (16342651980843/50000000000000 : ℝ)^785
        have hw : |(1075775611/2500000000 : ℝ)|=(1075775611/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1135_box_12 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2096891787/10000000000 : ℝ)*x 0 + (169998819/312500000 : ℝ)*x 1 + (1318254419/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2096891787/10000000000 : ℝ)^1041 ≤ (12598882327291/100000000000000 : ℝ)^785 := by
    have hnat : (2096891787 : ℕ)^1041*100000000000000^785 ≤ 12598882327291^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2096891787 10000000000 12598882327291 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169998819/312500000 : ℝ)^1041 ≤ (44603591172291/100000000000000 : ℝ)^785 := by
    have hnat : (169998819 : ℕ)^1041*100000000000000^785 ≤ 44603591172291^785*312500000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169998819 312500000 44603591172291 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1318254419/2500000000 : ℝ)^1041 ≤ (42797526487619/100000000000000 : ℝ)^785 := by
    have hnat : (1318254419 : ℕ)^1041*100000000000000^785 ≤ 42797526487619^785*2500000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318254419 2500000000 42797526487619 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2096891787/10000000000 : ℝ), (169998819/312500000 : ℝ), (1318254419/2500000000 : ℝ)] ![(12598882327291/100000000000000 : ℝ), (44603591172291/100000000000000 : ℝ), (42797526487619/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2096891787/10000000000 : ℝ)|^1041 ≤ (12598882327291/100000000000000 : ℝ)^785
        have hw : |(-2096891787/10000000000 : ℝ)|=(2096891787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(169998819/312500000 : ℝ)|^1041 ≤ (44603591172291/100000000000000 : ℝ)^785
        have hw : |(169998819/312500000 : ℝ)|=(169998819/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1318254419/2500000000 : ℝ)|^1041 ≤ (42797526487619/100000000000000 : ℝ)^785
        have hw : |(1318254419/2500000000 : ℝ)|=(1318254419/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1135_box_13 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5368973607/10000000000 : ℝ)*x 0 + (-2192849069/10000000000 : ℝ)*x 1 + (5273018447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368973607/10000000000 : ℝ)^1041 ≤ (43833369342231/100000000000000 : ℝ)^785 := by
    have hnat : (5368973607 : ℕ)^1041*100000000000000^785 ≤ 43833369342231^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368973607 10000000000 43833369342231 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2192849069/10000000000 : ℝ)^1041 ≤ (13369095854393/100000000000000 : ℝ)^785 := by
    have hnat : (2192849069 : ℕ)^1041*100000000000000^785 ≤ 13369095854393^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2192849069 10000000000 13369095854393 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5273018447/10000000000 : ℝ)^1041 ≤ (42797534786029/100000000000000 : ℝ)^785 := by
    have hnat : (5273018447 : ℕ)^1041*100000000000000^785 ≤ 42797534786029^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5273018447 10000000000 42797534786029 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368973607/10000000000 : ℝ), (-2192849069/10000000000 : ℝ), (5273018447/10000000000 : ℝ)] ![(43833369342231/100000000000000 : ℝ), (13369095854393/100000000000000 : ℝ), (42797534786029/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368973607/10000000000 : ℝ)|^1041 ≤ (43833369342231/100000000000000 : ℝ)^785
        have hw : |(5368973607/10000000000 : ℝ)|=(5368973607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2192849069/10000000000 : ℝ)|^1041 ≤ (13369095854393/100000000000000 : ℝ)^785
        have hw : |(-2192849069/10000000000 : ℝ)|=(2192849069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5273018447/10000000000 : ℝ)|^1041 ≤ (42797534786029/100000000000000 : ℝ)^785
        have hw : |(5273018447/10000000000 : ℝ)|=(5273018447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1135_box_14 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2684487019/5000000000 : ℝ)*x 0 + (82390907/156250000 : ℝ)*x 1 + (-1096424511/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684487019/5000000000 : ℝ)^1041 ≤ (10958343502131/25000000000000 : ℝ)^785 := by
    have hnat : (2684487019 : ℕ)^1041*25000000000000^785 ≤ 10958343502131^785*5000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684487019 5000000000 10958343502131 25000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (82390907/156250000 : ℝ)^1041 ≤ (42797530491521/100000000000000 : ℝ)^785 := by
    have hnat : (82390907 : ℕ)^1041*100000000000000^785 ≤ 42797530491521^785*156250000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82390907 156250000 42797530491521 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1096424511/5000000000 : ℝ)^1041 ≤ (13369095474403/100000000000000 : ℝ)^785 := by
    have hnat : (1096424511 : ℕ)^1041*100000000000000^785 ≤ 13369095474403^785*5000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1096424511 5000000000 13369095474403 100000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684487019/5000000000 : ℝ), (82390907/156250000 : ℝ), (-1096424511/5000000000 : ℝ)] ![(10958343502131/25000000000000 : ℝ), (42797530491521/100000000000000 : ℝ), (13369095474403/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684487019/5000000000 : ℝ)|^1041 ≤ (10958343502131/25000000000000 : ℝ)^785
        have hw : |(2684487019/5000000000 : ℝ)|=(2684487019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(82390907/156250000 : ℝ)|^1041 ≤ (42797530491521/100000000000000 : ℝ)^785
        have hw : |(82390907/156250000 : ℝ)|=(82390907/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1096424511/5000000000 : ℝ)|^1041 ≤ (13369095474403/100000000000000 : ℝ)^785
        have hw : |(-1096424511/5000000000 : ℝ)|=(1096424511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1135_box_15 (p : ℝ) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4239290501/10000000000 : ℝ)*x 0 + (4430818387/10000000000 : ℝ)*x 1 + (221540929/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4239290501/10000000000 : ℝ)^1041 ≤ (16022047968151/50000000000000 : ℝ)^785 := by
    have hnat : (4239290501 : ℕ)^1041*50000000000000^785 ≤ 16022047968151^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4239290501 10000000000 16022047968151 50000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4430818387/10000000000 : ℝ)^1041 ≤ (6795590208297/20000000000000 : ℝ)^785 := by
    have hnat : (4430818387 : ℕ)^1041*20000000000000^785 ≤ 6795590208297^785*10000000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4430818387 10000000000 6795590208297 20000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (221540929/500000000 : ℝ)^1041 ≤ (1359118120167/4000000000000 : ℝ)^785 := by
    have hnat : (221540929 : ℕ)^1041*4000000000000^785 ≤ 1359118120167^785*500000000^1041 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221540929 500000000 1359118120167 4000000000000 1041 785 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1041/256 : ℝ)) 1041 785 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4239290501/10000000000 : ℝ), (4430818387/10000000000 : ℝ), (221540929/500000000 : ℝ)] ![(16022047968151/50000000000000 : ℝ), (6795590208297/20000000000000 : ℝ), (1359118120167/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4239290501/10000000000 : ℝ)|^1041 ≤ (16022047968151/50000000000000 : ℝ)^785
        have hw : |(4239290501/10000000000 : ℝ)|=(4239290501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4430818387/10000000000 : ℝ)|^1041 ≤ (6795590208297/20000000000000 : ℝ)^785
        have hw : |(4430818387/10000000000 : ℝ)|=(4430818387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(221540929/500000000 : ℝ)|^1041 ≤ (1359118120167/4000000000000 : ℝ)^785
        have hw : |(221540929/500000000 : ℝ)|=(221540929/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1135_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37334287/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3511/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2269/20000 : ℝ)*pair X i i ≤ pair X i h) :
    -(6223/10000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59293/100000 : ℝ) ∧ (79787/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (83109/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3511/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2269/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3511/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2269/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3511/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2269/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3511/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2269/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3511/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2269/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3511/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2269/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2269/20000 : ℝ) ^ (8327/2048 : ℝ) ≤ (2870401373201317/20000000000000000000 : ℝ) := by
    have hpowers : (2269/20000 : ℝ)^8327 ≤ (2870401373201317/20000000000000000000 : ℝ)^2048 := by
      have hnat : (2269 : ℕ)^8327*20000000000000000000^2048 ≤ 2870401373201317^2048*20000^8327 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2269 20000 2870401373201317 20000000000000000000 8327 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2269/20000 : ℝ)) (X := (2870401373201317/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8327 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3511/25000 : ℝ) ^ (8327/2048 : ℝ) ≤ (17089824941450229/50000000000000000000 : ℝ) := by
    have hpowers : (3511/25000 : ℝ)^8327 ≤ (17089824941450229/50000000000000000000 : ℝ)^2048 := by
      have hnat : (3511 : ℕ)^8327*50000000000000000000^2048 ≤ 17089824941450229^2048*25000^8327 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3511 25000 17089824941450229 50000000000000000000 8327 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3511/25000 : ℝ)) (X := (17089824941450229/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8327 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002870401373201317/10000000000000000000 : ℝ) ≤ (10000705889987827/10000000000000000 : ℝ) ^ (8327/2048 : ℝ) := by
    have hpowers : (10002870401373201317/10000000000000000000 : ℝ)^2048 ≤ (10000705889987827/10000000000000000 : ℝ)^8327 := by
      have hnat : (10002870401373201317 : ℕ)^2048*10000000000000000^8327 ≤ 10000705889987827^8327*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002870401373201317 10000000000000000000 10000705889987827 10000000000000000 2048 8327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000705889987827/10000000000000000 : ℝ)) (X := (10002870401373201317/10000000000000000000 : ℝ)) (by norm_num) 8327 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048531656748907043/100000000000000000000 : ℝ) ≤ (10001193402804801/10000000000000000 : ℝ) ^ (8327/2048 : ℝ) := by
    have hpowers : (100048531656748907043/100000000000000000000 : ℝ)^2048 ≤ (10001193402804801/10000000000000000 : ℝ)^8327 := by
      have hnat : (100048531656748907043 : ℕ)^2048*10000000000000000^8327 ≤ 10001193402804801^8327*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048531656748907043 100000000000000000000 10001193402804801 10000000000000000 2048 8327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001193402804801/10000000000000000 : ℝ)) (X := (100048531656748907043/100000000000000000000 : ℝ)) (by norm_num) 8327 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017089824941450229/25000000000000000000 : ℝ) ≤ (400067236624871/400000000000000 : ℝ) ^ (8327/2048 : ℝ) := by
    have hpowers : (25017089824941450229/25000000000000000000 : ℝ)^2048 ≤ (400067236624871/400000000000000 : ℝ)^8327 := by
      have hnat : (25017089824941450229 : ℕ)^2048*400000000000000^8327 ≤ 400067236624871^8327*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017089824941450229 25000000000000000000 400067236624871 400000000000000 2048 8327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400067236624871/400000000000000 : ℝ)) (X := (25017089824941450229/25000000000000000000 : ℝ)) (by norm_num) 8327 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2870401373201317/20000000000000000000 : ℝ) ≤ ((26980843531260005013/26990000000000000000 : ℝ)+2*(243756408487/134950000000000 : ℝ)*(2269/20000 : ℝ))^(8327/2048 : ℝ) := by
    rw [show (26980843531260005013/26990000000000000000 : ℝ)+2*(243756408487/134950000000000 : ℝ)*(2269/20000 : ℝ)=(10000705889987827/10000000000000000 : ℝ) by norm_num, show 1+2*(2870401373201317/20000000000000000000 : ℝ)=(10002870401373201317/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17089824941450229/50000000000000000000 : ℝ)+(2870401373201317/20000000000000000000 : ℝ) ≤ ((26980843531260005013/26990000000000000000 : ℝ)+(243756408487/134950000000000 : ℝ)*((3511/25000 : ℝ)+(2269/20000 : ℝ)))^(8327/2048 : ℝ) := by
    rw [show (26980843531260005013/26990000000000000000 : ℝ)+(243756408487/134950000000000 : ℝ)*((3511/25000 : ℝ)+(2269/20000 : ℝ))=(10001193402804801/10000000000000000 : ℝ) by norm_num, show 1+(17089824941450229/50000000000000000000 : ℝ)+(2870401373201317/20000000000000000000 : ℝ)=(100048531656748907043/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17089824941450229/50000000000000000000 : ℝ) ≤ ((26980843531260005013/26990000000000000000 : ℝ)+2*(243756408487/134950000000000 : ℝ)*(3511/25000 : ℝ))^(8327/2048 : ℝ) := by
    rw [show (26980843531260005013/26990000000000000000 : ℝ)+2*(243756408487/134950000000000 : ℝ)*(3511/25000 : ℝ)=(400067236624871/400000000000000 : ℝ) by norm_num, show 1+2*(17089824941450229/50000000000000000000 : ℝ)=(25017089824941450229/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26980843531260005013/26990000000000000000 : ℝ)*(X 1 0+X 2 0)+(243756408487/134950000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8327/2048 : ℝ)) (lo := (2269/20000 : ℝ)) (hi := (3511/25000 : ℝ)) (c := (26980843531260005013/26990000000000000000 : ℝ)) (alpha := (243756408487/134950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26980843531260005013/26990000000000000000 : ℝ)*(X 0 1+X 2 1)+(243756408487/134950000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8327/2048 : ℝ)) (lo := (2269/20000 : ℝ)) (hi := (3511/25000 : ℝ)) (c := (26980843531260005013/26990000000000000000 : ℝ)) (alpha := (243756408487/134950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26980843531260005013/26990000000000000000 : ℝ)*(X 0 2+X 1 2)+(243756408487/134950000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8327/2048 : ℝ)) (lo := (2269/20000 : ℝ)) (hi := (3511/25000 : ℝ)) (c := (26980843531260005013/26990000000000000000 : ℝ)) (alpha := (243756408487/134950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2043121617/10000000000 : ℝ)*X 0 0+(2688203801/5000000000 : ℝ)*X 0 1+(2688203743/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2647959899/5000000000 : ℝ)*X 1 0+(-215225927/1000000000 : ℝ)*X 1 1+(2688203819/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((661990037/1250000000 : ℝ)*X 2 0+(2688203733/5000000000 : ℝ)*X 2 1+(-2152258833/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2236639287/5000000000 : ℝ)*X 0 0+(539245953/1250000000 : ℝ)*X 0 1+(431396739/1000000000 : ℝ)*X 0 2+(2236639287/5000000000 : ℝ)*X 1 0+(539245953/1250000000 : ℝ)*X 1 1+(431396739/1000000000 : ℝ)*X 1 2+(2236639287/5000000000 : ℝ)*X 2 0+(539245953/1250000000 : ℝ)*X 2 1+(431396739/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-287343389/1250000000 : ℝ)*X 0 0+(2640526307/5000000000 : ℝ)*X 0 1+(5281052663/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((13408247/25000000 : ℝ)*X 1 0+(-2189747971/10000000000 : ℝ)*X 1 1+(5281052637/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2681649399/5000000000 : ℝ)*X 2 0+(528105269/1000000000 : ℝ)*X 2 1+(-437949581/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((212884423/500000000 : ℝ)*X 0 0+(110543543/250000000 : ℝ)*X 0 1+(552717703/1250000000 : ℝ)*X 0 2+(212884423/500000000 : ℝ)*X 1 0+(110543543/250000000 : ℝ)*X 1 1+(552717703/1250000000 : ℝ)*X 1 2+(212884423/500000000 : ℝ)*X 2 0+(110543543/250000000 : ℝ)*X 2 1+(552717703/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2245299951/10000000000 : ℝ)*X 0 0+(2608107663/5000000000 : ℝ)*X 0 1+(5386015349/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5289127687/10000000000 : ℝ)*X 1 0+(-214841239/1000000000 : ℝ)*X 1 1+(215440613/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5289127683/10000000000 : ℝ)*X 2 0+(269300769/500000000 : ℝ)*X 2 1+(-2148412323/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4494727819/10000000000 : ℝ)*X 0 0+(4303102279/10000000000 : ℝ)*X 0 1+(1075775611/2500000000 : ℝ)*X 0 2+(4494727819/10000000000 : ℝ)*X 1 0+(4303102279/10000000000 : ℝ)*X 1 1+(1075775611/2500000000 : ℝ)*X 1 2+(4494727819/10000000000 : ℝ)*X 2 0+(4303102279/10000000000 : ℝ)*X 2 1+(1075775611/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2096891787/10000000000 : ℝ)*X 0 0+(169998819/312500000 : ℝ)*X 0 1+(1318254419/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5368973607/10000000000 : ℝ)*X 1 0+(-2192849069/10000000000 : ℝ)*X 1 1+(5273018447/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2684487019/5000000000 : ℝ)*X 2 0+(82390907/156250000 : ℝ)*X 2 1+(-1096424511/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4239290501/10000000000 : ℝ)*X 0 0+(4430818387/10000000000 : ℝ)*X 0 1+(221540929/500000000 : ℝ)*X 0 2+(4239290501/10000000000 : ℝ)*X 1 0+(4430818387/10000000000 : ℝ)*X 1 1+(221540929/500000000 : ℝ)*X 1 2+(4239290501/10000000000 : ℝ)*X 2 0+(4430818387/10000000000 : ℝ)*X 2 1+(221540929/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1135_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-6223/10000 : ℝ) ≤ (-419881613077202453277723433986411/674750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6778541/12500000000000 : ℝ)*(upper1) + (556273/12500000000000 : ℝ)*(upper4) + (60554653/100000000000000 : ℝ)*(upper5) + (1957397910170549/50000000000000 : ℝ)*(major0) + (1957397910170549/50000000000000 : ℝ)*(major1) + (1957397910170549/50000000000000 : ℝ)*(major2) + (113293831/50000000000000 : ℝ)*(sp1) + (96068081/2000000000000 : ℝ)*(sp3) + (2614441023114321/50000000000000 : ℝ)*(sp4) + (1307221474173643/25000000000000 : ℝ)*(sp5) + (1307219782332177/25000000000000 : ℝ)*(sp6) + (131072164545237/5000000000000 : ℝ)*(sp7) + (509631699/12500000000000 : ℝ)*(sp8) + (279758141/4000000000000 : ℝ)*(sp14) + (262144809430879/10000000000000 : ℝ)*(f.failure) + (5228886123282233/100000000000000 : ℝ)*(f.sum) + (2737491243421/421718750000000000000000000 : ℝ)*base65 + (7045302577887562137/1349500000000000000000000000000000 : ℝ)*base67 + (7735546006345437863/1349500000000000000000000000000000 : ℝ)*base70 + (14329067163185562137/1349500000000000000000000000000000 : ℝ)*base71 + (23629244549673/3373750000000000000000000000 : ℝ)*base73 + (23320909989712437863/1349500000000000000000000000000000 : ℝ)*base76 + (17399947450414562137/1349500000000000000000000000000000 : ℝ)*base77 + (13406410310157562137/1349500000000000000000000000000000 : ℝ)*base79 + (27762767278849/6747500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1751727/250000000000000000000 : ℝ)*base90 + (1751727/250000000000000000000 : ℝ)*base92 + (1751727/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (59293/100000 : ℝ) ≤ (80019413689059770983872690065739/134950000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (30249001/100000000000000 : ℝ)*(upper0) + (42060923/50000000000000 : ℝ)*(lower1) + (22439597/6250000000000 : ℝ)*(upper4) + (397883525966233/10000000000000 : ℝ)*(major0) + (397883525966233/10000000000000 : ℝ)*(major1) + (397883525966233/10000000000000 : ℝ)*(major2) + (5273564523063003/100000000000000 : ℝ)*(sp0) + (1318390099380633/25000000000000 : ℝ)*(sp1) + (5273561906814459/100000000000000 : ℝ)*(sp2) + (1332159453134099/50000000000000 : ℝ)*(sp3) + (6430066881/50000000000000 : ℝ)*(sp6) + (11645740421/100000000000000 : ℝ)*(sp7) + (5121942609/50000000000000 : ℝ)*(sp8) + (1796178211/12500000000000 : ℝ)*(sp9) + (133216527600431/5000000000000 : ℝ)*(f.failure) + (5273574766948221/100000000000000 : ℝ)*(f.sum) + (230995362927/2699000000000000000000000000 : ℝ)*base65 + (1552595234277526029/269900000000000000000000000000000 : ℝ)*base67 + (1967212127709326029/269900000000000000000000000000000 : ℝ)*base69 + (2046226691413326029/269900000000000000000000000000000 : ℝ)*base71 + (14704163448799/674750000000000000000000000 : ℝ)*base73 + (2556264430836926029/269900000000000000000000000000000 : ℝ)*base75 + (1528432786028126029/269900000000000000000000000000000 : ℝ)*base77 + (13524368485357526029/269900000000000000000000000000000 : ℝ)*base79 + (891628921049/2699000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (222303/125000000000000000000 : ℝ)*base90 + (222303/125000000000000000000 : ℝ)*base92 + (222303/125000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (79787/100000 : ℝ) ≤ (269189132908248325138908101255667/337375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15797777/50000000000000 : ℝ)*(upper0) + (12028327/25000000000000 : ℝ)*(lower3) + (3332837/25000000000000 : ℝ)*(upper4) + (2223388879437453/50000000000000 : ℝ)*(major0) + (2223388879437453/50000000000000 : ℝ)*(major1) + (2223388879437453/50000000000000 : ℝ)*(major2) + (1482321899/3125000000000 : ℝ)*(sp1) + (1763127259/2500000000000 : ℝ)*(sp2) + (5396898121/25000000000000 : ℝ)*(sp3) + (138077173/12500000000000 : ℝ)*(sp4) + (5889281081734883/100000000000000 : ℝ)*(sp8) + (5889234752051499/100000000000000 : ℝ)*(sp9) + (5889211661261907/100000000000000 : ℝ)*(sp10) + (297765531224687/10000000000000 : ℝ)*(sp11) + (2977676899839353/100000000000000 : ℝ)*(f.failure) + (5889282186352267/100000000000000 : ℝ)*(f.sum) + (36216469570031/13495000000000000000000000000 : ℝ)*base66 + (6998866450187848111/1349500000000000000000000000000000 : ℝ)*base68 + (12540515892628348111/1349500000000000000000000000000000 : ℝ)*base70 + (12780743388916348111/1349500000000000000000000000000000 : ℝ)*base72 + (133707885051919/3373750000000000000000000000 : ℝ)*base74 + (12961121844928348111/1349500000000000000000000000000000 : ℝ)*base76 + (13909546650134348111/1349500000000000000000000000000000 : ℝ)*base78 + (393291338105151889/1349500000000000000000000000000000 : ℝ)*base79 + (16743462353939/13495000000000000000000000000 : ℝ)*base81 + (8796311/2500000000000000000000 : ℝ)*base89 + (8796311/2500000000000000000000 : ℝ)*base91 + (8796311/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-83109/100000 : ℝ) ≤ (-1121518421388368878041982239011163/1349500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (649999/2500000000000 : ℝ)*(lower1) + (22269181/25000000000000 : ℝ)*(lower2) + (76230811/50000000000000 : ℝ)*(upper5) + (4481748266274839/100000000000000 : ℝ)*(major0) + (4481748266274839/100000000000000 : ℝ)*(major1) + (4481748266274839/100000000000000 : ℝ)*(major2) + (24290977169/100000000000000 : ℝ)*(sp4) + (74488824047/25000000000000 : ℝ)*(sp6) + (215364880721/50000000000000 : ℝ)*(sp7) + (1842158873/5000000000000 : ℝ)*(sp8) + (5990043419148237/100000000000000 : ℝ)*(sp12) + (1198020910660573/20000000000000 : ℝ)*(sp13) + (5989806598006677/100000000000000 : ℝ)*(sp14) + (93770728824567/3125000000000 : ℝ)*(sp15) + (1500547026073793/50000000000000 : ℝ)*(f.failure) + (1198020910660573/20000000000000 : ℝ)*(f.sum) + (73499710085471/13495000000000000000000000000 : ℝ)*base65 + (7195702923684367907/2699000000000000000000000000000000 : ℝ)*base67 + (23543545553921367907/2699000000000000000000000000000000 : ℝ)*base69 + (43079656817913367907/2699000000000000000000000000000000 : ℝ)*base71 + (21612371466899/13495000000000000000000000000 : ℝ)*base74 + (21796674871577367907/2699000000000000000000000000000000 : ℝ)*base75 + (23281008191108367907/2699000000000000000000000000000000 : ℝ)*base77 + (37294132603078367907/2699000000000000000000000000000000 : ℝ)*base79 + (859305568459/843437500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (16459409/1250000000000000000000 : ℝ)*base90 + (16459409/1250000000000000000000 : ℝ)*base92 + (16459409/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1135_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37334287/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3511/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2269/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(6223/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(59293/100000 : ℝ) else (79787/100000 : ℝ) ≤ X j i ∧ X j i ≤ (83109/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1135_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1135_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37334287/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2809/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2269/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(6223/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(59293/100000 : ℝ) else (79787/100000 : ℝ) ≤ X j i ∧ X j i ≤ (83109/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1135_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1135_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8327/2048 : ℝ) ≤ p) (hpb : p ≤ (1041/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37334287/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2809/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2269/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(6223/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(59293/100000 : ℝ) else (79787/100000 : ℝ) ≤ X j i ∧ X j i ≤ (83109/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1135_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
