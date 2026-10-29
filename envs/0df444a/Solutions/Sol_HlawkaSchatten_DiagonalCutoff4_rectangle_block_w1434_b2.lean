-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1434_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:55:11.653327+00:00
-- url     : https://prove2.me/submissions/efd83671-ae10-4173-b8e5-01b20c3dd0b0

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
theorem support_rectangle_w1434_s6_0 (p : ℝ) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-393415981/2000000000 : ℝ)*x 0 + (1081592543/2000000000 : ℝ)*x 1 + (5247016253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (393415981/2000000000 : ℝ)^2197 ≤ (12001747168309/100000000000000 : ℝ)^1685 := by
    have hnat : (393415981 : ℕ)^2197*100000000000000^1685 ≤ 12001747168309^1685*2000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      393415981 2000000000 12001747168309 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081592543/2000000000 : ℝ)^2197 ≤ (22432824530037/50000000000000 : ℝ)^1685 := by
    have hnat : (1081592543 : ℕ)^2197*50000000000000^1685 ≤ 22432824530037^1685*2000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081592543 2000000000 22432824530037 50000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5247016253/10000000000 : ℝ)^2197 ≤ (43132603758317/100000000000000 : ℝ)^1685 := by
    have hnat : (5247016253 : ℕ)^2197*100000000000000^1685 ≤ 43132603758317^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247016253 10000000000 43132603758317 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2197/512 : ℝ)) 2197 1685 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-393415981/2000000000 : ℝ), (1081592543/2000000000 : ℝ), (5247016253/10000000000 : ℝ)] ![(12001747168309/100000000000000 : ℝ), (22432824530037/50000000000000 : ℝ), (43132603758317/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-393415981/2000000000 : ℝ)|^2197 ≤ (12001747168309/100000000000000 : ℝ)^1685
        have hw : |(-393415981/2000000000 : ℝ)|=(393415981/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1081592543/2000000000 : ℝ)|^2197 ≤ (22432824530037/50000000000000 : ℝ)^1685
        have hw : |(1081592543/2000000000 : ℝ)|=(1081592543/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5247016253/10000000000 : ℝ)|^2197 ≤ (43132603758317/100000000000000 : ℝ)^1685
        have hw : |(5247016253/10000000000 : ℝ)|=(5247016253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1434_s6_1 (p : ℝ) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5347222047/10000000000 : ℝ)*x 0 + (-256127109/1250000000 : ℝ)*x 1 + (5247016253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347222047/10000000000 : ℝ)^2197 ≤ (44209735943343/100000000000000 : ℝ)^1685 := by
    have hnat : (5347222047 : ℕ)^2197*100000000000000^1685 ≤ 44209735943343^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347222047 10000000000 44209735943343 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (256127109/1250000000 : ℝ)^2197 ≤ (12657660289607/100000000000000 : ℝ)^1685 := by
    have hnat : (256127109 : ℕ)^2197*100000000000000^1685 ≤ 12657660289607^1685*1250000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256127109 1250000000 12657660289607 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5247016253/10000000000 : ℝ)^2197 ≤ (43132603758317/100000000000000 : ℝ)^1685 := by
    have hnat : (5247016253 : ℕ)^2197*100000000000000^1685 ≤ 43132603758317^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247016253 10000000000 43132603758317 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2197/512 : ℝ)) 2197 1685 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347222047/10000000000 : ℝ), (-256127109/1250000000 : ℝ), (5247016253/10000000000 : ℝ)] ![(44209735943343/100000000000000 : ℝ), (12657660289607/100000000000000 : ℝ), (43132603758317/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347222047/10000000000 : ℝ)|^2197 ≤ (44209735943343/100000000000000 : ℝ)^1685
        have hw : |(5347222047/10000000000 : ℝ)|=(5347222047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-256127109/1250000000 : ℝ)|^2197 ≤ (12657660289607/100000000000000 : ℝ)^1685
        have hw : |(-256127109/1250000000 : ℝ)|=(256127109/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5247016253/10000000000 : ℝ)|^2197 ≤ (43132603758317/100000000000000 : ℝ)^1685
        have hw : |(5247016253/10000000000 : ℝ)|=(5247016253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1434_s6_2 (p : ℝ) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5347222047/10000000000 : ℝ)*x 0 + (5247016253/10000000000 : ℝ)*x 1 + (-256127109/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347222047/10000000000 : ℝ)^2197 ≤ (44209735943343/100000000000000 : ℝ)^1685 := by
    have hnat : (5347222047 : ℕ)^2197*100000000000000^1685 ≤ 44209735943343^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347222047 10000000000 44209735943343 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247016253/10000000000 : ℝ)^2197 ≤ (43132603758317/100000000000000 : ℝ)^1685 := by
    have hnat : (5247016253 : ℕ)^2197*100000000000000^1685 ≤ 43132603758317^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247016253 10000000000 43132603758317 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (256127109/1250000000 : ℝ)^2197 ≤ (12657660289607/100000000000000 : ℝ)^1685 := by
    have hnat : (256127109 : ℕ)^2197*100000000000000^1685 ≤ 12657660289607^1685*1250000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256127109 1250000000 12657660289607 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2197/512 : ℝ)) 2197 1685 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347222047/10000000000 : ℝ), (5247016253/10000000000 : ℝ), (-256127109/1250000000 : ℝ)] ![(44209735943343/100000000000000 : ℝ), (43132603758317/100000000000000 : ℝ), (12657660289607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347222047/10000000000 : ℝ)|^2197 ≤ (44209735943343/100000000000000 : ℝ)^1685
        have hw : |(5347222047/10000000000 : ℝ)|=(5347222047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247016253/10000000000 : ℝ)|^2197 ≤ (43132603758317/100000000000000 : ℝ)^1685
        have hw : |(5247016253/10000000000 : ℝ)|=(5247016253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-256127109/1250000000 : ℝ)|^2197 ≤ (12657660289607/100000000000000 : ℝ)^1685
        have hw : |(-256127109/1250000000 : ℝ)|=(256127109/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1434_s6_3 (p : ℝ) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2151562257/5000000000 : ℝ)*x 0 + (2065943689/5000000000 : ℝ)*x 1 + (4480706353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2151562257/5000000000 : ℝ)^2197 ≤ (16652382889017/50000000000000 : ℝ)^1685 := by
    have hnat : (2151562257 : ℕ)^2197*50000000000000^1685 ≤ 16652382889017^1685*5000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151562257 5000000000 16652382889017 50000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2065943689/5000000000 : ℝ)^2197 ≤ (31587284011829/100000000000000 : ℝ)^1685 := by
    have hnat : (2065943689 : ℕ)^2197*100000000000000^1685 ≤ 31587284011829^1685*5000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2065943689 5000000000 31587284011829 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4480706353/10000000000 : ℝ)^2197 ≤ (4388493775053/12500000000000 : ℝ)^1685 := by
    have hnat : (4480706353 : ℕ)^2197*12500000000000^1685 ≤ 4388493775053^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4480706353 10000000000 4388493775053 12500000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2197/512 : ℝ)) 2197 1685 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2151562257/5000000000 : ℝ), (2065943689/5000000000 : ℝ), (4480706353/10000000000 : ℝ)] ![(16652382889017/50000000000000 : ℝ), (31587284011829/100000000000000 : ℝ), (4388493775053/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2151562257/5000000000 : ℝ)|^2197 ≤ (16652382889017/50000000000000 : ℝ)^1685
        have hw : |(2151562257/5000000000 : ℝ)|=(2151562257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2065943689/5000000000 : ℝ)|^2197 ≤ (31587284011829/100000000000000 : ℝ)^1685
        have hw : |(2065943689/5000000000 : ℝ)|=(2065943689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4480706353/10000000000 : ℝ)|^2197 ≤ (4388493775053/12500000000000 : ℝ)^1685
        have hw : |(4480706353/10000000000 : ℝ)|=(4480706353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1434_s6_4 (p : ℝ) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-983545543/5000000000 : ℝ)*x 0 + (5247597029/10000000000 : ℝ)*x 1 + (1351844751/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (983545543/5000000000 : ℝ)^2197 ≤ (12001836115789/100000000000000 : ℝ)^1685 := by
    have hnat : (983545543 : ℕ)^2197*100000000000000^1685 ≤ 12001836115789^1685*5000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      983545543 5000000000 12001836115789 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247597029/10000000000 : ℝ)^2197 ≤ (43138828758697/100000000000000 : ℝ)^1685 := by
    have hnat : (5247597029 : ℕ)^2197*100000000000000^1685 ≤ 43138828758697^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247597029 10000000000 43138828758697 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1351844751/2500000000 : ℝ)^2197 ≤ (22429667554781/50000000000000 : ℝ)^1685 := by
    have hnat : (1351844751 : ℕ)^2197*50000000000000^1685 ≤ 22429667554781^1685*2500000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351844751 2500000000 22429667554781 50000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2197/512 : ℝ)) 2197 1685 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-983545543/5000000000 : ℝ), (5247597029/10000000000 : ℝ), (1351844751/2500000000 : ℝ)] ![(12001836115789/100000000000000 : ℝ), (43138828758697/100000000000000 : ℝ), (22429667554781/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-983545543/5000000000 : ℝ)|^2197 ≤ (12001836115789/100000000000000 : ℝ)^1685
        have hw : |(-983545543/5000000000 : ℝ)|=(983545543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247597029/10000000000 : ℝ)|^2197 ≤ (43138828758697/100000000000000 : ℝ)^1685
        have hw : |(5247597029/10000000000 : ℝ)|=(5247597029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1351844751/2500000000 : ℝ)|^2197 ≤ (22429667554781/50000000000000 : ℝ)^1685
        have hw : |(1351844751/2500000000 : ℝ)|=(1351844751/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1434_s6_5 (p : ℝ) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1326340003/2500000000 : ℝ)*x 0 + (-377730801/2000000000 : ℝ)*x 1 + (216295157/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326340003/2500000000 : ℝ)^2197 ≤ (43758999799067/100000000000000 : ℝ)^1685 := by
    have hnat : (1326340003 : ℕ)^2197*100000000000000^1685 ≤ 43758999799067^1685*2500000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326340003 2500000000 43758999799067 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (377730801/2000000000 : ℝ)^2197 ≤ (2845416485509/25000000000000 : ℝ)^1685 := by
    have hnat : (377730801 : ℕ)^2197*25000000000000^1685 ≤ 2845416485509^1685*2000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      377730801 2000000000 2845416485509 25000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216295157/400000000 : ℝ)^2197 ≤ (140185419547/312500000000 : ℝ)^1685 := by
    have hnat : (216295157 : ℕ)^2197*312500000000^1685 ≤ 140185419547^1685*400000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216295157 400000000 140185419547 312500000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2197/512 : ℝ)) 2197 1685 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326340003/2500000000 : ℝ), (-377730801/2000000000 : ℝ), (216295157/400000000 : ℝ)] ![(43758999799067/100000000000000 : ℝ), (2845416485509/25000000000000 : ℝ), (140185419547/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326340003/2500000000 : ℝ)|^2197 ≤ (43758999799067/100000000000000 : ℝ)^1685
        have hw : |(1326340003/2500000000 : ℝ)|=(1326340003/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-377730801/2000000000 : ℝ)|^2197 ≤ (2845416485509/25000000000000 : ℝ)^1685
        have hw : |(-377730801/2000000000 : ℝ)|=(377730801/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216295157/400000000 : ℝ)|^2197 ≤ (140185419547/312500000000 : ℝ)^1685
        have hw : |(216295157/400000000 : ℝ)|=(216295157/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1434_s6_6 (p : ℝ) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1326339939/2500000000 : ℝ)*x 0 + (2703689511/5000000000 : ℝ)*x 1 + (-94432711/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326339939/2500000000 : ℝ)^2197 ≤ (43758997045963/100000000000000 : ℝ)^1685 := by
    have hnat : (1326339939 : ℕ)^2197*100000000000000^1685 ≤ 43758997045963^1685*2500000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326339939 2500000000 43758997045963 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2703689511/5000000000 : ℝ)^2197 ≤ (5607416913033/12500000000000 : ℝ)^1685 := by
    have hnat : (2703689511 : ℕ)^2197*12500000000000^1685 ≤ 5607416913033^1685*5000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703689511 5000000000 5607416913033 12500000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (94432711/500000000 : ℝ)^2197 ≤ (2845416907849/25000000000000 : ℝ)^1685 := by
    have hnat : (94432711 : ℕ)^2197*25000000000000^1685 ≤ 2845416907849^1685*500000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94432711 500000000 2845416907849 25000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2197/512 : ℝ)) 2197 1685 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326339939/2500000000 : ℝ), (2703689511/5000000000 : ℝ), (-94432711/500000000 : ℝ)] ![(43758997045963/100000000000000 : ℝ), (5607416913033/12500000000000 : ℝ), (2845416907849/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326339939/2500000000 : ℝ)|^2197 ≤ (43758997045963/100000000000000 : ℝ)^1685
        have hw : |(1326339939/2500000000 : ℝ)|=(1326339939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2703689511/5000000000 : ℝ)|^2197 ≤ (5607416913033/12500000000000 : ℝ)^1685
        have hw : |(2703689511/5000000000 : ℝ)|=(2703689511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-94432711/500000000 : ℝ)|^2197 ≤ (2845416907849/25000000000000 : ℝ)^1685
        have hw : |(-94432711/500000000 : ℝ)|=(94432711/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1434_s6_7 (p : ℝ) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4303148851/10000000000 : ℝ)*x 0 + (2239723849/5000000000 : ℝ)*x 1 + (4133152661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4303148851/10000000000 : ℝ)^2197 ≤ (16652505686663/50000000000000 : ℝ)^1685 := by
    have hnat : (4303148851 : ℕ)^2197*50000000000000^1685 ≤ 16652505686663^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4303148851 10000000000 16652505686663 50000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2239723849/5000000000 : ℝ)^2197 ≤ (35095092085251/100000000000000 : ℝ)^1685 := by
    have hnat : (2239723849 : ℕ)^2197*100000000000000^1685 ≤ 35095092085251^1685*5000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2239723849 5000000000 35095092085251 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4133152661/10000000000 : ℝ)^2197 ≤ (6319979306191/20000000000000 : ℝ)^1685 := by
    have hnat : (4133152661 : ℕ)^2197*20000000000000^1685 ≤ 6319979306191^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4133152661 10000000000 6319979306191 20000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2197/512 : ℝ)) 2197 1685 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4303148851/10000000000 : ℝ), (2239723849/5000000000 : ℝ), (4133152661/10000000000 : ℝ)] ![(16652505686663/50000000000000 : ℝ), (35095092085251/100000000000000 : ℝ), (6319979306191/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4303148851/10000000000 : ℝ)|^2197 ≤ (16652505686663/50000000000000 : ℝ)^1685
        have hw : |(4303148851/10000000000 : ℝ)|=(4303148851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2239723849/5000000000 : ℝ)|^2197 ≤ (35095092085251/100000000000000 : ℝ)^1685
        have hw : |(2239723849/5000000000 : ℝ)|=(2239723849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4133152661/10000000000 : ℝ)|^2197 ≤ (6319979306191/20000000000000 : ℝ)^1685
        have hw : |(4133152661/10000000000 : ℝ)|=(4133152661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1434_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158364909/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14763/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11347/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (227/2000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (369/2500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14763/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11347/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14763/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11347/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14763/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11347/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14763/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11347/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14763/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11347/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14763/100000 : ℝ)*(X 0 2+X 1 2) := by
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
  have hpowlo : (11347/100000 : ℝ) ^ (4393/1024 : ℝ) ≤ (1763732843829301/20000000000000000000 : ℝ) := by
    have hpowers : (11347/100000 : ℝ)^4393 ≤ (1763732843829301/20000000000000000000 : ℝ)^1024 := by
      have hnat : (11347 : ℕ)^4393*20000000000000000000^1024 ≤ 1763732843829301^1024*100000^4393 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11347 100000 1763732843829301 20000000000000000000 4393 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11347/100000 : ℝ)) (X := (1763732843829301/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4393 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14763/100000 : ℝ) ^ (4393/1024 : ℝ) ≤ (2727260764735389/10000000000000000000 : ℝ) := by
    have hpowers : (14763/100000 : ℝ)^4393 ≤ (2727260764735389/10000000000000000000 : ℝ)^1024 := by
      have hnat : (14763 : ℕ)^4393*10000000000000000000^1024 ≤ 2727260764735389^1024*100000^4393 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14763 100000 2727260764735389 10000000000000000000 4393 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14763/100000 : ℝ)) (X := (2727260764735389/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4393 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001763732843829301/10000000000000000000 : ℝ) ≤ (10000411094992001/10000000000000000 : ℝ) ^ (4393/1024 : ℝ) := by
    have hpowers : (10001763732843829301/10000000000000000000 : ℝ)^1024 ≤ (10000411094992001/10000000000000000 : ℝ)^4393 := by
      have hnat : (10001763732843829301 : ℕ)^1024*10000000000000000^4393 ≤ 10000411094992001^4393*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001763732843829301 10000000000000000000 10000411094992001 10000000000000000 1024 4393 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000411094992001/10000000000000000 : ℝ)) (X := (10001763732843829301/10000000000000000000 : ℝ)) (by norm_num) 4393 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20007218254373300079/20000000000000000000 : ℝ) ≤ (5000420582163091/5000000000000000 : ℝ) ^ (4393/1024 : ℝ) := by
    have hpowers : (20007218254373300079/20000000000000000000 : ℝ)^1024 ≤ (5000420582163091/5000000000000000 : ℝ)^4393 := by
      have hnat : (20007218254373300079 : ℕ)^1024*5000000000000000^4393 ≤ 5000420582163091^4393*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20007218254373300079 20000000000000000000 5000420582163091 5000000000000000 1024 4393 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000420582163091/5000000000000000 : ℝ)) (X := (20007218254373300079/20000000000000000000 : ℝ)) (by norm_num) 4393 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5002727260764735389/5000000000000000000 : ℝ) ≤ (10001271233660363/10000000000000000 : ℝ) ^ (4393/1024 : ℝ) := by
    have hpowers : (5002727260764735389/5000000000000000000 : ℝ)^1024 ≤ (10001271233660363/10000000000000000 : ℝ)^4393 := by
      have hnat : (5002727260764735389 : ℕ)^1024*10000000000000000^4393 ≤ 10001271233660363^4393*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002727260764735389 5000000000000000000 10001271233660363 10000000000000000 1024 4393 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001271233660363/10000000000000000 : ℝ)) (X := (5002727260764735389/5000000000000000000 : ℝ)) (by norm_num) 4393 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1763732843829301/20000000000000000000 : ℝ) ≤ ((2439403164787340843/2440000000000000000 : ℝ)+2*(430069334181/341600000000000 : ℝ)*(11347/100000 : ℝ))^(4393/1024 : ℝ) := by
    rw [show (2439403164787340843/2440000000000000000 : ℝ)+2*(430069334181/341600000000000 : ℝ)*(11347/100000 : ℝ)=(10000411094992001/10000000000000000 : ℝ) by norm_num, show 1+2*(1763732843829301/20000000000000000000 : ℝ)=(10001763732843829301/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2727260764735389/10000000000000000000 : ℝ)+(1763732843829301/20000000000000000000 : ℝ) ≤ ((2439403164787340843/2440000000000000000 : ℝ)+(430069334181/341600000000000 : ℝ)*((14763/100000 : ℝ)+(11347/100000 : ℝ)))^(4393/1024 : ℝ) := by
    rw [show (2439403164787340843/2440000000000000000 : ℝ)+(430069334181/341600000000000 : ℝ)*((14763/100000 : ℝ)+(11347/100000 : ℝ))=(5000420582163091/5000000000000000 : ℝ) by norm_num, show 1+(2727260764735389/10000000000000000000 : ℝ)+(1763732843829301/20000000000000000000 : ℝ)=(20007218254373300079/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2727260764735389/10000000000000000000 : ℝ) ≤ ((2439403164787340843/2440000000000000000 : ℝ)+2*(430069334181/341600000000000 : ℝ)*(14763/100000 : ℝ))^(4393/1024 : ℝ) := by
    rw [show (2439403164787340843/2440000000000000000 : ℝ)+2*(430069334181/341600000000000 : ℝ)*(14763/100000 : ℝ)=(10001271233660363/10000000000000000 : ℝ) by norm_num, show 1+2*(2727260764735389/10000000000000000000 : ℝ)=(5002727260764735389/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2439403164787340843/2440000000000000000 : ℝ)*(X 1 0+X 2 0)+(430069334181/341600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4393/1024 : ℝ)) (lo := (11347/100000 : ℝ)) (hi := (14763/100000 : ℝ)) (c := (2439403164787340843/2440000000000000000 : ℝ)) (alpha := (430069334181/341600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2439403164787340843/2440000000000000000 : ℝ)*(X 0 1+X 2 1)+(430069334181/341600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4393/1024 : ℝ)) (lo := (11347/100000 : ℝ)) (hi := (14763/100000 : ℝ)) (c := (2439403164787340843/2440000000000000000 : ℝ)) (alpha := (430069334181/341600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2439403164787340843/2440000000000000000 : ℝ)*(X 0 2+X 1 2)+(430069334181/341600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4393/1024 : ℝ)) (lo := (11347/100000 : ℝ)) (hi := (14763/100000 : ℝ)) (c := (2439403164787340843/2440000000000000000 : ℝ)) (alpha := (430069334181/341600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-393415981/2000000000 : ℝ)*X 0 0+(1081592543/2000000000 : ℝ)*X 0 1+(5247016253/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1434_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347222047/10000000000 : ℝ)*X 1 0+(-256127109/1250000000 : ℝ)*X 1 1+(5247016253/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1434_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347222047/10000000000 : ℝ)*X 2 0+(5247016253/10000000000 : ℝ)*X 2 1+(-256127109/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1434_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2151562257/5000000000 : ℝ)*X 0 0+(2065943689/5000000000 : ℝ)*X 0 1+(4480706353/10000000000 : ℝ)*X 0 2+(2151562257/5000000000 : ℝ)*X 1 0+(2065943689/5000000000 : ℝ)*X 1 1+(4480706353/10000000000 : ℝ)*X 1 2+(2151562257/5000000000 : ℝ)*X 2 0+(2065943689/5000000000 : ℝ)*X 2 1+(4480706353/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1434_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-983545543/5000000000 : ℝ)*X 0 0+(5247597029/10000000000 : ℝ)*X 0 1+(1351844751/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1434_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326340003/2500000000 : ℝ)*X 1 0+(-377730801/2000000000 : ℝ)*X 1 1+(216295157/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1434_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326339939/2500000000 : ℝ)*X 2 0+(2703689511/5000000000 : ℝ)*X 2 1+(-94432711/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1434_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4303148851/10000000000 : ℝ)*X 0 0+(2239723849/5000000000 : ℝ)*X 0 1+(4133152661/10000000000 : ℝ)*X 0 2+(4303148851/10000000000 : ℝ)*X 1 0+(2239723849/5000000000 : ℝ)*X 1 1+(4133152661/10000000000 : ℝ)*X 1 2+(4303148851/10000000000 : ℝ)*X 2 0+(2239723849/5000000000 : ℝ)*X 2 1+(4133152661/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1434_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3703625301181779667403332701/427000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (157473/10000000000 : ℝ)*(base19) + (733755767/50000000000000 : ℝ)*(base23) + (28666047/50000000000000 : ℝ)*(lower2) + (3375879/1562500000000 : ℝ)*(upper3) + (13812703/10000000000000 : ℝ)*(upper5) + (4540081163082733/100000000000000 : ℝ)*(major0) + (4540081163082733/100000000000000 : ℝ)*(major1) + (4540081163082733/100000000000000 : ℝ)*(major2) + (6213280876632039/100000000000000 : ℝ)*(sp0) + (1553328125569369/25000000000000 : ℝ)*(sp1) + (3106656304747971/50000000000000 : ℝ)*(sp2) + (286683137786461/10000000000000 : ℝ)*(sp3) + (8300093859/25000000000000 : ℝ)*(sp4) + (3316434703/20000000000000 : ℝ)*(sp7) + (716711990009531/25000000000000 : ℝ)*(f.failure) + (248532563080299/4000000000000 : ℝ)*(f.sum) + (78250530722447/17080000000000000000000000000 : ℝ)*base66 + (13594058013254397433/1708000000000000000000000000000000 : ℝ)*base67 + (10064817994138397433/1708000000000000000000000000000000 : ℝ)*base69 + (17199940475870397433/1708000000000000000000000000000000 : ℝ)*base71 + (5582465292433/17080000000000000000000000000 : ℝ)*base73 + (6630812570702397433/1708000000000000000000000000000000 : ℝ)*base75 + (8248790883254397433/1708000000000000000000000000000000 : ℝ)*base77 + (901635160021602567/1708000000000000000000000000000000 : ℝ)*base80 + (104515438753993/17080000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (39052321/2500000000000000000000 : ℝ)*base90 + (39052321/2500000000000000000000 : ℝ)*base92 + (39052321/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4830867823958102982976194087/427000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1946889477/100000000000000 : ℝ)*(base19) + (1787046541/100000000000000 : ℝ)*(base23) + (71176351/12500000000000 : ℝ)*(lower1) + (162708473/100000000000000 : ℝ)*(upper3) + (104801107/100000000000000 : ℝ)*(lower4) + (12794463/6250000000000 : ℝ)*(upper5) + (4573090607371929/100000000000000 : ℝ)*(major0) + (4573090607371929/100000000000000 : ℝ)*(major1) + (4573090607371929/100000000000000 : ℝ)*(major2) + (7019789489/100000000000000 : ℝ)*(sp1) + (97788890067411/1562500000000 : ℝ)*(sp4) + (3129239998817669/50000000000000 : ℝ)*(sp5) + (3129243588633881/50000000000000 : ℝ)*(sp6) + (1443845936656311/50000000000000 : ℝ)*(sp7) + (1443845936656311/50000000000000 : ℝ)*(f.failure) + (97788890067411/1562500000000 : ℝ)*(f.sum) + (36779386675091/17080000000000000000000000000 : ℝ)*base66 + (20902537779764776971/1708000000000000000000000000000000 : ℝ)*base68 + (7384993756947223029/1708000000000000000000000000000000 : ℝ)*base69 + (14358708788176776971/1708000000000000000000000000000000 : ℝ)*base72 + (76701390945491/17080000000000000000000000000 : ℝ)*base74 + (1584641944960776971/1708000000000000000000000000000000 : ℝ)*base76 + (5627443588540776971/1708000000000000000000000000000000 : ℝ)*base78 + (8644368578948776971/1708000000000000000000000000000000 : ℝ)*base80 + (110403210449011/17080000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (5790699/5000000000000000000000 : ℝ)*base89 + (5790699/5000000000000000000000 : ℝ)*base91 + (5790699/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1434_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158364909/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14763/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11347/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (227/2000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (369/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1434_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1434_s7_0 (p : ℝ) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1967081953/10000000000 : ℝ)*x 0 + (1081588261/2000000000 : ℝ)*x 1 + (262351817/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1967081953/10000000000 : ℝ)^2197 ≤ (12001763460619/100000000000000 : ℝ)^1685 := by
    have hnat : (1967081953 : ℕ)^2197*100000000000000^1685 ≤ 12001763460619^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1967081953 10000000000 12001763460619 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081588261/2000000000 : ℝ)^2197 ≤ (4486541746633/10000000000000 : ℝ)^1685 := by
    have hnat : (1081588261 : ℕ)^2197*10000000000000^1685 ≤ 4486541746633^1685*2000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081588261 2000000000 4486541746633 10000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262351817/500000000 : ℝ)^2197 ≤ (431328190557/1000000000000 : ℝ)^1685 := by
    have hnat : (262351817 : ℕ)^2197*1000000000000^1685 ≤ 431328190557^1685*500000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262351817 500000000 431328190557 1000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2197/512 : ℝ)) 2197 1685 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1967081953/10000000000 : ℝ), (1081588261/2000000000 : ℝ), (262351817/500000000 : ℝ)] ![(12001763460619/100000000000000 : ℝ), (4486541746633/10000000000000 : ℝ), (431328190557/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1967081953/10000000000 : ℝ)|^2197 ≤ (12001763460619/100000000000000 : ℝ)^1685
        have hw : |(-1967081953/10000000000 : ℝ)|=(1967081953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1081588261/2000000000 : ℝ)|^2197 ≤ (4486541746633/10000000000000 : ℝ)^1685
        have hw : |(1081588261/2000000000 : ℝ)|=(1081588261/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(262351817/500000000 : ℝ)|^2197 ≤ (431328190557/1000000000000 : ℝ)^1685
        have hw : |(262351817/500000000 : ℝ)|=(262351817/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1434_s7_1 (p : ℝ) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5347216607/10000000000 : ℝ)*x 0 + (-204899741/1000000000 : ℝ)*x 1 + (5247036349/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347216607/10000000000 : ℝ)^2197 ≤ (11052419325001/25000000000000 : ℝ)^1685 := by
    have hnat : (5347216607 : ℕ)^2197*25000000000000^1685 ≤ 11052419325001^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347216607 10000000000 11052419325001 25000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (204899741/1000000000 : ℝ)^2197 ≤ (12657503533347/100000000000000 : ℝ)^1685 := by
    have hnat : (204899741 : ℕ)^2197*100000000000000^1685 ≤ 12657503533347^1685*1000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      204899741 1000000000 12657503533347 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5247036349/10000000000 : ℝ)^2197 ≤ (10783204788041/25000000000000 : ℝ)^1685 := by
    have hnat : (5247036349 : ℕ)^2197*25000000000000^1685 ≤ 10783204788041^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247036349 10000000000 10783204788041 25000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2197/512 : ℝ)) 2197 1685 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347216607/10000000000 : ℝ), (-204899741/1000000000 : ℝ), (5247036349/10000000000 : ℝ)] ![(11052419325001/25000000000000 : ℝ), (12657503533347/100000000000000 : ℝ), (10783204788041/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347216607/10000000000 : ℝ)|^2197 ≤ (11052419325001/25000000000000 : ℝ)^1685
        have hw : |(5347216607/10000000000 : ℝ)|=(5347216607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-204899741/1000000000 : ℝ)|^2197 ≤ (12657503533347/100000000000000 : ℝ)^1685
        have hw : |(-204899741/1000000000 : ℝ)|=(204899741/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5247036349/10000000000 : ℝ)|^2197 ≤ (10783204788041/25000000000000 : ℝ)^1685
        have hw : |(5247036349/10000000000 : ℝ)|=(5247036349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1434_s7_2 (p : ℝ) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5347216591/10000000000 : ℝ)*x 0 + (5247036379/10000000000 : ℝ)*x 1 + (-128062337/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347216591/10000000000 : ℝ)^2197 ≤ (11052419281881/25000000000000 : ℝ)^1685 := by
    have hnat : (5347216591 : ℕ)^2197*25000000000000^1685 ≤ 11052419281881^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347216591 10000000000 11052419281881 25000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247036379/10000000000 : ℝ)^2197 ≤ (43132819473711/100000000000000 : ℝ)^1685 := by
    have hnat : (5247036379 : ℕ)^2197*100000000000000^1685 ≤ 43132819473711^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247036379 10000000000 43132819473711 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (128062337/625000000 : ℝ)^2197 ≤ (12657503388367/100000000000000 : ℝ)^1685 := by
    have hnat : (128062337 : ℕ)^2197*100000000000000^1685 ≤ 12657503388367^1685*625000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128062337 625000000 12657503388367 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2197/512 : ℝ)) 2197 1685 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347216591/10000000000 : ℝ), (5247036379/10000000000 : ℝ), (-128062337/625000000 : ℝ)] ![(11052419281881/25000000000000 : ℝ), (43132819473711/100000000000000 : ℝ), (12657503388367/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347216591/10000000000 : ℝ)|^2197 ≤ (11052419281881/25000000000000 : ℝ)^1685
        have hw : |(5347216591/10000000000 : ℝ)|=(5347216591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247036379/10000000000 : ℝ)|^2197 ≤ (43132819473711/100000000000000 : ℝ)^1685
        have hw : |(5247036379/10000000000 : ℝ)|=(5247036379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-128062337/625000000 : ℝ)|^2197 ≤ (12657503388367/100000000000000 : ℝ)^1685
        have hw : |(-128062337/625000000 : ℝ)|=(128062337/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1434_s7_3 (p : ℝ) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ)) (x : Fin 3 → ℝ) :
    (215156299/500000000 : ℝ)*x 0 + (413193219/1000000000 : ℝ)*x 1 + (2240330591/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215156299/500000000 : ℝ)^2197 ≤ (8326195143017/25000000000000 : ℝ)^1685 := by
    have hnat : (215156299 : ℕ)^2197*25000000000000^1685 ≤ 8326195143017^1685*500000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215156299 500000000 8326195143017 25000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (413193219/1000000000 : ℝ)^2197 ≤ (1974233167757/6250000000000 : ℝ)^1685 := by
    have hnat : (413193219 : ℕ)^2197*6250000000000^1685 ≤ 1974233167757^1685*1000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      413193219 1000000000 1974233167757 6250000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2240330591/5000000000 : ℝ)^2197 ≤ (1755374436271/5000000000000 : ℝ)^1685 := by
    have hnat : (2240330591 : ℕ)^2197*5000000000000^1685 ≤ 1755374436271^1685*5000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2240330591 5000000000 1755374436271 5000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2197/512 : ℝ)) 2197 1685 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(215156299/500000000 : ℝ), (413193219/1000000000 : ℝ), (2240330591/5000000000 : ℝ)] ![(8326195143017/25000000000000 : ℝ), (1974233167757/6250000000000 : ℝ), (1755374436271/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(215156299/500000000 : ℝ)|^2197 ≤ (8326195143017/25000000000000 : ℝ)^1685
        have hw : |(215156299/500000000 : ℝ)|=(215156299/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(413193219/1000000000 : ℝ)|^2197 ≤ (1974233167757/6250000000000 : ℝ)^1685
        have hw : |(413193219/1000000000 : ℝ)|=(413193219/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2240330591/5000000000 : ℝ)|^2197 ≤ (1755374436271/5000000000000 : ℝ)^1685
        have hw : |(2240330591/5000000000 : ℝ)|=(2240330591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1434_s7_4 (p : ℝ) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-983546589/5000000000 : ℝ)*x 0 + (5247616799/10000000000 : ℝ)*x 1 + (43258863/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (983546589/5000000000 : ℝ)^2197 ≤ (12001852758157/100000000000000 : ℝ)^1685 := by
    have hnat : (983546589 : ℕ)^2197*100000000000000^1685 ≤ 12001852758157^1685*5000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      983546589 5000000000 12001852758157 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247616799/10000000000 : ℝ)^2197 ≤ (43139040665521/100000000000000 : ℝ)^1685 := by
    have hnat : (5247616799 : ℕ)^2197*100000000000000^1685 ≤ 43139040665521^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247616799 10000000000 43139040665521 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (43258863/80000000 : ℝ)^2197 ≤ (44859106562913/100000000000000 : ℝ)^1685 := by
    have hnat : (43258863 : ℕ)^2197*100000000000000^1685 ≤ 44859106562913^1685*80000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43258863 80000000 44859106562913 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2197/512 : ℝ)) 2197 1685 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-983546589/5000000000 : ℝ), (5247616799/10000000000 : ℝ), (43258863/80000000 : ℝ)] ![(12001852758157/100000000000000 : ℝ), (43139040665521/100000000000000 : ℝ), (44859106562913/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-983546589/5000000000 : ℝ)|^2197 ≤ (12001852758157/100000000000000 : ℝ)^1685
        have hw : |(-983546589/5000000000 : ℝ)|=(983546589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247616799/10000000000 : ℝ)|^2197 ≤ (43139040665521/100000000000000 : ℝ)^1685
        have hw : |(5247616799/10000000000 : ℝ)|=(5247616799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(43258863/80000000 : ℝ)|^2197 ≤ (44859106562913/100000000000000 : ℝ)^1685
        have hw : |(43258863/80000000 : ℝ)|=(43258863/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1434_s7_5 (p : ℝ) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1326341307/2500000000 : ℝ)*x 0 + (-94433793/500000000 : ℝ)*x 1 + (5407357863/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326341307/2500000000 : ℝ)^2197 ≤ (43759055893573/100000000000000 : ℝ)^1685 := by
    have hnat : (1326341307 : ℕ)^2197*100000000000000^1685 ≤ 43759055893573^1685*2500000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326341307 2500000000 43759055893573 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (94433793/500000000 : ℝ)^2197 ≤ (11381837667681/100000000000000 : ℝ)^1685 := by
    have hnat : (94433793 : ℕ)^2197*100000000000000^1685 ≤ 11381837667681^1685*500000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94433793 500000000 11381837667681 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407357863/10000000000 : ℝ)^2197 ≤ (5607388304139/12500000000000 : ℝ)^1685 := by
    have hnat : (5407357863 : ℕ)^2197*12500000000000^1685 ≤ 5607388304139^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407357863 10000000000 5607388304139 12500000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2197/512 : ℝ)) 2197 1685 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326341307/2500000000 : ℝ), (-94433793/500000000 : ℝ), (5407357863/10000000000 : ℝ)] ![(43759055893573/100000000000000 : ℝ), (11381837667681/100000000000000 : ℝ), (5607388304139/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326341307/2500000000 : ℝ)|^2197 ≤ (43759055893573/100000000000000 : ℝ)^1685
        have hw : |(1326341307/2500000000 : ℝ)|=(1326341307/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-94433793/500000000 : ℝ)|^2197 ≤ (11381837667681/100000000000000 : ℝ)^1685
        have hw : |(-94433793/500000000 : ℝ)|=(94433793/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407357863/10000000000 : ℝ)|^2197 ≤ (5607388304139/12500000000000 : ℝ)^1685
        have hw : |(5407357863/10000000000 : ℝ)|=(5407357863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1434_s7_6 (p : ℝ) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ)) (x : Fin 3 → ℝ) :
    (13263413/25000000 : ℝ)*x 0 + (2703678927/5000000000 : ℝ)*x 1 + (-1888675909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13263413/25000000 : ℝ)^2197 ≤ (10939763898113/25000000000000 : ℝ)^1685 := by
    have hnat : (13263413 : ℕ)^2197*25000000000000^1685 ≤ 10939763898113^1685*25000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13263413 25000000 10939763898113 25000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2703678927/5000000000 : ℝ)^2197 ≤ (22429553167881/50000000000000 : ℝ)^1685 := by
    have hnat : (2703678927 : ℕ)^2197*50000000000000^1685 ≤ 22429553167881^1685*5000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703678927 5000000000 22429553167881 50000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1888675909/10000000000 : ℝ)^2197 ≤ (113818380527/1000000000000 : ℝ)^1685 := by
    have hnat : (1888675909 : ℕ)^2197*1000000000000^1685 ≤ 113818380527^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1888675909 10000000000 113818380527 1000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2197/512 : ℝ)) 2197 1685 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(13263413/25000000 : ℝ), (2703678927/5000000000 : ℝ), (-1888675909/10000000000 : ℝ)] ![(10939763898113/25000000000000 : ℝ), (22429553167881/50000000000000 : ℝ), (113818380527/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(13263413/25000000 : ℝ)|^2197 ≤ (10939763898113/25000000000000 : ℝ)^1685
        have hw : |(13263413/25000000 : ℝ)|=(13263413/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2703678927/5000000000 : ℝ)|^2197 ≤ (22429553167881/50000000000000 : ℝ)^1685
        have hw : |(2703678927/5000000000 : ℝ)|=(2703678927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1888675909/10000000000 : ℝ)|^2197 ≤ (113818380527/1000000000000 : ℝ)^1685
        have hw : |(-1888675909/10000000000 : ℝ)|=(1888675909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1434_s7_7 (p : ℝ) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2151575217/5000000000 : ℝ)*x 0 + (1119850787/2500000000 : ℝ)*x 1 + (413319671/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2151575217/5000000000 : ℝ)^2197 ≤ (6661005469617/20000000000000 : ℝ)^1685 := by
    have hnat : (2151575217 : ℕ)^2197*20000000000000^1685 ≤ 6661005469617^1685*5000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151575217 5000000000 6661005469617 20000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1119850787/2500000000 : ℝ)^2197 ≤ (4386829624167/12500000000000 : ℝ)^1685 := by
    have hnat : (1119850787 : ℕ)^2197*12500000000000^1685 ≤ 4386829624167^1685*2500000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119850787 2500000000 4386829624167 12500000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (413319671/1000000000 : ℝ)^2197 ≤ (15800167819363/50000000000000 : ℝ)^1685 := by
    have hnat : (413319671 : ℕ)^2197*50000000000000^1685 ≤ 15800167819363^1685*1000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      413319671 1000000000 15800167819363 50000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2197/512 : ℝ)) 2197 1685 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2151575217/5000000000 : ℝ), (1119850787/2500000000 : ℝ), (413319671/1000000000 : ℝ)] ![(6661005469617/20000000000000 : ℝ), (4386829624167/12500000000000 : ℝ), (15800167819363/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2151575217/5000000000 : ℝ)|^2197 ≤ (6661005469617/20000000000000 : ℝ)^1685
        have hw : |(2151575217/5000000000 : ℝ)|=(2151575217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1119850787/2500000000 : ℝ)|^2197 ≤ (4386829624167/12500000000000 : ℝ)^1685
        have hw : |(1119850787/2500000000 : ℝ)|=(1119850787/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(413319671/1000000000 : ℝ)|^2197 ≤ (15800167819363/50000000000000 : ℝ)^1685
        have hw : |(413319671/1000000000 : ℝ)|=(413319671/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1434_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158364909/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (369/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (227/2000 : ℝ)*pair X i i ≤ pair X i h) :
    (11351/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14759/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (369/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (227/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (369/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (227/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (369/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (227/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (369/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (227/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (369/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (227/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (369/2500 : ℝ)*(X 0 2+X 1 2) := by
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
  have hpowlo : (227/2000 : ℝ) ^ (4393/1024 : ℝ) ≤ (8828670971092817/100000000000000000000 : ℝ) := by
    have hpowers : (227/2000 : ℝ)^4393 ≤ (8828670971092817/100000000000000000000 : ℝ)^1024 := by
      have hnat : (227 : ℕ)^4393*100000000000000000000^1024 ≤ 8828670971092817^1024*2000^4393 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        227 2000 8828670971092817 100000000000000000000 4393 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (227/2000 : ℝ)) (X := (8828670971092817/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4393 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (369/2500 : ℝ) ^ (4393/1024 : ℝ) ≤ (6812209956615551/25000000000000000000 : ℝ) := by
    have hpowers : (369/2500 : ℝ)^4393 ≤ (6812209956615551/25000000000000000000 : ℝ)^1024 := by
      have hnat : (369 : ℕ)^4393*25000000000000000000^1024 ≤ 6812209956615551^1024*2500^4393 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        369 2500 6812209956615551 25000000000000000000 4393 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (369/2500 : ℝ)) (X := (6812209956615551/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4393 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008828670971092817/50000000000000000000 : ℝ) ≤ (10000411561439869/10000000000000000 : ℝ) ^ (4393/1024 : ℝ) := by
    have hpowers : (50008828670971092817/50000000000000000000 : ℝ)^1024 ≤ (10000411561439869/10000000000000000 : ℝ)^4393 := by
      have hnat : (50008828670971092817 : ℕ)^1024*10000000000000000^4393 ≤ 10000411561439869^4393*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008828670971092817 50000000000000000000 10000411561439869 10000000000000000 1024 4393 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000411561439869/10000000000000000 : ℝ)) (X := (50008828670971092817/50000000000000000000 : ℝ)) (by norm_num) 4393 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100036077510797555021/100000000000000000000 : ℝ) ≤ (10000840843647003/10000000000000000 : ℝ) ^ (4393/1024 : ℝ) := by
    have hpowers : (100036077510797555021/100000000000000000000 : ℝ)^1024 ≤ (10000840843647003/10000000000000000 : ℝ)^4393 := by
      have hnat : (100036077510797555021 : ℕ)^1024*10000000000000000^4393 ≤ 10000840843647003^4393*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100036077510797555021 100000000000000000000 10000840843647003 10000000000000000 1024 4393 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000840843647003/10000000000000000 : ℝ)) (X := (100036077510797555021/100000000000000000000 : ℝ)) (by norm_num) 4393 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12506812209956615551/12500000000000000000 : ℝ) ≤ (10001270125854137/10000000000000000 : ℝ) ^ (4393/1024 : ℝ) := by
    have hpowers : (12506812209956615551/12500000000000000000 : ℝ)^1024 ≤ (10001270125854137/10000000000000000 : ℝ)^4393 := by
      have hnat : (12506812209956615551 : ℕ)^1024*10000000000000000^4393 ≤ 10001270125854137^4393*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506812209956615551 12500000000000000000 10001270125854137 10000000000000000 1024 4393 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001270125854137/10000000000000000 : ℝ)) (X := (12506812209956615551/12500000000000000000 : ℝ)) (by norm_num) 4393 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8828670971092817/100000000000000000000 : ℝ) ≤ ((309924170167345559/310000000000000000 : ℝ)+2*(19512827597/15500000000000 : ℝ)*(227/2000 : ℝ))^(4393/1024 : ℝ) := by
    rw [show (309924170167345559/310000000000000000 : ℝ)+2*(19512827597/15500000000000 : ℝ)*(227/2000 : ℝ)=(10000411561439869/10000000000000000 : ℝ) by norm_num, show 1+2*(8828670971092817/100000000000000000000 : ℝ)=(50008828670971092817/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6812209956615551/25000000000000000000 : ℝ)+(8828670971092817/100000000000000000000 : ℝ) ≤ ((309924170167345559/310000000000000000 : ℝ)+(19512827597/15500000000000 : ℝ)*((369/2500 : ℝ)+(227/2000 : ℝ)))^(4393/1024 : ℝ) := by
    rw [show (309924170167345559/310000000000000000 : ℝ)+(19512827597/15500000000000 : ℝ)*((369/2500 : ℝ)+(227/2000 : ℝ))=(10000840843647003/10000000000000000 : ℝ) by norm_num, show 1+(6812209956615551/25000000000000000000 : ℝ)+(8828670971092817/100000000000000000000 : ℝ)=(100036077510797555021/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6812209956615551/25000000000000000000 : ℝ) ≤ ((309924170167345559/310000000000000000 : ℝ)+2*(19512827597/15500000000000 : ℝ)*(369/2500 : ℝ))^(4393/1024 : ℝ) := by
    rw [show (309924170167345559/310000000000000000 : ℝ)+2*(19512827597/15500000000000 : ℝ)*(369/2500 : ℝ)=(10001270125854137/10000000000000000 : ℝ) by norm_num, show 1+2*(6812209956615551/25000000000000000000 : ℝ)=(12506812209956615551/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (309924170167345559/310000000000000000 : ℝ)*(X 1 0+X 2 0)+(19512827597/15500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4393/1024 : ℝ)) (lo := (227/2000 : ℝ)) (hi := (369/2500 : ℝ)) (c := (309924170167345559/310000000000000000 : ℝ)) (alpha := (19512827597/15500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (309924170167345559/310000000000000000 : ℝ)*(X 0 1+X 2 1)+(19512827597/15500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4393/1024 : ℝ)) (lo := (227/2000 : ℝ)) (hi := (369/2500 : ℝ)) (c := (309924170167345559/310000000000000000 : ℝ)) (alpha := (19512827597/15500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (309924170167345559/310000000000000000 : ℝ)*(X 0 2+X 1 2)+(19512827597/15500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4393/1024 : ℝ)) (lo := (227/2000 : ℝ)) (hi := (369/2500 : ℝ)) (c := (309924170167345559/310000000000000000 : ℝ)) (alpha := (19512827597/15500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1967081953/10000000000 : ℝ)*X 0 0+(1081588261/2000000000 : ℝ)*X 0 1+(262351817/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1434_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347216607/10000000000 : ℝ)*X 1 0+(-204899741/1000000000 : ℝ)*X 1 1+(5247036349/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1434_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347216591/10000000000 : ℝ)*X 2 0+(5247036379/10000000000 : ℝ)*X 2 1+(-128062337/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1434_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((215156299/500000000 : ℝ)*X 0 0+(413193219/1000000000 : ℝ)*X 0 1+(2240330591/5000000000 : ℝ)*X 0 2+(215156299/500000000 : ℝ)*X 1 0+(413193219/1000000000 : ℝ)*X 1 1+(2240330591/5000000000 : ℝ)*X 1 2+(215156299/500000000 : ℝ)*X 2 0+(413193219/1000000000 : ℝ)*X 2 1+(2240330591/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1434_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-983546589/5000000000 : ℝ)*X 0 0+(5247616799/10000000000 : ℝ)*X 0 1+(43258863/80000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1434_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326341307/2500000000 : ℝ)*X 1 0+(-94433793/500000000 : ℝ)*X 1 1+(5407357863/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1434_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((13263413/25000000 : ℝ)*X 2 0+(2703678927/5000000000 : ℝ)*X 2 1+(-1888675909/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1434_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2151575217/5000000000 : ℝ)*X 0 0+(1119850787/2500000000 : ℝ)*X 0 1+(413319671/1000000000 : ℝ)*X 0 2+(2151575217/5000000000 : ℝ)*X 1 0+(1119850787/2500000000 : ℝ)*X 1 1+(413319671/1000000000 : ℝ)*X 1 2+(2151575217/5000000000 : ℝ)*X 2 0+(1119850787/2500000000 : ℝ)*X 2 1+(413319671/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1434_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (23260828618501087496202261/7750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (537486567/100000000000000 : ℝ)*(base19) + (494590441/100000000000000 : ℝ)*(base23) + (12993691/100000000000000 : ℝ)*(lower2) + (66098203/100000000000000 : ℝ)*(upper3) + (13719029/20000000000000 : ℝ)*(upper5) + (2270609917342331/50000000000000 : ℝ)*(major0) + (2270609917342331/50000000000000 : ℝ)*(major1) + (2270609917342331/50000000000000 : ℝ)*(major2) + (6214860431063951/100000000000000 : ℝ)*(sp0) + (6214872054176583/100000000000000 : ℝ)*(sp1) + (1553718024268177/25000000000000 : ℝ)*(sp2) + (1433780797489147/50000000000000 : ℝ)*(sp3) + (6080299599/50000000000000 : ℝ)*(sp4) + (2691340649/50000000000000 : ℝ)*(sp7) + (358445872207449/12500000000000 : ℝ)*(f.failure) + (6214872591663149/100000000000000 : ℝ)*(f.sum) + (5496164559161/775000000000000000000000000 : ℝ)*base66 + (116584936577801971/15500000000000000000000000000000 : ℝ)*base68 + (96846360161301971/15500000000000000000000000000000 : ℝ)*base70 + (44960089313801971/15500000000000000000000000000000 : ℝ)*base72 + (295823067091/193750000000000000000000000 : ℝ)*base73 + (321296464254801971/15500000000000000000000000000000 : ℝ)*base76 + (175513249792301971/15500000000000000000000000000000 : ℝ)*base78 + (42865713240301971/15500000000000000000000000000000 : ℝ)*base80 + (331369417793/387500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (15007141/1250000000000000000000 : ℝ)*base89 + (15007141/1250000000000000000000 : ℝ)*base91 + (15007141/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1691815942602441946984179/310000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (901789809/100000000000000 : ℝ)*(base19) + (988892613/100000000000000 : ℝ)*(base23) + (154072599/50000000000000 : ℝ)*(lower1) + (18377071/20000000000000 : ℝ)*(upper3) + (65466897/100000000000000 : ℝ)*(lower4) + (61163919/50000000000000 : ℝ)*(upper5) + (91485508856909/2000000000000 : ℝ)*(major0) + (91485508856909/2000000000000 : ℝ)*(major1) + (91485508856909/2000000000000 : ℝ)*(major2) + (412739459/100000000000000 : ℝ)*(sp1) + (3130055331262497/50000000000000 : ℝ)*(sp4) + (3130054673997863/50000000000000 : ℝ)*(sp5) + (6260109673632381/100000000000000 : ℝ)*(sp6) + (1444220020625103/50000000000000 : ℝ)*(sp7) + (1444220020625103/50000000000000 : ℝ)*(f.failure) + (3130055331262497/50000000000000 : ℝ)*(f.sum) + (84584458643/15500000000000000000000000 : ℝ)*base66 + (4232594829202869/620000000000000000000000000000 : ℝ)*base68 + (5298639765122869/620000000000000000000000000000 : ℝ)*base70 + (4492795096822869/620000000000000000000000000000 : ℝ)*base72 + (20106106433/7750000000000000000000000 : ℝ)*base74 + (6926673572102869/620000000000000000000000000000 : ℝ)*base76 + (2018083733402869/620000000000000000000000000000 : ℝ)*base78 + (6611718453362869/620000000000000000000000000000 : ℝ)*base80 + (29552153103/6200000000000000000000000 : ℝ)*base82 + (59710627/5000000000000000000000 : ℝ)*base89 + (59710627/5000000000000000000000 : ℝ)*base91 + (59710627/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1434_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158364909/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (369/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (227/2000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11351/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14759/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1434_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1434_box_0 (p : ℝ) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-903392539/5000000000 : ℝ)*x 0 + (2693020423/5000000000 : ℝ)*x 1 + (2693020847/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (903392539/5000000000 : ℝ)^2197 ≤ (10742661981681/100000000000000 : ℝ)^1685 := by
    have hnat : (903392539 : ℕ)^2197*100000000000000^1685 ≤ 10742661981681^1685*5000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903392539 5000000000 10742661981681 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2693020423/5000000000 : ℝ)^2197 ≤ (22314332210761/50000000000000 : ℝ)^1685 := by
    have hnat : (2693020423 : ℕ)^2197*50000000000000^1685 ≤ 22314332210761^1685*5000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693020423 5000000000 22314332210761 50000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2693020847/5000000000 : ℝ)^2197 ≤ (446286735831/1000000000000 : ℝ)^1685 := by
    have hnat : (2693020847 : ℕ)^2197*1000000000000^1685 ≤ 446286735831^1685*5000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693020847 5000000000 446286735831 1000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2197/512 : ℝ)) 2197 1685 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-903392539/5000000000 : ℝ), (2693020423/5000000000 : ℝ), (2693020847/5000000000 : ℝ)] ![(10742661981681/100000000000000 : ℝ), (22314332210761/50000000000000 : ℝ), (446286735831/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-903392539/5000000000 : ℝ)|^2197 ≤ (10742661981681/100000000000000 : ℝ)^1685
        have hw : |(-903392539/5000000000 : ℝ)|=(903392539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2693020423/5000000000 : ℝ)|^2197 ≤ (22314332210761/50000000000000 : ℝ)^1685
        have hw : |(2693020423/5000000000 : ℝ)|=(2693020423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2693020847/5000000000 : ℝ)|^2197 ≤ (446286735831/1000000000000 : ℝ)^1685
        have hw : |(2693020847/5000000000 : ℝ)|=(2693020847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1434_box_1 (p : ℝ) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2643050027/5000000000 : ℝ)*x 0 + (-1944110411/10000000000 : ℝ)*x 1 + (1346510313/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643050027/5000000000 : ℝ)^2197 ≤ (2177599325787/5000000000000 : ℝ)^1685 := by
    have hnat : (2643050027 : ℕ)^2197*5000000000000^1685 ≤ 2177599325787^1685*5000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643050027 5000000000 2177599325787 5000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1944110411/10000000000 : ℝ)^2197 ≤ (2954836165759/25000000000000 : ℝ)^1685 := by
    have hnat : (1944110411 : ℕ)^2197*25000000000000^1685 ≤ 2954836165759^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1944110411 10000000000 2954836165759 25000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1346510313/2500000000 : ℝ)^2197 ≤ (44628668807843/100000000000000 : ℝ)^1685 := by
    have hnat : (1346510313 : ℕ)^2197*100000000000000^1685 ≤ 44628668807843^1685*2500000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346510313 2500000000 44628668807843 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2197/512 : ℝ)) 2197 1685 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643050027/5000000000 : ℝ), (-1944110411/10000000000 : ℝ), (1346510313/2500000000 : ℝ)] ![(2177599325787/5000000000000 : ℝ), (2954836165759/25000000000000 : ℝ), (44628668807843/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643050027/5000000000 : ℝ)|^2197 ≤ (2177599325787/5000000000000 : ℝ)^1685
        have hw : |(2643050027/5000000000 : ℝ)|=(2643050027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1944110411/10000000000 : ℝ)|^2197 ≤ (2954836165759/25000000000000 : ℝ)^1685
        have hw : |(-1944110411/10000000000 : ℝ)|=(1944110411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1346510313/2500000000 : ℝ)|^2197 ≤ (44628668807843/100000000000000 : ℝ)^1685
        have hw : |(1346510313/2500000000 : ℝ)|=(1346510313/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1434_box_2 (p : ℝ) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ)) (x : Fin 3 → ℝ) :
    (66076253/125000000 : ℝ)*x 0 + (2693020541/5000000000 : ℝ)*x 1 + (-194411039/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66076253/125000000 : ℝ)^2197 ≤ (43551988513833/100000000000000 : ℝ)^1685 := by
    have hnat : (66076253 : ℕ)^2197*100000000000000^1685 ≤ 43551988513833^1685*125000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66076253 125000000 43551988513833 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2693020541/5000000000 : ℝ)^2197 ≤ (22314333485603/50000000000000 : ℝ)^1685 := by
    have hnat : (2693020541 : ℕ)^2197*50000000000000^1685 ≤ 22314333485603^1685*5000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693020541 5000000000 22314333485603 50000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (194411039/1000000000 : ℝ)^2197 ≤ (11819344496571/100000000000000 : ℝ)^1685 := by
    have hnat : (194411039 : ℕ)^2197*100000000000000^1685 ≤ 11819344496571^1685*1000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      194411039 1000000000 11819344496571 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2197/512 : ℝ)) 2197 1685 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66076253/125000000 : ℝ), (2693020541/5000000000 : ℝ), (-194411039/1000000000 : ℝ)] ![(43551988513833/100000000000000 : ℝ), (22314333485603/50000000000000 : ℝ), (11819344496571/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66076253/125000000 : ℝ)|^2197 ≤ (43551988513833/100000000000000 : ℝ)^1685
        have hw : |(66076253/125000000 : ℝ)|=(66076253/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2693020541/5000000000 : ℝ)|^2197 ≤ (22314333485603/50000000000000 : ℝ)^1685
        have hw : |(2693020541/5000000000 : ℝ)|=(2693020541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-194411039/1000000000 : ℝ)|^2197 ≤ (11819344496571/100000000000000 : ℝ)^1685
        have hw : |(-194411039/1000000000 : ℝ)|=(194411039/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1434_box_3 (p : ℝ) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2224660637/5000000000 : ℝ)*x 0 + (4233727463/10000000000 : ℝ)*x 1 + (4233727311/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2224660637/5000000000 : ℝ)^2197 ≤ (6957531181719/20000000000000 : ℝ)^1685 := by
    have hnat : (2224660637 : ℕ)^2197*20000000000000^1685 ≤ 6957531181719^1685*5000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2224660637 5000000000 6957531181719 20000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4233727463/10000000000 : ℝ)^2197 ≤ (2037885800057/6250000000000 : ℝ)^1685 := by
    have hnat : (4233727463 : ℕ)^2197*6250000000000^1685 ≤ 2037885800057^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4233727463 10000000000 2037885800057 6250000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4233727311/10000000000 : ℝ)^2197 ≤ (16303085637287/50000000000000 : ℝ)^1685 := by
    have hnat : (4233727311 : ℕ)^2197*50000000000000^1685 ≤ 16303085637287^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4233727311 10000000000 16303085637287 50000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2197/512 : ℝ)) 2197 1685 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2224660637/5000000000 : ℝ), (4233727463/10000000000 : ℝ), (4233727311/10000000000 : ℝ)] ![(6957531181719/20000000000000 : ℝ), (2037885800057/6250000000000 : ℝ), (16303085637287/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2224660637/5000000000 : ℝ)|^2197 ≤ (6957531181719/20000000000000 : ℝ)^1685
        have hw : |(2224660637/5000000000 : ℝ)|=(2224660637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4233727463/10000000000 : ℝ)|^2197 ≤ (2037885800057/6250000000000 : ℝ)^1685
        have hw : |(4233727463/10000000000 : ℝ)|=(4233727463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4233727311/10000000000 : ℝ)|^2197 ≤ (16303085637287/50000000000000 : ℝ)^1685
        have hw : |(4233727311/10000000000 : ℝ)|=(4233727311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1434_box_4 (p : ℝ) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1065056603/5000000000 : ℝ)*x 0 + (5266600231/10000000000 : ℝ)*x 1 + (2633300163/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1065056603/5000000000 : ℝ)^2197 ≤ (6657371050823/50000000000000 : ℝ)^1685 := by
    have hnat : (1065056603 : ℕ)^2197*50000000000000^1685 ≤ 6657371050823^1685*5000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065056603 5000000000 6657371050823 50000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266600231/10000000000 : ℝ)^2197 ≤ (21671314216021/50000000000000 : ℝ)^1685 := by
    have hnat : (5266600231 : ℕ)^2197*50000000000000^1685 ≤ 21671314216021^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266600231 10000000000 21671314216021 50000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633300163/5000000000 : ℝ)^2197 ≤ (10835657362857/25000000000000 : ℝ)^1685 := by
    have hnat : (2633300163 : ℕ)^2197*25000000000000^1685 ≤ 10835657362857^1685*5000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633300163 5000000000 10835657362857 25000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2197/512 : ℝ)) 2197 1685 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1065056603/5000000000 : ℝ), (5266600231/10000000000 : ℝ), (2633300163/5000000000 : ℝ)] ![(6657371050823/50000000000000 : ℝ), (21671314216021/50000000000000 : ℝ), (10835657362857/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1065056603/5000000000 : ℝ)|^2197 ≤ (6657371050823/50000000000000 : ℝ)^1685
        have hw : |(-1065056603/5000000000 : ℝ)|=(1065056603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266600231/10000000000 : ℝ)|^2197 ≤ (21671314216021/50000000000000 : ℝ)^1685
        have hw : |(5266600231/10000000000 : ℝ)|=(5266600231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633300163/5000000000 : ℝ)|^2197 ≤ (10835657362857/25000000000000 : ℝ)^1685
        have hw : |(2633300163/5000000000 : ℝ)|=(2633300163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1434_box_5 (p : ℝ) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2684836873/5000000000 : ℝ)*x 0 + (-1992635709/10000000000 : ℝ)*x 1 + (5266600413/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684836873/5000000000 : ℝ)^2197 ≤ (222259600557/500000000000 : ℝ)^1685 := by
    have hnat : (2684836873 : ℕ)^2197*500000000000^1685 ≤ 222259600557^1685*5000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684836873 5000000000 222259600557 500000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1992635709/10000000000 : ℝ)^2197 ≤ (3051362372799/25000000000000 : ℝ)^1685 := by
    have hnat : (1992635709 : ℕ)^2197*25000000000000^1685 ≤ 3051362372799^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1992635709 10000000000 3051362372799 25000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266600413/10000000000 : ℝ)^2197 ≤ (43342630384971/100000000000000 : ℝ)^1685 := by
    have hnat : (5266600413 : ℕ)^2197*100000000000000^1685 ≤ 43342630384971^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266600413 10000000000 43342630384971 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2197/512 : ℝ)) 2197 1685 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684836873/5000000000 : ℝ), (-1992635709/10000000000 : ℝ), (5266600413/10000000000 : ℝ)] ![(222259600557/500000000000 : ℝ), (3051362372799/25000000000000 : ℝ), (43342630384971/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684836873/5000000000 : ℝ)|^2197 ≤ (222259600557/500000000000 : ℝ)^1685
        have hw : |(2684836873/5000000000 : ℝ)|=(2684836873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1992635709/10000000000 : ℝ)|^2197 ≤ (3051362372799/25000000000000 : ℝ)^1685
        have hw : |(-1992635709/10000000000 : ℝ)|=(1992635709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266600413/10000000000 : ℝ)|^2197 ≤ (43342630384971/100000000000000 : ℝ)^1685
        have hw : |(5266600413/10000000000 : ℝ)|=(5266600413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1434_box_6 (p : ℝ) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5369673893/10000000000 : ℝ)*x 0 + (658325029/1250000000 : ℝ)*x 1 + (-1992635753/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369673893/10000000000 : ℝ)^2197 ≤ (44451921698083/100000000000000 : ℝ)^1685 := by
    have hnat : (5369673893 : ℕ)^2197*100000000000000^1685 ≤ 44451921698083^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369673893 10000000000 44451921698083 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658325029/1250000000 : ℝ)^2197 ≤ (43342628442773/100000000000000 : ℝ)^1685 := by
    have hnat : (658325029 : ℕ)^2197*100000000000000^1685 ≤ 43342628442773^1685*1250000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658325029 1250000000 43342628442773 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1992635753/10000000000 : ℝ)^2197 ≤ (6102724921301/50000000000000 : ℝ)^1685 := by
    have hnat : (1992635753 : ℕ)^2197*50000000000000^1685 ≤ 6102724921301^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1992635753 10000000000 6102724921301 50000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2197/512 : ℝ)) 2197 1685 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369673893/10000000000 : ℝ), (658325029/1250000000 : ℝ), (-1992635753/10000000000 : ℝ)] ![(44451921698083/100000000000000 : ℝ), (43342628442773/100000000000000 : ℝ), (6102724921301/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369673893/10000000000 : ℝ)|^2197 ≤ (44451921698083/100000000000000 : ℝ)^1685
        have hw : |(5369673893/10000000000 : ℝ)|=(5369673893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658325029/1250000000 : ℝ)|^2197 ≤ (43342628442773/100000000000000 : ℝ)^1685
        have hw : |(658325029/1250000000 : ℝ)|=(658325029/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1992635753/10000000000 : ℝ)|^2197 ≤ (6102724921301/50000000000000 : ℝ)^1685
        have hw : |(-1992635753/10000000000 : ℝ)|=(1992635753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1434_box_7 (p : ℝ) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ)) (x : Fin 3 → ℝ) :
    (415587583/1000000000 : ℝ)*x 0 + (273774957/625000000 : ℝ)*x 1 + (4380399411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (415587583/1000000000 : ℝ)^2197 ≤ (497290684047/1562500000000 : ℝ)^1685 := by
    have hnat : (415587583 : ℕ)^2197*1562500000000^1685 ≤ 497290684047^1685*1000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415587583 1000000000 497290684047 1562500000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (273774957/625000000 : ℝ)^2197 ≤ (3408669760657/10000000000000 : ℝ)^1685 := by
    have hnat : (273774957 : ℕ)^2197*10000000000000^1685 ≤ 3408669760657^1685*625000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273774957 625000000 3408669760657 10000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4380399411/10000000000 : ℝ)^2197 ≤ (34086698611039/100000000000000 : ℝ)^1685 := by
    have hnat : (4380399411 : ℕ)^2197*100000000000000^1685 ≤ 34086698611039^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4380399411 10000000000 34086698611039 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2197/512 : ℝ)) 2197 1685 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(415587583/1000000000 : ℝ), (273774957/625000000 : ℝ), (4380399411/10000000000 : ℝ)] ![(497290684047/1562500000000 : ℝ), (3408669760657/10000000000000 : ℝ), (34086698611039/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(415587583/1000000000 : ℝ)|^2197 ≤ (497290684047/1562500000000 : ℝ)^1685
        have hw : |(415587583/1000000000 : ℝ)|=(415587583/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(273774957/625000000 : ℝ)|^2197 ≤ (3408669760657/10000000000000 : ℝ)^1685
        have hw : |(273774957/625000000 : ℝ)|=(273774957/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4380399411/10000000000 : ℝ)|^2197 ≤ (34086698611039/100000000000000 : ℝ)^1685
        have hw : |(4380399411/10000000000 : ℝ)|=(4380399411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1434_box_8 (p : ℝ) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2061999693/10000000000 : ℝ)*x 0 + (5183961539/10000000000 : ℝ)*x 1 + (5400011891/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2061999693/10000000000 : ℝ)^2197 ≤ (12762330808639/100000000000000 : ℝ)^1685 := by
    have hnat : (2061999693 : ℕ)^2197*100000000000000^1685 ≤ 12762330808639^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2061999693 10000000000 12762330808639 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5183961539/10000000000 : ℝ)^2197 ≤ (42458005669257/100000000000000 : ℝ)^1685 := by
    have hnat : (5183961539 : ℕ)^2197*100000000000000^1685 ≤ 42458005669257^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183961539 10000000000 42458005669257 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5400011891/10000000000 : ℝ)^2197 ≤ (559745793793/1250000000000 : ℝ)^1685 := by
    have hnat : (5400011891 : ℕ)^2197*1250000000000^1685 ≤ 559745793793^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400011891 10000000000 559745793793 1250000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2197/512 : ℝ)) 2197 1685 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2061999693/10000000000 : ℝ), (5183961539/10000000000 : ℝ), (5400011891/10000000000 : ℝ)] ![(12762330808639/100000000000000 : ℝ), (42458005669257/100000000000000 : ℝ), (559745793793/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2061999693/10000000000 : ℝ)|^2197 ≤ (12762330808639/100000000000000 : ℝ)^1685
        have hw : |(-2061999693/10000000000 : ℝ)|=(2061999693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5183961539/10000000000 : ℝ)|^2197 ≤ (42458005669257/100000000000000 : ℝ)^1685
        have hw : |(5183961539/10000000000 : ℝ)|=(5183961539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5400011891/10000000000 : ℝ)|^2197 ≤ (559745793793/1250000000000 : ℝ)^1685
        have hw : |(5400011891/10000000000 : ℝ)|=(5400011891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1434_box_9 (p : ℝ) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ)) (x : Fin 3 → ℝ) :
    (65954009/125000000 : ℝ)*x 0 + (-15506467/80000000 : ℝ)*x 1 + (84375187/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (65954009/125000000 : ℝ)^2197 ≤ (8689392438863/20000000000000 : ℝ)^1685 := by
    have hnat : (65954009 : ℕ)^2197*20000000000000^1685 ≤ 8689392438863^1685*125000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65954009 125000000 8689392438863 20000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (15506467/80000000 : ℝ)^2197 ≤ (2354674690423/20000000000000 : ℝ)^1685 := by
    have hnat : (15506467 : ℕ)^2197*20000000000000^1685 ≤ 2354674690423^1685*80000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15506467 80000000 2354674690423 20000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84375187/156250000 : ℝ)^2197 ≤ (44779664335983/100000000000000 : ℝ)^1685 := by
    have hnat : (84375187 : ℕ)^2197*100000000000000^1685 ≤ 44779664335983^1685*156250000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84375187 156250000 44779664335983 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2197/512 : ℝ)) 2197 1685 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(65954009/125000000 : ℝ), (-15506467/80000000 : ℝ), (84375187/156250000 : ℝ)] ![(8689392438863/20000000000000 : ℝ), (2354674690423/20000000000000 : ℝ), (44779664335983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(65954009/125000000 : ℝ)|^2197 ≤ (8689392438863/20000000000000 : ℝ)^1685
        have hw : |(65954009/125000000 : ℝ)|=(65954009/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-15506467/80000000 : ℝ)|^2197 ≤ (2354674690423/20000000000000 : ℝ)^1685
        have hw : |(-15506467/80000000 : ℝ)|=(15506467/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84375187/156250000 : ℝ)|^2197 ≤ (44779664335983/100000000000000 : ℝ)^1685
        have hw : |(84375187/156250000 : ℝ)|=(84375187/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1434_box_10 (p : ℝ) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5276320501/10000000000 : ℝ)*x 0 + (2700006079/5000000000 : ℝ)*x 1 + (-1938308413/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276320501/10000000000 : ℝ)^2197 ≤ (8689391968609/20000000000000 : ℝ)^1685 := by
    have hnat : (5276320501 : ℕ)^2197*20000000000000^1685 ≤ 8689391968609^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276320501 10000000000 8689391968609 20000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2700006079/5000000000 : ℝ)^2197 ≤ (5597458298789/12500000000000 : ℝ)^1685 := by
    have hnat : (2700006079 : ℕ)^2197*12500000000000^1685 ≤ 5597458298789^1685*5000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700006079 5000000000 5597458298789 12500000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1938308413/10000000000 : ℝ)^2197 ≤ (1471671719133/12500000000000 : ℝ)^1685 := by
    have hnat : (1938308413 : ℕ)^2197*12500000000000^1685 ≤ 1471671719133^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1938308413 10000000000 1471671719133 12500000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2197/512 : ℝ)) 2197 1685 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276320501/10000000000 : ℝ), (2700006079/5000000000 : ℝ), (-1938308413/10000000000 : ℝ)] ![(8689391968609/20000000000000 : ℝ), (5597458298789/12500000000000 : ℝ), (1471671719133/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276320501/10000000000 : ℝ)|^2197 ≤ (8689391968609/20000000000000 : ℝ)^1685
        have hw : |(5276320501/10000000000 : ℝ)|=(5276320501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2700006079/5000000000 : ℝ)|^2197 ≤ (5597458298789/12500000000000 : ℝ)^1685
        have hw : |(2700006079/5000000000 : ℝ)|=(2700006079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1938308413/10000000000 : ℝ)|^2197 ≤ (1471671719133/12500000000000 : ℝ)^1685
        have hw : |(-1938308413/10000000000 : ℝ)|=(1938308413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1434_box_11 (p : ℝ) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ)) (x : Fin 3 → ℝ) :
    (448308801/1000000000 : ℝ)*x 0 + (527069623/1250000000 : ℝ)*x 1 + (2108278469/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (448308801/1000000000 : ℝ)^2197 ≤ (4391535454457/12500000000000 : ℝ)^1685 := by
    have hnat : (448308801 : ℕ)^2197*12500000000000^1685 ≤ 4391535454457^1685*1000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448308801 1000000000 4391535454457 12500000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (527069623/1250000000 : ℝ)^2197 ≤ (16216929203483/50000000000000 : ℝ)^1685 := by
    have hnat : (527069623 : ℕ)^2197*50000000000000^1685 ≤ 16216929203483^1685*1250000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527069623 1250000000 16216929203483 50000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2108278469/5000000000 : ℝ)^2197 ≤ (16216928972809/50000000000000 : ℝ)^1685 := by
    have hnat : (2108278469 : ℕ)^2197*50000000000000^1685 ≤ 16216928972809^1685*5000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108278469 5000000000 16216928972809 50000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2197/512 : ℝ)) 2197 1685 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(448308801/1000000000 : ℝ), (527069623/1250000000 : ℝ), (2108278469/5000000000 : ℝ)] ![(4391535454457/12500000000000 : ℝ), (16216929203483/50000000000000 : ℝ), (16216928972809/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(448308801/1000000000 : ℝ)|^2197 ≤ (4391535454457/12500000000000 : ℝ)^1685
        have hw : |(448308801/1000000000 : ℝ)|=(448308801/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(527069623/1250000000 : ℝ)|^2197 ≤ (16216929203483/50000000000000 : ℝ)^1685
        have hw : |(527069623/1250000000 : ℝ)|=(527069623/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2108278469/5000000000 : ℝ)|^2197 ≤ (16216928972809/50000000000000 : ℝ)^1685
        have hw : |(2108278469/5000000000 : ℝ)|=(2108278469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1434_box_12 (p : ℝ) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1875070591/10000000000 : ℝ)*x 0 + (683333221/1250000000 : ℝ)*x 1 + (5255472207/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1875070591/10000000000 : ℝ)^2197 ≤ (11275051284463/100000000000000 : ℝ)^1685 := by
    have hnat : (1875070591 : ℕ)^2197*100000000000000^1685 ≤ 11275051284463^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1875070591 10000000000 11275051284463 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (683333221/1250000000 : ℝ)^2197 ≤ (1421927807053/3125000000000 : ℝ)^1685 := by
    have hnat : (683333221 : ℕ)^2197*3125000000000^1685 ≤ 1421927807053^1685*1250000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      683333221 1250000000 1421927807053 3125000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5255472207/10000000000 : ℝ)^2197 ≤ (10805814718247/25000000000000 : ℝ)^1685 := by
    have hnat : (5255472207 : ℕ)^2197*25000000000000^1685 ≤ 10805814718247^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255472207 10000000000 10805814718247 25000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2197/512 : ℝ)) 2197 1685 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1875070591/10000000000 : ℝ), (683333221/1250000000 : ℝ), (5255472207/10000000000 : ℝ)] ![(11275051284463/100000000000000 : ℝ), (1421927807053/3125000000000 : ℝ), (10805814718247/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1875070591/10000000000 : ℝ)|^2197 ≤ (11275051284463/100000000000000 : ℝ)^1685
        have hw : |(-1875070591/10000000000 : ℝ)|=(1875070591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(683333221/1250000000 : ℝ)|^2197 ≤ (1421927807053/3125000000000 : ℝ)^1685
        have hw : |(683333221/1250000000 : ℝ)|=(683333221/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5255472207/10000000000 : ℝ)|^2197 ≤ (10805814718247/25000000000000 : ℝ)^1685
        have hw : |(5255472207/10000000000 : ℝ)|=(5255472207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1434_box_13 (p : ℝ) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ)) (x : Fin 3 → ℝ) :
    (336091231/625000000 : ℝ)*x 0 + (-1997057461/10000000000 : ℝ)*x 1 + (5255471007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (336091231/625000000 : ℝ)^2197 ≤ (5566997287281/12500000000000 : ℝ)^1685 := by
    have hnat : (336091231 : ℕ)^2197*12500000000000^1685 ≤ 5566997287281^1685*625000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336091231 625000000 5566997287281 12500000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1997057461/10000000000 : ℝ)^2197 ≤ (1224077567453/10000000000000 : ℝ)^1685 := by
    have hnat : (1997057461 : ℕ)^2197*10000000000000^1685 ≤ 1224077567453^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1997057461 10000000000 1224077567453 10000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5255471007/10000000000 : ℝ)^2197 ≤ (43223246004807/100000000000000 : ℝ)^1685 := by
    have hnat : (5255471007 : ℕ)^2197*100000000000000^1685 ≤ 43223246004807^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255471007 10000000000 43223246004807 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2197/512 : ℝ)) 2197 1685 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(336091231/625000000 : ℝ), (-1997057461/10000000000 : ℝ), (5255471007/10000000000 : ℝ)] ![(5566997287281/12500000000000 : ℝ), (1224077567453/10000000000000 : ℝ), (43223246004807/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(336091231/625000000 : ℝ)|^2197 ≤ (5566997287281/12500000000000 : ℝ)^1685
        have hw : |(336091231/625000000 : ℝ)|=(336091231/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1997057461/10000000000 : ℝ)|^2197 ≤ (1224077567453/10000000000000 : ℝ)^1685
        have hw : |(-1997057461/10000000000 : ℝ)|=(1997057461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5255471007/10000000000 : ℝ)|^2197 ≤ (43223246004807/100000000000000 : ℝ)^1685
        have hw : |(5255471007/10000000000 : ℝ)|=(5255471007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1434_box_14 (p : ℝ) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ)) (x : Fin 3 → ℝ) :
    (672182417/1250000000 : ℝ)*x 0 + (2627735761/5000000000 : ℝ)*x 1 + (-1997057257/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (672182417/1250000000 : ℝ)^2197 ≤ (1391749200337/3125000000000 : ℝ)^1685 := by
    have hnat : (672182417 : ℕ)^2197*3125000000000^1685 ≤ 1391749200337^1685*1250000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672182417 1250000000 1391749200337 3125000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2627735761/5000000000 : ℝ)^2197 ≤ (43223251527401/100000000000000 : ℝ)^1685 := by
    have hnat : (2627735761 : ℕ)^2197*100000000000000^1685 ≤ 43223251527401^1685*5000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627735761 5000000000 43223251527401 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1997057257/10000000000 : ℝ)^2197 ≤ (3060193511047/25000000000000 : ℝ)^1685 := by
    have hnat : (1997057257 : ℕ)^2197*25000000000000^1685 ≤ 3060193511047^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1997057257 10000000000 3060193511047 25000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2197/512 : ℝ)) 2197 1685 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(672182417/1250000000 : ℝ), (2627735761/5000000000 : ℝ), (-1997057257/10000000000 : ℝ)] ![(1391749200337/3125000000000 : ℝ), (43223251527401/100000000000000 : ℝ), (3060193511047/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(672182417/1250000000 : ℝ)|^2197 ≤ (1391749200337/3125000000000 : ℝ)^1685
        have hw : |(672182417/1250000000 : ℝ)|=(672182417/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2627735761/5000000000 : ℝ)|^2197 ≤ (43223251527401/100000000000000 : ℝ)^1685
        have hw : |(2627735761/5000000000 : ℝ)|=(2627735761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1997057257/10000000000 : ℝ)|^2197 ≤ (3060193511047/25000000000000 : ℝ)^1685
        have hw : |(-1997057257/10000000000 : ℝ)|=(1997057257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1434_box_15 (p : ℝ) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4128086129/10000000000 : ℝ)*x 0 + (2197027013/5000000000 : ℝ)*x 1 + (4394052877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4128086129/10000000000 : ℝ)^2197 ≤ (31549399686163/100000000000000 : ℝ)^1685 := by
    have hnat : (4128086129 : ℕ)^2197*100000000000000^1685 ≤ 31549399686163^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4128086129 10000000000 31549399686163 100000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2197027013/5000000000 : ℝ)^2197 ≤ (17112652990317/50000000000000 : ℝ)^1685 := by
    have hnat : (2197027013 : ℕ)^2197*50000000000000^1685 ≤ 17112652990317^1685*5000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2197027013 5000000000 17112652990317 50000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4394052877/10000000000 : ℝ)^2197 ≤ (1369011772467/4000000000000 : ℝ)^1685 := by
    have hnat : (4394052877 : ℕ)^2197*4000000000000^1685 ≤ 1369011772467^1685*10000000000^2197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4394052877 10000000000 1369011772467 4000000000000 2197 1685 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2197/512 : ℝ)) 2197 1685 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4128086129/10000000000 : ℝ), (2197027013/5000000000 : ℝ), (4394052877/10000000000 : ℝ)] ![(31549399686163/100000000000000 : ℝ), (17112652990317/50000000000000 : ℝ), (1369011772467/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4128086129/10000000000 : ℝ)|^2197 ≤ (31549399686163/100000000000000 : ℝ)^1685
        have hw : |(4128086129/10000000000 : ℝ)|=(4128086129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2197027013/5000000000 : ℝ)|^2197 ≤ (17112652990317/50000000000000 : ℝ)^1685
        have hw : |(2197027013/5000000000 : ℝ)|=(2197027013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4394052877/10000000000 : ℝ)|^2197 ≤ (1369011772467/4000000000000 : ℝ)^1685
        have hw : |(4394052877/10000000000 : ℝ)|=(4394052877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1434_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158364909/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14759/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11351/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62903/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59123/100000 : ℝ) ∧ (20119/25000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84703/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14759/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11351/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14759/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11351/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14759/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11351/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14759/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11351/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14759/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11351/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14759/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11351/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11351/100000 : ℝ) ^ (4393/1024 : ℝ) ≤ (4416004244717877/50000000000000000000 : ℝ) := by
    have hpowers : (11351/100000 : ℝ)^4393 ≤ (4416004244717877/50000000000000000000 : ℝ)^1024 := by
      have hnat : (11351 : ℕ)^4393*50000000000000000000^1024 ≤ 4416004244717877^1024*100000^4393 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11351 100000 4416004244717877 50000000000000000000 4393 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11351/100000 : ℝ)) (X := (4416004244717877/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4393 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14759/100000 : ℝ) ^ (4393/1024 : ℝ) ≤ (1362046037530933/5000000000000000000 : ℝ) := by
    have hpowers : (14759/100000 : ℝ)^4393 ≤ (1362046037530933/5000000000000000000 : ℝ)^1024 := by
      have hnat : (14759 : ℕ)^4393*5000000000000000000^1024 ≤ 1362046037530933^1024*100000^4393 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14759 100000 1362046037530933 5000000000000000000 4393 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14759/100000 : ℝ)) (X := (1362046037530933/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4393 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004416004244717877/25000000000000000000 : ℝ) ≤ (5000205858506321/5000000000000000 : ℝ) ^ (4393/1024 : ℝ) := by
    have hpowers : (25004416004244717877/25000000000000000000 : ℝ)^1024 ≤ (5000205858506321/5000000000000000 : ℝ)^4393 := by
      have hnat : (25004416004244717877 : ℕ)^1024*5000000000000000^4393 ≤ 5000205858506321^4393*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004416004244717877 25000000000000000000 5000205858506321 5000000000000000 1024 4393 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000205858506321/5000000000000000 : ℝ)) (X := (25004416004244717877/25000000000000000000 : ℝ)) (by norm_num) 4393 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50018036464620027207/50000000000000000000 : ℝ) ≤ (100008407368813/100000000000000 : ℝ) ^ (4393/1024 : ℝ) := by
    have hpowers : (50018036464620027207/50000000000000000000 : ℝ)^1024 ≤ (100008407368813/100000000000000 : ℝ)^4393 := by
      have hnat : (50018036464620027207 : ℕ)^1024*100000000000000^4393 ≤ 100008407368813^4393*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018036464620027207 50000000000000000000 100008407368813 100000000000000 1024 4393 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (100008407368813/100000000000000 : ℝ)) (X := (50018036464620027207/50000000000000000000 : ℝ)) (by norm_num) 4393 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501362046037530933/2500000000000000000 : ℝ) ≤ (5000634878374979/5000000000000000 : ℝ) ^ (4393/1024 : ℝ) := by
    have hpowers : (2501362046037530933/2500000000000000000 : ℝ)^1024 ≤ (5000634878374979/5000000000000000 : ℝ)^4393 := by
      have hnat : (2501362046037530933 : ℕ)^1024*5000000000000000^4393 ≤ 5000634878374979^4393*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501362046037530933 2500000000000000000 5000634878374979 5000000000000000 1024 4393 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000634878374979/5000000000000000 : ℝ)) (X := (2501362046037530933/2500000000000000000 : ℝ)) (by norm_num) 4393 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4416004244717877/50000000000000000000 : ℝ) ≤ ((567861058708680167/568000000000000000 : ℝ)+2*(71503311443/56800000000000 : ℝ)*(11351/100000 : ℝ))^(4393/1024 : ℝ) := by
    rw [show (567861058708680167/568000000000000000 : ℝ)+2*(71503311443/56800000000000 : ℝ)*(11351/100000 : ℝ)=(5000205858506321/5000000000000000 : ℝ) by norm_num, show 1+2*(4416004244717877/50000000000000000000 : ℝ)=(25004416004244717877/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1362046037530933/5000000000000000000 : ℝ)+(4416004244717877/50000000000000000000 : ℝ) ≤ ((567861058708680167/568000000000000000 : ℝ)+(71503311443/56800000000000 : ℝ)*((14759/100000 : ℝ)+(11351/100000 : ℝ)))^(4393/1024 : ℝ) := by
    rw [show (567861058708680167/568000000000000000 : ℝ)+(71503311443/56800000000000 : ℝ)*((14759/100000 : ℝ)+(11351/100000 : ℝ))=(100008407368813/100000000000000 : ℝ) by norm_num, show 1+(1362046037530933/5000000000000000000 : ℝ)+(4416004244717877/50000000000000000000 : ℝ)=(50018036464620027207/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1362046037530933/5000000000000000000 : ℝ) ≤ ((567861058708680167/568000000000000000 : ℝ)+2*(71503311443/56800000000000 : ℝ)*(14759/100000 : ℝ))^(4393/1024 : ℝ) := by
    rw [show (567861058708680167/568000000000000000 : ℝ)+2*(71503311443/56800000000000 : ℝ)*(14759/100000 : ℝ)=(5000634878374979/5000000000000000 : ℝ) by norm_num, show 1+2*(1362046037530933/5000000000000000000 : ℝ)=(2501362046037530933/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (567861058708680167/568000000000000000 : ℝ)*(X 1 0+X 2 0)+(71503311443/56800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4393/1024 : ℝ)) (lo := (11351/100000 : ℝ)) (hi := (14759/100000 : ℝ)) (c := (567861058708680167/568000000000000000 : ℝ)) (alpha := (71503311443/56800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (567861058708680167/568000000000000000 : ℝ)*(X 0 1+X 2 1)+(71503311443/56800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4393/1024 : ℝ)) (lo := (11351/100000 : ℝ)) (hi := (14759/100000 : ℝ)) (c := (567861058708680167/568000000000000000 : ℝ)) (alpha := (71503311443/56800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (567861058708680167/568000000000000000 : ℝ)*(X 0 2+X 1 2)+(71503311443/56800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4393/1024 : ℝ)) (lo := (11351/100000 : ℝ)) (hi := (14759/100000 : ℝ)) (c := (567861058708680167/568000000000000000 : ℝ)) (alpha := (71503311443/56800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-903392539/5000000000 : ℝ)*X 0 0+(2693020423/5000000000 : ℝ)*X 0 1+(2693020847/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1434_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2643050027/5000000000 : ℝ)*X 1 0+(-1944110411/10000000000 : ℝ)*X 1 1+(1346510313/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1434_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((66076253/125000000 : ℝ)*X 2 0+(2693020541/5000000000 : ℝ)*X 2 1+(-194411039/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1434_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2224660637/5000000000 : ℝ)*X 0 0+(4233727463/10000000000 : ℝ)*X 0 1+(4233727311/10000000000 : ℝ)*X 0 2+(2224660637/5000000000 : ℝ)*X 1 0+(4233727463/10000000000 : ℝ)*X 1 1+(4233727311/10000000000 : ℝ)*X 1 2+(2224660637/5000000000 : ℝ)*X 2 0+(4233727463/10000000000 : ℝ)*X 2 1+(4233727311/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1434_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1065056603/5000000000 : ℝ)*X 0 0+(5266600231/10000000000 : ℝ)*X 0 1+(2633300163/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1434_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2684836873/5000000000 : ℝ)*X 1 0+(-1992635709/10000000000 : ℝ)*X 1 1+(5266600413/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1434_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5369673893/10000000000 : ℝ)*X 2 0+(658325029/1250000000 : ℝ)*X 2 1+(-1992635753/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1434_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((415587583/1000000000 : ℝ)*X 0 0+(273774957/625000000 : ℝ)*X 0 1+(4380399411/10000000000 : ℝ)*X 0 2+(415587583/1000000000 : ℝ)*X 1 0+(273774957/625000000 : ℝ)*X 1 1+(4380399411/10000000000 : ℝ)*X 1 2+(415587583/1000000000 : ℝ)*X 2 0+(273774957/625000000 : ℝ)*X 2 1+(4380399411/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1434_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2061999693/10000000000 : ℝ)*X 0 0+(5183961539/10000000000 : ℝ)*X 0 1+(5400011891/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1434_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((65954009/125000000 : ℝ)*X 1 0+(-15506467/80000000 : ℝ)*X 1 1+(84375187/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1434_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5276320501/10000000000 : ℝ)*X 2 0+(2700006079/5000000000 : ℝ)*X 2 1+(-1938308413/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1434_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((448308801/1000000000 : ℝ)*X 0 0+(527069623/1250000000 : ℝ)*X 0 1+(2108278469/5000000000 : ℝ)*X 0 2+(448308801/1000000000 : ℝ)*X 1 0+(527069623/1250000000 : ℝ)*X 1 1+(2108278469/5000000000 : ℝ)*X 1 2+(448308801/1000000000 : ℝ)*X 2 0+(527069623/1250000000 : ℝ)*X 2 1+(2108278469/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1434_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1875070591/10000000000 : ℝ)*X 0 0+(683333221/1250000000 : ℝ)*X 0 1+(5255472207/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1434_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((336091231/625000000 : ℝ)*X 1 0+(-1997057461/10000000000 : ℝ)*X 1 1+(5255471007/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1434_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((672182417/1250000000 : ℝ)*X 2 0+(2627735761/5000000000 : ℝ)*X 2 1+(-1997057257/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1434_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4128086129/10000000000 : ℝ)*X 0 0+(2197027013/5000000000 : ℝ)*X 0 1+(4394052877/10000000000 : ℝ)*X 0 2+(4128086129/10000000000 : ℝ)*X 1 0+(2197027013/5000000000 : ℝ)*X 1 1+(4394052877/10000000000 : ℝ)*X 1 2+(4128086129/10000000000 : ℝ)*X 2 0+(2197027013/5000000000 : ℝ)*X 2 1+(4394052877/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1434_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62903/100000 : ℝ) ≤ (-17863601282393907157874596102257/28400000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (60357/500000000000 : ℝ)*(lower3) + (1386451/100000000000000 : ℝ)*(lower4) + (24380799/100000000000000 : ℝ)*(upper5) + (3022297928623757/100000000000000 : ℝ)*(major0) + (3022297928623757/100000000000000 : ℝ)*(major1) + (3022297928623757/100000000000000 : ℝ)*(major2) + (672896429/20000000000000 : ℝ)*(sp2) + (398687261/100000000000000 : ℝ)*(sp3) + (4157122561242763/100000000000000 : ℝ)*(sp4) + (4157079218167159/100000000000000 : ℝ)*(sp5) + (519640000940453/12500000000000 : ℝ)*(sp6) + (19084387547263/1000000000000 : ℝ)*(sp7) + (162152601/20000000000000 : ℝ)*(sp12) + (44153838609/100000000000000 : ℝ)*(sp13) + (954219576706781/50000000000000 : ℝ)*(f.failure) + (519640421500721/12500000000000 : ℝ)*(f.sum) + (13054968469311/2840000000000000000000000000 : ℝ)*base65 + (274530635259637419/56800000000000000000000000000000 : ℝ)*base67 + (477392306245237419/56800000000000000000000000000000 : ℝ)*base69 + (395293998158837419/56800000000000000000000000000000 : ℝ)*base71 + (17106067776431/2840000000000000000000000000 : ℝ)*base73 + (237304206927637419/56800000000000000000000000000000 : ℝ)*base75 + (60574426908362581/56800000000000000000000000000000 : ℝ)*base78 + (286208652832362581/56800000000000000000000000000000 : ℝ)*base80 + (24698191252191/2840000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (42747929/5000000000000000000000 : ℝ)*base89 + (42747929/5000000000000000000000 : ℝ)*base91 + (42747929/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (59123/100000 : ℝ) ≤ (8395856134768346722087489499961/14200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1745029/12500000000000 : ℝ)*(upper1) + (8476319/100000000000000 : ℝ)*(upper2) + (17080403/100000000000000 : ℝ)*(upper3) + (26862701/50000000000000 : ℝ)*(upper4) + (14928691/50000000000000 : ℝ)*(upper5) + (1547036479936487/50000000000000 : ℝ)*(major0) + (1547036479936487/50000000000000 : ℝ)*(major1) + (1547036479936487/50000000000000 : ℝ)*(major2) + (52683263965919/1250000000000 : ℝ)*(sp0) + (2107337811818091/50000000000000 : ℝ)*(sp1) + (263415108330061/6250000000000 : ℝ)*(sp2) + (1953761713633779/100000000000000 : ℝ)*(sp3) + (16945177603/50000000000000 : ℝ)*(sp10) + (7253181331/50000000000000 : ℝ)*(sp12) + (1953761713633779/100000000000000 : ℝ)*(f.failure) + (2107337811818091/50000000000000 : ℝ)*(f.sum) + (8931860886261/1420000000000000000000000000 : ℝ)*base65 + (77949939405236671/28400000000000000000000000000000 : ℝ)*base68 + (200768328633236671/28400000000000000000000000000000 : ℝ)*base70 + (208236168017636671/28400000000000000000000000000000 : ℝ)*base72 + (2004659941759/1420000000000000000000000000 : ℝ)*base74 + (69165624013236671/28400000000000000000000000000000 : ℝ)*base76 + (420223952768836671/28400000000000000000000000000000 : ℝ)*base78 + (1289769534836671/28400000000000000000000000000000 : ℝ)*base80 + (657176041679/1420000000000000000000000000 : ℝ)*base82 + (70661111/10000000000000000000000 : ℝ)*base89 + (70661111/10000000000000000000000 : ℝ)*base91 + (70661111/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (20119/25000 : ℝ) ≤ (2856988824738706469969755397793/3550000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4092489/20000000000000 : ℝ)*(upper1) + (2783717/5000000000000 : ℝ)*(upper2) + (6822521/20000000000000 : ℝ)*(lower5) + (850422994493707/25000000000000 : ℝ)*(major0) + (850422994493707/25000000000000 : ℝ)*(major1) + (850422994493707/25000000000000 : ℝ)*(major2) + (20634089/50000000000 : ℝ)*(sp1) + (43993205859/50000000000000 : ℝ)*(sp2) + (14646833123/100000000000000 : ℝ)*(sp3) + (116356167/100000000000000 : ℝ)*(sp4) + (2314274490959671/50000000000000 : ℝ)*(sp8) + (4628507830097509/100000000000000 : ℝ)*(sp9) + (4628461111863791/100000000000000 : ℝ)*(sp10) + (536998506173309/25000000000000 : ℝ)*(sp11) + (2148008671526359/100000000000000 : ℝ)*(f.failure) + (4628549098275509/100000000000000 : ℝ)*(f.sum) + (3515901074861/710000000000000000000000000 : ℝ)*base65 + (49857349199619069/14200000000000000000000000000000 : ℝ)*base67 + (29756955302219069/14200000000000000000000000000000 : ℝ)*base69 + (17386444847180931/14200000000000000000000000000000 : ℝ)*base72 + (1724169467621/710000000000000000000000000 : ℝ)*base73 + (111710302120619069/14200000000000000000000000000000 : ℝ)*base75 + (76435892692619069/14200000000000000000000000000000 : ℝ)*base77 + (63695136465819069/14200000000000000000000000000000 : ℝ)*base79 + (1638224947421/710000000000000000000000000 : ℝ)*base81 + (65863669/10000000000000000000000 : ℝ)*base90 + (65863669/10000000000000000000000 : ℝ)*base92 + (65863669/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-84703/100000 : ℝ) ≤ (-2405507810251179244242824174121/2840000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (478081/160000000000 : ℝ)*(lower0) + (49064599/100000000000000 : ℝ)*(lower1) + (5827517/25000000000000 : ℝ)*(lower2) + (23318927/100000000000000 : ℝ)*(lower4) + (343923326141207/10000000000000 : ℝ)*(major0) + (343923326141207/10000000000000 : ℝ)*(major1) + (343923326141207/10000000000000 : ℝ)*(major2) + (615696529/12500000000000 : ℝ)*(sp0) + (612409915203/100000000000000 : ℝ)*(sp5) + (19675737289/5000000000000 : ℝ)*(sp6) + (4734981028681021/100000000000000 : ℝ)*(sp12) + (4734373544338049/100000000000000 : ℝ)*(sp13) + (295912027469217/6250000000000 : ℝ)*(sp14) + (2171714228315611/100000000000000 : ℝ)*(sp15) + (2171714228315611/100000000000000 : ℝ)*(f.failure) + (4734985954253251/100000000000000 : ℝ)*(f.sum) + (856932075093/284000000000000000000000000 : ℝ)*base65 + (21154418374871569/5680000000000000000000000000000 : ℝ)*base67 + (41355850051991569/5680000000000000000000000000000 : ℝ)*base69 + (51653655068871569/5680000000000000000000000000000 : ℝ)*base71 + (868149261379/284000000000000000000000000 : ℝ)*base74 + (13826595034631569/5680000000000000000000000000000 : ℝ)*base75 + (35670438437671569/5680000000000000000000000000000 : ℝ)*base77 + (9772516612951569/5680000000000000000000000000000 : ℝ)*base79 + (1291191069951/284000000000000000000000000 : ℝ)*base82 + (1/50000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (40705601/10000000000000000000000 : ℝ)*base90 + (40705601/10000000000000000000000 : ℝ)*base92 + (40705601/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1434_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158364909/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14759/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11351/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62903/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59123/100000 : ℝ) else (20119/25000 : ℝ) ≤ X j i ∧ X j i ≤ (84703/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1434_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1434_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158364909/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14763/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11347/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62903/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59123/100000 : ℝ) else (20119/25000 : ℝ) ≤ X j i ∧ X j i ≤ (84703/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1434_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1434_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1434_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4393/1024 : ℝ) ≤ p) (hpb : p ≤ (2197/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158364909/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14763/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11347/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62903/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59123/100000 : ℝ) else (20119/25000 : ℝ) ≤ X j i ∧ X j i ≤ (84703/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1434_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
