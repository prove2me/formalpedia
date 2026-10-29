-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1374_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:21:26.165246+00:00
-- url     : https://prove2.me/submissions/30f1f25d-2259-4fb8-a75f-bb4f6bd8cd7c

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
theorem support_rectangle_w1374_s3_0 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-201518493/1000000000 : ℝ)*x 0 + (5423255077/10000000000 : ℝ)*x 1 + (5234300349/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (201518493/1000000000 : ℝ)^2167 ≤ (6138523225851/50000000000000 : ℝ)^1655 := by
    have hnat : (201518493 : ℕ)^2167*50000000000000^1655 ≤ 6138523225851^1655*1000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201518493 1000000000 6138523225851 50000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5423255077/10000000000 : ℝ)^2167 ≤ (5609953359759/12500000000000 : ℝ)^1655 := by
    have hnat : (5423255077 : ℕ)^2167*12500000000000^1655 ≤ 5609953359759^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423255077 10000000000 5609953359759 12500000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5234300349/10000000000 : ℝ)^2167 ≤ (2677707915371/6250000000000 : ℝ)^1655 := by
    have hnat : (5234300349 : ℕ)^2167*6250000000000^1655 ≤ 2677707915371^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5234300349 10000000000 2677707915371 6250000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-201518493/1000000000 : ℝ), (5423255077/10000000000 : ℝ), (5234300349/10000000000 : ℝ)] ![(6138523225851/50000000000000 : ℝ), (5609953359759/12500000000000 : ℝ), (2677707915371/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-201518493/1000000000 : ℝ)|^2167 ≤ (6138523225851/50000000000000 : ℝ)^1655
        have hw : |(-201518493/1000000000 : ℝ)|=(201518493/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5423255077/10000000000 : ℝ)|^2167 ≤ (5609953359759/12500000000000 : ℝ)^1655
        have hw : |(5423255077/10000000000 : ℝ)|=(5423255077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5234300349/10000000000 : ℝ)|^2167 ≤ (2677707915371/6250000000000 : ℝ)^1655
        have hw : |(5234300349/10000000000 : ℝ)|=(5234300349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_s3_1 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (214061939/400000000 : ℝ)*x 0 + (-6599001/31250000 : ℝ)*x 1 + (5234300439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214061939/400000000 : ℝ)^2167 ≤ (44104241872671/100000000000000 : ℝ)^1655 := by
    have hnat : (214061939 : ℕ)^2167*100000000000000^1655 ≤ 44104241872671^1655*400000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214061939 400000000 44104241872671 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6599001/31250000 : ℝ)^2167 ≤ (3263107626457/25000000000000 : ℝ)^1655 := by
    have hnat : (6599001 : ℕ)^2167*25000000000000^1655 ≤ 3263107626457^1655*31250000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6599001 31250000 3263107626457 25000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5234300439/10000000000 : ℝ)^2167 ≤ (21421663805247/50000000000000 : ℝ)^1655 := by
    have hnat : (5234300439 : ℕ)^2167*50000000000000^1655 ≤ 21421663805247^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5234300439 10000000000 21421663805247 50000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214061939/400000000 : ℝ), (-6599001/31250000 : ℝ), (5234300439/10000000000 : ℝ)] ![(44104241872671/100000000000000 : ℝ), (3263107626457/25000000000000 : ℝ), (21421663805247/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214061939/400000000 : ℝ)|^2167 ≤ (44104241872671/100000000000000 : ℝ)^1655
        have hw : |(214061939/400000000 : ℝ)|=(214061939/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6599001/31250000 : ℝ)|^2167 ≤ (3263107626457/25000000000000 : ℝ)^1655
        have hw : |(-6599001/31250000 : ℝ)|=(6599001/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5234300439/10000000000 : ℝ)|^2167 ≤ (21421663805247/50000000000000 : ℝ)^1655
        have hw : |(5234300439/10000000000 : ℝ)|=(5234300439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_s3_2 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (214061939/400000000 : ℝ)*x 0 + (5234300349/10000000000 : ℝ)*x 1 + (-2111680439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214061939/400000000 : ℝ)^2167 ≤ (44104241872671/100000000000000 : ℝ)^1655 := by
    have hnat : (214061939 : ℕ)^2167*100000000000000^1655 ≤ 44104241872671^1655*400000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214061939 400000000 44104241872671 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5234300349/10000000000 : ℝ)^2167 ≤ (2677707915371/6250000000000 : ℝ)^1655 := by
    have hnat : (5234300349 : ℕ)^2167*6250000000000^1655 ≤ 2677707915371^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5234300349 10000000000 2677707915371 6250000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2111680439/10000000000 : ℝ)^2167 ≤ (13052431468927/100000000000000 : ℝ)^1655 := by
    have hnat : (2111680439 : ℕ)^2167*100000000000000^1655 ≤ 13052431468927^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111680439 10000000000 13052431468927 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214061939/400000000 : ℝ), (5234300349/10000000000 : ℝ), (-2111680439/10000000000 : ℝ)] ![(44104241872671/100000000000000 : ℝ), (2677707915371/6250000000000 : ℝ), (13052431468927/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214061939/400000000 : ℝ)|^2167 ≤ (44104241872671/100000000000000 : ℝ)^1655
        have hw : |(214061939/400000000 : ℝ)|=(214061939/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5234300349/10000000000 : ℝ)|^2167 ≤ (2677707915371/6250000000000 : ℝ)^1655
        have hw : |(5234300349/10000000000 : ℝ)|=(5234300349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2111680439/10000000000 : ℝ)|^2167 ≤ (13052431468927/100000000000000 : ℝ)^1655
        have hw : |(-2111680439/10000000000 : ℝ)|=(2111680439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_s3_3 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2158717459/5000000000 : ℝ)*x 0 + (164857523/400000000 : ℝ)*x 1 + (2260993797/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2158717459/5000000000 : ℝ)^2167 ≤ (33294862466591/100000000000000 : ℝ)^1655 := by
    have hnat : (2158717459 : ℕ)^2167*100000000000000^1655 ≤ 33294862466591^1655*5000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158717459 5000000000 33294862466591 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (164857523/400000000 : ℝ)^2167 ≤ (15664918278783/50000000000000 : ℝ)^1655 := by
    have hnat : (164857523 : ℕ)^2167*50000000000000^1655 ≤ 15664918278783^1655*400000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164857523 400000000 15664918278783 50000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2260993797/5000000000 : ℝ)^2167 ≤ (35375300960171/100000000000000 : ℝ)^1655 := by
    have hnat : (2260993797 : ℕ)^2167*100000000000000^1655 ≤ 35375300960171^1655*5000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2260993797 5000000000 35375300960171 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2158717459/5000000000 : ℝ), (164857523/400000000 : ℝ), (2260993797/5000000000 : ℝ)] ![(33294862466591/100000000000000 : ℝ), (15664918278783/50000000000000 : ℝ), (35375300960171/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2158717459/5000000000 : ℝ)|^2167 ≤ (33294862466591/100000000000000 : ℝ)^1655
        have hw : |(2158717459/5000000000 : ℝ)|=(2158717459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(164857523/400000000 : ℝ)|^2167 ≤ (15664918278783/50000000000000 : ℝ)^1655
        have hw : |(164857523/400000000 : ℝ)|=(164857523/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2260993797/5000000000 : ℝ)|^2167 ≤ (35375300960171/100000000000000 : ℝ)^1655
        have hw : |(2260993797/5000000000 : ℝ)|=(2260993797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_s3_4 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2015202549/10000000000 : ℝ)*x 0 + (2617536993/5000000000 : ℝ)*x 1 + (5422476877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2015202549/10000000000 : ℝ)^2167 ≤ (12277186998757/100000000000000 : ℝ)^1655 := by
    have hnat : (2015202549 : ℕ)^2167*100000000000000^1655 ≤ 12277186998757^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2015202549 10000000000 12277186998757 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2617536993/5000000000 : ℝ)^2167 ≤ (4285161813667/10000000000000 : ℝ)^1655 := by
    have hnat : (2617536993 : ℕ)^2167*10000000000000^1655 ≤ 4285161813667^1655*5000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2617536993 5000000000 4285161813667 10000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5422476877/10000000000 : ℝ)^2167 ≤ (44871194856561/100000000000000 : ℝ)^1655 := by
    have hnat : (5422476877 : ℕ)^2167*100000000000000^1655 ≤ 44871194856561^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422476877 10000000000 44871194856561 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2015202549/10000000000 : ℝ), (2617536993/5000000000 : ℝ), (5422476877/10000000000 : ℝ)] ![(12277186998757/100000000000000 : ℝ), (4285161813667/10000000000000 : ℝ), (44871194856561/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2015202549/10000000000 : ℝ)|^2167 ≤ (12277186998757/100000000000000 : ℝ)^1655
        have hw : |(-2015202549/10000000000 : ℝ)|=(2015202549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2617536993/5000000000 : ℝ)|^2167 ≤ (4285161813667/10000000000000 : ℝ)^1655
        have hw : |(2617536993/5000000000 : ℝ)|=(2617536993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5422476877/10000000000 : ℝ)|^2167 ≤ (44871194856561/100000000000000 : ℝ)^1655
        have hw : |(5422476877/10000000000 : ℝ)|=(5422476877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_s3_5 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5302703173/10000000000 : ℝ)*x 0 + (-240437977/1250000000 : ℝ)*x 1 + (5422476877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302703173/10000000000 : ℝ)^2167 ≤ (5447237226401/12500000000000 : ℝ)^1655 := by
    have hnat : (5302703173 : ℕ)^2167*12500000000000^1655 ≤ 5447237226401^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302703173 10000000000 5447237226401 12500000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (240437977/1250000000 : ℝ)^2167 ≤ (11550907318623/100000000000000 : ℝ)^1655 := by
    have hnat : (240437977 : ℕ)^2167*100000000000000^1655 ≤ 11550907318623^1655*1250000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      240437977 1250000000 11550907318623 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5422476877/10000000000 : ℝ)^2167 ≤ (44871194856561/100000000000000 : ℝ)^1655 := by
    have hnat : (5422476877 : ℕ)^2167*100000000000000^1655 ≤ 44871194856561^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422476877 10000000000 44871194856561 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302703173/10000000000 : ℝ), (-240437977/1250000000 : ℝ), (5422476877/10000000000 : ℝ)] ![(5447237226401/12500000000000 : ℝ), (11550907318623/100000000000000 : ℝ), (44871194856561/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302703173/10000000000 : ℝ)|^2167 ≤ (5447237226401/12500000000000 : ℝ)^1655
        have hw : |(5302703173/10000000000 : ℝ)|=(5302703173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-240437977/1250000000 : ℝ)|^2167 ≤ (11550907318623/100000000000000 : ℝ)^1655
        have hw : |(-240437977/1250000000 : ℝ)|=(240437977/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5422476877/10000000000 : ℝ)|^2167 ≤ (44871194856561/100000000000000 : ℝ)^1655
        have hw : |(5422476877/10000000000 : ℝ)|=(5422476877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_s3_6 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2651351557/5000000000 : ℝ)*x 0 + (2711238463/5000000000 : ℝ)*x 1 + (-1923503829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651351557/5000000000 : ℝ)^2167 ≤ (21788948588171/50000000000000 : ℝ)^1655 := by
    have hnat : (2651351557 : ℕ)^2167*50000000000000^1655 ≤ 21788948588171^1655*5000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651351557 5000000000 21788948588171 50000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2711238463/5000000000 : ℝ)^2167 ≤ (44871195387479/100000000000000 : ℝ)^1655 := by
    have hnat : (2711238463 : ℕ)^2167*100000000000000^1655 ≤ 44871195387479^1655*5000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711238463 5000000000 44871195387479 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1923503829/10000000000 : ℝ)^2167 ≤ (11550907420841/100000000000000 : ℝ)^1655 := by
    have hnat : (1923503829 : ℕ)^2167*100000000000000^1655 ≤ 11550907420841^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1923503829 10000000000 11550907420841 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651351557/5000000000 : ℝ), (2711238463/5000000000 : ℝ), (-1923503829/10000000000 : ℝ)] ![(21788948588171/50000000000000 : ℝ), (44871195387479/100000000000000 : ℝ), (11550907420841/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651351557/5000000000 : ℝ)|^2167 ≤ (21788948588171/50000000000000 : ℝ)^1655
        have hw : |(2651351557/5000000000 : ℝ)|=(2651351557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2711238463/5000000000 : ℝ)|^2167 ≤ (44871195387479/100000000000000 : ℝ)^1655
        have hw : |(2711238463/5000000000 : ℝ)|=(2711238463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1923503829/10000000000 : ℝ)|^2167 ≤ (11550907420841/100000000000000 : ℝ)^1655
        have hw : |(-1923503829/10000000000 : ℝ)|=(1923503829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_s3_7 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (53968403/125000000 : ℝ)*x 0 + (4520347663/10000000000 : ℝ)*x 1 + (4123087683/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53968403/125000000 : ℝ)^2167 ≤ (33295239324669/100000000000000 : ℝ)^1655 := by
    have hnat : (53968403 : ℕ)^2167*100000000000000^1655 ≤ 33295239324669^1655*125000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53968403 125000000 33295239324669 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4520347663/10000000000 : ℝ)^2167 ≤ (35358503914607/100000000000000 : ℝ)^1655 := by
    have hnat : (4520347663 : ℕ)^2167*100000000000000^1655 ≤ 35358503914607^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4520347663 10000000000 35358503914607 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4123087683/10000000000 : ℝ)^2167 ≤ (1567312836857/5000000000000 : ℝ)^1655 := by
    have hnat : (4123087683 : ℕ)^2167*5000000000000^1655 ≤ 1567312836857^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4123087683 10000000000 1567312836857 5000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53968403/125000000 : ℝ), (4520347663/10000000000 : ℝ), (4123087683/10000000000 : ℝ)] ![(33295239324669/100000000000000 : ℝ), (35358503914607/100000000000000 : ℝ), (1567312836857/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53968403/125000000 : ℝ)|^2167 ≤ (33295239324669/100000000000000 : ℝ)^1655
        have hw : |(53968403/125000000 : ℝ)|=(53968403/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4520347663/10000000000 : ℝ)|^2167 ≤ (35358503914607/100000000000000 : ℝ)^1655
        have hw : |(4520347663/10000000000 : ℝ)|=(4520347663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4123087683/10000000000 : ℝ)|^2167 ≤ (1567312836857/5000000000000 : ℝ)^1655
        have hw : |(4123087683/10000000000 : ℝ)|=(4123087683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1374_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31198181/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15983/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5027/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5491/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7491/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15983/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5027/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15983/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5027/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15983/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5027/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15983/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5027/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15983/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5027/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15983/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5027/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5027/50000 : ℝ) ^ (4333/1024 : ℝ) ≤ (3002075003614293/50000000000000000000 : ℝ) := by
    have hpowers : (5027/50000 : ℝ)^4333 ≤ (3002075003614293/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5027 : ℕ)^4333*50000000000000000000^1024 ≤ 3002075003614293^1024*50000^4333 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5027 50000 3002075003614293 50000000000000000000 4333 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5027/50000 : ℝ)) (X := (3002075003614293/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4333 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15983/100000 : ℝ) ^ (4333/1024 : ℝ) ≤ (42689753203759317/100000000000000000000 : ℝ) := by
    have hpowers : (15983/100000 : ℝ)^4333 ≤ (42689753203759317/100000000000000000000 : ℝ)^1024 := by
      have hnat : (15983 : ℕ)^4333*100000000000000000000^1024 ≤ 42689753203759317^1024*100000^4333 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15983 100000 42689753203759317 100000000000000000000 4333 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15983/100000 : ℝ)) (X := (42689753203759317/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4333 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25003002075003614293/25000000000000000000 : ℝ) ≤ (10000283774184949/10000000000000000 : ℝ) ^ (4333/1024 : ℝ) := by
    have hpowers : (25003002075003614293/25000000000000000000 : ℝ)^1024 ≤ (10000283774184949/10000000000000000 : ℝ)^4333 := by
      have hnat : (25003002075003614293 : ℕ)^1024*10000000000000000^4333 ≤ 10000283774184949^4333*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003002075003614293 25000000000000000000 10000283774184949 10000000000000000 1024 4333 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000283774184949/10000000000000000 : ℝ)) (X := (25003002075003614293/25000000000000000000 : ℝ)) (by norm_num) 4333 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048693903210987903/100000000000000000000 : ℝ) ≤ (5000575274504127/5000000000000000 : ℝ) ^ (4333/1024 : ℝ) := by
    have hpowers : (100048693903210987903/100000000000000000000 : ℝ)^1024 ≤ (5000575274504127/5000000000000000 : ℝ)^4333 := by
      have hnat : (100048693903210987903 : ℕ)^1024*5000000000000000^4333 ≤ 5000575274504127^4333*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048693903210987903 100000000000000000000 5000575274504127 5000000000000000 1024 4333 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000575274504127/5000000000000000 : ℝ)) (X := (100048693903210987903/100000000000000000000 : ℝ)) (by norm_num) 4333 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50042689753203759317/50000000000000000000 : ℝ) ≤ (10002017323831559/10000000000000000 : ℝ) ^ (4333/1024 : ℝ) := by
    have hpowers : (50042689753203759317/50000000000000000000 : ℝ)^1024 ≤ (10002017323831559/10000000000000000 : ℝ)^4333 := by
      have hnat : (50042689753203759317 : ℕ)^1024*10000000000000000^4333 ≤ 10002017323831559^4333*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50042689753203759317 50000000000000000000 10002017323831559 10000000000000000 1024 4333 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002017323831559/10000000000000000 : ℝ)) (X := (50042689753203759317/50000000000000000000 : ℝ)) (by norm_num) 4333 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3002075003614293/50000000000000000000 : ℝ) ≤ ((5388568489908685971/5390000000000000000 : ℝ)+2*(173354964661/118580000000000 : ℝ)*(5027/50000 : ℝ))^(4333/1024 : ℝ) := by
    rw [show (5388568489908685971/5390000000000000000 : ℝ)+2*(173354964661/118580000000000 : ℝ)*(5027/50000 : ℝ)=(10000283774184949/10000000000000000 : ℝ) by norm_num, show 1+2*(3002075003614293/50000000000000000000 : ℝ)=(25003002075003614293/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(42689753203759317/100000000000000000000 : ℝ)+(3002075003614293/50000000000000000000 : ℝ) ≤ ((5388568489908685971/5390000000000000000 : ℝ)+(173354964661/118580000000000 : ℝ)*((15983/100000 : ℝ)+(5027/50000 : ℝ)))^(4333/1024 : ℝ) := by
    rw [show (5388568489908685971/5390000000000000000 : ℝ)+(173354964661/118580000000000 : ℝ)*((15983/100000 : ℝ)+(5027/50000 : ℝ))=(5000575274504127/5000000000000000 : ℝ) by norm_num, show 1+(42689753203759317/100000000000000000000 : ℝ)+(3002075003614293/50000000000000000000 : ℝ)=(100048693903210987903/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(42689753203759317/100000000000000000000 : ℝ) ≤ ((5388568489908685971/5390000000000000000 : ℝ)+2*(173354964661/118580000000000 : ℝ)*(15983/100000 : ℝ))^(4333/1024 : ℝ) := by
    rw [show (5388568489908685971/5390000000000000000 : ℝ)+2*(173354964661/118580000000000 : ℝ)*(15983/100000 : ℝ)=(10002017323831559/10000000000000000 : ℝ) by norm_num, show 1+2*(42689753203759317/100000000000000000000 : ℝ)=(50042689753203759317/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5388568489908685971/5390000000000000000 : ℝ)*(X 1 0+X 2 0)+(173354964661/118580000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4333/1024 : ℝ)) (lo := (5027/50000 : ℝ)) (hi := (15983/100000 : ℝ)) (c := (5388568489908685971/5390000000000000000 : ℝ)) (alpha := (173354964661/118580000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5388568489908685971/5390000000000000000 : ℝ)*(X 0 1+X 2 1)+(173354964661/118580000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4333/1024 : ℝ)) (lo := (5027/50000 : ℝ)) (hi := (15983/100000 : ℝ)) (c := (5388568489908685971/5390000000000000000 : ℝ)) (alpha := (173354964661/118580000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5388568489908685971/5390000000000000000 : ℝ)*(X 0 2+X 1 2)+(173354964661/118580000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4333/1024 : ℝ)) (lo := (5027/50000 : ℝ)) (hi := (15983/100000 : ℝ)) (c := (5388568489908685971/5390000000000000000 : ℝ)) (alpha := (173354964661/118580000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-201518493/1000000000 : ℝ)*X 0 0+(5423255077/10000000000 : ℝ)*X 0 1+(5234300349/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((214061939/400000000 : ℝ)*X 1 0+(-6599001/31250000 : ℝ)*X 1 1+(5234300439/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((214061939/400000000 : ℝ)*X 2 0+(5234300349/10000000000 : ℝ)*X 2 1+(-2111680439/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2158717459/5000000000 : ℝ)*X 0 0+(164857523/400000000 : ℝ)*X 0 1+(2260993797/5000000000 : ℝ)*X 0 2+(2158717459/5000000000 : ℝ)*X 1 0+(164857523/400000000 : ℝ)*X 1 1+(2260993797/5000000000 : ℝ)*X 1 2+(2158717459/5000000000 : ℝ)*X 2 0+(164857523/400000000 : ℝ)*X 2 1+(2260993797/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2015202549/10000000000 : ℝ)*X 0 0+(2617536993/5000000000 : ℝ)*X 0 1+(5422476877/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5302703173/10000000000 : ℝ)*X 1 0+(-240437977/1250000000 : ℝ)*X 1 1+(5422476877/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2651351557/5000000000 : ℝ)*X 2 0+(2711238463/5000000000 : ℝ)*X 2 1+(-1923503829/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((53968403/125000000 : ℝ)*X 0 0+(4520347663/10000000000 : ℝ)*X 0 1+(4123087683/10000000000 : ℝ)*X 0 2+(53968403/125000000 : ℝ)*X 1 0+(4520347663/10000000000 : ℝ)*X 1 1+(4123087683/10000000000 : ℝ)*X 1 2+(53968403/125000000 : ℝ)*X 2 0+(4520347663/10000000000 : ℝ)*X 2 1+(4123087683/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (955243318211669704542144861/105875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1611596019/100000000000000 : ℝ)*(base19) + (736433143/50000000000000 : ℝ)*(base23) + (2320059/3125000000000 : ℝ)*(lower2) + (238109/78125000000 : ℝ)*(upper3) + (68452149/100000000000000 : ℝ)*(upper5) + (1947232983625489/50000000000000 : ℝ)*(major0) + (1947232983625489/50000000000000 : ℝ)*(major1) + (1947232983625489/50000000000000 : ℝ)*(major2) + (2646153193142129/50000000000000 : ℝ)*(sp0) + (1323082981045203/25000000000000 : ℝ)*(sp1) + (1058466412582109/20000000000000 : ℝ)*(sp2) + (39009098358431/1562500000000 : ℝ)*(sp3) + (13574746287/50000000000000 : ℝ)*(sp4) + (15803039897/100000000000000 : ℝ)*(sp7) + (62414952449487/2500000000000 : ℝ)*(f.failure) + (5292333535776831/100000000000000 : ℝ)*(f.sum) + (466818892657/211750000000000000000000000 : ℝ)*base66 + (6055866289712076713/423500000000000000000000000000000 : ℝ)*base68 + (5466141542793076713/423500000000000000000000000000000 : ℝ)*base70 + (2565583344739423287/423500000000000000000000000000000 : ℝ)*base71 + (3753715109843/847000000000000000000000000 : ℝ)*base74 + (7035699891151076713/423500000000000000000000000000000 : ℝ)*base76 + (2123962243873076713/423500000000000000000000000000000 : ℝ)*base78 + (3107468765524576713/423500000000000000000000000000000 : ℝ)*base80 + (428099685183/84700000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (216853/50000000000000000000 : ℝ)*base90 + (216853/50000000000000000000 : ℝ)*base92 + (216853/50000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (52442217800512623819951/5929000000000000000000000000 : ℝ) := by norm_num
    linear_combination (784925537/50000000000000 : ℝ)*(base19) + (824112367/50000000000000 : ℝ)*(base23) + (35132723/20000000000000 : ℝ)*(upper3) + (66337269/100000000000000 : ℝ)*(lower4) + (189744839/100000000000000 : ℝ)*(upper5) + (3926669266726219/100000000000000 : ℝ)*(major0) + (3926669266726219/100000000000000 : ℝ)*(major1) + (3926669266726219/100000000000000 : ℝ)*(major2) + (7213168557/25000000000000 : ℝ)*(sp1) + (3022532067/10000000000000 : ℝ)*(sp2) + (2668047898178713/50000000000000 : ℝ)*(sp4) + (5336065373832123/100000000000000 : ℝ)*(sp5) + (2668031961406011/50000000000000 : ℝ)*(sp6) + (629310610565119/25000000000000 : ℝ)*(sp7) + (629310610565119/25000000000000 : ℝ)*(f.failure) + (2668047898178713/50000000000000 : ℝ)*(f.sum) + (2353175074749/1185800000000000000000000000 : ℝ)*base65 + (29779284547018410139/5929000000000000000000000000000000 : ℝ)*base67 + (35348219634875589861/5929000000000000000000000000000000 : ℝ)*base70 + (21363837792136589861/5929000000000000000000000000000000 : ℝ)*base72 + (40448682308219/5929000000000000000000000000 : ℝ)*base73 + (127821018381755410139/5929000000000000000000000000000000 : ℝ)*base75 + (11248288947427589861/5929000000000000000000000000000000 : ℝ)*base78 + (20661679220804410139/5929000000000000000000000000000000 : ℝ)*base79 + (5895449830701/5929000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (151461/500000000000000000000 : ℝ)*base90 + (151461/500000000000000000000 : ℝ)*base92 + (151461/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1374_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31198181/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15983/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5027/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5491/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7491/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1374_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1374_s4_0 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2016409787/10000000000 : ℝ)*x 0 + (5413097173/10000000000 : ℝ)*x 1 + (5243652989/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2016409787/10000000000 : ℝ)^2167 ≤ (12286818061539/100000000000000 : ℝ)^1655 := by
    have hnat : (2016409787 : ℕ)^2167*100000000000000^1655 ≤ 12286818061539^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2016409787 10000000000 12286818061539 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5413097173/10000000000 : ℝ)^2167 ≤ (8953918503457/20000000000000 : ℝ)^1655 := by
    have hnat : (5413097173 : ℕ)^2167*20000000000000^1655 ≤ 8953918503457^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413097173 10000000000 8953918503457 20000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243652989/10000000000 : ℝ)^2167 ≤ (42943589403341/100000000000000 : ℝ)^1655 := by
    have hnat : (5243652989 : ℕ)^2167*100000000000000^1655 ≤ 42943589403341^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243652989 10000000000 42943589403341 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2016409787/10000000000 : ℝ), (5413097173/10000000000 : ℝ), (5243652989/10000000000 : ℝ)] ![(12286818061539/100000000000000 : ℝ), (8953918503457/20000000000000 : ℝ), (42943589403341/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2016409787/10000000000 : ℝ)|^2167 ≤ (12286818061539/100000000000000 : ℝ)^1655
        have hw : |(-2016409787/10000000000 : ℝ)|=(2016409787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5413097173/10000000000 : ℝ)|^2167 ≤ (8953918503457/20000000000000 : ℝ)^1655
        have hw : |(5413097173/10000000000 : ℝ)|=(5413097173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243652989/10000000000 : ℝ)|^2167 ≤ (42943589403341/100000000000000 : ℝ)^1655
        have hw : |(5243652989/10000000000 : ℝ)|=(5243652989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_s4_1 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5348946641/10000000000 : ℝ)*x 0 + (-525688777/2500000000 : ℝ)*x 1 + (5243652931/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348946641/10000000000 : ℝ)^2167 ≤ (8815233517207/20000000000000 : ℝ)^1655 := by
    have hnat : (5348946641 : ℕ)^2167*20000000000000^1655 ≤ 8815233517207^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348946641 10000000000 8815233517207 20000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (525688777/2500000000 : ℝ)^2167 ≤ (6490121804921/50000000000000 : ℝ)^1655 := by
    have hnat : (525688777 : ℕ)^2167*50000000000000^1655 ≤ 6490121804921^1655*2500000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525688777 2500000000 6490121804921 50000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243652931/10000000000 : ℝ)^2167 ≤ (21471794390697/50000000000000 : ℝ)^1655 := by
    have hnat : (5243652931 : ℕ)^2167*50000000000000^1655 ≤ 21471794390697^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243652931 10000000000 21471794390697 50000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348946641/10000000000 : ℝ), (-525688777/2500000000 : ℝ), (5243652931/10000000000 : ℝ)] ![(8815233517207/20000000000000 : ℝ), (6490121804921/50000000000000 : ℝ), (21471794390697/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348946641/10000000000 : ℝ)|^2167 ≤ (8815233517207/20000000000000 : ℝ)^1655
        have hw : |(5348946641/10000000000 : ℝ)|=(5348946641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-525688777/2500000000 : ℝ)|^2167 ≤ (6490121804921/50000000000000 : ℝ)^1655
        have hw : |(-525688777/2500000000 : ℝ)|=(525688777/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243652931/10000000000 : ℝ)|^2167 ≤ (21471794390697/50000000000000 : ℝ)^1655
        have hw : |(5243652931/10000000000 : ℝ)|=(5243652931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_s4_2 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2674473311/5000000000 : ℝ)*x 0 + (1310913259/2500000000 : ℝ)*x 1 + (-1051377497/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674473311/5000000000 : ℝ)^2167 ≤ (44076167381037/100000000000000 : ℝ)^1655 := by
    have hnat : (2674473311 : ℕ)^2167*100000000000000^1655 ≤ 44076167381037^1655*5000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674473311 5000000000 44076167381037 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310913259/2500000000 : ℝ)^2167 ≤ (10735897476833/25000000000000 : ℝ)^1655 := by
    have hnat : (1310913259 : ℕ)^2167*25000000000000^1655 ≤ 10735897476833^1655*2500000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310913259 2500000000 10735897476833 25000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1051377497/5000000000 : ℝ)^2167 ≤ (12980242688417/100000000000000 : ℝ)^1655 := by
    have hnat : (1051377497 : ℕ)^2167*100000000000000^1655 ≤ 12980242688417^1655*5000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051377497 5000000000 12980242688417 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674473311/5000000000 : ℝ), (1310913259/2500000000 : ℝ), (-1051377497/5000000000 : ℝ)] ![(44076167381037/100000000000000 : ℝ), (10735897476833/25000000000000 : ℝ), (12980242688417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674473311/5000000000 : ℝ)|^2167 ≤ (44076167381037/100000000000000 : ℝ)^1655
        have hw : |(2674473311/5000000000 : ℝ)|=(2674473311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310913259/2500000000 : ℝ)|^2167 ≤ (10735897476833/25000000000000 : ℝ)^1655
        have hw : |(1310913259/2500000000 : ℝ)|=(1310913259/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1051377497/5000000000 : ℝ)|^2167 ≤ (12980242688417/100000000000000 : ℝ)^1655
        have hw : |(-1051377497/5000000000 : ℝ)|=(1051377497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_s4_3 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (107954511/250000000 : ℝ)*x 0 + (2071013049/5000000000 : ℝ)*x 1 + (4501216763/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107954511/250000000 : ℝ)^2167 ≤ (666047810993/2000000000000 : ℝ)^1655 := by
    have hnat : (107954511 : ℕ)^2167*2000000000000^1655 ≤ 666047810993^1655*250000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107954511 250000000 666047810993 2000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2071013049/5000000000 : ℝ)^2167 ≤ (15767457490687/50000000000000 : ℝ)^1655 := by
    have hnat : (2071013049 : ℕ)^2167*50000000000000^1655 ≤ 15767457490687^1655*5000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2071013049 5000000000 15767457490687 50000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4501216763/10000000000 : ℝ)^2167 ≤ (17581347225337/50000000000000 : ℝ)^1655 := by
    have hnat : (4501216763 : ℕ)^2167*50000000000000^1655 ≤ 17581347225337^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4501216763 10000000000 17581347225337 50000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(107954511/250000000 : ℝ), (2071013049/5000000000 : ℝ), (4501216763/10000000000 : ℝ)] ![(666047810993/2000000000000 : ℝ), (15767457490687/50000000000000 : ℝ), (17581347225337/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(107954511/250000000 : ℝ)|^2167 ≤ (666047810993/2000000000000 : ℝ)^1655
        have hw : |(107954511/250000000 : ℝ)|=(107954511/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2071013049/5000000000 : ℝ)|^2167 ≤ (15767457490687/50000000000000 : ℝ)^1655
        have hw : |(2071013049/5000000000 : ℝ)|=(2071013049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4501216763/10000000000 : ℝ)|^2167 ≤ (17581347225337/50000000000000 : ℝ)^1655
        have hw : |(4501216763/10000000000 : ℝ)|=(4501216763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_s4_4 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-100821149/500000000 : ℝ)*x 0 + (524427553/1000000000 : ℝ)*x 1 + (1082494197/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (100821149/500000000 : ℝ)^2167 ≤ (12286923322067/100000000000000 : ℝ)^1655 := by
    have hnat : (100821149 : ℕ)^2167*100000000000000^1655 ≤ 12286923322067^1655*500000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100821149 500000000 12286923322067 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524427553/1000000000 : ℝ)^2167 ≤ (21475132585749/50000000000000 : ℝ)^1655 := by
    have hnat : (524427553 : ℕ)^2167*50000000000000^1655 ≤ 21475132585749^1655*1000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524427553 1000000000 21475132585749 50000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082494197/2000000000 : ℝ)^2167 ≤ (22381405747273/50000000000000 : ℝ)^1655 := by
    have hnat : (1082494197 : ℕ)^2167*50000000000000^1655 ≤ 22381405747273^1655*2000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082494197 2000000000 22381405747273 50000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-100821149/500000000 : ℝ), (524427553/1000000000 : ℝ), (1082494197/2000000000 : ℝ)] ![(12286923322067/100000000000000 : ℝ), (21475132585749/50000000000000 : ℝ), (22381405747273/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-100821149/500000000 : ℝ)|^2167 ≤ (12286923322067/100000000000000 : ℝ)^1655
        have hw : |(-100821149/500000000 : ℝ)|=(100821149/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524427553/1000000000 : ℝ)|^2167 ≤ (21475132585749/50000000000000 : ℝ)^1655
        have hw : |(524427553/1000000000 : ℝ)|=(524427553/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1082494197/2000000000 : ℝ)|^2167 ≤ (22381405747273/50000000000000 : ℝ)^1655
        have hw : |(1082494197/2000000000 : ℝ)|=(1082494197/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_s4_5 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652572617/5000000000 : ℝ)*x 0 + (-1933936797/10000000000 : ℝ)*x 1 + (2706235557/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652572617/5000000000 : ℝ)^2167 ≤ (8720835464843/20000000000000 : ℝ)^1655 := by
    have hnat : (2652572617 : ℕ)^2167*20000000000000^1655 ≤ 8720835464843^1655*5000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652572617 5000000000 8720835464843 20000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1933936797/10000000000 : ℝ)^2167 ≤ (11633009772881/100000000000000 : ℝ)^1655 := by
    have hnat : (1933936797 : ℕ)^2167*100000000000000^1655 ≤ 11633009772881^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1933936797 10000000000 11633009772881 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2706235557/5000000000 : ℝ)^2167 ≤ (44762812891469/100000000000000 : ℝ)^1655 := by
    have hnat : (2706235557 : ℕ)^2167*100000000000000^1655 ≤ 44762812891469^1655*5000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706235557 5000000000 44762812891469 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652572617/5000000000 : ℝ), (-1933936797/10000000000 : ℝ), (2706235557/5000000000 : ℝ)] ![(8720835464843/20000000000000 : ℝ), (11633009772881/100000000000000 : ℝ), (44762812891469/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652572617/5000000000 : ℝ)|^2167 ≤ (8720835464843/20000000000000 : ℝ)^1655
        have hw : |(2652572617/5000000000 : ℝ)|=(2652572617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1933936797/10000000000 : ℝ)|^2167 ≤ (11633009772881/100000000000000 : ℝ)^1655
        have hw : |(-1933936797/10000000000 : ℝ)|=(1933936797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2706235557/5000000000 : ℝ)|^2167 ≤ (44762812891469/100000000000000 : ℝ)^1655
        have hw : |(2706235557/5000000000 : ℝ)|=(2706235557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_s4_6 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652572743/5000000000 : ℝ)*x 0 + (270623549/500000000 : ℝ)*x 1 + (-1933936637/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652572743/5000000000 : ℝ)^2167 ≤ (43604180036231/100000000000000 : ℝ)^1655 := by
    have hnat : (2652572743 : ℕ)^2167*100000000000000^1655 ≤ 43604180036231^1655*5000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652572743 5000000000 43604180036231 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (270623549/500000000 : ℝ)^2167 ≤ (22381405720201/50000000000000 : ℝ)^1655 := by
    have hnat : (270623549 : ℕ)^2167*50000000000000^1655 ≤ 22381405720201^1655*500000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270623549 500000000 22381405720201 50000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1933936637/10000000000 : ℝ)^2167 ≤ (11633008512707/100000000000000 : ℝ)^1655 := by
    have hnat : (1933936637 : ℕ)^2167*100000000000000^1655 ≤ 11633008512707^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1933936637 10000000000 11633008512707 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652572743/5000000000 : ℝ), (270623549/500000000 : ℝ), (-1933936637/10000000000 : ℝ)] ![(43604180036231/100000000000000 : ℝ), (22381405720201/50000000000000 : ℝ), (11633008512707/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652572743/5000000000 : ℝ)|^2167 ≤ (43604180036231/100000000000000 : ℝ)^1655
        have hw : |(2652572743/5000000000 : ℝ)|=(2652572743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(270623549/500000000 : ℝ)|^2167 ≤ (22381405720201/50000000000000 : ℝ)^1655
        have hw : |(270623549/500000000 : ℝ)|=(270623549/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1933936637/10000000000 : ℝ)|^2167 ≤ (11633008512707/100000000000000 : ℝ)^1655
        have hw : |(-1933936637/10000000000 : ℝ)|=(1933936637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_s4_7 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (53977587/125000000 : ℝ)*x 0 + (2249948733/5000000000 : ℝ)*x 1 + (4143352787/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53977587/125000000 : ℝ)^2167 ≤ (3330265834897/10000000000000 : ℝ)^1655 := by
    have hnat : (53977587 : ℕ)^2167*10000000000000^1655 ≤ 3330265834897^1655*125000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53977587 125000000 3330265834897 10000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2249948733/5000000000 : ℝ)^2167 ≤ (17574600298197/50000000000000 : ℝ)^1655 := by
    have hnat : (2249948733 : ℕ)^2167*50000000000000^1655 ≤ 17574600298197^1655*5000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2249948733 5000000000 17574600298197 50000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4143352787/10000000000 : ℝ)^2167 ≤ (3154814103837/10000000000000 : ℝ)^1655 := by
    have hnat : (4143352787 : ℕ)^2167*10000000000000^1655 ≤ 3154814103837^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4143352787 10000000000 3154814103837 10000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53977587/125000000 : ℝ), (2249948733/5000000000 : ℝ), (4143352787/10000000000 : ℝ)] ![(3330265834897/10000000000000 : ℝ), (17574600298197/50000000000000 : ℝ), (3154814103837/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53977587/125000000 : ℝ)|^2167 ≤ (3330265834897/10000000000000 : ℝ)^1655
        have hw : |(53977587/125000000 : ℝ)|=(53977587/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2249948733/5000000000 : ℝ)|^2167 ≤ (17574600298197/50000000000000 : ℝ)^1655
        have hw : |(2249948733/5000000000 : ℝ)|=(2249948733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4143352787/10000000000 : ℝ)|^2167 ≤ (3154814103837/10000000000000 : ℝ)^1655
        have hw : |(4143352787/10000000000 : ℝ)|=(4143352787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1374_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31198181/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7491/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5491/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5591/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1477/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7491/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5491/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7491/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5491/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7491/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5491/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7491/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5491/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7491/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5491/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7491/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5491/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5491/50000 : ℝ) ^ (4333/1024 : ℝ) ≤ (8723604612399543/100000000000000000000 : ℝ) := by
    have hpowers : (5491/50000 : ℝ)^4333 ≤ (8723604612399543/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5491 : ℕ)^4333*100000000000000000000^1024 ≤ 8723604612399543^1024*50000^4333 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5491 50000 8723604612399543 100000000000000000000 4333 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5491/50000 : ℝ)) (X := (8723604612399543/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4333 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7491/50000 : ℝ) ^ (4333/1024 : ℝ) ≤ (16234490685272297/50000000000000000000 : ℝ) := by
    have hpowers : (7491/50000 : ℝ)^4333 ≤ (16234490685272297/50000000000000000000 : ℝ)^1024 := by
      have hnat : (7491 : ℕ)^4333*50000000000000000000^1024 ≤ 16234490685272297^1024*50000^4333 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7491 50000 16234490685272297 50000000000000000000 4333 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7491/50000 : ℝ)) (X := (16234490685272297/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4333 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008723604612399543/50000000000000000000 : ℝ) ≤ (10000412295225959/10000000000000000 : ℝ) ^ (4333/1024 : ℝ) := by
    have hpowers : (50008723604612399543/50000000000000000000 : ℝ)^1024 ≤ (10000412295225959/10000000000000000 : ℝ)^4333 := by
      have hnat : (50008723604612399543 : ℕ)^1024*10000000000000000^4333 ≤ 10000412295225959^4333*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008723604612399543 50000000000000000000 10000412295225959 10000000000000000 1024 4333 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000412295225959/10000000000000000 : ℝ)) (X := (50008723604612399543/50000000000000000000 : ℝ)) (by norm_num) 4333 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100041192585982944137/100000000000000000000 : ℝ) ≤ (10000973334295667/10000000000000000 : ℝ) ^ (4333/1024 : ℝ) := by
    have hpowers : (100041192585982944137/100000000000000000000 : ℝ)^1024 ≤ (10000973334295667/10000000000000000 : ℝ)^4333 := by
      have hnat : (100041192585982944137 : ℕ)^1024*10000000000000000^4333 ≤ 10000973334295667^4333*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100041192585982944137 100000000000000000000 10000973334295667 10000000000000000 1024 4333 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000973334295667/10000000000000000 : ℝ)) (X := (100041192585982944137/100000000000000000000 : ℝ)) (by norm_num) 4333 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016234490685272297/25000000000000000000 : ℝ) ≤ (80012274986923/80000000000000 : ℝ) ^ (4333/1024 : ℝ) := by
    have hpowers : (25016234490685272297/25000000000000000000 : ℝ)^1024 ≤ (80012274986923/80000000000000 : ℝ)^4333 := by
      have hnat : (25016234490685272297 : ℕ)^1024*80000000000000^4333 ≤ 80012274986923^4333*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016234490685272297 25000000000000000000 80012274986923 80000000000000 1024 4333 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (80012274986923/80000000000000 : ℝ)) (X := (25016234490685272297/25000000000000000000 : ℝ)) (by norm_num) 4333 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8723604612399543/100000000000000000000 : ℝ) ≤ ((2499332907423548093/2500000000000000000 : ℝ)+2*(140259767427/100000000000000 : ℝ)*(5491/50000 : ℝ))^(4333/1024 : ℝ) := by
    rw [show (2499332907423548093/2500000000000000000 : ℝ)+2*(140259767427/100000000000000 : ℝ)*(5491/50000 : ℝ)=(10000412295225959/10000000000000000 : ℝ) by norm_num, show 1+2*(8723604612399543/100000000000000000000 : ℝ)=(50008723604612399543/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16234490685272297/50000000000000000000 : ℝ)+(8723604612399543/100000000000000000000 : ℝ) ≤ ((2499332907423548093/2500000000000000000 : ℝ)+(140259767427/100000000000000 : ℝ)*((7491/50000 : ℝ)+(5491/50000 : ℝ)))^(4333/1024 : ℝ) := by
    rw [show (2499332907423548093/2500000000000000000 : ℝ)+(140259767427/100000000000000 : ℝ)*((7491/50000 : ℝ)+(5491/50000 : ℝ))=(10000973334295667/10000000000000000 : ℝ) by norm_num, show 1+(16234490685272297/50000000000000000000 : ℝ)+(8723604612399543/100000000000000000000 : ℝ)=(100041192585982944137/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16234490685272297/50000000000000000000 : ℝ) ≤ ((2499332907423548093/2500000000000000000 : ℝ)+2*(140259767427/100000000000000 : ℝ)*(7491/50000 : ℝ))^(4333/1024 : ℝ) := by
    rw [show (2499332907423548093/2500000000000000000 : ℝ)+2*(140259767427/100000000000000 : ℝ)*(7491/50000 : ℝ)=(80012274986923/80000000000000 : ℝ) by norm_num, show 1+2*(16234490685272297/50000000000000000000 : ℝ)=(25016234490685272297/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2499332907423548093/2500000000000000000 : ℝ)*(X 1 0+X 2 0)+(140259767427/100000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4333/1024 : ℝ)) (lo := (5491/50000 : ℝ)) (hi := (7491/50000 : ℝ)) (c := (2499332907423548093/2500000000000000000 : ℝ)) (alpha := (140259767427/100000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2499332907423548093/2500000000000000000 : ℝ)*(X 0 1+X 2 1)+(140259767427/100000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4333/1024 : ℝ)) (lo := (5491/50000 : ℝ)) (hi := (7491/50000 : ℝ)) (c := (2499332907423548093/2500000000000000000 : ℝ)) (alpha := (140259767427/100000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2499332907423548093/2500000000000000000 : ℝ)*(X 0 2+X 1 2)+(140259767427/100000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4333/1024 : ℝ)) (lo := (5491/50000 : ℝ)) (hi := (7491/50000 : ℝ)) (c := (2499332907423548093/2500000000000000000 : ℝ)) (alpha := (140259767427/100000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2016409787/10000000000 : ℝ)*X 0 0+(5413097173/10000000000 : ℝ)*X 0 1+(5243652989/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348946641/10000000000 : ℝ)*X 1 0+(-525688777/2500000000 : ℝ)*X 1 1+(5243652931/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674473311/5000000000 : ℝ)*X 2 0+(1310913259/2500000000 : ℝ)*X 2 1+(-1051377497/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((107954511/250000000 : ℝ)*X 0 0+(2071013049/5000000000 : ℝ)*X 0 1+(4501216763/10000000000 : ℝ)*X 0 2+(107954511/250000000 : ℝ)*X 1 0+(2071013049/5000000000 : ℝ)*X 1 1+(4501216763/10000000000 : ℝ)*X 1 2+(107954511/250000000 : ℝ)*X 2 0+(2071013049/5000000000 : ℝ)*X 2 1+(4501216763/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-100821149/500000000 : ℝ)*X 0 0+(524427553/1000000000 : ℝ)*X 0 1+(1082494197/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652572617/5000000000 : ℝ)*X 1 0+(-1933936797/10000000000 : ℝ)*X 1 1+(2706235557/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652572743/5000000000 : ℝ)*X 2 0+(270623549/500000000 : ℝ)*X 2 1+(-1933936637/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((53977587/125000000 : ℝ)*X 0 0+(2249948733/5000000000 : ℝ)*X 0 1+(4143352787/10000000000 : ℝ)*X 0 2+(53977587/125000000 : ℝ)*X 1 0+(2249948733/5000000000 : ℝ)*X 1 1+(4143352787/10000000000 : ℝ)*X 1 2+(53977587/125000000 : ℝ)*X 2 0+(2249948733/5000000000 : ℝ)*X 2 1+(4143352787/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14786755258250429284689/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14683359/1250000000000 : ℝ)*(base19) + (5448021/500000000000 : ℝ)*(base23) + (34287333/100000000000000 : ℝ)*(lower2) + (16271493/25000000000000 : ℝ)*(upper3) + (30581943/20000000000000 : ℝ)*(upper5) + (2171439511973369/50000000000000 : ℝ)*(major0) + (2171439511973369/50000000000000 : ℝ)*(major1) + (2171439511973369/50000000000000 : ℝ)*(major2) + (5901671513714343/100000000000000 : ℝ)*(sp0) + (1475424387907371/25000000000000 : ℝ)*(sp1) + (1475424409173501/25000000000000 : ℝ)*(sp2) + (1392024208290121/50000000000000 : ℝ)*(sp3) + (13606291931/50000000000000 : ℝ)*(sp4) + (10707858287/100000000000000 : ℝ)*(sp7) + (278405912443853/10000000000000 : ℝ)*(f.failure) + (1475424681574551/25000000000000 : ℝ)*(f.sum) + (1508543095937/2500000000000000000000000000 : ℝ)*base66 + (16604411729189683/125000000000000000000000000000000 : ℝ)*base68 + (54948431104189683/125000000000000000000000000000000 : ℝ)*base70 + (562129610104189683/125000000000000000000000000000000 : ℝ)*base72 + (10544877186563/2500000000000000000000000000 : ℝ)*base73 + (134520030520810317/125000000000000000000000000000000 : ℝ)*base75 + (259733984395810317/125000000000000000000000000000000 : ℝ)*base77 + (896489720145810317/125000000000000000000000000000000 : ℝ)*base79 + (2148833695937/2500000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (2231393/200000000000000000000 : ℝ)*base89 + (2231393/200000000000000000000 : ℝ)*base91 + (2231393/200000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (572700289418129695557358713/62500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2246651771/100000000000000 : ℝ)*(base19) + (3400787401/100000000000000 : ℝ)*(base23) + (174841803/50000000000000 : ℝ)*(upper2) + (14241747/4000000000000 : ℝ)*(upper3) + (4384343/2500000000000 : ℝ)*(upper5) + (2187537979631851/50000000000000 : ℝ)*(major0) + (2187537979631851/50000000000000 : ℝ)*(major1) + (2187537979631851/50000000000000 : ℝ)*(major2) + (22252065349/50000000000000 : ℝ)*(sp1) + (2195370803/3125000000000 : ℝ)*(sp2) + (5945452224194211/100000000000000 : ℝ)*(sp4) + (2972702736705871/50000000000000 : ℝ)*(sp5) + (5945378571541113/100000000000000 : ℝ)*(sp6) + (1402349694446513/50000000000000 : ℝ)*(sp7) + (1402349694446513/50000000000000 : ℝ)*(f.failure) + (5945452224194211/100000000000000 : ℝ)*(f.sum) + (11571111067377/2500000000000000000000000000 : ℝ)*base65 + (990963920017535143/125000000000000000000000000000000 : ℝ)*base67 + (703813626142535143/125000000000000000000000000000000 : ℝ)*base69 + (1304907037517535143/125000000000000000000000000000000 : ℝ)*base71 + (15540100622377/2500000000000000000000000000 : ℝ)*base73 + (361847552267535143/125000000000000000000000000000000 : ℝ)*base75 + (926254314517535143/125000000000000000000000000000000 : ℝ)*base77 + (394826799267535143/125000000000000000000000000000000 : ℝ)*base79 + (12738789874877/2500000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (12607147/1000000000000000000000 : ℝ)*base90 + (12607147/1000000000000000000000 : ℝ)*base92 + (12607147/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1374_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31198181/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7491/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5491/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5591/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1477/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1374_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1374_s5_0 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2016608593/10000000000 : ℝ)*x 0 + (84552379/156250000 : ℝ)*x 1 + (40978649/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2016608593/10000000000 : ℝ)^2167 ≤ (3072101065119/25000000000000 : ℝ)^1655 := by
    have hnat : (2016608593 : ℕ)^2167*25000000000000^1655 ≤ 3072101065119^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2016608593 10000000000 3072101065119 25000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84552379/156250000 : ℝ)^2167 ≤ (5593837165449/12500000000000 : ℝ)^1655 := by
    have hnat : (84552379 : ℕ)^2167*12500000000000^1655 ≤ 5593837165449^1655*156250000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84552379 156250000 5593837165449 12500000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (40978649/78125000 : ℝ)^2167 ≤ (42960898398297/100000000000000 : ℝ)^1655 := by
    have hnat : (40978649 : ℕ)^2167*100000000000000^1655 ≤ 42960898398297^1655*78125000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40978649 78125000 42960898398297 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2016608593/10000000000 : ℝ), (84552379/156250000 : ℝ), (40978649/78125000 : ℝ)] ![(3072101065119/25000000000000 : ℝ), (5593837165449/12500000000000 : ℝ), (42960898398297/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2016608593/10000000000 : ℝ)|^2167 ≤ (3072101065119/25000000000000 : ℝ)^1655
        have hw : |(-2016608593/10000000000 : ℝ)|=(2016608593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(84552379/156250000 : ℝ)|^2167 ≤ (5593837165449/12500000000000 : ℝ)^1655
        have hw : |(84552379/156250000 : ℝ)|=(84552379/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(40978649/78125000 : ℝ)|^2167 ≤ (42960898398297/100000000000000 : ℝ)^1655
        have hw : |(40978649/78125000 : ℝ)|=(40978649/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_s5_1 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2674249549/5000000000 : ℝ)*x 0 + (-2101210829/10000000000 : ℝ)*x 1 + (1311316757/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674249549/5000000000 : ℝ)^2167 ≤ (44071338937213/100000000000000 : ℝ)^1655 := by
    have hnat : (2674249549 : ℕ)^2167*100000000000000^1655 ≤ 44071338937213^1655*5000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674249549 5000000000 44071338937213 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2101210829/10000000000 : ℝ)^2167 ≤ (3241940781097/25000000000000 : ℝ)^1655 := by
    have hnat : (2101210829 : ℕ)^2167*25000000000000^1655 ≤ 3241940781097^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2101210829 10000000000 3241940781097 25000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311316757/2500000000 : ℝ)^2167 ≤ (4296089792643/10000000000000 : ℝ)^1655 := by
    have hnat : (1311316757 : ℕ)^2167*10000000000000^1655 ≤ 4296089792643^1655*2500000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311316757 2500000000 4296089792643 10000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674249549/5000000000 : ℝ), (-2101210829/10000000000 : ℝ), (1311316757/2500000000 : ℝ)] ![(44071338937213/100000000000000 : ℝ), (3241940781097/25000000000000 : ℝ), (4296089792643/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674249549/5000000000 : ℝ)|^2167 ≤ (44071338937213/100000000000000 : ℝ)^1655
        have hw : |(2674249549/5000000000 : ℝ)|=(2674249549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2101210829/10000000000 : ℝ)|^2167 ≤ (3241940781097/25000000000000 : ℝ)^1655
        have hw : |(-2101210829/10000000000 : ℝ)|=(2101210829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311316757/2500000000 : ℝ)|^2167 ≤ (4296089792643/10000000000000 : ℝ)^1655
        have hw : |(1311316757/2500000000 : ℝ)|=(1311316757/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_s5_2 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5348499183/10000000000 : ℝ)*x 0 + (5245267059/10000000000 : ℝ)*x 1 + (-1050605337/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348499183/10000000000 : ℝ)^2167 ≤ (44071339854287/100000000000000 : ℝ)^1655 := by
    have hnat : (5348499183 : ℕ)^2167*100000000000000^1655 ≤ 44071339854287^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348499183 10000000000 44071339854287 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245267059/10000000000 : ℝ)^2167 ≤ (21480449129441/50000000000000 : ℝ)^1655 := by
    have hnat : (5245267059 : ℕ)^2167*50000000000000^1655 ≤ 21480449129441^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245267059 10000000000 21480449129441 50000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1050605337/5000000000 : ℝ)^2167 ≤ (6483880935929/50000000000000 : ℝ)^1655 := by
    have hnat : (1050605337 : ℕ)^2167*50000000000000^1655 ≤ 6483880935929^1655*5000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050605337 5000000000 6483880935929 50000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348499183/10000000000 : ℝ), (5245267059/10000000000 : ℝ), (-1050605337/5000000000 : ℝ)] ![(44071339854287/100000000000000 : ℝ), (21480449129441/50000000000000 : ℝ), (6483880935929/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348499183/10000000000 : ℝ)|^2167 ≤ (44071339854287/100000000000000 : ℝ)^1655
        have hw : |(5348499183/10000000000 : ℝ)|=(5348499183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245267059/10000000000 : ℝ)|^2167 ≤ (21480449129441/50000000000000 : ℝ)^1655
        have hw : |(5245267059/10000000000 : ℝ)|=(5245267059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1050605337/5000000000 : ℝ)|^2167 ≤ (6483880935929/50000000000000 : ℝ)^1655
        have hw : |(-1050605337/5000000000 : ℝ)|=(1050605337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_s5_3 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4318300411/10000000000 : ℝ)*x 0 + (64774563/156250000 : ℝ)*x 1 + (4497641557/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4318300411/10000000000 : ℝ)^2167 ≤ (3330360202249/10000000000000 : ℝ)^1655 := by
    have hnat : (4318300411 : ℕ)^2167*10000000000000^1655 ≤ 3330360202249^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4318300411 10000000000 3330360202249 10000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (64774563/156250000 : ℝ)^2167 ≤ (15785134056473/50000000000000 : ℝ)^1655 := by
    have hnat : (64774563 : ℕ)^2167*50000000000000^1655 ≤ 15785134056473^1655*156250000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64774563 156250000 15785134056473 50000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4497641557/10000000000 : ℝ)^2167 ≤ (35126129850219/100000000000000 : ℝ)^1655 := by
    have hnat : (4497641557 : ℕ)^2167*100000000000000^1655 ≤ 35126129850219^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4497641557 10000000000 35126129850219 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4318300411/10000000000 : ℝ), (64774563/156250000 : ℝ), (4497641557/10000000000 : ℝ)] ![(3330360202249/10000000000000 : ℝ), (15785134056473/50000000000000 : ℝ), (35126129850219/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4318300411/10000000000 : ℝ)|^2167 ≤ (3330360202249/10000000000000 : ℝ)^1655
        have hw : |(4318300411/10000000000 : ℝ)|=(4318300411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(64774563/156250000 : ℝ)|^2167 ≤ (15785134056473/50000000000000 : ℝ)^1655
        have hw : |(64774563/156250000 : ℝ)|=(64774563/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4497641557/10000000000 : ℝ)|^2167 ≤ (35126129850219/100000000000000 : ℝ)^1655
        have hw : |(4497641557/10000000000 : ℝ)|=(4497641557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_s5_4 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1008310317/5000000000 : ℝ)*x 0 + (1311466337/2500000000 : ℝ)*x 1 + (5410750829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1008310317/5000000000 : ℝ)^2167 ≤ (6144250166339/50000000000000 : ℝ)^1655 := by
    have hnat : (1008310317 : ℕ)^2167*50000000000000^1655 ≤ 6144250166339^1655*5000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1008310317 5000000000 6144250166339 50000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311466337/2500000000 : ℝ)^2167 ≤ (21483657284467/50000000000000 : ℝ)^1655 := by
    have hnat : (1311466337 : ℕ)^2167*50000000000000^1655 ≤ 21483657284467^1655*2500000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311466337 2500000000 21483657284467 50000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5410750829/10000000000 : ℝ)^2167 ≤ (8948837016803/20000000000000 : ℝ)^1655 := by
    have hnat : (5410750829 : ℕ)^2167*20000000000000^1655 ≤ 8948837016803^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410750829 10000000000 8948837016803 20000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1008310317/5000000000 : ℝ), (1311466337/2500000000 : ℝ), (5410750829/10000000000 : ℝ)] ![(6144250166339/50000000000000 : ℝ), (21483657284467/50000000000000 : ℝ), (8948837016803/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1008310317/5000000000 : ℝ)|^2167 ≤ (6144250166339/50000000000000 : ℝ)^1655
        have hw : |(-1008310317/5000000000 : ℝ)|=(1008310317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311466337/2500000000 : ℝ)|^2167 ≤ (21483657284467/50000000000000 : ℝ)^1655
        have hw : |(1311466337/2500000000 : ℝ)|=(1311466337/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5410750829/10000000000 : ℝ)|^2167 ≤ (8948837016803/20000000000000 : ℝ)^1655
        have hw : |(5410750829/10000000000 : ℝ)|=(5410750829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_s5_5 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305565761/10000000000 : ℝ)*x 0 + (-120982939/625000000 : ℝ)*x 1 + (338171927/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305565761/10000000000 : ℝ)^2167 ≤ (218043515391/500000000000 : ℝ)^1655 := by
    have hnat : (5305565761 : ℕ)^2167*500000000000^1655 ≤ 218043515391^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305565761 10000000000 218043515391 500000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (120982939/625000000 : ℝ)^2167 ≤ (116471117823/1000000000000 : ℝ)^1655 := by
    have hnat : (120982939 : ℕ)^2167*1000000000000^1655 ≤ 116471117823^1655*625000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      120982939 625000000 116471117823 1000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (338171927/625000000 : ℝ)^2167 ≤ (44744185116499/100000000000000 : ℝ)^1655 := by
    have hnat : (338171927 : ℕ)^2167*100000000000000^1655 ≤ 44744185116499^1655*625000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338171927 625000000 44744185116499 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305565761/10000000000 : ℝ), (-120982939/625000000 : ℝ), (338171927/625000000 : ℝ)] ![(218043515391/500000000000 : ℝ), (116471117823/1000000000000 : ℝ), (44744185116499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305565761/10000000000 : ℝ)|^2167 ≤ (218043515391/500000000000 : ℝ)^1655
        have hw : |(5305565761/10000000000 : ℝ)|=(5305565761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-120982939/625000000 : ℝ)|^2167 ≤ (116471117823/1000000000000 : ℝ)^1655
        have hw : |(-120982939/625000000 : ℝ)|=(120982939/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(338171927/625000000 : ℝ)|^2167 ≤ (44744185116499/100000000000000 : ℝ)^1655
        have hw : |(338171927/625000000 : ℝ)|=(338171927/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_s5_6 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652782881/5000000000 : ℝ)*x 0 + (541075083/1000000000 : ℝ)*x 1 + (-1935727027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652782881/5000000000 : ℝ)^2167 ≤ (43608703088963/100000000000000 : ℝ)^1655 := by
    have hnat : (2652782881 : ℕ)^2167*100000000000000^1655 ≤ 43608703088963^1655*5000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652782881 5000000000 43608703088963 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (541075083/1000000000 : ℝ)^2167 ≤ (44744185094843/100000000000000 : ℝ)^1655 := by
    have hnat : (541075083 : ℕ)^2167*100000000000000^1655 ≤ 44744185094843^1655*1000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541075083 1000000000 44744185094843 100000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1935727027/10000000000 : ℝ)^2167 ≤ (2329422361187/20000000000000 : ℝ)^1655 := by
    have hnat : (1935727027 : ℕ)^2167*20000000000000^1655 ≤ 2329422361187^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1935727027 10000000000 2329422361187 20000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652782881/5000000000 : ℝ), (541075083/1000000000 : ℝ), (-1935727027/10000000000 : ℝ)] ![(43608703088963/100000000000000 : ℝ), (44744185094843/100000000000000 : ℝ), (2329422361187/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652782881/5000000000 : ℝ)|^2167 ≤ (43608703088963/100000000000000 : ℝ)^1655
        have hw : |(2652782881/5000000000 : ℝ)|=(2652782881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(541075083/1000000000 : ℝ)|^2167 ≤ (44744185094843/100000000000000 : ℝ)^1655
        have hw : |(541075083/1000000000 : ℝ)|=(541075083/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1935727027/10000000000 : ℝ)|^2167 ≤ (2329422361187/20000000000000 : ℝ)^1655
        have hw : |(-1935727027/10000000000 : ℝ)|=(1935727027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1374_s5_7 (p : ℝ) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ)) (x : Fin 3 → ℝ) :
    (539790757/1250000000 : ℝ)*x 0 + (1124093389/2500000000 : ℝ)*x 1 + (4146846327/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (539790757/1250000000 : ℝ)^2167 ≤ (16651930494133/50000000000000 : ℝ)^1655 := by
    have hnat : (539790757 : ℕ)^2167*50000000000000^1655 ≤ 16651930494133^1655*1250000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539790757 1250000000 16651930494133 50000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1124093389/2500000000 : ℝ)^2167 ≤ (8778290954997/25000000000000 : ℝ)^1655 := by
    have hnat : (1124093389 : ℕ)^2167*25000000000000^1655 ≤ 8778290954997^1655*2500000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124093389 2500000000 8778290954997 25000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4146846327/10000000000 : ℝ)^2167 ≤ (15791487590333/50000000000000 : ℝ)^1655 := by
    have hnat : (4146846327 : ℕ)^2167*50000000000000^1655 ≤ 15791487590333^1655*10000000000^2167 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4146846327 10000000000 15791487590333 50000000000000 2167 1655 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2167/512 : ℝ)) 2167 1655 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(539790757/1250000000 : ℝ), (1124093389/2500000000 : ℝ), (4146846327/10000000000 : ℝ)] ![(16651930494133/50000000000000 : ℝ), (8778290954997/25000000000000 : ℝ), (15791487590333/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(539790757/1250000000 : ℝ)|^2167 ≤ (16651930494133/50000000000000 : ℝ)^1655
        have hw : |(539790757/1250000000 : ℝ)|=(539790757/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1124093389/2500000000 : ℝ)|^2167 ≤ (8778290954997/25000000000000 : ℝ)^1655
        have hw : |(1124093389/2500000000 : ℝ)|=(1124093389/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4146846327/10000000000 : ℝ)|^2167 ≤ (15791487590333/50000000000000 : ℝ)^1655
        have hw : |(4146846327/10000000000 : ℝ)|=(4146846327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1374_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31198181/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1477/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5591/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (701/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14733/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1477/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5591/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1477/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5591/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1477/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5591/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1477/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5591/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1477/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5591/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1477/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5591/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5591/50000 : ℝ) ^ (4333/1024 : ℝ) ≤ (2353977220818291/25000000000000000000 : ℝ) := by
    have hpowers : (5591/50000 : ℝ)^4333 ≤ (2353977220818291/25000000000000000000 : ℝ)^1024 := by
      have hnat : (5591 : ℕ)^4333*25000000000000000000^1024 ≤ 2353977220818291^1024*50000^4333 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5591 50000 2353977220818291 25000000000000000000 4333 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5591/50000 : ℝ)) (X := (2353977220818291/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4333 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1477/10000 : ℝ) ^ (4333/1024 : ℝ) ≤ (15284421112496367/50000000000000000000 : ℝ) := by
    have hpowers : (1477/10000 : ℝ)^4333 ≤ (15284421112496367/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1477 : ℕ)^4333*50000000000000000000^1024 ≤ 15284421112496367^1024*10000^4333 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1477 10000 15284421112496367 50000000000000000000 4333 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1477/10000 : ℝ)) (X := (15284421112496367/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4333 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502353977220818291/12500000000000000000 : ℝ) ≤ (500022250628791/500000000000000 : ℝ) ^ (4333/1024 : ℝ) := by
    have hpowers : (12502353977220818291/12500000000000000000 : ℝ)^1024 ≤ (500022250628791/500000000000000 : ℝ)^4333 := by
      have hnat : (12502353977220818291 : ℕ)^1024*500000000000000^4333 ≤ 500022250628791^4333*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502353977220818291 12500000000000000000 500022250628791 500000000000000 1024 4333 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500022250628791/500000000000000 : ℝ)) (X := (12502353977220818291/12500000000000000000 : ℝ)) (by norm_num) 4333 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50019992375554132949/50000000000000000000 : ℝ) ≤ (2500236199719331/2500000000000000 : ℝ) ^ (4333/1024 : ℝ) := by
    have hpowers : (50019992375554132949/50000000000000000000 : ℝ)^1024 ≤ (2500236199719331/2500000000000000 : ℝ)^4333 := by
      have hnat : (50019992375554132949 : ℕ)^1024*2500000000000000^4333 ≤ 2500236199719331^4333*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50019992375554132949 50000000000000000000 2500236199719331 2500000000000000 1024 4333 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500236199719331/2500000000000000 : ℝ)) (X := (50019992375554132949/50000000000000000000 : ℝ)) (by norm_num) 4333 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015284421112496367/25000000000000000000 : ℝ) ≤ (2500361146294707/2500000000000000 : ℝ) ^ (4333/1024 : ℝ) := by
    have hpowers : (25015284421112496367/25000000000000000000 : ℝ)^1024 ≤ (2500361146294707/2500000000000000 : ℝ)^4333 := by
      have hnat : (25015284421112496367 : ℕ)^1024*2500000000000000^4333 ≤ 2500361146294707^4333*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015284421112496367 25000000000000000000 2500361146294707 2500000000000000 1024 4333 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500361146294707/2500000000000000 : ℝ)) (X := (25015284421112496367/25000000000000000000 : ℝ)) (by norm_num) 4333 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2353977220818291/25000000000000000000 : ℝ) ≤ ((2241901217767200419/2242500000000000000 : ℝ)+2*(7809160961/5606250000000 : ℝ)*(5591/50000 : ℝ))^(4333/1024 : ℝ) := by
    rw [show (2241901217767200419/2242500000000000000 : ℝ)+2*(7809160961/5606250000000 : ℝ)*(5591/50000 : ℝ)=(500022250628791/500000000000000 : ℝ) by norm_num, show 1+2*(2353977220818291/25000000000000000000 : ℝ)=(12502353977220818291/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15284421112496367/50000000000000000000 : ℝ)+(2353977220818291/25000000000000000000 : ℝ) ≤ ((2241901217767200419/2242500000000000000 : ℝ)+(7809160961/5606250000000 : ℝ)*((1477/10000 : ℝ)+(5591/50000 : ℝ)))^(4333/1024 : ℝ) := by
    rw [show (2241901217767200419/2242500000000000000 : ℝ)+(7809160961/5606250000000 : ℝ)*((1477/10000 : ℝ)+(5591/50000 : ℝ))=(2500236199719331/2500000000000000 : ℝ) by norm_num, show 1+(15284421112496367/50000000000000000000 : ℝ)+(2353977220818291/25000000000000000000 : ℝ)=(50019992375554132949/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15284421112496367/50000000000000000000 : ℝ) ≤ ((2241901217767200419/2242500000000000000 : ℝ)+2*(7809160961/5606250000000 : ℝ)*(1477/10000 : ℝ))^(4333/1024 : ℝ) := by
    rw [show (2241901217767200419/2242500000000000000 : ℝ)+2*(7809160961/5606250000000 : ℝ)*(1477/10000 : ℝ)=(2500361146294707/2500000000000000 : ℝ) by norm_num, show 1+2*(15284421112496367/50000000000000000000 : ℝ)=(25015284421112496367/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2241901217767200419/2242500000000000000 : ℝ)*(X 1 0+X 2 0)+(7809160961/5606250000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4333/1024 : ℝ)) (lo := (5591/50000 : ℝ)) (hi := (1477/10000 : ℝ)) (c := (2241901217767200419/2242500000000000000 : ℝ)) (alpha := (7809160961/5606250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2241901217767200419/2242500000000000000 : ℝ)*(X 0 1+X 2 1)+(7809160961/5606250000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4333/1024 : ℝ)) (lo := (5591/50000 : ℝ)) (hi := (1477/10000 : ℝ)) (c := (2241901217767200419/2242500000000000000 : ℝ)) (alpha := (7809160961/5606250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2241901217767200419/2242500000000000000 : ℝ)*(X 0 2+X 1 2)+(7809160961/5606250000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4333/1024 : ℝ)) (lo := (5591/50000 : ℝ)) (hi := (1477/10000 : ℝ)) (c := (2241901217767200419/2242500000000000000 : ℝ)) (alpha := (7809160961/5606250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2016608593/10000000000 : ℝ)*X 0 0+(84552379/156250000 : ℝ)*X 0 1+(40978649/78125000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674249549/5000000000 : ℝ)*X 1 0+(-2101210829/10000000000 : ℝ)*X 1 1+(1311316757/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348499183/10000000000 : ℝ)*X 2 0+(5245267059/10000000000 : ℝ)*X 2 1+(-1050605337/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4318300411/10000000000 : ℝ)*X 0 0+(64774563/156250000 : ℝ)*X 0 1+(4497641557/10000000000 : ℝ)*X 0 2+(4318300411/10000000000 : ℝ)*X 1 0+(64774563/156250000 : ℝ)*X 1 1+(4497641557/10000000000 : ℝ)*X 1 2+(4318300411/10000000000 : ℝ)*X 2 0+(64774563/156250000 : ℝ)*X 2 1+(4497641557/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1008310317/5000000000 : ℝ)*X 0 0+(1311466337/2500000000 : ℝ)*X 0 1+(5410750829/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305565761/10000000000 : ℝ)*X 1 0+(-120982939/625000000 : ℝ)*X 1 1+(338171927/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652782881/5000000000 : ℝ)*X 2 0+(541075083/1000000000 : ℝ)*X 2 1+(-1935727027/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((539790757/1250000000 : ℝ)*X 0 0+(1124093389/2500000000 : ℝ)*X 0 1+(4146846327/10000000000 : ℝ)*X 0 2+(539790757/1250000000 : ℝ)*X 1 0+(1124093389/2500000000 : ℝ)*X 1 1+(4146846327/10000000000 : ℝ)*X 1 2+(539790757/1250000000 : ℝ)*X 2 0+(1124093389/2500000000 : ℝ)*X 2 1+(4146846327/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1374_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (100728342701506937864510967/9343750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1798623423/100000000000000 : ℝ)*(base19) + (913864359/50000000000000 : ℝ)*(base23) + (17806139/50000000000000 : ℝ)*(lower2) + (4972103/6250000000000 : ℝ)*(upper3) + (239038357/100000000000000 : ℝ)*(upper5) + (4430734952192457/100000000000000 : ℝ)*(major0) + (4430734952192457/100000000000000 : ℝ)*(major1) + (2215367476096229/50000000000000 : ℝ)*(major2) + (24084175855687/400000000000 : ℝ)*(sp0) + (1204217487132187/20000000000000 : ℝ)*(sp1) + (150527185163891/2500000000000 : ℝ)*(sp2) + (1420182496844491/50000000000000 : ℝ)*(sp3) + (45270362607/100000000000000 : ℝ)*(sp4) + (15317068533/100000000000000 : ℝ)*(sp7) + (1420190155378757/50000000000000 : ℝ)*(f.failure) + (6021089234284357/100000000000000 : ℝ)*(f.sum) + (551298507991/89700000000000000000000000 : ℝ)*base66 + (1644690460709760517/224250000000000000000000000000000 : ℝ)*base68 + (1158848613365980049/112125000000000000000000000000000 : ℝ)*base70 + (3943977080105760517/224250000000000000000000000000000 : ℝ)*base72 + (9253040281/35880000000000000000000000 : ℝ)*base74 + (2002890179287105049/112125000000000000000000000000000 : ℝ)*base76 + (132848267964683603/5750000000000000000000000000000 : ℝ)*base78 + (118246246246183603/5750000000000000000000000000000 : ℝ)*base80 + (9674249885031/1495000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (14441017/1000000000000000000000 : ℝ)*base89 + (14441017/1000000000000000000000 : ℝ)*base91 + (4441017/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2740524350851243628612469/406250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (232952121/20000000000000 : ℝ)*(base19) + (1259390051/100000000000000 : ℝ)*(base23) + (138792381/100000000000000 : ℝ)*(upper3) + (2665651/6250000000000 : ℝ)*(lower4) + (69615711/50000000000000 : ℝ)*(upper5) + (2231455453634873/50000000000000 : ℝ)*(major0) + (2231455453634873/50000000000000 : ℝ)*(major1) + (2231455453634873/50000000000000 : ℝ)*(major2) + (24024389007/100000000000000 : ℝ)*(sp1) + (12821491313/50000000000000 : ℝ)*(sp2) + (6064814464119657/100000000000000 : ℝ)*(sp4) + (1212957854994009/20000000000000 : ℝ)*(sp5) + (6064787561746981/100000000000000 : ℝ)*(sp6) + (715251781389073/25000000000000 : ℝ)*(sp7) + (715251781389073/25000000000000 : ℝ)*(f.failure) + (6064814464119657/100000000000000 : ℝ)*(f.sum) + (176801688289/97500000000000000000000000 : ℝ)*base66 + (294484768677887/375000000000000000000000000000 : ℝ)*base68 + (1297206699552887/375000000000000000000000000000 : ℝ)*base70 + (1737645754302887/375000000000000000000000000000 : ℝ)*base72 + (1140658290697/195000000000000000000000000 : ℝ)*base73 + (2770177181822113/375000000000000000000000000000 : ℝ)*base75 + (5169426060177887/375000000000000000000000000000 : ℝ)*base78 + (3437328091677887/375000000000000000000000000000 : ℝ)*base80 + (1280556632917/195000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (876213/500000000000000000000 : ℝ)*base89 + (876213/500000000000000000000 : ℝ)*base91 + (876213/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1374_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31198181/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1477/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5591/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (701/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14733/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1374_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1374_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31198181/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15983/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5027/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (701/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14733/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1374_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1374_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1374_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4333/1024 : ℝ) ≤ p) (hpb : p ≤ (2167/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31198181/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15983/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5027/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (701/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14733/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1374_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
