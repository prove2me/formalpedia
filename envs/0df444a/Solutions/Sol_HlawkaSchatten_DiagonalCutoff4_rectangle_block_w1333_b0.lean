-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1333_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:02:35.277377+00:00
-- url     : https://prove2.me/submissions/55deab8f-e06f-45aa-a6ac-1b46f6d1a6c2

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
theorem support_rectangle_w1333_s0_0 (p : ℝ) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-907239359/5000000000 : ℝ)*x 0 + (600081297/1000000000 : ℝ)*x 1 + (4808757143/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (907239359/5000000000 : ℝ)^4293 ≤ (10630633260111/100000000000000 : ℝ)^3269 := by
    have hnat : (907239359 : ℕ)^4293*100000000000000^3269 ≤ 10630633260111^3269*5000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      907239359 5000000000 10630633260111 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (600081297/1000000000 : ℝ)^4293 ≤ (25568507232063/50000000000000 : ℝ)^3269 := by
    have hnat : (600081297 : ℕ)^4293*50000000000000^3269 ≤ 25568507232063^3269*1000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      600081297 1000000000 25568507232063 50000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4808757143/10000000000 : ℝ)^4293 ≤ (38232352262189/100000000000000 : ℝ)^3269 := by
    have hnat : (4808757143 : ℕ)^4293*100000000000000^3269 ≤ 38232352262189^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4808757143 10000000000 38232352262189 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4293/1024 : ℝ)) 4293 3269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-907239359/5000000000 : ℝ), (600081297/1000000000 : ℝ), (4808757143/10000000000 : ℝ)] ![(10630633260111/100000000000000 : ℝ), (25568507232063/50000000000000 : ℝ), (38232352262189/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-907239359/5000000000 : ℝ)|^4293 ≤ (10630633260111/100000000000000 : ℝ)^3269
        have hw : |(-907239359/5000000000 : ℝ)|=(907239359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(600081297/1000000000 : ℝ)|^4293 ≤ (25568507232063/50000000000000 : ℝ)^3269
        have hw : |(600081297/1000000000 : ℝ)|=(600081297/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4808757143/10000000000 : ℝ)|^4293 ≤ (38232352262189/100000000000000 : ℝ)^3269
        have hw : |(4808757143/10000000000 : ℝ)|=(4808757143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1333_s0_1 (p : ℝ) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1100564167/2000000000 : ℝ)*x 0 + (-2492482173/10000000000 : ℝ)*x 1 + (601094687/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1100564167/2000000000 : ℝ)^4293 ≤ (45637817975009/100000000000000 : ℝ)^3269 := by
    have hnat : (1100564167 : ℕ)^4293*100000000000000^3269 ≤ 45637817975009^3269*2000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100564167 2000000000 45637817975009 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2492482173/10000000000 : ℝ)^4293 ≤ (16129826056177/100000000000000 : ℝ)^3269 := by
    have hnat : (2492482173 : ℕ)^4293*100000000000000^3269 ≤ 16129826056177^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2492482173 10000000000 16129826056177 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (601094687/1250000000 : ℝ)^4293 ≤ (38232355947879/100000000000000 : ℝ)^3269 := by
    have hnat : (601094687 : ℕ)^4293*100000000000000^3269 ≤ 38232355947879^3269*1250000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      601094687 1250000000 38232355947879 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4293/1024 : ℝ)) 4293 3269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1100564167/2000000000 : ℝ), (-2492482173/10000000000 : ℝ), (601094687/1250000000 : ℝ)] ![(45637817975009/100000000000000 : ℝ), (16129826056177/100000000000000 : ℝ), (38232355947879/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1100564167/2000000000 : ℝ)|^4293 ≤ (45637817975009/100000000000000 : ℝ)^3269
        have hw : |(1100564167/2000000000 : ℝ)|=(1100564167/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2492482173/10000000000 : ℝ)|^4293 ≤ (16129826056177/100000000000000 : ℝ)^3269
        have hw : |(-2492482173/10000000000 : ℝ)|=(2492482173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(601094687/1250000000 : ℝ)|^4293 ≤ (38232355947879/100000000000000 : ℝ)^3269
        have hw : |(601094687/1250000000 : ℝ)|=(601094687/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1333_s0_2 (p : ℝ) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2751410183/5000000000 : ℝ)*x 0 + (4808757513/10000000000 : ℝ)*x 1 + (-1246241377/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2751410183/5000000000 : ℝ)^4293 ≤ (22818906433461/50000000000000 : ℝ)^3269 := by
    have hnat : (2751410183 : ℕ)^4293*50000000000000^3269 ≤ 22818906433461^3269*5000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2751410183 5000000000 22818906433461 50000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4808757513/10000000000 : ℝ)^4293 ≤ (38232356125377/100000000000000 : ℝ)^3269 := by
    have hnat : (4808757513 : ℕ)^4293*100000000000000^3269 ≤ 38232356125377^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4808757513 10000000000 38232356125377 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1246241377/5000000000 : ℝ)^4293 ≤ (16129830993821/100000000000000 : ℝ)^3269 := by
    have hnat : (1246241377 : ℕ)^4293*100000000000000^3269 ≤ 16129830993821^3269*5000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1246241377 5000000000 16129830993821 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4293/1024 : ℝ)) 4293 3269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2751410183/5000000000 : ℝ), (4808757513/10000000000 : ℝ), (-1246241377/5000000000 : ℝ)] ![(22818906433461/50000000000000 : ℝ), (38232356125377/100000000000000 : ℝ), (16129830993821/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2751410183/5000000000 : ℝ)|^4293 ≤ (22818906433461/50000000000000 : ℝ)^3269
        have hw : |(2751410183/5000000000 : ℝ)|=(2751410183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4808757513/10000000000 : ℝ)|^4293 ≤ (38232356125377/100000000000000 : ℝ)^3269
        have hw : |(4808757513/10000000000 : ℝ)|=(4808757513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1246241377/5000000000 : ℝ)|^4293 ≤ (16129830993821/100000000000000 : ℝ)^3269
        have hw : |(-1246241377/5000000000 : ℝ)|=(1246241377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1333_s0_3 (p : ℝ) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (418009711/1000000000 : ℝ)*x 0 + (3107024187/10000000000 : ℝ)*x 1 + (699427259/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (418009711/1000000000 : ℝ)^4293 ≤ (31807142405973/100000000000000 : ℝ)^3269 := by
    have hnat : (418009711 : ℕ)^4293*100000000000000^3269 ≤ 31807142405973^3269*1000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      418009711 1000000000 31807142405973 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3107024187/10000000000 : ℝ)^4293 ≤ (21543874159853/100000000000000 : ℝ)^3269 := by
    have hnat : (3107024187 : ℕ)^4293*100000000000000^3269 ≤ 21543874159853^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3107024187 10000000000 21543874159853 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (699427259/1250000000 : ℝ)^4293 ≤ (23324491707859/50000000000000 : ℝ)^3269 := by
    have hnat : (699427259 : ℕ)^4293*50000000000000^3269 ≤ 23324491707859^3269*1250000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      699427259 1250000000 23324491707859 50000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4293/1024 : ℝ)) 4293 3269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(418009711/1000000000 : ℝ), (3107024187/10000000000 : ℝ), (699427259/1250000000 : ℝ)] ![(31807142405973/100000000000000 : ℝ), (21543874159853/100000000000000 : ℝ), (23324491707859/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(418009711/1000000000 : ℝ)|^4293 ≤ (31807142405973/100000000000000 : ℝ)^3269
        have hw : |(418009711/1000000000 : ℝ)|=(418009711/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3107024187/10000000000 : ℝ)|^4293 ≤ (21543874159853/100000000000000 : ℝ)^3269
        have hw : |(3107024187/10000000000 : ℝ)|=(3107024187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(699427259/1250000000 : ℝ)|^4293 ≤ (23324491707859/50000000000000 : ℝ)^3269
        have hw : |(699427259/1250000000 : ℝ)|=(699427259/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1333_s0_4 (p : ℝ) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-56843213/312500000 : ℝ)*x 0 + (4839453871/10000000000 : ℝ)*x 1 + (5969020657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (56843213/312500000 : ℝ)^4293 ≤ (10665301338953/100000000000000 : ℝ)^3269 := by
    have hnat : (56843213 : ℕ)^4293*100000000000000^3269 ≤ 10665301338953^3269*312500000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56843213 312500000 10665301338953 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4839453871/10000000000 : ℝ)^4293 ≤ (38553178285479/100000000000000 : ℝ)^3269 := by
    have hnat : (4839453871 : ℕ)^4293*100000000000000^3269 ≤ 38553178285479^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4839453871 10000000000 38553178285479 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5969020657/10000000000 : ℝ)^4293 ≤ (25390760176481/50000000000000 : ℝ)^3269 := by
    have hnat : (5969020657 : ℕ)^4293*50000000000000^3269 ≤ 25390760176481^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5969020657 10000000000 25390760176481 50000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4293/1024 : ℝ)) 4293 3269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-56843213/312500000 : ℝ), (4839453871/10000000000 : ℝ), (5969020657/10000000000 : ℝ)] ![(10665301338953/100000000000000 : ℝ), (38553178285479/100000000000000 : ℝ), (25390760176481/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-56843213/312500000 : ℝ)|^4293 ≤ (10665301338953/100000000000000 : ℝ)^3269
        have hw : |(-56843213/312500000 : ℝ)|=(56843213/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4839453871/10000000000 : ℝ)|^4293 ≤ (38553178285479/100000000000000 : ℝ)^3269
        have hw : |(4839453871/10000000000 : ℝ)|=(4839453871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5969020657/10000000000 : ℝ)|^4293 ≤ (25390760176481/50000000000000 : ℝ)^3269
        have hw : |(5969020657/10000000000 : ℝ)|=(5969020657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1333_s0_5 (p : ℝ) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1294501373/2500000000 : ℝ)*x 0 + (-1332220349/10000000000 : ℝ)*x 1 + (746127477/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1294501373/2500000000 : ℝ)^4293 ≤ (526665864759/1250000000000 : ℝ)^3269 := by
    have hnat : (1294501373 : ℕ)^4293*1250000000000^3269 ≤ 526665864759^3269*2500000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294501373 2500000000 526665864759 1250000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1332220349/10000000000 : ℝ)^4293 ≤ (1417043970469/20000000000000 : ℝ)^3269 := by
    have hnat : (1332220349 : ℕ)^4293*20000000000000^3269 ≤ 1417043970469^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1332220349 10000000000 1417043970469 20000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (746127477/1250000000 : ℝ)^4293 ≤ (396730554351/781250000000 : ℝ)^3269 := by
    have hnat : (746127477 : ℕ)^4293*781250000000^3269 ≤ 396730554351^3269*1250000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      746127477 1250000000 396730554351 781250000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4293/1024 : ℝ)) 4293 3269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1294501373/2500000000 : ℝ), (-1332220349/10000000000 : ℝ), (746127477/1250000000 : ℝ)] ![(526665864759/1250000000000 : ℝ), (1417043970469/20000000000000 : ℝ), (396730554351/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1294501373/2500000000 : ℝ)|^4293 ≤ (526665864759/1250000000000 : ℝ)^3269
        have hw : |(1294501373/2500000000 : ℝ)|=(1294501373/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1332220349/10000000000 : ℝ)|^4293 ≤ (1417043970469/20000000000000 : ℝ)^3269
        have hw : |(-1332220349/10000000000 : ℝ)|=(1332220349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(746127477/1250000000 : ℝ)|^4293 ≤ (396730554351/781250000000 : ℝ)^3269
        have hw : |(746127477/1250000000 : ℝ)|=(746127477/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1333_s0_6 (p : ℝ) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2589002933/5000000000 : ℝ)*x 0 + (298451007/500000000 : ℝ)*x 1 + (-666109629/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2589002933/5000000000 : ℝ)^4293 ≤ (42133273177223/100000000000000 : ℝ)^3269 := by
    have hnat : (2589002933 : ℕ)^4293*100000000000000^3269 ≤ 42133273177223^3269*5000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2589002933 5000000000 42133273177223 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (298451007/500000000 : ℝ)^4293 ≤ (50781514576803/100000000000000 : ℝ)^3269 := by
    have hnat : (298451007 : ℕ)^4293*100000000000000^3269 ≤ 50781514576803^3269*500000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      298451007 500000000 50781514576803 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (666109629/5000000000 : ℝ)^4293 ≤ (7085212232469/100000000000000 : ℝ)^3269 := by
    have hnat : (666109629 : ℕ)^4293*100000000000000^3269 ≤ 7085212232469^3269*5000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      666109629 5000000000 7085212232469 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4293/1024 : ℝ)) 4293 3269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2589002933/5000000000 : ℝ), (298451007/500000000 : ℝ), (-666109629/5000000000 : ℝ)] ![(42133273177223/100000000000000 : ℝ), (50781514576803/100000000000000 : ℝ), (7085212232469/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2589002933/5000000000 : ℝ)|^4293 ≤ (42133273177223/100000000000000 : ℝ)^3269
        have hw : |(2589002933/5000000000 : ℝ)|=(2589002933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(298451007/500000000 : ℝ)|^4293 ≤ (50781514576803/100000000000000 : ℝ)^3269
        have hw : |(298451007/500000000 : ℝ)|=(298451007/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-666109629/5000000000 : ℝ)|^4293 ≤ (7085212232469/100000000000000 : ℝ)^3269
        have hw : |(-666109629/5000000000 : ℝ)|=(666109629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1333_s0_7 (p : ℝ) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4189497879/10000000000 : ℝ)*x 0 + (553133969/1000000000 : ℝ)*x 1 + (3173389359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4189497879/10000000000 : ℝ)^4293 ≤ (1595055742251/5000000000000 : ℝ)^3269 := by
    have hnat : (4189497879 : ℕ)^4293*5000000000000^3269 ≤ 1595055742251^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4189497879 10000000000 1595055742251 5000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (553133969/1000000000 : ℝ)^4293 ≤ (45948681318527/100000000000000 : ℝ)^3269 := by
    have hnat : (553133969 : ℕ)^4293*100000000000000^3269 ≤ 45948681318527^3269*1000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      553133969 1000000000 45948681318527 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3173389359/10000000000 : ℝ)^4293 ≤ (22150203824843/100000000000000 : ℝ)^3269 := by
    have hnat : (3173389359 : ℕ)^4293*100000000000000^3269 ≤ 22150203824843^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3173389359 10000000000 22150203824843 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4293/1024 : ℝ)) 4293 3269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4189497879/10000000000 : ℝ), (553133969/1000000000 : ℝ), (3173389359/10000000000 : ℝ)] ![(1595055742251/5000000000000 : ℝ), (45948681318527/100000000000000 : ℝ), (22150203824843/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4189497879/10000000000 : ℝ)|^4293 ≤ (1595055742251/5000000000000 : ℝ)^3269
        have hw : |(4189497879/10000000000 : ℝ)|=(4189497879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(553133969/1000000000 : ℝ)|^4293 ≤ (45948681318527/100000000000000 : ℝ)^3269
        have hw : |(553133969/1000000000 : ℝ)|=(553133969/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3173389359/10000000000 : ℝ)|^4293 ≤ (22150203824843/100000000000000 : ℝ)^3269
        have hw : |(3173389359/10000000000 : ℝ)|=(3173389359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1333_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77187049/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (673/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3367/12500 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (1073/256 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^1073 ≤ (0 : ℝ)^256 := by
      have hnat : (0 : ℕ)^1073*1^256 ≤ 0^256*1^1073 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 1073 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 1073 256 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (1073/256 : ℝ) ≤ (429637079923800851/20000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^1073 ≤ (429637079923800851/20000000000000000000 : ℝ)^256 := by
      have hnat : (2 : ℕ)^1073*20000000000000000000^256 ≤ 429637079923800851^256*5^1073 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 429637079923800851 20000000000000000000 1073 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (429637079923800851/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1073 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (1073/256 : ℝ) := by
    have hpowers : (1 : ℝ)^256 ≤ (1 : ℝ)^1073 := by
      have hnat : (1 : ℕ)^256*1^1073 ≤ 1^1073*1^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 256 1073 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 1073 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (20429637079923800851/20000000000000000000 : ℝ) ≤ (10050838193199837/10000000000000000 : ℝ) ^ (1073/256 : ℝ) := by
    have hpowers : (20429637079923800851/20000000000000000000 : ℝ)^256 ≤ (10050838193199837/10000000000000000 : ℝ)^1073 := by
      have hnat : (20429637079923800851 : ℕ)^256*10000000000000000^1073 ≤ 10050838193199837^1073*20000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20429637079923800851 20000000000000000000 10050838193199837 10000000000000000 256 1073 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10050838193199837/10000000000000000 : ℝ)) (X := (20429637079923800851/20000000000000000000 : ℝ)) (by norm_num) 1073 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (10429637079923800851/10000000000000000000 : ℝ) ≤ (5050838193199837/5000000000000000 : ℝ) ^ (1073/256 : ℝ) := by
    have hpowers : (10429637079923800851/10000000000000000000 : ℝ)^256 ≤ (5050838193199837/5000000000000000 : ℝ)^1073 := by
      have hnat : (10429637079923800851 : ℕ)^256*5000000000000000^1073 ≤ 5050838193199837^1073*10000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10429637079923800851 10000000000000000000 5050838193199837 5000000000000000 256 1073 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5050838193199837/5000000000000000 : ℝ)) (X := (10429637079923800851/10000000000000000000 : ℝ)) (by norm_num) 1073 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(50838193199837/4000000000000000 : ℝ)*(0 : ℝ))^(1073/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(50838193199837/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(429637079923800851/20000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(50838193199837/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(1073/256 : ℝ) := by
    rw [show (1 : ℝ)+(50838193199837/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10050838193199837/10000000000000000 : ℝ) by norm_num, show 1+(429637079923800851/20000000000000000000 : ℝ)+(0 : ℝ)=(20429637079923800851/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(429637079923800851/20000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(50838193199837/4000000000000000 : ℝ)*(2/5 : ℝ))^(1073/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(50838193199837/4000000000000000 : ℝ)*(2/5 : ℝ)=(5050838193199837/5000000000000000 : ℝ) by norm_num, show 1+2*(429637079923800851/20000000000000000000 : ℝ)=(10429637079923800851/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(50838193199837/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1073/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (50838193199837/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(50838193199837/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1073/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (50838193199837/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(50838193199837/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1073/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (50838193199837/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-907239359/5000000000 : ℝ)*X 0 0+(600081297/1000000000 : ℝ)*X 0 1+(4808757143/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1333_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1100564167/2000000000 : ℝ)*X 1 0+(-2492482173/10000000000 : ℝ)*X 1 1+(601094687/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1333_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2751410183/5000000000 : ℝ)*X 2 0+(4808757513/10000000000 : ℝ)*X 2 1+(-1246241377/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1333_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((418009711/1000000000 : ℝ)*X 0 0+(3107024187/10000000000 : ℝ)*X 0 1+(699427259/1250000000 : ℝ)*X 0 2+(418009711/1000000000 : ℝ)*X 1 0+(3107024187/10000000000 : ℝ)*X 1 1+(699427259/1250000000 : ℝ)*X 1 2+(418009711/1000000000 : ℝ)*X 2 0+(3107024187/10000000000 : ℝ)*X 2 1+(699427259/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1333_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-56843213/312500000 : ℝ)*X 0 0+(4839453871/10000000000 : ℝ)*X 0 1+(5969020657/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1333_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1294501373/2500000000 : ℝ)*X 1 0+(-1332220349/10000000000 : ℝ)*X 1 1+(746127477/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1333_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2589002933/5000000000 : ℝ)*X 2 0+(298451007/500000000 : ℝ)*X 2 1+(-666109629/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1333_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4189497879/10000000000 : ℝ)*X 0 0+(553133969/1000000000 : ℝ)*X 0 1+(3173389359/10000000000 : ℝ)*X 0 2+(4189497879/10000000000 : ℝ)*X 1 0+(553133969/1000000000 : ℝ)*X 1 1+(3173389359/10000000000 : ℝ)*X 1 2+(4189497879/10000000000 : ℝ)*X 2 0+(553133969/1000000000 : ℝ)*X 2 1+(3173389359/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1333_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (156821082314305013410251/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (113783557/100000000000000 : ℝ)*(base1) + (1901751273/100000000000000 : ℝ)*(base19) + (1830252881/100000000000000 : ℝ)*(base23) + (11683301/4000000000000 : ℝ)*(upper3) + (2433277/2000000000000 : ℝ)*(upper5) + (310192716187341/50000000000000 : ℝ)*(major0) + (310192716187341/50000000000000 : ℝ)*(major1) + (310192716187341/50000000000000 : ℝ)*(major2) + (838893488003999/100000000000000 : ℝ)*(sp0) + (419448623768589/50000000000000 : ℝ)*(sp1) + (83889731903557/10000000000000 : ℝ)*(sp2) + (25116762431101/6250000000000 : ℝ)*(sp3) + (5775068009/100000000000000 : ℝ)*(sp4) + (49084551/1562500000000 : ℝ)*(sp7) + (100467863523109/25000000000000 : ℝ)*(f.failure) + (209724787322113/25000000000000 : ℝ)*(f.sum) + (85807676336583/100000000000000000000000000000 : ℝ)*base66 + (728117701536583/200000000000000000000000000000 : ℝ)*base68 + (706087036936583/200000000000000000000000000000 : ℝ)*base70 + (343800946536583/200000000000000000000000000000 : ℝ)*base72 + (2778313136583/100000000000000000000000000000 : ℝ)*base74 + (105611059463417/200000000000000000000000000000 : ℝ)*base75 + (51583944536583/200000000000000000000000000000 : ℝ)*base78 + (147589209736583/200000000000000000000000000000 : ℝ)*base80 + (184950092136583/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (2015341/1250000000000000000000 : ℝ)*base89 + (2015341/1250000000000000000000 : ℝ)*base91 + (2015341/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (24526358386210614480327/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (157692663/12500000000000 : ℝ)*(base19) + (284785119/20000000000000 : ℝ)*(base23) + (10661137/20000000000000 : ℝ)*(base39) + (34955921/25000000000000 : ℝ)*(upper3) + (39657787/25000000000000 : ℝ)*(upper5) + (130939235498703/20000000000000 : ℝ)*(major0) + (130939235498703/20000000000000 : ℝ)*(major1) + (65469612418783/10000000000000 : ℝ)*(major2) + (317005693/12500000000000 : ℝ)*(sp1) + (1638213857/50000000000000 : ℝ)*(sp2) + (177058994066849/20000000000000 : ℝ)*(sp4) + (885291172747397/100000000000000 : ℝ)*(sp5) + (885290323286621/100000000000000 : ℝ)*(sp6) + (106024291959509/25000000000000 : ℝ)*(sp7) + (106024291959509/25000000000000 : ℝ)*(f.failure) + (88529502363993/10000000000000 : ℝ)*(f.sum) + (101704798068153/80000000000000000000000000000 : ℝ)*base65 + (292013601938371/40000000000000000000000000000 : ℝ)*base67 + (492179402191411/80000000000000000000000000000 : ℝ)*base69 + (167342483018371/40000000000000000000000000000 : ℝ)*base71 + (281225721988153/80000000000000000000000000000 : ℝ)*base73 + (399113977311411/80000000000000000000000000000 : ℝ)*base75 + (330298612991411/80000000000000000000000000000 : ℝ)*base77 + (317655148351411/80000000000000000000000000000 : ℝ)*base79 + (168157339311411/40000000000000000000000000000 : ℝ)*base81 + (10301059/1250000000000000000000 : ℝ)*base90 + (10301059/1250000000000000000000 : ℝ)*base92 + (10301059/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1333_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77187049/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (673/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3367/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1333_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1333_s1_0 (p : ℝ) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1000296847/5000000000 : ℝ)*x 0 + (2823099167/5000000000 : ℝ)*x 1 + (5044190569/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1000296847/5000000000 : ℝ)^4293 ≤ (12085092139527/100000000000000 : ℝ)^3269 := by
    have hnat : (1000296847 : ℕ)^4293*100000000000000^3269 ≤ 12085092139527^3269*5000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1000296847 5000000000 12085092139527 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2823099167/5000000000 : ℝ)^4293 ≤ (47205740999787/100000000000000 : ℝ)^3269 := by
    have hnat : (2823099167 : ℕ)^4293*100000000000000^3269 ≤ 47205740999787^3269*5000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2823099167 5000000000 47205740999787 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5044190569/10000000000 : ℝ)^4293 ≤ (20354583428427/50000000000000 : ℝ)^3269 := by
    have hnat : (5044190569 : ℕ)^4293*50000000000000^3269 ≤ 20354583428427^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5044190569 10000000000 20354583428427 50000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4293/1024 : ℝ)) 4293 3269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1000296847/5000000000 : ℝ), (2823099167/5000000000 : ℝ), (5044190569/10000000000 : ℝ)] ![(12085092139527/100000000000000 : ℝ), (47205740999787/100000000000000 : ℝ), (20354583428427/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1000296847/5000000000 : ℝ)|^4293 ≤ (12085092139527/100000000000000 : ℝ)^3269
        have hw : |(-1000296847/5000000000 : ℝ)|=(1000296847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2823099167/5000000000 : ℝ)|^4293 ≤ (47205740999787/100000000000000 : ℝ)^3269
        have hw : |(2823099167/5000000000 : ℝ)|=(2823099167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5044190569/10000000000 : ℝ)|^4293 ≤ (20354583428427/50000000000000 : ℝ)^3269
        have hw : |(5044190569/10000000000 : ℝ)|=(5044190569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1333_s1_1 (p : ℝ) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5406658349/10000000000 : ℝ)*x 0 + (-2322089059/10000000000 : ℝ)*x 1 + (5044190067/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5406658349/10000000000 : ℝ)^4293 ≤ (11148336945769/25000000000000 : ℝ)^3269 := by
    have hnat : (5406658349 : ℕ)^4293*25000000000000^3269 ≤ 11148336945769^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406658349 10000000000 11148336945769 25000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2322089059/10000000000 : ℝ)^4293 ≤ (7348745334453/50000000000000 : ℝ)^3269 := by
    have hnat : (2322089059 : ℕ)^4293*50000000000000^3269 ≤ 7348745334453^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2322089059 10000000000 7348745334453 50000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5044190067/10000000000 : ℝ)^4293 ≤ (40709161536379/100000000000000 : ℝ)^3269 := by
    have hnat : (5044190067 : ℕ)^4293*100000000000000^3269 ≤ 40709161536379^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5044190067 10000000000 40709161536379 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4293/1024 : ℝ)) 4293 3269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5406658349/10000000000 : ℝ), (-2322089059/10000000000 : ℝ), (5044190067/10000000000 : ℝ)] ![(11148336945769/25000000000000 : ℝ), (7348745334453/50000000000000 : ℝ), (40709161536379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5406658349/10000000000 : ℝ)|^4293 ≤ (11148336945769/25000000000000 : ℝ)^3269
        have hw : |(5406658349/10000000000 : ℝ)|=(5406658349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2322089059/10000000000 : ℝ)|^4293 ≤ (7348745334453/50000000000000 : ℝ)^3269
        have hw : |(-2322089059/10000000000 : ℝ)|=(2322089059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5044190067/10000000000 : ℝ)|^4293 ≤ (40709161536379/100000000000000 : ℝ)^3269
        have hw : |(5044190067/10000000000 : ℝ)|=(5044190067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1333_s1_2 (p : ℝ) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2703329103/5000000000 : ℝ)*x 0 + (5044189797/10000000000 : ℝ)*x 1 + (-2322089589/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2703329103/5000000000 : ℝ)^4293 ≤ (44593346234177/100000000000000 : ℝ)^3269 := by
    have hnat : (2703329103 : ℕ)^4293*100000000000000^3269 ≤ 44593346234177^3269*5000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703329103 5000000000 44593346234177 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5044189797/10000000000 : ℝ)^4293 ≤ (40709158674769/100000000000000 : ℝ)^3269 := by
    have hnat : (5044189797 : ℕ)^4293*100000000000000^3269 ≤ 40709158674769^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5044189797 10000000000 40709158674769 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2322089589/10000000000 : ℝ)^4293 ≤ (7348747537157/50000000000000 : ℝ)^3269 := by
    have hnat : (2322089589 : ℕ)^4293*50000000000000^3269 ≤ 7348747537157^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2322089589 10000000000 7348747537157 50000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4293/1024 : ℝ)) 4293 3269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2703329103/5000000000 : ℝ), (5044189797/10000000000 : ℝ), (-2322089589/10000000000 : ℝ)] ![(44593346234177/100000000000000 : ℝ), (40709158674769/100000000000000 : ℝ), (7348747537157/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2703329103/5000000000 : ℝ)|^4293 ≤ (44593346234177/100000000000000 : ℝ)^3269
        have hw : |(2703329103/5000000000 : ℝ)|=(2703329103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5044189797/10000000000 : ℝ)|^4293 ≤ (40709158674769/100000000000000 : ℝ)^3269
        have hw : |(5044189797/10000000000 : ℝ)|=(5044189797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2322089589/10000000000 : ℝ)|^4293 ≤ (7348747537157/50000000000000 : ℝ)^3269
        have hw : |(-2322089589/10000000000 : ℝ)|=(2322089589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1333_s1_3 (p : ℝ) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4293907811/10000000000 : ℝ)*x 0 + (74166809/200000000 : ℝ)*x 1 + (4965021951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4293907811/10000000000 : ℝ)^4293 ≤ (6589848425651/20000000000000 : ℝ)^3269 := by
    have hnat : (4293907811 : ℕ)^4293*20000000000000^3269 ≤ 6589848425651^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4293907811 10000000000 6589848425651 20000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (74166809/200000000 : ℝ)^4293 ≤ (27178593967541/100000000000000 : ℝ)^3269 := by
    have hnat : (74166809 : ℕ)^4293*100000000000000^3269 ≤ 27178593967541^3269*200000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      74166809 200000000 27178593967541 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4965021951/10000000000 : ℝ)^4293 ≤ (9968040974227/25000000000000 : ℝ)^3269 := by
    have hnat : (4965021951 : ℕ)^4293*25000000000000^3269 ≤ 9968040974227^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4965021951 10000000000 9968040974227 25000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4293/1024 : ℝ)) 4293 3269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4293907811/10000000000 : ℝ), (74166809/200000000 : ℝ), (4965021951/10000000000 : ℝ)] ![(6589848425651/20000000000000 : ℝ), (27178593967541/100000000000000 : ℝ), (9968040974227/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4293907811/10000000000 : ℝ)|^4293 ≤ (6589848425651/20000000000000 : ℝ)^3269
        have hw : |(4293907811/10000000000 : ℝ)|=(4293907811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(74166809/200000000 : ℝ)|^4293 ≤ (27178593967541/100000000000000 : ℝ)^3269
        have hw : |(74166809/200000000 : ℝ)|=(74166809/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4965021951/10000000000 : ℝ)|^4293 ≤ (9968040974227/25000000000000 : ℝ)^3269
        have hw : |(4965021951/10000000000 : ℝ)|=(4965021951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1333_s1_4 (p : ℝ) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2001147419/10000000000 : ℝ)*x 0 + (1262948927/2500000000 : ℝ)*x 1 + (2819226801/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2001147419/10000000000 : ℝ)^4293 ≤ (3022371256539/25000000000000 : ℝ)^3269 := by
    have hnat : (2001147419 : ℕ)^4293*25000000000000^3269 ≤ 3022371256539^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2001147419 10000000000 3022371256539 25000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1262948927/2500000000 : ℝ)^4293 ≤ (40789789375171/100000000000000 : ℝ)^3269 := by
    have hnat : (1262948927 : ℕ)^4293*100000000000000^3269 ≤ 40789789375171^3269*2500000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1262948927 2500000000 40789789375171 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2819226801/5000000000 : ℝ)^4293 ≤ (942414511573/2000000000000 : ℝ)^3269 := by
    have hnat : (2819226801 : ℕ)^4293*2000000000000^3269 ≤ 942414511573^3269*5000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2819226801 5000000000 942414511573 2000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4293/1024 : ℝ)) 4293 3269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2001147419/10000000000 : ℝ), (1262948927/2500000000 : ℝ), (2819226801/5000000000 : ℝ)] ![(3022371256539/25000000000000 : ℝ), (40789789375171/100000000000000 : ℝ), (942414511573/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2001147419/10000000000 : ℝ)|^4293 ≤ (3022371256539/25000000000000 : ℝ)^3269
        have hw : |(-2001147419/10000000000 : ℝ)|=(2001147419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1262948927/2500000000 : ℝ)|^4293 ≤ (40789789375171/100000000000000 : ℝ)^3269
        have hw : |(1262948927/2500000000 : ℝ)|=(1262948927/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2819226801/5000000000 : ℝ)|^4293 ≤ (942414511573/2000000000000 : ℝ)^3269
        have hw : |(2819226801/5000000000 : ℝ)|=(2819226801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1333_s1_5 (p : ℝ) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1050112823/2000000000 : ℝ)*x 0 + (-1727825687/10000000000 : ℝ)*x 1 + (5638453011/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050112823/2000000000 : ℝ)^4293 ≤ (8582063037901/20000000000000 : ℝ)^3269 := by
    have hnat : (1050112823 : ℕ)^4293*20000000000000^3269 ≤ 8582063037901^3269*2000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050112823 2000000000 8582063037901 20000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1727825687/10000000000 : ℝ)^4293 ≤ (4984482852531/50000000000000 : ℝ)^3269 := by
    have hnat : (1727825687 : ℕ)^4293*50000000000000^3269 ≤ 4984482852531^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1727825687 10000000000 4984482852531 50000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5638453011/10000000000 : ℝ)^4293 ≤ (11780179773131/25000000000000 : ℝ)^3269 := by
    have hnat : (5638453011 : ℕ)^4293*25000000000000^3269 ≤ 11780179773131^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5638453011 10000000000 11780179773131 25000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4293/1024 : ℝ)) 4293 3269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050112823/2000000000 : ℝ), (-1727825687/10000000000 : ℝ), (5638453011/10000000000 : ℝ)] ![(8582063037901/20000000000000 : ℝ), (4984482852531/50000000000000 : ℝ), (11780179773131/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050112823/2000000000 : ℝ)|^4293 ≤ (8582063037901/20000000000000 : ℝ)^3269
        have hw : |(1050112823/2000000000 : ℝ)|=(1050112823/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1727825687/10000000000 : ℝ)|^4293 ≤ (4984482852531/50000000000000 : ℝ)^3269
        have hw : |(-1727825687/10000000000 : ℝ)|=(1727825687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5638453011/10000000000 : ℝ)|^4293 ≤ (11780179773131/25000000000000 : ℝ)^3269
        have hw : |(5638453011/10000000000 : ℝ)|=(5638453011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1333_s1_6 (p : ℝ) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2625281827/5000000000 : ℝ)*x 0 + (5638452829/10000000000 : ℝ)*x 1 + (-1727826603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2625281827/5000000000 : ℝ)^4293 ≤ (42910310241813/100000000000000 : ℝ)^3269 := by
    have hnat : (2625281827 : ℕ)^4293*100000000000000^3269 ≤ 42910310241813^3269*5000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2625281827 5000000000 42910310241813 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5638452829/10000000000 : ℝ)^4293 ≤ (736261204611/1562500000000 : ℝ)^3269 := by
    have hnat : (5638452829 : ℕ)^4293*1562500000000^3269 ≤ 736261204611^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5638452829 10000000000 736261204611 1562500000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1727826603/10000000000 : ℝ)^4293 ≤ (1246121580697/12500000000000 : ℝ)^3269 := by
    have hnat : (1727826603 : ℕ)^4293*12500000000000^3269 ≤ 1246121580697^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1727826603 10000000000 1246121580697 12500000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4293/1024 : ℝ)) 4293 3269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2625281827/5000000000 : ℝ), (5638452829/10000000000 : ℝ), (-1727826603/10000000000 : ℝ)] ![(42910310241813/100000000000000 : ℝ), (736261204611/1562500000000 : ℝ), (1246121580697/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2625281827/5000000000 : ℝ)|^4293 ≤ (42910310241813/100000000000000 : ℝ)^3269
        have hw : |(2625281827/5000000000 : ℝ)|=(2625281827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5638452829/10000000000 : ℝ)|^4293 ≤ (736261204611/1562500000000 : ℝ)^3269
        have hw : |(5638452829/10000000000 : ℝ)|=(5638452829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1727826603/10000000000 : ℝ)|^4293 ≤ (1246121580697/12500000000000 : ℝ)^3269
        have hw : |(-1727826603/10000000000 : ℝ)|=(1727826603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1333_s1_7 (p : ℝ) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (85901249/200000000 : ℝ)*x 0 + (4949144543/10000000000 : ℝ)*x 1 + (744901801/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (85901249/200000000 : ℝ)^4293 ≤ (16480439057173/50000000000000 : ℝ)^3269 := by
    have hnat : (85901249 : ℕ)^4293*50000000000000^3269 ≤ 16480439057173^3269*200000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85901249 200000000 16480439057173 50000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4949144543/10000000000 : ℝ)^4293 ≤ (19852401022567/50000000000000 : ℝ)^3269 := by
    have hnat : (4949144543 : ℕ)^4293*50000000000000^3269 ≤ 19852401022567^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4949144543 10000000000 19852401022567 50000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (744901801/2000000000 : ℝ)^4293 ≤ (3416789978511/12500000000000 : ℝ)^3269 := by
    have hnat : (744901801 : ℕ)^4293*12500000000000^3269 ≤ 3416789978511^3269*2000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      744901801 2000000000 3416789978511 12500000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4293/1024 : ℝ)) 4293 3269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(85901249/200000000 : ℝ), (4949144543/10000000000 : ℝ), (744901801/2000000000 : ℝ)] ![(16480439057173/50000000000000 : ℝ), (19852401022567/50000000000000 : ℝ), (3416789978511/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(85901249/200000000 : ℝ)|^4293 ≤ (16480439057173/50000000000000 : ℝ)^3269
        have hw : |(85901249/200000000 : ℝ)|=(85901249/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4949144543/10000000000 : ℝ)|^4293 ≤ (19852401022567/50000000000000 : ℝ)^3269
        have hw : |(4949144543/10000000000 : ℝ)|=(4949144543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(744901801/2000000000 : ℝ)|^4293 ≤ (3416789978511/12500000000000 : ℝ)^3269
        have hw : |(744901801/2000000000 : ℝ)|=(744901801/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1333_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77187049/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3367/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (673/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (3403/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (19529/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3367/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (673/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3367/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (673/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3367/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (673/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3367/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (673/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3367/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (673/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3367/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (673/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (673/50000 : ℝ) ^ (1073/256 : ℝ) ≤ (1439023116623/100000000000000000000 : ℝ) := by
    have hpowers : (673/50000 : ℝ)^1073 ≤ (1439023116623/100000000000000000000 : ℝ)^256 := by
      have hnat : (673 : ℕ)^1073*100000000000000000000^256 ≤ 1439023116623^256*50000^1073 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        673 50000 1439023116623 100000000000000000000 1073 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (673/50000 : ℝ)) (X := (1439023116623/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1073 256 (by norm_num) hpowers
    exact h
  have hpowhi : (3367/12500 : ℝ) ^ (1073/256 : ℝ) ≤ (40953838100006433/10000000000000000000 : ℝ) := by
    have hpowers : (3367/12500 : ℝ)^1073 ≤ (40953838100006433/10000000000000000000 : ℝ)^256 := by
      have hnat : (3367 : ℕ)^1073*10000000000000000000^256 ≤ 40953838100006433^256*12500^1073 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3367 12500 40953838100006433 10000000000000000000 1073 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3367/12500 : ℝ)) (X := (40953838100006433/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1073 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000001439023116623/50000000000000000000 : ℝ) ≤ (156250001072897/156250000000000 : ℝ) ^ (1073/256 : ℝ) := by
    have hpowers : (50000001439023116623/50000000000000000000 : ℝ)^256 ≤ (156250001072897/156250000000000 : ℝ)^1073 := by
      have hnat : (50000001439023116623 : ℕ)^256*156250000000000^1073 ≤ 156250001072897^1073*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000001439023116623 50000000000000000000 156250001072897 156250000000000 256 1073 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156250001072897/156250000000000 : ℝ)) (X := (50000001439023116623/50000000000000000000 : ℝ)) (by norm_num) 1073 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100409539820023180953/100000000000000000000 : ℝ) ≤ (10009755742866489/10000000000000000 : ℝ) ^ (1073/256 : ℝ) := by
    have hpowers : (100409539820023180953/100000000000000000000 : ℝ)^256 ≤ (10009755742866489/10000000000000000 : ℝ)^1073 := by
      have hnat : (100409539820023180953 : ℕ)^256*10000000000000000^1073 ≤ 10009755742866489^1073*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100409539820023180953 100000000000000000000 10009755742866489 10000000000000000 256 1073 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10009755742866489/10000000000000000 : ℝ)) (X := (100409539820023180953/100000000000000000000 : ℝ)) (by norm_num) 1073 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (5040953838100006433/5000000000000000000 : ℝ) ≤ (1001951141706757/1000000000000000 : ℝ) ^ (1073/256 : ℝ) := by
    have hpowers : (5040953838100006433/5000000000000000000 : ℝ)^256 ≤ (1001951141706757/1000000000000000 : ℝ)^1073 := by
      have hnat : (5040953838100006433 : ℕ)^256*1000000000000000^1073 ≤ 1001951141706757^1073*5000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5040953838100006433 5000000000000000000 1001951141706757 1000000000000000 256 1073 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1001951141706757/1000000000000000 : ℝ)) (X := (5040953838100006433/5000000000000000000 : ℝ)) (by norm_num) 1073 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1439023116623/100000000000000000000 : ℝ) ≤ ((63968434870549620167/63975000000000000000 : ℝ)+2*(9755674201081/2559000000000000 : ℝ)*(673/50000 : ℝ))^(1073/256 : ℝ) := by
    rw [show (63968434870549620167/63975000000000000000 : ℝ)+2*(9755674201081/2559000000000000 : ℝ)*(673/50000 : ℝ)=(156250001072897/156250000000000 : ℝ) by norm_num, show 1+2*(1439023116623/100000000000000000000 : ℝ)=(50000001439023116623/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(40953838100006433/10000000000000000000 : ℝ)+(1439023116623/100000000000000000000 : ℝ) ≤ ((63968434870549620167/63975000000000000000 : ℝ)+(9755674201081/2559000000000000 : ℝ)*((3367/12500 : ℝ)+(673/50000 : ℝ)))^(1073/256 : ℝ) := by
    rw [show (63968434870549620167/63975000000000000000 : ℝ)+(9755674201081/2559000000000000 : ℝ)*((3367/12500 : ℝ)+(673/50000 : ℝ))=(10009755742866489/10000000000000000 : ℝ) by norm_num, show 1+(40953838100006433/10000000000000000000 : ℝ)+(1439023116623/100000000000000000000 : ℝ)=(100409539820023180953/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(40953838100006433/10000000000000000000 : ℝ) ≤ ((63968434870549620167/63975000000000000000 : ℝ)+2*(9755674201081/2559000000000000 : ℝ)*(3367/12500 : ℝ))^(1073/256 : ℝ) := by
    rw [show (63968434870549620167/63975000000000000000 : ℝ)+2*(9755674201081/2559000000000000 : ℝ)*(3367/12500 : ℝ)=(1001951141706757/1000000000000000 : ℝ) by norm_num, show 1+2*(40953838100006433/10000000000000000000 : ℝ)=(5040953838100006433/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (63968434870549620167/63975000000000000000 : ℝ)*(X 1 0+X 2 0)+(9755674201081/2559000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1073/256 : ℝ)) (lo := (673/50000 : ℝ)) (hi := (3367/12500 : ℝ)) (c := (63968434870549620167/63975000000000000000 : ℝ)) (alpha := (9755674201081/2559000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (63968434870549620167/63975000000000000000 : ℝ)*(X 0 1+X 2 1)+(9755674201081/2559000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1073/256 : ℝ)) (lo := (673/50000 : ℝ)) (hi := (3367/12500 : ℝ)) (c := (63968434870549620167/63975000000000000000 : ℝ)) (alpha := (9755674201081/2559000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (63968434870549620167/63975000000000000000 : ℝ)*(X 0 2+X 1 2)+(9755674201081/2559000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1073/256 : ℝ)) (lo := (673/50000 : ℝ)) (hi := (3367/12500 : ℝ)) (c := (63968434870549620167/63975000000000000000 : ℝ)) (alpha := (9755674201081/2559000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1000296847/5000000000 : ℝ)*X 0 0+(2823099167/5000000000 : ℝ)*X 0 1+(5044190569/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1333_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5406658349/10000000000 : ℝ)*X 1 0+(-2322089059/10000000000 : ℝ)*X 1 1+(5044190067/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1333_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2703329103/5000000000 : ℝ)*X 2 0+(5044189797/10000000000 : ℝ)*X 2 1+(-2322089589/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1333_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4293907811/10000000000 : ℝ)*X 0 0+(74166809/200000000 : ℝ)*X 0 1+(4965021951/10000000000 : ℝ)*X 0 2+(4293907811/10000000000 : ℝ)*X 1 0+(74166809/200000000 : ℝ)*X 1 1+(4965021951/10000000000 : ℝ)*X 1 2+(4293907811/10000000000 : ℝ)*X 2 0+(74166809/200000000 : ℝ)*X 2 1+(4965021951/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1333_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2001147419/10000000000 : ℝ)*X 0 0+(1262948927/2500000000 : ℝ)*X 0 1+(2819226801/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1333_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1050112823/2000000000 : ℝ)*X 1 0+(-1727825687/10000000000 : ℝ)*X 1 1+(5638453011/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1333_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2625281827/5000000000 : ℝ)*X 2 0+(5638452829/10000000000 : ℝ)*X 2 1+(-1727826603/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1333_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((85901249/200000000 : ℝ)*X 0 0+(4949144543/10000000000 : ℝ)*X 0 1+(744901801/2000000000 : ℝ)*X 0 2+(85901249/200000000 : ℝ)*X 1 0+(4949144543/10000000000 : ℝ)*X 1 1+(744901801/2000000000 : ℝ)*X 1 2+(85901249/200000000 : ℝ)*X 2 0+(4949144543/10000000000 : ℝ)*X 2 1+(744901801/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1333_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2081801878073219315389334107/533125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15769227/20000000000000 : ℝ)*(base1) + (64987329/100000000000000 : ℝ)*(base19) + (2113789/12500000000000 : ℝ)*(lower4) + (11980037/25000000000000 : ℝ)*(upper5) + (614213774468179/50000000000000 : ℝ)*(major0) + (614213774468179/50000000000000 : ℝ)*(major1) + (614213774468179/50000000000000 : ℝ)*(major2) + (415276963812769/25000000000000 : ℝ)*(sp0) + (1661106180906277/100000000000000 : ℝ)*(sp1) + (830552216673921/50000000000000 : ℝ)*(sp2) + (397873507397427/50000000000000 : ℝ)*(sp3) + (306102267/20000000000000 : ℝ)*(sp5) + (3343057099/100000000000000 : ℝ)*(sp6) + (48831659/50000000000000 : ℝ)*(sp7) + (795747191304307/100000000000000 : ℝ)*(f.failure) + (1661107776404941/100000000000000 : ℝ)*(f.sum) + (39920276575249/63975000000000000000000000000 : ℝ)*base65 + (4766186020162286369/1066250000000000000000000000000000 : ℝ)*base68 + (5986096889350213631/1066250000000000000000000000000000 : ℝ)*base69 + (9866900544539786369/1066250000000000000000000000000000 : ℝ)*base72 + (272414216390351/63975000000000000000000000000 : ℝ)*base74 + (18764646784350213631/1066250000000000000000000000000000 : ℝ)*base75 + (3805121001710213631/1066250000000000000000000000000000 : ℝ)*base77 + (5821096694671463631/1066250000000000000000000000000000 : ℝ)*base79 + (5341113518347/7996875000000000000000000000 : ℝ)*base82 + (18320043/5000000000000000000000 : ℝ)*base89 + (18320043/5000000000000000000000 : ℝ)*base91 + (18320043/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (39554562510649757722500929/13328125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (91137281/50000000000000 : ℝ)*(base19) + (52667117/100000000000000 : ℝ)*(base23) + (40760877/100000000000000 : ℝ)*(upper2) + (64162847/100000000000000 : ℝ)*(upper3) + (7878583989397/625000000000 : ℝ)*(major0) + (7878583989397/625000000000 : ℝ)*(major1) + (7878583989397/625000000000 : ℝ)*(major2) + (42173179/1250000000000 : ℝ)*(sp0) + (1936723407/100000000000000 : ℝ)*(sp1) + (266238297/50000000000000 : ℝ)*(sp3) + (852286421340559/50000000000000 : ℝ)*(sp4) + (170457409753747/10000000000000 : ℝ)*(sp5) + (852288081934161/50000000000000 : ℝ)*(sp6) + (816570028669953/100000000000000 : ℝ)*(sp7) + (816570561146547/100000000000000 : ℝ)*(f.failure) + (1704576216535439/100000000000000 : ℝ)*(f.sum) + (17478336971389/6397500000000000000000000000 : ℝ)*base66 + (35847857571661029/6664062500000000000000000000000 : ℝ)*base67 + (72995017478567279/6664062500000000000000000000000 : ℝ)*base69 + (8650058821973851/1666015625000000000000000000000 : ℝ)*base71 + (10335664015727/3198750000000000000000000000 : ℝ)*base74 + (62366375574025183/13328125000000000000000000000000 : ℝ)*base75 + (48875020040868933/13328125000000000000000000000000 : ℝ)*base77 + (215481876596381/416503906250000000000000000000 : ℝ)*base80 + (12997406757577/12795000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (19469803/5000000000000000000000 : ℝ)*base89 + (19469803/5000000000000000000000 : ℝ)*base91 + (19469803/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1333_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77187049/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3367/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (673/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3403/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (19529/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1333_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1333_s2_0 (p : ℝ) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2041538799/10000000000 : ℝ)*x 0 + (2741115037/5000000000 : ℝ)*x 1 + (2590972347/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2041538799/10000000000 : ℝ)^4293 ≤ (12410945716977/100000000000000 : ℝ)^3269 := by
    have hnat : (2041538799 : ℕ)^4293*100000000000000^3269 ≤ 12410945716977^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2041538799 10000000000 12410945716977 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2741115037/5000000000 : ℝ)^4293 ≤ (4541368639701/10000000000000 : ℝ)^3269 := by
    have hnat : (2741115037 : ℕ)^4293*10000000000000^3269 ≤ 4541368639701^3269*5000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2741115037 5000000000 4541368639701 10000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2590972347/5000000000 : ℝ)^4293 ≤ (4217536787303/10000000000000 : ℝ)^3269 := by
    have hnat : (2590972347 : ℕ)^4293*10000000000000^3269 ≤ 4217536787303^3269*5000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590972347 5000000000 4217536787303 10000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4293/1024 : ℝ)) 4293 3269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2041538799/10000000000 : ℝ), (2741115037/5000000000 : ℝ), (2590972347/5000000000 : ℝ)] ![(12410945716977/100000000000000 : ℝ), (4541368639701/10000000000000 : ℝ), (4217536787303/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2041538799/10000000000 : ℝ)|^4293 ≤ (12410945716977/100000000000000 : ℝ)^3269
        have hw : |(-2041538799/10000000000 : ℝ)|=(2041538799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2741115037/5000000000 : ℝ)|^4293 ≤ (4541368639701/10000000000000 : ℝ)^3269
        have hw : |(2741115037/5000000000 : ℝ)|=(2741115037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2590972347/5000000000 : ℝ)|^4293 ≤ (4217536787303/10000000000000 : ℝ)^3269
        have hw : |(2590972347/5000000000 : ℝ)|=(2590972347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1333_s2_1 (p : ℝ) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (335411789/625000000 : ℝ)*x 0 + (-2196775639/10000000000 : ℝ)*x 1 + (1036389013/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (335411789/625000000 : ℝ)^4293 ≤ (22079919342281/50000000000000 : ℝ)^3269 := by
    have hnat : (335411789 : ℕ)^4293*50000000000000^3269 ≤ 22079919342281^3269*625000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335411789 625000000 22079919342281 50000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2196775639/10000000000 : ℝ)^4293 ≤ (1366478946357/10000000000000 : ℝ)^3269 := by
    have hnat : (2196775639 : ℕ)^4293*10000000000000^3269 ≤ 1366478946357^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2196775639 10000000000 1366478946357 10000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1036389013/2000000000 : ℝ)^4293 ≤ (42175371838421/100000000000000 : ℝ)^3269 := by
    have hnat : (1036389013 : ℕ)^4293*100000000000000^3269 ≤ 42175371838421^3269*2000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036389013 2000000000 42175371838421 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4293/1024 : ℝ)) 4293 3269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(335411789/625000000 : ℝ), (-2196775639/10000000000 : ℝ), (1036389013/2000000000 : ℝ)] ![(22079919342281/50000000000000 : ℝ), (1366478946357/10000000000000 : ℝ), (42175371838421/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(335411789/625000000 : ℝ)|^4293 ≤ (22079919342281/50000000000000 : ℝ)^3269
        have hw : |(335411789/625000000 : ℝ)|=(335411789/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2196775639/10000000000 : ℝ)|^4293 ≤ (1366478946357/10000000000000 : ℝ)^3269
        have hw : |(-2196775639/10000000000 : ℝ)|=(2196775639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1036389013/2000000000 : ℝ)|^4293 ≤ (42175371838421/100000000000000 : ℝ)^3269
        have hw : |(1036389013/2000000000 : ℝ)|=(1036389013/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1333_s2_2 (p : ℝ) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5366588713/10000000000 : ℝ)*x 0 + (5181944959/10000000000 : ℝ)*x 1 + (-2196775659/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5366588713/10000000000 : ℝ)^4293 ≤ (22079919823159/50000000000000 : ℝ)^3269 := by
    have hnat : (5366588713 : ℕ)^4293*50000000000000^3269 ≤ 22079919823159^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5366588713 10000000000 22079919823159 50000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5181944959/10000000000 : ℝ)^4293 ≤ (10543842676363/25000000000000 : ℝ)^3269 := by
    have hnat : (5181944959 : ℕ)^4293*25000000000000^3269 ≤ 10543842676363^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181944959 10000000000 10543842676363 25000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2196775659/10000000000 : ℝ)^4293 ≤ (3416197406737/25000000000000 : ℝ)^3269 := by
    have hnat : (2196775659 : ℕ)^4293*25000000000000^3269 ≤ 3416197406737^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2196775659 10000000000 3416197406737 25000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4293/1024 : ℝ)) 4293 3269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5366588713/10000000000 : ℝ), (5181944959/10000000000 : ℝ), (-2196775659/10000000000 : ℝ)] ![(22079919823159/50000000000000 : ℝ), (10543842676363/25000000000000 : ℝ), (3416197406737/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5366588713/10000000000 : ℝ)|^4293 ≤ (22079919823159/50000000000000 : ℝ)^3269
        have hw : |(5366588713/10000000000 : ℝ)|=(5366588713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5181944959/10000000000 : ℝ)|^4293 ≤ (10543842676363/25000000000000 : ℝ)^3269
        have hw : |(5181944959/10000000000 : ℝ)|=(5181944959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2196775659/10000000000 : ℝ)|^4293 ≤ (3416197406737/25000000000000 : ℝ)^3269
        have hw : |(-2196775659/10000000000 : ℝ)|=(2196775659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1333_s2_3 (p : ℝ) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4322510677/10000000000 : ℝ)*x 0 + (2009862769/5000000000 : ℝ)*x 1 + (2323282581/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4322510677/10000000000 : ℝ)^4293 ≤ (4154722299587/12500000000000 : ℝ)^3269 := by
    have hnat : (4322510677 : ℕ)^4293*12500000000000^3269 ≤ 4154722299587^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4322510677 10000000000 4154722299587 12500000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2009862769/5000000000 : ℝ)^4293 ≤ (3776788473377/12500000000000 : ℝ)^3269 := by
    have hnat : (2009862769 : ℕ)^4293*12500000000000^3269 ≤ 3776788473377^3269*5000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2009862769 5000000000 3776788473377 12500000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2323282581/5000000000 : ℝ)^4293 ≤ (36547913802091/100000000000000 : ℝ)^3269 := by
    have hnat : (2323282581 : ℕ)^4293*100000000000000^3269 ≤ 36547913802091^3269*5000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2323282581 5000000000 36547913802091 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4293/1024 : ℝ)) 4293 3269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4322510677/10000000000 : ℝ), (2009862769/5000000000 : ℝ), (2323282581/5000000000 : ℝ)] ![(4154722299587/12500000000000 : ℝ), (3776788473377/12500000000000 : ℝ), (36547913802091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4322510677/10000000000 : ℝ)|^4293 ≤ (4154722299587/12500000000000 : ℝ)^3269
        have hw : |(4322510677/10000000000 : ℝ)|=(4322510677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2009862769/5000000000 : ℝ)|^4293 ≤ (3776788473377/12500000000000 : ℝ)^3269
        have hw : |(2009862769/5000000000 : ℝ)|=(2009862769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2323282581/5000000000 : ℝ)|^4293 ≤ (36547913802091/100000000000000 : ℝ)^3269
        have hw : |(2323282581/5000000000 : ℝ)|=(2323282581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1333_s2_4 (p : ℝ) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2041607467/10000000000 : ℝ)*x 0 + (103676949/200000000 : ℝ)*x 1 + (5480309993/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2041607467/10000000000 : ℝ)^4293 ≤ (12411493930687/100000000000000 : ℝ)^3269 := by
    have hnat : (2041607467 : ℕ)^4293*100000000000000^3269 ≤ 12411493930687^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2041607467 10000000000 12411493930687 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (103676949/200000000 : ℝ)^4293 ≤ (21097853215261/50000000000000 : ℝ)^3269 := by
    have hnat : (103676949 : ℕ)^4293*50000000000000^3269 ≤ 21097853215261^3269*200000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103676949 200000000 21097853215261 50000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5480309993/10000000000 : ℝ)^4293 ≤ (45392799631499/100000000000000 : ℝ)^3269 := by
    have hnat : (5480309993 : ℕ)^4293*100000000000000^3269 ≤ 45392799631499^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5480309993 10000000000 45392799631499 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4293/1024 : ℝ)) 4293 3269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2041607467/10000000000 : ℝ), (103676949/200000000 : ℝ), (5480309993/10000000000 : ℝ)] ![(12411493930687/100000000000000 : ℝ), (21097853215261/50000000000000 : ℝ), (45392799631499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2041607467/10000000000 : ℝ)|^4293 ≤ (12411493930687/100000000000000 : ℝ)^3269
        have hw : |(-2041607467/10000000000 : ℝ)|=(2041607467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(103676949/200000000 : ℝ)|^4293 ≤ (21097853215261/50000000000000 : ℝ)^3269
        have hw : |(103676949/200000000 : ℝ)|=(103676949/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5480309993/10000000000 : ℝ)|^4293 ≤ (45392799631499/100000000000000 : ℝ)^3269
        have hw : |(5480309993/10000000000 : ℝ)|=(5480309993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1333_s2_5 (p : ℝ) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1322316551/2500000000 : ℝ)*x 0 + (-118650651/625000000 : ℝ)*x 1 + (2740155009/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322316551/2500000000 : ℝ)^4293 ≤ (5415770607659/12500000000000 : ℝ)^3269 := by
    have hnat : (1322316551 : ℕ)^4293*12500000000000^3269 ≤ 5415770607659^3269*2500000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322316551 2500000000 5415770607659 12500000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (118650651/625000000 : ℝ)^4293 ≤ (11281035216911/100000000000000 : ℝ)^3269 := by
    have hnat : (118650651 : ℕ)^4293*100000000000000^3269 ≤ 11281035216911^3269*625000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      118650651 625000000 11281035216911 100000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2740155009/5000000000 : ℝ)^4293 ≤ (11348199975859/25000000000000 : ℝ)^3269 := by
    have hnat : (2740155009 : ℕ)^4293*25000000000000^3269 ≤ 11348199975859^3269*5000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2740155009 5000000000 11348199975859 25000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4293/1024 : ℝ)) 4293 3269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322316551/2500000000 : ℝ), (-118650651/625000000 : ℝ), (2740155009/5000000000 : ℝ)] ![(5415770607659/12500000000000 : ℝ), (11281035216911/100000000000000 : ℝ), (11348199975859/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322316551/2500000000 : ℝ)|^4293 ≤ (5415770607659/12500000000000 : ℝ)^3269
        have hw : |(1322316551/2500000000 : ℝ)|=(1322316551/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-118650651/625000000 : ℝ)|^4293 ≤ (11281035216911/100000000000000 : ℝ)^3269
        have hw : |(-118650651/625000000 : ℝ)|=(118650651/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2740155009/5000000000 : ℝ)|^4293 ≤ (11348199975859/25000000000000 : ℝ)^3269
        have hw : |(2740155009/5000000000 : ℝ)|=(2740155009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1333_s2_6 (p : ℝ) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5289266249/10000000000 : ℝ)*x 0 + (548031/1000000 : ℝ)*x 1 + (-1898410379/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289266249/10000000000 : ℝ)^4293 ≤ (10831541336337/25000000000000 : ℝ)^3269 := by
    have hnat : (5289266249 : ℕ)^4293*25000000000000^3269 ≤ 10831541336337^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289266249 10000000000 10831541336337 25000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (548031/1000000 : ℝ)^4293 ≤ (22696399853821/50000000000000 : ℝ)^3269 := by
    have hnat : (548031 : ℕ)^4293*50000000000000^3269 ≤ 22696399853821^3269*1000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548031 1000000 22696399853821 50000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1898410379/10000000000 : ℝ)^4293 ≤ (2820258732043/25000000000000 : ℝ)^3269 := by
    have hnat : (1898410379 : ℕ)^4293*25000000000000^3269 ≤ 2820258732043^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1898410379 10000000000 2820258732043 25000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4293/1024 : ℝ)) 4293 3269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289266249/10000000000 : ℝ), (548031/1000000 : ℝ), (-1898410379/10000000000 : ℝ)] ![(10831541336337/25000000000000 : ℝ), (22696399853821/50000000000000 : ℝ), (2820258732043/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289266249/10000000000 : ℝ)|^4293 ≤ (10831541336337/25000000000000 : ℝ)^3269
        have hw : |(5289266249/10000000000 : ℝ)|=(5289266249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(548031/1000000 : ℝ)|^4293 ≤ (22696399853821/50000000000000 : ℝ)^3269
        have hw : |(548031/1000000 : ℝ)|=(548031/1000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1898410379/10000000000 : ℝ)|^4293 ≤ (2820258732043/25000000000000 : ℝ)^3269
        have hw : |(-1898410379/10000000000 : ℝ)|=(1898410379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1333_s2_7 (p : ℝ) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4322654391/10000000000 : ℝ)*x 0 + (290162117/625000000 : ℝ)*x 1 + (4023733051/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4322654391/10000000000 : ℝ)^4293 ≤ (6647845929999/20000000000000 : ℝ)^3269 := by
    have hnat : (4322654391 : ℕ)^4293*20000000000000^3269 ≤ 6647845929999^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4322654391 10000000000 6647845929999 20000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (290162117/625000000 : ℝ)^4293 ≤ (4563362264511/12500000000000 : ℝ)^3269 := by
    have hnat : (290162117 : ℕ)^4293*12500000000000^3269 ≤ 4563362264511^3269*625000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      290162117 625000000 4563362264511 12500000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4023733051/10000000000 : ℝ)^4293 ≤ (6050774444049/20000000000000 : ℝ)^3269 := by
    have hnat : (4023733051 : ℕ)^4293*20000000000000^3269 ≤ 6050774444049^3269*10000000000^4293 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4023733051 10000000000 6050774444049 20000000000000 4293 3269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4293/1024 : ℝ)) 4293 3269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4322654391/10000000000 : ℝ), (290162117/625000000 : ℝ), (4023733051/10000000000 : ℝ)] ![(6647845929999/20000000000000 : ℝ), (4563362264511/12500000000000 : ℝ), (6050774444049/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4322654391/10000000000 : ℝ)|^4293 ≤ (6647845929999/20000000000000 : ℝ)^3269
        have hw : |(4322654391/10000000000 : ℝ)|=(4322654391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(290162117/625000000 : ℝ)|^4293 ≤ (4563362264511/12500000000000 : ℝ)^3269
        have hw : |(290162117/625000000 : ℝ)|=(290162117/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4023733051/10000000000 : ℝ)|^4293 ≤ (6050774444049/20000000000000 : ℝ)^3269
        have hw : |(4023733051/10000000000 : ℝ)|=(4023733051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1333_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77187049/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19529/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3403/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (306/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (807/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (19529/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3403/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (19529/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3403/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (19529/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3403/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (19529/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3403/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (19529/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3403/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (19529/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3403/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3403/50000 : ℝ) ^ (1073/256 : ℝ) ≤ (1282850367211297/100000000000000000000 : ℝ) := by
    have hpowers : (3403/50000 : ℝ)^1073 ≤ (1282850367211297/100000000000000000000 : ℝ)^256 := by
      have hnat : (3403 : ℕ)^1073*100000000000000000000^256 ≤ 1282850367211297^256*50000^1073 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3403 50000 1282850367211297 100000000000000000000 1073 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3403/50000 : ℝ)) (X := (1282850367211297/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1073 256 (by norm_num) hpowers
    exact h
  have hpowhi : (19529/100000 : ℝ) ^ (1073/256 : ℝ) ≤ (26600619446547353/25000000000000000000 : ℝ) := by
    have hpowers : (19529/100000 : ℝ)^1073 ≤ (26600619446547353/25000000000000000000 : ℝ)^256 := by
      have hnat : (19529 : ℕ)^1073*25000000000000000000^256 ≤ 26600619446547353^256*100000^1073 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19529 100000 26600619446547353 25000000000000000000 1073 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19529/100000 : ℝ)) (X := (26600619446547353/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1073 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001282850367211297/50000000000000000000 : ℝ) ≤ (10000061212765369/10000000000000000 : ℝ) ^ (1073/256 : ℝ) := by
    have hpowers : (50001282850367211297/50000000000000000000 : ℝ)^256 ≤ (10000061212765369/10000000000000000 : ℝ)^1073 := by
      have hnat : (50001282850367211297 : ℕ)^256*10000000000000000^1073 ≤ 10000061212765369^1073*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001282850367211297 50000000000000000000 10000061212765369 10000000000000000 256 1073 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000061212765369/10000000000000000 : ℝ)) (X := (50001282850367211297/50000000000000000000 : ℝ)) (by norm_num) 1073 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100107685328153400709/100000000000000000000 : ℝ) ≤ (2500642035167893/2500000000000000 : ℝ) ^ (1073/256 : ℝ) := by
    have hpowers : (100107685328153400709/100000000000000000000 : ℝ)^256 ≤ (2500642035167893/2500000000000000 : ℝ)^1073 := by
      have hnat : (100107685328153400709 : ℕ)^256*2500000000000000^1073 ≤ 2500642035167893^1073*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100107685328153400709 100000000000000000000 2500642035167893 2500000000000000 256 1073 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500642035167893/2500000000000000 : ℝ)) (X := (100107685328153400709/100000000000000000000 : ℝ)) (by norm_num) 1073 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (12526600619446547353/12500000000000000000 : ℝ) ≤ (400203002743111/400000000000000 : ℝ) ^ (1073/256 : ℝ) := by
    have hpowers : (12526600619446547353/12500000000000000000 : ℝ)^256 ≤ (400203002743111/400000000000000 : ℝ)^1073 := by
      have hnat : (12526600619446547353 : ℕ)^256*400000000000000^1073 ≤ 400203002743111^1073*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12526600619446547353 12500000000000000000 400203002743111 400000000000000 256 1073 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400203002743111/400000000000000 : ℝ)) (X := (12526600619446547353/12500000000000000000 : ℝ)) (by norm_num) 1073 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1282850367211297/100000000000000000000 : ℝ) ≤ ((42398884835784851517/42410000000000000000 : ℝ)+2*(835642635401/424100000000000 : ℝ)*(3403/50000 : ℝ))^(1073/256 : ℝ) := by
    rw [show (42398884835784851517/42410000000000000000 : ℝ)+2*(835642635401/424100000000000 : ℝ)*(3403/50000 : ℝ)=(10000061212765369/10000000000000000 : ℝ) by norm_num, show 1+2*(1282850367211297/100000000000000000000 : ℝ)=(50001282850367211297/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(26600619446547353/25000000000000000000 : ℝ)+(1282850367211297/100000000000000000000 : ℝ) ≤ ((42398884835784851517/42410000000000000000 : ℝ)+(835642635401/424100000000000 : ℝ)*((19529/100000 : ℝ)+(3403/50000 : ℝ)))^(1073/256 : ℝ) := by
    rw [show (42398884835784851517/42410000000000000000 : ℝ)+(835642635401/424100000000000 : ℝ)*((19529/100000 : ℝ)+(3403/50000 : ℝ))=(2500642035167893/2500000000000000 : ℝ) by norm_num, show 1+(26600619446547353/25000000000000000000 : ℝ)+(1282850367211297/100000000000000000000 : ℝ)=(100107685328153400709/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(26600619446547353/25000000000000000000 : ℝ) ≤ ((42398884835784851517/42410000000000000000 : ℝ)+2*(835642635401/424100000000000 : ℝ)*(19529/100000 : ℝ))^(1073/256 : ℝ) := by
    rw [show (42398884835784851517/42410000000000000000 : ℝ)+2*(835642635401/424100000000000 : ℝ)*(19529/100000 : ℝ)=(400203002743111/400000000000000 : ℝ) by norm_num, show 1+2*(26600619446547353/25000000000000000000 : ℝ)=(12526600619446547353/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (42398884835784851517/42410000000000000000 : ℝ)*(X 1 0+X 2 0)+(835642635401/424100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1073/256 : ℝ)) (lo := (3403/50000 : ℝ)) (hi := (19529/100000 : ℝ)) (c := (42398884835784851517/42410000000000000000 : ℝ)) (alpha := (835642635401/424100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (42398884835784851517/42410000000000000000 : ℝ)*(X 0 1+X 2 1)+(835642635401/424100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1073/256 : ℝ)) (lo := (3403/50000 : ℝ)) (hi := (19529/100000 : ℝ)) (c := (42398884835784851517/42410000000000000000 : ℝ)) (alpha := (835642635401/424100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (42398884835784851517/42410000000000000000 : ℝ)*(X 0 2+X 1 2)+(835642635401/424100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1073/256 : ℝ)) (lo := (3403/50000 : ℝ)) (hi := (19529/100000 : ℝ)) (c := (42398884835784851517/42410000000000000000 : ℝ)) (alpha := (835642635401/424100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2041538799/10000000000 : ℝ)*X 0 0+(2741115037/5000000000 : ℝ)*X 0 1+(2590972347/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1333_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((335411789/625000000 : ℝ)*X 1 0+(-2196775639/10000000000 : ℝ)*X 1 1+(1036389013/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1333_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5366588713/10000000000 : ℝ)*X 2 0+(5181944959/10000000000 : ℝ)*X 2 1+(-2196775659/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1333_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4322510677/10000000000 : ℝ)*X 0 0+(2009862769/5000000000 : ℝ)*X 0 1+(2323282581/5000000000 : ℝ)*X 0 2+(4322510677/10000000000 : ℝ)*X 1 0+(2009862769/5000000000 : ℝ)*X 1 1+(2323282581/5000000000 : ℝ)*X 1 2+(4322510677/10000000000 : ℝ)*X 2 0+(2009862769/5000000000 : ℝ)*X 2 1+(2323282581/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1333_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2041607467/10000000000 : ℝ)*X 0 0+(103676949/200000000 : ℝ)*X 0 1+(5480309993/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1333_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1322316551/2500000000 : ℝ)*X 1 0+(-118650651/625000000 : ℝ)*X 1 1+(2740155009/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1333_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5289266249/10000000000 : ℝ)*X 2 0+(548031/1000000 : ℝ)*X 2 1+(-1898410379/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1333_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4322654391/10000000000 : ℝ)*X 0 0+(290162117/625000000 : ℝ)*X 0 1+(4023733051/10000000000 : ℝ)*X 0 2+(4322654391/10000000000 : ℝ)*X 1 0+(290162117/625000000 : ℝ)*X 1 1+(4023733051/10000000000 : ℝ)*X 1 2+(4322654391/10000000000 : ℝ)*X 2 0+(290162117/625000000 : ℝ)*X 2 1+(4023733051/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1333_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (19703777564939691750473684229/2120500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13232761/781250000000 : ℝ)*(base19) + (1687549823/100000000000000 : ℝ)*(base23) + (32989559/100000000000000 : ℝ)*(lower2) + (55921/24414062500 : ℝ)*(upper3) + (174256071/100000000000000 : ℝ)*(upper5) + (2462769678660221/100000000000000 : ℝ)*(major0) + (2462769678660221/100000000000000 : ℝ)*(major1) + (2462769678660221/100000000000000 : ℝ)*(major2) + (3330189519510813/100000000000000 : ℝ)*(sp0) + (333021164140479/10000000000000 : ℝ)*(sp1) + (1665105823824187/50000000000000 : ℝ)*(sp2) + (797657302148213/50000000000000 : ℝ)*(sp3) + (4763137477/20000000000000 : ℝ)*(sp4) + (11108091037/100000000000000 : ℝ)*(sp7) + (199415714048433/12500000000000 : ℝ)*(f.failure) + (1665106667599099/50000000000000 : ℝ)*(f.sum) + (34927918538393/10602500000000000000000000000 : ℝ)*base65 + (8911839196117505257/4241000000000000000000000000000000 : ℝ)*base67 + (5538217135324494743/4241000000000000000000000000000000 : ℝ)*base70 + (13493287317447494743/4241000000000000000000000000000000 : ℝ)*base72 + (54625448565011/21205000000000000000000000000 : ℝ)*base73 + (44813704988332505257/4241000000000000000000000000000000 : ℝ)*base75 + (14038887292370505257/4241000000000000000000000000000000 : ℝ)*base77 + (66896325360903505257/4241000000000000000000000000000000 : ℝ)*base79 + (3707615064259/1325312500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (5094217/625000000000000000000 : ℝ)*base89 + (5094217/625000000000000000000 : ℝ)*base91 + (5094217/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (269732356161730892980460463/42410000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (649465373/50000000000000 : ℝ)*(base19) + (303155863/20000000000000 : ℝ)*(base23) + (171273921/100000000000000 : ℝ)*(upper3) + (18142003/25000000000000 : ℝ)*(lower4) + (43796517/50000000000000 : ℝ)*(upper5) + (49889779486313/2000000000000 : ℝ)*(major0) + (49889779486313/2000000000000 : ℝ)*(major1) + (49889779486313/2000000000000 : ℝ)*(major2) + (7109334821/50000000000000 : ℝ)*(sp1) + (8852032817/50000000000000 : ℝ)*(sp2) + (337310499202007/10000000000000 : ℝ)*(sp4) + (1686544737209841/50000000000000 : ℝ)*(sp5) + (42163572152189/1250000000000 : ℝ)*(sp6) + (807936372303743/50000000000000 : ℝ)*(sp7) + (807936372303743/50000000000000 : ℝ)*(f.failure) + (337310499202007/10000000000000 : ℝ)*(f.sum) + (313095593923/2120500000000000000000000000 : ℝ)*base66 + (135550317417353179/84820000000000000000000000000000 : ℝ)*base68 + (1470619831996633179/84820000000000000000000000000000 : ℝ)*base70 + (234739119742753179/84820000000000000000000000000000 : ℝ)*base72 + (876187874263/265062500000000000000000000 : ℝ)*base73 + (1076260395487353179/84820000000000000000000000000000 : ℝ)*base76 + (148415366600726821/84820000000000000000000000000000 : ℝ)*base77 + (69687151723726821/84820000000000000000000000000000 : ℝ)*base79 + (2400910654137/424100000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (3824407/2500000000000000000000 : ℝ)*base89 + (3824407/2500000000000000000000 : ℝ)*base91 + (3824407/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1333_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77187049/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19529/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3403/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (306/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (807/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1333_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1333_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77187049/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (306/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (807/5000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1333_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1333_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1333_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1073/256 : ℝ) ≤ p) (hpb : p ≤ (4293/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77187049/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (306/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (807/5000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1333_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
