-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1443_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:57:27.834994+00:00
-- url     : https://prove2.me/submissions/d4309d41-fdb3-4c2a-90f6-67c792b862fc

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
theorem support_rectangle_w1443_s6_0 (p : ℝ) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1959828381/10000000000 : ℝ)*x 0 + (337968657/625000000 : ℝ)*x 1 + (2623604503/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1959828381/10000000000 : ℝ)^4403 ≤ (2391971288191/20000000000000 : ℝ)^3379 := by
    have hnat : (1959828381 : ℕ)^4403*20000000000000^3379 ≤ 2391971288191^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1959828381 10000000000 2391971288191 20000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337968657/625000000 : ℝ)^4403 ≤ (11220738702509/25000000000000 : ℝ)^3379 := by
    have hnat : (337968657 : ℕ)^4403*25000000000000^3379 ≤ 11220738702509^3379*625000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337968657 625000000 11220738702509 25000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623604503/5000000000 : ℝ)^4403 ≤ (43157188737689/100000000000000 : ℝ)^3379 := by
    have hnat : (2623604503 : ℕ)^4403*100000000000000^3379 ≤ 43157188737689^3379*5000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623604503 5000000000 43157188737689 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4403/1024 : ℝ)) 4403 3379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1959828381/10000000000 : ℝ), (337968657/625000000 : ℝ), (2623604503/5000000000 : ℝ)] ![(2391971288191/20000000000000 : ℝ), (11220738702509/25000000000000 : ℝ), (43157188737689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1959828381/10000000000 : ℝ)|^4403 ≤ (2391971288191/20000000000000 : ℝ)^3379
        have hw : |(-1959828381/10000000000 : ℝ)|=(1959828381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337968657/625000000 : ℝ)|^4403 ≤ (11220738702509/25000000000000 : ℝ)^3379
        have hw : |(337968657/625000000 : ℝ)|=(337968657/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623604503/5000000000 : ℝ)|^4403 ≤ (43157188737689/100000000000000 : ℝ)^3379
        have hw : |(2623604503/5000000000 : ℝ)|=(2623604503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1443_s6_1 (p : ℝ) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3341893/6250000 : ℝ)*x 0 + (-1020712413/5000000000 : ℝ)*x 1 + (5247209009/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3341893/6250000 : ℝ)^4403 ≤ (44230057323949/100000000000000 : ℝ)^3379 := by
    have hnat : (3341893 : ℕ)^4403*100000000000000^3379 ≤ 44230057323949^3379*6250000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3341893 6250000 44230057323949 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1020712413/5000000000 : ℝ)^4403 ≤ (12612753890369/100000000000000 : ℝ)^3379 := by
    have hnat : (1020712413 : ℕ)^4403*100000000000000^3379 ≤ 12612753890369^3379*5000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1020712413 5000000000 12612753890369 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5247209009/10000000000 : ℝ)^4403 ≤ (43157188769841/100000000000000 : ℝ)^3379 := by
    have hnat : (5247209009 : ℕ)^4403*100000000000000^3379 ≤ 43157188769841^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247209009 10000000000 43157188769841 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4403/1024 : ℝ)) 4403 3379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3341893/6250000 : ℝ), (-1020712413/5000000000 : ℝ), (5247209009/10000000000 : ℝ)] ![(44230057323949/100000000000000 : ℝ), (12612753890369/100000000000000 : ℝ), (43157188769841/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3341893/6250000 : ℝ)|^4403 ≤ (44230057323949/100000000000000 : ℝ)^3379
        have hw : |(3341893/6250000 : ℝ)|=(3341893/6250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1020712413/5000000000 : ℝ)|^4403 ≤ (12612753890369/100000000000000 : ℝ)^3379
        have hw : |(-1020712413/5000000000 : ℝ)|=(1020712413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5247209009/10000000000 : ℝ)|^4403 ≤ (43157188769841/100000000000000 : ℝ)^3379
        have hw : |(5247209009/10000000000 : ℝ)|=(5247209009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1443_s6_2 (p : ℝ) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347028799/10000000000 : ℝ)*x 0 + (327950563/625000000 : ℝ)*x 1 + (-510356207/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347028799/10000000000 : ℝ)^4403 ≤ (44230057313171/100000000000000 : ℝ)^3379 := by
    have hnat : (5347028799 : ℕ)^4403*100000000000000^3379 ≤ 44230057313171^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347028799 10000000000 44230057313171 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (327950563/625000000 : ℝ)^4403 ≤ (10789297189781/25000000000000 : ℝ)^3379 := by
    have hnat : (327950563 : ℕ)^4403*25000000000000^3379 ≤ 10789297189781^3379*625000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327950563 625000000 10789297189781 25000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (510356207/2500000000 : ℝ)^4403 ≤ (1261275390647/10000000000000 : ℝ)^3379 := by
    have hnat : (510356207 : ℕ)^4403*10000000000000^3379 ≤ 1261275390647^3379*2500000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      510356207 2500000000 1261275390647 10000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4403/1024 : ℝ)) 4403 3379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347028799/10000000000 : ℝ), (327950563/625000000 : ℝ), (-510356207/2500000000 : ℝ)] ![(44230057313171/100000000000000 : ℝ), (10789297189781/25000000000000 : ℝ), (1261275390647/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347028799/10000000000 : ℝ)|^4403 ≤ (44230057313171/100000000000000 : ℝ)^3379
        have hw : |(5347028799/10000000000 : ℝ)|=(5347028799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(327950563/625000000 : ℝ)|^4403 ≤ (10789297189781/25000000000000 : ℝ)^3379
        have hw : |(327950563/625000000 : ℝ)|=(327950563/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-510356207/2500000000 : ℝ)|^4403 ≤ (1261275390647/10000000000000 : ℝ)^3379
        have hw : |(-510356207/2500000000 : ℝ)|=(510356207/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1443_s6_3 (p : ℝ) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (172035393/400000000 : ℝ)*x 0 + (4129771803/10000000000 : ℝ)*x 1 + (139947221/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (172035393/400000000 : ℝ)^4403 ≤ (33304901452233/100000000000000 : ℝ)^3379 := by
    have hnat : (172035393 : ℕ)^4403*100000000000000^3379 ≤ 33304901452233^3379*400000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172035393 400000000 33304901452233 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4129771803/10000000000 : ℝ)^4403 ≤ (31588799542197/100000000000000 : ℝ)^3379 := by
    have hnat : (4129771803 : ℕ)^4403*100000000000000^3379 ≤ 31588799542197^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4129771803 10000000000 31588799542197 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (139947221/312500000 : ℝ)^4403 ≤ (35106298984763/100000000000000 : ℝ)^3379 := by
    have hnat : (139947221 : ℕ)^4403*100000000000000^3379 ≤ 35106298984763^3379*312500000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      139947221 312500000 35106298984763 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4403/1024 : ℝ)) 4403 3379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(172035393/400000000 : ℝ), (4129771803/10000000000 : ℝ), (139947221/312500000 : ℝ)] ![(33304901452233/100000000000000 : ℝ), (31588799542197/100000000000000 : ℝ), (35106298984763/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(172035393/400000000 : ℝ)|^4403 ≤ (33304901452233/100000000000000 : ℝ)^3379
        have hw : |(172035393/400000000 : ℝ)|=(172035393/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4129771803/10000000000 : ℝ)|^4403 ≤ (31588799542197/100000000000000 : ℝ)^3379
        have hw : |(4129771803/10000000000 : ℝ)|=(4129771803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(139947221/312500000 : ℝ)|^4403 ≤ (35106298984763/100000000000000 : ℝ)^3379
        have hw : |(139947221/312500000 : ℝ)|=(139947221/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1443_s6_4 (p : ℝ) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-979919759/5000000000 : ℝ)*x 0 + (5247787881/10000000000 : ℝ)*x 1 + (1351729171/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (979919759/5000000000 : ℝ)^4403 ≤ (5979972500417/50000000000000 : ℝ)^3379 := by
    have hnat : (979919759 : ℕ)^4403*50000000000000^3379 ≤ 5979972500417^3379*5000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      979919759 5000000000 5979972500417 50000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247787881/10000000000 : ℝ)^4403 ≤ (8632678563371/20000000000000 : ℝ)^3379 := by
    have hnat : (5247787881 : ℕ)^4403*20000000000000^3379 ≤ 8632678563371^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247787881 10000000000 8632678563371 20000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1351729171/2500000000 : ℝ)^4403 ≤ (44876662167491/100000000000000 : ℝ)^3379 := by
    have hnat : (1351729171 : ℕ)^4403*100000000000000^3379 ≤ 44876662167491^3379*2500000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351729171 2500000000 44876662167491 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4403/1024 : ℝ)) 4403 3379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-979919759/5000000000 : ℝ), (5247787881/10000000000 : ℝ), (1351729171/2500000000 : ℝ)] ![(5979972500417/50000000000000 : ℝ), (8632678563371/20000000000000 : ℝ), (44876662167491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-979919759/5000000000 : ℝ)|^4403 ≤ (5979972500417/50000000000000 : ℝ)^3379
        have hw : |(-979919759/5000000000 : ℝ)|=(979919759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247787881/10000000000 : ℝ)|^4403 ≤ (8632678563371/20000000000000 : ℝ)^3379
        have hw : |(5247787881/10000000000 : ℝ)|=(5247787881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1351729171/2500000000 : ℝ)|^4403 ≤ (44876662167491/100000000000000 : ℝ)^3379
        have hw : |(1351729171/2500000000 : ℝ)|=(1351729171/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1443_s6_5 (p : ℝ) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326325371/2500000000 : ℝ)*x 0 + (-1881717079/10000000000 : ℝ)*x 1 + (5406916663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326325371/2500000000 : ℝ)^4403 ≤ (4378082484817/10000000000000 : ℝ)^3379 := by
    have hnat : (1326325371 : ℕ)^4403*10000000000000^3379 ≤ 4378082484817^3379*2500000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326325371 2500000000 4378082484817 10000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1881717079/10000000000 : ℝ)^4403 ≤ (2835628296619/25000000000000 : ℝ)^3379 := by
    have hnat : (1881717079 : ℕ)^4403*25000000000000^3379 ≤ 2835628296619^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1881717079 10000000000 2835628296619 25000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406916663/10000000000 : ℝ)^4403 ≤ (44876661940373/100000000000000 : ℝ)^3379 := by
    have hnat : (5406916663 : ℕ)^4403*100000000000000^3379 ≤ 44876661940373^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406916663 10000000000 44876661940373 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4403/1024 : ℝ)) 4403 3379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326325371/2500000000 : ℝ), (-1881717079/10000000000 : ℝ), (5406916663/10000000000 : ℝ)] ![(4378082484817/10000000000000 : ℝ), (2835628296619/25000000000000 : ℝ), (44876661940373/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326325371/2500000000 : ℝ)|^4403 ≤ (4378082484817/10000000000000 : ℝ)^3379
        have hw : |(1326325371/2500000000 : ℝ)|=(1326325371/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1881717079/10000000000 : ℝ)|^4403 ≤ (2835628296619/25000000000000 : ℝ)^3379
        have hw : |(-1881717079/10000000000 : ℝ)|=(1881717079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406916663/10000000000 : ℝ)|^4403 ≤ (44876661940373/100000000000000 : ℝ)^3379
        have hw : |(5406916663/10000000000 : ℝ)|=(5406916663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1443_s6_6 (p : ℝ) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (663162673/1250000000 : ℝ)*x 0 + (216276669/400000000 : ℝ)*x 1 + (-470429283/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663162673/1250000000 : ℝ)^4403 ≤ (43780823772859/100000000000000 : ℝ)^3379 := by
    have hnat : (663162673 : ℕ)^4403*100000000000000^3379 ≤ 43780823772859^3379*1250000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663162673 1250000000 43780823772859 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216276669/400000000 : ℝ)^4403 ≤ (44876662610911/100000000000000 : ℝ)^3379 := by
    have hnat : (216276669 : ℕ)^4403*100000000000000^3379 ≤ 44876662610911^3379*400000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216276669 400000000 44876662610911 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (470429283/2500000000 : ℝ)^4403 ≤ (5671256801381/50000000000000 : ℝ)^3379 := by
    have hnat : (470429283 : ℕ)^4403*50000000000000^3379 ≤ 5671256801381^3379*2500000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      470429283 2500000000 5671256801381 50000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4403/1024 : ℝ)) 4403 3379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663162673/1250000000 : ℝ), (216276669/400000000 : ℝ), (-470429283/2500000000 : ℝ)] ![(43780823772859/100000000000000 : ℝ), (44876662610911/100000000000000 : ℝ), (5671256801381/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663162673/1250000000 : ℝ)|^4403 ≤ (43780823772859/100000000000000 : ℝ)^3379
        have hw : |(663162673/1250000000 : ℝ)|=(663162673/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(216276669/400000000 : ℝ)|^4403 ≤ (44876662610911/100000000000000 : ℝ)^3379
        have hw : |(216276669/400000000 : ℝ)|=(216276669/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-470429283/2500000000 : ℝ)|^4403 ≤ (5671256801381/50000000000000 : ℝ)^3379
        have hw : |(-470429283/2500000000 : ℝ)|=(470429283/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1443_s6_7 (p : ℝ) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4300909151/10000000000 : ℝ)*x 0 + (2238526163/5000000000 : ℝ)*x 1 + (4131037099/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4300909151/10000000000 : ℝ)^4403 ≤ (33305146912899/100000000000000 : ℝ)^3379 := by
    have hnat : (4300909151 : ℕ)^4403*100000000000000^3379 ≤ 33305146912899^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4300909151 10000000000 33305146912899 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2238526163/5000000000 : ℝ)^4403 ≤ (17546720825927/50000000000000 : ℝ)^3379 := by
    have hnat : (2238526163 : ℕ)^4403*50000000000000^3379 ≤ 17546720825927^3379*5000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2238526163 5000000000 17546720825927 50000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4131037099/10000000000 : ℝ)^4403 ≤ (31601411422957/100000000000000 : ℝ)^3379 := by
    have hnat : (4131037099 : ℕ)^4403*100000000000000^3379 ≤ 31601411422957^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4131037099 10000000000 31601411422957 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4403/1024 : ℝ)) 4403 3379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4300909151/10000000000 : ℝ), (2238526163/5000000000 : ℝ), (4131037099/10000000000 : ℝ)] ![(33305146912899/100000000000000 : ℝ), (17546720825927/50000000000000 : ℝ), (31601411422957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4300909151/10000000000 : ℝ)|^4403 ≤ (33305146912899/100000000000000 : ℝ)^3379
        have hw : |(4300909151/10000000000 : ℝ)|=(4300909151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2238526163/5000000000 : ℝ)|^4403 ≤ (17546720825927/50000000000000 : ℝ)^3379
        have hw : |(2238526163/5000000000 : ℝ)|=(2238526163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4131037099/10000000000 : ℝ)|^4403 ≤ (31601411422957/100000000000000 : ℝ)^3379
        have hw : |(4131037099/10000000000 : ℝ)|=(4131037099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1443_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158721801/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14767/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2273/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (1421/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3691/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14767/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2273/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14767/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2273/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14767/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2273/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14767/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2273/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14767/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2273/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14767/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2273/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2273/20000 : ℝ) ^ (2201/512 : ℝ) ≤ (2177686483256669/25000000000000000000 : ℝ) := by
    have hpowers : (2273/20000 : ℝ)^2201 ≤ (2177686483256669/25000000000000000000 : ℝ)^512 := by
      have hnat : (2273 : ℕ)^2201*25000000000000000000^512 ≤ 2177686483256669^512*20000^2201 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2273 20000 2177686483256669 25000000000000000000 2201 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2273/20000 : ℝ)) (X := (2177686483256669/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2201 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14767/100000 : ℝ) ^ (2201/512 : ℝ) ≤ (26849133085137259/100000000000000000000 : ℝ) := by
    have hpowers : (14767/100000 : ℝ)^2201 ≤ (26849133085137259/100000000000000000000 : ℝ)^512 := by
      have hnat : (14767 : ℕ)^2201*100000000000000000000^512 ≤ 26849133085137259^512*100000^2201 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14767 100000 26849133085137259 100000000000000000000 2201 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14767/100000 : ℝ)) (X := (26849133085137259/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2201 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502177686483256669/12500000000000000000 : ℝ) ≤ (2500101308583119/2500000000000000 : ℝ) ^ (2201/512 : ℝ) := by
    have hpowers : (12502177686483256669/12500000000000000000 : ℝ)^512 ≤ (2500101308583119/2500000000000000 : ℝ)^2201 := by
      have hnat : (12502177686483256669 : ℕ)^512*2500000000000000^2201 ≤ 2500101308583119^2201*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502177686483256669 12500000000000000000 2500101308583119 2500000000000000 512 2201 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500101308583119/2500000000000000 : ℝ)) (X := (12502177686483256669/12500000000000000000 : ℝ)) (by norm_num) 2201 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (20007111975803632787/20000000000000000000 : ℝ) ≤ (250020677163189/250000000000000 : ℝ) ^ (2201/512 : ℝ) := by
    have hpowers : (20007111975803632787/20000000000000000000 : ℝ)^512 ≤ (250020677163189/250000000000000 : ℝ)^2201 := by
      have hnat : (20007111975803632787 : ℕ)^512*250000000000000^2201 ≤ 250020677163189^2201*20000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20007111975803632787 20000000000000000000 250020677163189 250000000000000 512 2201 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250020677163189/250000000000000 : ℝ)) (X := (20007111975803632787/20000000000000000000 : ℝ)) (by norm_num) 2201 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50026849133085137259/50000000000000000000 : ℝ) ≤ (2500312234680661/2500000000000000 : ℝ) ^ (2201/512 : ℝ) := by
    have hpowers : (50026849133085137259/50000000000000000000 : ℝ)^512 ≤ (2500312234680661/2500000000000000 : ℝ)^2201 := by
      have hnat : (50026849133085137259 : ℕ)^512*2500000000000000^2201 ≤ 2500312234680661^2201*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026849133085137259 50000000000000000000 2500312234680661 2500000000000000 512 2201 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500312234680661/2500000000000000 : ℝ)) (X := (50026849133085137259/50000000000000000000 : ℝ)) (by norm_num) 2201 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2177686483256669/25000000000000000000 : ℝ) ≤ ((1062868434587650751/1063125000000000000 : ℝ)+2*(105463048771/85050000000000 : ℝ)*(2273/20000 : ℝ))^(2201/512 : ℝ) := by
    rw [show (1062868434587650751/1063125000000000000 : ℝ)+2*(105463048771/85050000000000 : ℝ)*(2273/20000 : ℝ)=(2500101308583119/2500000000000000 : ℝ) by norm_num, show 1+2*(2177686483256669/25000000000000000000 : ℝ)=(12502177686483256669/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(26849133085137259/100000000000000000000 : ℝ)+(2177686483256669/25000000000000000000 : ℝ) ≤ ((1062868434587650751/1063125000000000000 : ℝ)+(105463048771/85050000000000 : ℝ)*((14767/100000 : ℝ)+(2273/20000 : ℝ)))^(2201/512 : ℝ) := by
    rw [show (1062868434587650751/1063125000000000000 : ℝ)+(105463048771/85050000000000 : ℝ)*((14767/100000 : ℝ)+(2273/20000 : ℝ))=(250020677163189/250000000000000 : ℝ) by norm_num, show 1+(26849133085137259/100000000000000000000 : ℝ)+(2177686483256669/25000000000000000000 : ℝ)=(20007111975803632787/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(26849133085137259/100000000000000000000 : ℝ) ≤ ((1062868434587650751/1063125000000000000 : ℝ)+2*(105463048771/85050000000000 : ℝ)*(14767/100000 : ℝ))^(2201/512 : ℝ) := by
    rw [show (1062868434587650751/1063125000000000000 : ℝ)+2*(105463048771/85050000000000 : ℝ)*(14767/100000 : ℝ)=(2500312234680661/2500000000000000 : ℝ) by norm_num, show 1+2*(26849133085137259/100000000000000000000 : ℝ)=(50026849133085137259/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1062868434587650751/1063125000000000000 : ℝ)*(X 1 0+X 2 0)+(105463048771/85050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2201/512 : ℝ)) (lo := (2273/20000 : ℝ)) (hi := (14767/100000 : ℝ)) (c := (1062868434587650751/1063125000000000000 : ℝ)) (alpha := (105463048771/85050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1062868434587650751/1063125000000000000 : ℝ)*(X 0 1+X 2 1)+(105463048771/85050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2201/512 : ℝ)) (lo := (2273/20000 : ℝ)) (hi := (14767/100000 : ℝ)) (c := (1062868434587650751/1063125000000000000 : ℝ)) (alpha := (105463048771/85050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1062868434587650751/1063125000000000000 : ℝ)*(X 0 2+X 1 2)+(105463048771/85050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2201/512 : ℝ)) (lo := (2273/20000 : ℝ)) (hi := (14767/100000 : ℝ)) (c := (1062868434587650751/1063125000000000000 : ℝ)) (alpha := (105463048771/85050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1959828381/10000000000 : ℝ)*X 0 0+(337968657/625000000 : ℝ)*X 0 1+(2623604503/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1443_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((3341893/6250000 : ℝ)*X 1 0+(-1020712413/5000000000 : ℝ)*X 1 1+(5247209009/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1443_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347028799/10000000000 : ℝ)*X 2 0+(327950563/625000000 : ℝ)*X 2 1+(-510356207/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1443_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((172035393/400000000 : ℝ)*X 0 0+(4129771803/10000000000 : ℝ)*X 0 1+(139947221/312500000 : ℝ)*X 0 2+(172035393/400000000 : ℝ)*X 1 0+(4129771803/10000000000 : ℝ)*X 1 1+(139947221/312500000 : ℝ)*X 1 2+(172035393/400000000 : ℝ)*X 2 0+(4129771803/10000000000 : ℝ)*X 2 1+(139947221/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1443_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-979919759/5000000000 : ℝ)*X 0 0+(5247787881/10000000000 : ℝ)*X 0 1+(1351729171/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1443_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326325371/2500000000 : ℝ)*X 1 0+(-1881717079/10000000000 : ℝ)*X 1 1+(5406916663/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1443_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((663162673/1250000000 : ℝ)*X 2 0+(216276669/400000000 : ℝ)*X 2 1+(-470429283/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1443_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4300909151/10000000000 : ℝ)*X 0 0+(2238526163/5000000000 : ℝ)*X 0 1+(4131037099/10000000000 : ℝ)*X 0 2+(4300909151/10000000000 : ℝ)*X 1 0+(2238526163/5000000000 : ℝ)*X 1 1+(4131037099/10000000000 : ℝ)*X 1 2+(4300909151/10000000000 : ℝ)*X 2 0+(2238526163/5000000000 : ℝ)*X 2 1+(4131037099/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1443_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (139369842217856900485919/13671875000000000000000000000 : ℝ) := by norm_num
    linear_combination (57581839/3125000000000 : ℝ)*(base19) + (857849049/50000000000000 : ℝ)*(base23) + (67241011/100000000000000 : ℝ)*(lower2) + (1022743/400000000000 : ℝ)*(upper3) + (32256577/20000000000000 : ℝ)*(upper5) + (4553972773117863/100000000000000 : ℝ)*(major0) + (4553972773117863/100000000000000 : ℝ)*(major1) + (4553972773117863/100000000000000 : ℝ)*(major2) + (6238752345148991/100000000000000 : ℝ)*(sp0) + (6238789445185983/100000000000000 : ℝ)*(sp1) + (6238789572106733/100000000000000 : ℝ)*(sp2) + (2869134507772549/100000000000000 : ℝ)*(sp3) + (243391599/625000000000 : ℝ)*(sp4) + (1941086139/10000000000000 : ℝ)*(sp7) + (2869153918633939/100000000000000 : ℝ)*(f.failure) + (6238791287804831/100000000000000 : ℝ)*(f.sum) + (4351077951979/1417500000000000000000000000 : ℝ)*base66 + (150750246883563371/35437500000000000000000000000000 : ℝ)*base67 + (261998757410125871/35437500000000000000000000000000 : ℝ)*base69 + (194953077987813371/35437500000000000000000000000000 : ℝ)*base71 + (17298012090367/2835000000000000000000000000 : ℝ)*base73 + (434753970888438371/35437500000000000000000000000000 : ℝ)*base75 + (17512214661499129/35437500000000000000000000000000 : ℝ)*base78 + (342879102949563371/35437500000000000000000000000000 : ℝ)*base79 + (2615285103527/708750000000000000000000000 : ℝ)*base82 + (42195861/10000000000000000000000 : ℝ)*base90 + (42195861/10000000000000000000000 : ℝ)*base92 + (42195861/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (26945770441099553037990757/4429687500000000000000000000000 : ℝ) := by norm_num
    linear_combination (206603447/20000000000000 : ℝ)*(base19) + (260184757/25000000000000 : ℝ)*(base23) + (365396219/100000000000000 : ℝ)*(lower1) + (76599027/100000000000000 : ℝ)*(upper3) + (71976273/100000000000000 : ℝ)*(lower4) + (124747197/100000000000000 : ℝ)*(upper5) + (4587113868855389/100000000000000 : ℝ)*(major0) + (4587113868855389/100000000000000 : ℝ)*(major1) + (4587113868855389/100000000000000 : ℝ)*(major2) + (1207291589/100000000000000 : ℝ)*(sp1) + (6284193626586949/100000000000000 : ℝ)*(sp4) + (2010941243609/32000000000 : ℝ)*(sp5) + (6284192585847921/100000000000000 : ℝ)*(sp6) + (180627119272331/6250000000000 : ℝ)*(sp7) + (180627119272331/6250000000000 : ℝ)*(f.failure) + (6284193626586949/100000000000000 : ℝ)*(f.sum) + (11048387735183/2126250000000000000000000000 : ℝ)*base66 + (872301274186327861/106312500000000000000000000000000 : ℝ)*base68 + (321894442896015361/106312500000000000000000000000000 : ℝ)*base70 + (100215336282015361/106312500000000000000000000000000 : ℝ)*base72 + (3394385481197/8505000000000000000000000000 : ℝ)*base74 + (1957072659587265361/106312500000000000000000000000000 : ℝ)*base76 + (546715153670234639/106312500000000000000000000000000 : ℝ)*base77 + (1085608125989827861/106312500000000000000000000000000 : ℝ)*base80 + (24649451788411/4252500000000000000000000000 : ℝ)*base82 + (4538131/625000000000000000000 : ℝ)*base89 + (4538131/625000000000000000000 : ℝ)*base91 + (4538131/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1443_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158721801/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14767/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2273/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1421/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3691/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1443_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1443_s7_0 (p : ℝ) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-979915581/5000000000 : ℝ)*x 0 + (108149551/200000000 : ℝ)*x 1 + (81987939/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (979915581/5000000000 : ℝ)^4403 ≤ (11959878555067/100000000000000 : ℝ)^3379 := by
    have hnat : (979915581 : ℕ)^4403*100000000000000^3379 ≤ 11959878555067^3379*5000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      979915581 5000000000 11959878555067 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (108149551/200000000 : ℝ)^4403 ≤ (44882728096219/100000000000000 : ℝ)^3379 := by
    have hnat : (108149551 : ℕ)^4403*100000000000000^3379 ≤ 44882728096219^3379*200000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108149551 200000000 44882728096219 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (81987939/156250000 : ℝ)^4403 ≤ (43157393331007/100000000000000 : ℝ)^3379 := by
    have hnat : (81987939 : ℕ)^4403*100000000000000^3379 ≤ 43157393331007^3379*156250000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81987939 156250000 43157393331007 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4403/1024 : ℝ)) 4403 3379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-979915581/5000000000 : ℝ), (108149551/200000000 : ℝ), (81987939/156250000 : ℝ)] ![(11959878555067/100000000000000 : ℝ), (44882728096219/100000000000000 : ℝ), (43157393331007/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-979915581/5000000000 : ℝ)|^4403 ≤ (11959878555067/100000000000000 : ℝ)^3379
        have hw : |(-979915581/5000000000 : ℝ)|=(979915581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(108149551/200000000 : ℝ)|^4403 ≤ (44882728096219/100000000000000 : ℝ)^3379
        have hw : |(108149551/200000000 : ℝ)|=(108149551/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(81987939/156250000 : ℝ)|^4403 ≤ (43157393331007/100000000000000 : ℝ)^3379
        have hw : |(81987939/156250000 : ℝ)|=(81987939/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1443_s7_1 (p : ℝ) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069404779/2000000000 : ℝ)*x 0 + (-2041406007/10000000000 : ℝ)*x 1 + (5247228079/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069404779/2000000000 : ℝ)^4403 ≤ (2764375278409/6250000000000 : ℝ)^3379 := by
    have hnat : (1069404779 : ℕ)^4403*6250000000000^3379 ≤ 2764375278409^3379*2000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069404779 2000000000 2764375278409 6250000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2041406007/10000000000 : ℝ)^4403 ≤ (6306301191639/50000000000000 : ℝ)^3379 := by
    have hnat : (2041406007 : ℕ)^4403*50000000000000^3379 ≤ 6306301191639^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2041406007 10000000000 6306301191639 50000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5247228079/10000000000 : ℝ)^4403 ≤ (43157393148813/100000000000000 : ℝ)^3379 := by
    have hnat : (5247228079 : ℕ)^4403*100000000000000^3379 ≤ 43157393148813^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247228079 10000000000 43157393148813 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4403/1024 : ℝ)) 4403 3379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069404779/2000000000 : ℝ), (-2041406007/10000000000 : ℝ), (5247228079/10000000000 : ℝ)] ![(2764375278409/6250000000000 : ℝ), (6306301191639/50000000000000 : ℝ), (43157393148813/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069404779/2000000000 : ℝ)|^4403 ≤ (2764375278409/6250000000000 : ℝ)^3379
        have hw : |(1069404779/2000000000 : ℝ)|=(1069404779/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2041406007/10000000000 : ℝ)|^4403 ≤ (6306301191639/50000000000000 : ℝ)^3379
        have hw : |(-2041406007/10000000000 : ℝ)|=(2041406007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5247228079/10000000000 : ℝ)|^4403 ≤ (43157393148813/100000000000000 : ℝ)^3379
        have hw : |(5247228079/10000000000 : ℝ)|=(5247228079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1443_s7_2 (p : ℝ) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347023463/10000000000 : ℝ)*x 0 + (2623614427/5000000000 : ℝ)*x 1 + (-2041405553/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347023463/10000000000 : ℝ)^4403 ≤ (44229999798157/100000000000000 : ℝ)^3379 := by
    have hnat : (5347023463 : ℕ)^4403*100000000000000^3379 ≤ 44229999798157^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347023463 10000000000 44229999798157 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623614427/5000000000 : ℝ)^4403 ≤ (43157401454727/100000000000000 : ℝ)^3379 := by
    have hnat : (2623614427 : ℕ)^4403*100000000000000^3379 ≤ 43157401454727^3379*5000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623614427 5000000000 43157401454727 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2041405553/10000000000 : ℝ)^4403 ≤ (6306299364121/50000000000000 : ℝ)^3379 := by
    have hnat : (2041405553 : ℕ)^4403*50000000000000^3379 ≤ 6306299364121^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2041405553 10000000000 6306299364121 50000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4403/1024 : ℝ)) 4403 3379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347023463/10000000000 : ℝ), (2623614427/5000000000 : ℝ), (-2041405553/10000000000 : ℝ)] ![(44229999798157/100000000000000 : ℝ), (43157401454727/100000000000000 : ℝ), (6306299364121/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347023463/10000000000 : ℝ)|^4403 ≤ (44229999798157/100000000000000 : ℝ)^3379
        have hw : |(5347023463/10000000000 : ℝ)|=(5347023463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623614427/5000000000 : ℝ)|^4403 ≤ (43157401454727/100000000000000 : ℝ)^3379
        have hw : |(2623614427/5000000000 : ℝ)|=(2623614427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2041405553/10000000000 : ℝ)|^4403 ≤ (6306299364121/50000000000000 : ℝ)^3379
        have hw : |(-2041405553/10000000000 : ℝ)|=(2041405553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1443_s7_3 (p : ℝ) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (860177149/2000000000 : ℝ)*x 0 + (4129817119/10000000000 : ℝ)*x 1 + (4478265947/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (860177149/2000000000 : ℝ)^4403 ≤ (16652455367727/50000000000000 : ℝ)^3379 := by
    have hnat : (860177149 : ℕ)^4403*50000000000000^3379 ≤ 16652455367727^3379*2000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      860177149 2000000000 16652455367727 50000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4129817119/10000000000 : ℝ)^4403 ≤ (31589251210747/100000000000000 : ℝ)^3379 := by
    have hnat : (4129817119 : ℕ)^4403*100000000000000^3379 ≤ 31589251210747^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4129817119 10000000000 31589251210747 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4478265947/10000000000 : ℝ)^4403 ≤ (17552919020557/50000000000000 : ℝ)^3379 := by
    have hnat : (4478265947 : ℕ)^4403*50000000000000^3379 ≤ 17552919020557^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4478265947 10000000000 17552919020557 50000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4403/1024 : ℝ)) 4403 3379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(860177149/2000000000 : ℝ), (4129817119/10000000000 : ℝ), (4478265947/10000000000 : ℝ)] ![(16652455367727/50000000000000 : ℝ), (31589251210747/100000000000000 : ℝ), (17552919020557/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(860177149/2000000000 : ℝ)|^4403 ≤ (16652455367727/50000000000000 : ℝ)^3379
        have hw : |(860177149/2000000000 : ℝ)|=(860177149/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4129817119/10000000000 : ℝ)|^4403 ≤ (31589251210747/100000000000000 : ℝ)^3379
        have hw : |(4129817119/10000000000 : ℝ)|=(4129817119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4478265947/10000000000 : ℝ)|^4403 ≤ (17552919020557/50000000000000 : ℝ)^3379
        have hw : |(4478265947/10000000000 : ℝ)|=(4478265947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1443_s7_4 (p : ℝ) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1959841817/10000000000 : ℝ)*x 0 + (5247807193/10000000000 : ℝ)*x 1 + (337930991/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1959841817/10000000000 : ℝ)^4403 ≤ (11959963282181/100000000000000 : ℝ)^3379 := by
    have hnat : (1959841817 : ℕ)^4403*100000000000000^3379 ≤ 11959963282181^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1959841817 10000000000 11959963282181 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247807193/10000000000 : ℝ)^4403 ≤ (21581799898167/50000000000000 : ℝ)^3379 := by
    have hnat : (5247807193 : ℕ)^4403*50000000000000^3379 ≤ 21581799898167^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247807193 10000000000 21581799898167 50000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337930991/625000000 : ℝ)^4403 ≤ (11219109227573/25000000000000 : ℝ)^3379 := by
    have hnat : (337930991 : ℕ)^4403*25000000000000^3379 ≤ 11219109227573^3379*625000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337930991 625000000 11219109227573 25000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4403/1024 : ℝ)) 4403 3379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1959841817/10000000000 : ℝ), (5247807193/10000000000 : ℝ), (337930991/625000000 : ℝ)] ![(11959963282181/100000000000000 : ℝ), (21581799898167/50000000000000 : ℝ), (11219109227573/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1959841817/10000000000 : ℝ)|^4403 ≤ (11959963282181/100000000000000 : ℝ)^3379
        have hw : |(-1959841817/10000000000 : ℝ)|=(1959841817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247807193/10000000000 : ℝ)|^4403 ≤ (21581799898167/50000000000000 : ℝ)^3379
        have hw : |(5247807193/10000000000 : ℝ)|=(5247807193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(337930991/625000000 : ℝ)|^4403 ≤ (11219109227573/25000000000000 : ℝ)^3379
        have hw : |(337930991/625000000 : ℝ)|=(337930991/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1443_s7_5 (p : ℝ) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4300911169/10000000000 : ℝ)*x 0 + (4477007851/10000000000 : ℝ)*x 1 + (1032770157/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4300911169/10000000000 : ℝ)^4403 ≤ (16652583637739/50000000000000 : ℝ)^3379 := by
    have hnat : (4300911169 : ℕ)^4403*50000000000000^3379 ≤ 16652583637739^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4300911169 10000000000 16652583637739 50000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4477007851/10000000000 : ℝ)^4403 ≤ (1096655855829/3125000000000 : ℝ)^3379 := by
    have hnat : (4477007851 : ℕ)^4403*3125000000000^3379 ≤ 1096655855829^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4477007851 10000000000 1096655855829 3125000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1032770157/2500000000 : ℝ)^4403 ≤ (31601845320571/100000000000000 : ℝ)^3379 := by
    have hnat : (1032770157 : ℕ)^4403*100000000000000^3379 ≤ 31601845320571^3379*2500000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1032770157 2500000000 31601845320571 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4403/1024 : ℝ)) 4403 3379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4300911169/10000000000 : ℝ), (4477007851/10000000000 : ℝ), (1032770157/2500000000 : ℝ)] ![(16652583637739/50000000000000 : ℝ), (1096655855829/3125000000000 : ℝ), (31601845320571/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4300911169/10000000000 : ℝ)|^4403 ≤ (16652583637739/50000000000000 : ℝ)^3379
        have hw : |(4300911169/10000000000 : ℝ)|=(4300911169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4477007851/10000000000 : ℝ)|^4403 ≤ (1096655855829/3125000000000 : ℝ)^3379
        have hw : |(4477007851/10000000000 : ℝ)|=(4477007851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1032770157/2500000000 : ℝ)|^4403 ≤ (31601845320571/100000000000000 : ℝ)^3379
        have hw : |(1032770157/2500000000 : ℝ)|=(1032770157/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1443_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158721801/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3691/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1421/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (11369/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3691/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3691/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1421/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3691/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1421/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3691/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1421/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3691/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1421/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3691/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1421/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3691/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1421/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1421/12500 : ℝ) ^ (2201/512 : ℝ) ≤ (4360317397657191/50000000000000000000 : ℝ) := by
    have hpowers : (1421/12500 : ℝ)^2201 ≤ (4360317397657191/50000000000000000000 : ℝ)^512 := by
      have hnat : (1421 : ℕ)^2201*50000000000000000000^512 ≤ 4360317397657191^512*12500^2201 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1421 12500 4360317397657191 50000000000000000000 2201 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1421/12500 : ℝ)) (X := (4360317397657191/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2201 512 (by norm_num) hpowers
    exact h
  have hpowhi : (3691/25000 : ℝ) ^ (2201/512 : ℝ) ≤ (13412846375437467/50000000000000000000 : ℝ) := by
    have hpowers : (3691/25000 : ℝ)^2201 ≤ (13412846375437467/50000000000000000000 : ℝ)^512 := by
      have hnat : (3691 : ℕ)^2201*50000000000000000000^512 ≤ 13412846375437467^512*25000^2201 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3691 25000 13412846375437467 50000000000000000000 2201 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3691/25000 : ℝ)) (X := (13412846375437467/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2201 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004360317397657191/25000000000000000000 : ℝ) ≤ (1000040569434341/1000000000000000 : ℝ) ^ (2201/512 : ℝ) := by
    have hpowers : (25004360317397657191/25000000000000000000 : ℝ)^512 ≤ (1000040569434341/1000000000000000 : ℝ)^2201 := by
      have hnat : (25004360317397657191 : ℕ)^512*1000000000000000^2201 ≤ 1000040569434341^2201*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004360317397657191 25000000000000000000 1000040569434341 1000000000000000 512 2201 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000040569434341/1000000000000000 : ℝ)) (X := (25004360317397657191/25000000000000000000 : ℝ)) (by norm_num) 2201 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (25008886581886547329/25000000000000000000 : ℝ) ≤ (2500206692844279/2500000000000000 : ℝ) ^ (2201/512 : ℝ) := by
    have hpowers : (25008886581886547329/25000000000000000000 : ℝ)^512 ≤ (2500206692844279/2500000000000000 : ℝ)^2201 := by
      have hnat : (25008886581886547329 : ℕ)^512*2500000000000000^2201 ≤ 2500206692844279^2201*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25008886581886547329 25000000000000000000 2500206692844279 2500000000000000 512 2201 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500206692844279/2500000000000000 : ℝ)) (X := (25008886581886547329/25000000000000000000 : ℝ)) (by norm_num) 2201 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25013412846375437467/25000000000000000000 : ℝ) ≤ (5000623924205411/5000000000000000 : ℝ) ^ (2201/512 : ℝ) := by
    have hpowers : (25013412846375437467/25000000000000000000 : ℝ)^512 ≤ (5000623924205411/5000000000000000 : ℝ)^2201 := by
      have hnat : (25013412846375437467 : ℕ)^512*5000000000000000^2201 ≤ 5000623924205411^2201*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013412846375437467 25000000000000000000 5000623924205411 5000000000000000 512 2201 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000623924205411/5000000000000000 : ℝ)) (X := (25013412846375437467/25000000000000000000 : ℝ)) (by norm_num) 2201 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4360317397657191/50000000000000000000 : ℝ) ≤ ((4243975516318985093/4245000000000000000 : ℝ)+2*(210538516853/169800000000000 : ℝ)*(1421/12500 : ℝ))^(2201/512 : ℝ) := by
    rw [show (4243975516318985093/4245000000000000000 : ℝ)+2*(210538516853/169800000000000 : ℝ)*(1421/12500 : ℝ)=(1000040569434341/1000000000000000 : ℝ) by norm_num, show 1+2*(4360317397657191/50000000000000000000 : ℝ)=(25004360317397657191/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13412846375437467/50000000000000000000 : ℝ)+(4360317397657191/50000000000000000000 : ℝ) ≤ ((4243975516318985093/4245000000000000000 : ℝ)+(210538516853/169800000000000 : ℝ)*((3691/25000 : ℝ)+(1421/12500 : ℝ)))^(2201/512 : ℝ) := by
    rw [show (4243975516318985093/4245000000000000000 : ℝ)+(210538516853/169800000000000 : ℝ)*((3691/25000 : ℝ)+(1421/12500 : ℝ))=(2500206692844279/2500000000000000 : ℝ) by norm_num, show 1+(13412846375437467/50000000000000000000 : ℝ)+(4360317397657191/50000000000000000000 : ℝ)=(25008886581886547329/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13412846375437467/50000000000000000000 : ℝ) ≤ ((4243975516318985093/4245000000000000000 : ℝ)+2*(210538516853/169800000000000 : ℝ)*(3691/25000 : ℝ))^(2201/512 : ℝ) := by
    rw [show (4243975516318985093/4245000000000000000 : ℝ)+2*(210538516853/169800000000000 : ℝ)*(3691/25000 : ℝ)=(5000623924205411/5000000000000000 : ℝ) by norm_num, show 1+2*(13412846375437467/50000000000000000000 : ℝ)=(25013412846375437467/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4243975516318985093/4245000000000000000 : ℝ)*(X 1 0+X 2 0)+(210538516853/169800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2201/512 : ℝ)) (lo := (1421/12500 : ℝ)) (hi := (3691/25000 : ℝ)) (c := (4243975516318985093/4245000000000000000 : ℝ)) (alpha := (210538516853/169800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4243975516318985093/4245000000000000000 : ℝ)*(X 0 1+X 2 1)+(210538516853/169800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2201/512 : ℝ)) (lo := (1421/12500 : ℝ)) (hi := (3691/25000 : ℝ)) (c := (4243975516318985093/4245000000000000000 : ℝ)) (alpha := (210538516853/169800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4243975516318985093/4245000000000000000 : ℝ)*(X 0 2+X 1 2)+(210538516853/169800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2201/512 : ℝ)) (lo := (1421/12500 : ℝ)) (hi := (3691/25000 : ℝ)) (c := (4243975516318985093/4245000000000000000 : ℝ)) (alpha := (210538516853/169800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-979915581/5000000000 : ℝ)*X 0 0+(108149551/200000000 : ℝ)*X 0 1+(81987939/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1443_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069404779/2000000000 : ℝ)*X 1 0+(-2041406007/10000000000 : ℝ)*X 1 1+(5247228079/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1443_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347023463/10000000000 : ℝ)*X 2 0+(2623614427/5000000000 : ℝ)*X 2 1+(-2041405553/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1443_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((860177149/2000000000 : ℝ)*X 0 0+(4129817119/10000000000 : ℝ)*X 0 1+(4478265947/10000000000 : ℝ)*X 0 2+(860177149/2000000000 : ℝ)*X 1 0+(4129817119/10000000000 : ℝ)*X 1 1+(4478265947/10000000000 : ℝ)*X 1 2+(860177149/2000000000 : ℝ)*X 2 0+(4129817119/10000000000 : ℝ)*X 2 1+(4478265947/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1443_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1959841817/10000000000 : ℝ)*X 0 0+(5247807193/10000000000 : ℝ)*X 0 1+(337930991/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1443_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4300911169/10000000000 : ℝ)*X 0 0+(4477007851/10000000000 : ℝ)*X 0 1+(1032770157/2500000000 : ℝ)*X 0 2+(4300911169/10000000000 : ℝ)*X 1 0+(4477007851/10000000000 : ℝ)*X 1 1+(1032770157/2500000000 : ℝ)*X 1 2+(4300911169/10000000000 : ℝ)*X 2 0+(4477007851/10000000000 : ℝ)*X 2 1+(1032770157/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1443_s7_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (21037671732453469174499781/17687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2437951541/100000000000000 : ℝ)*(base19) + (76064657/10000000000000 : ℝ)*(base23) + (366519883/100000000000000 : ℝ)*(upper3) + (156818763/25000000000000 : ℝ)*(upper4) + (37974841/100000000000000 : ℝ)*(upper5) + (2277562226987583/50000000000000 : ℝ)*(major0) + (2277562226987583/50000000000000 : ℝ)*(major1) + (2277562226987583/50000000000000 : ℝ)*(major2) + (124806408049767/2000000000000 : ℝ)*(sp0) + (6240366914572399/100000000000000 : ℝ)*(sp1) + (624036859187737/10000000000000 : ℝ)*(sp2) + (1434933386492063/50000000000000 : ℝ)*(sp3) + (48950035589/100000000000000 : ℝ)*(sp4) + (1592849411/12500000000000 : ℝ)*(sp5) + (1434939757889707/50000000000000 : ℝ)*(f.failure) + (312018467626197/5000000000000 : ℝ)*(f.sum) + (924290025199/707500000000000000000000000 : ℝ)*base65 + (626714320319275073/70750000000000000000000000000000 : ℝ)*base67 + (336954461266025073/70750000000000000000000000000000 : ℝ)*base69 + (143312370868275073/70750000000000000000000000000000 : ℝ)*base71 + (310149366751/707500000000000000000000000 : ℝ)*base74 + (997625691623275073/70750000000000000000000000000000 : ℝ)*base75 + (383651897135474927/70750000000000000000000000000000 : ℝ)*base78 + (798502409257025073/70750000000000000000000000000000 : ℝ)*base79 + (12293070100393/1415000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (45597693/5000000000000000000000 : ℝ)*base90 + (45597693/5000000000000000000000 : ℝ)*base92 + (45597693/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1443_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158721801/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3691/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1421/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11369/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3691/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1443_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1443_box_0 (p : ℝ) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-360033993/2000000000 : ℝ)*x 0 + (538565719/1000000000 : ℝ)*x 1 + (215426267/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (360033993/2000000000 : ℝ)^4403 ≤ (10706254980991/100000000000000 : ℝ)^3379 := by
    have hnat : (360033993 : ℕ)^4403*100000000000000^3379 ≤ 10706254980991^3379*2000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      360033993 2000000000 10706254980991 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (538565719/1000000000 : ℝ)^4403 ≤ (44646875286711/100000000000000 : ℝ)^3379 := by
    have hnat : (538565719 : ℕ)^4403*100000000000000^3379 ≤ 44646875286711^3379*1000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538565719 1000000000 44646875286711 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215426267/400000000 : ℝ)^4403 ≤ (4464686972357/10000000000000 : ℝ)^3379 := by
    have hnat : (215426267 : ℕ)^4403*10000000000000^3379 ≤ 4464686972357^3379*400000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215426267 400000000 4464686972357 10000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4403/1024 : ℝ)) 4403 3379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-360033993/2000000000 : ℝ), (538565719/1000000000 : ℝ), (215426267/400000000 : ℝ)] ![(10706254980991/100000000000000 : ℝ), (44646875286711/100000000000000 : ℝ), (4464686972357/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-360033993/2000000000 : ℝ)|^4403 ≤ (10706254980991/100000000000000 : ℝ)^3379
        have hw : |(-360033993/2000000000 : ℝ)|=(360033993/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(538565719/1000000000 : ℝ)|^4403 ≤ (44646875286711/100000000000000 : ℝ)^3379
        have hw : |(538565719/1000000000 : ℝ)|=(538565719/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(215426267/400000000 : ℝ)|^4403 ≤ (4464686972357/10000000000000 : ℝ)^3379
        have hw : |(215426267/400000000 : ℝ)|=(215426267/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1443_box_1 (p : ℝ) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5286158479/10000000000 : ℝ)*x 0 + (-1936924539/10000000000 : ℝ)*x 1 + (5385655557/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5286158479/10000000000 : ℝ)^4403 ≤ (43575090518257/100000000000000 : ℝ)^3379 := by
    have hnat : (5286158479 : ℕ)^4403*100000000000000^3379 ≤ 43575090518257^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5286158479 10000000000 43575090518257 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1936924539/10000000000 : ℝ)^4403 ≤ (11778051819047/100000000000000 : ℝ)^3379 := by
    have hnat : (1936924539 : ℕ)^4403*100000000000000^3379 ≤ 11778051819047^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1936924539 10000000000 11778051819047 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5385655557/10000000000 : ℝ)^4403 ≤ (22323428823347/50000000000000 : ℝ)^3379 := by
    have hnat : (5385655557 : ℕ)^4403*50000000000000^3379 ≤ 22323428823347^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385655557 10000000000 22323428823347 50000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4403/1024 : ℝ)) 4403 3379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5286158479/10000000000 : ℝ), (-1936924539/10000000000 : ℝ), (5385655557/10000000000 : ℝ)] ![(43575090518257/100000000000000 : ℝ), (11778051819047/100000000000000 : ℝ), (22323428823347/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5286158479/10000000000 : ℝ)|^4403 ≤ (43575090518257/100000000000000 : ℝ)^3379
        have hw : |(5286158479/10000000000 : ℝ)|=(5286158479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1936924539/10000000000 : ℝ)|^4403 ≤ (11778051819047/100000000000000 : ℝ)^3379
        have hw : |(-1936924539/10000000000 : ℝ)|=(1936924539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5385655557/10000000000 : ℝ)|^4403 ≤ (22323428823347/50000000000000 : ℝ)^3379
        have hw : |(5385655557/10000000000 : ℝ)|=(5385655557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1443_box_2 (p : ℝ) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5286157707/10000000000 : ℝ)*x 0 + (5385656677/10000000000 : ℝ)*x 1 + (-1936924059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5286157707/10000000000 : ℝ)^4403 ≤ (2178754111297/5000000000000 : ℝ)^3379 := by
    have hnat : (5286157707 : ℕ)^4403*5000000000000^3379 ≤ 2178754111297^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5286157707 10000000000 2178754111297 5000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5385656677/10000000000 : ℝ)^4403 ≤ (1785874789807/4000000000000 : ℝ)^3379 := by
    have hnat : (5385656677 : ℕ)^4403*4000000000000^3379 ≤ 1785874789807^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385656677 10000000000 1785874789807 4000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1936924059/10000000000 : ℝ)^4403 ≤ (1177804801573/10000000000000 : ℝ)^3379 := by
    have hnat : (1936924059 : ℕ)^4403*10000000000000^3379 ≤ 1177804801573^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1936924059 10000000000 1177804801573 10000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4403/1024 : ℝ)) 4403 3379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5286157707/10000000000 : ℝ), (5385656677/10000000000 : ℝ), (-1936924059/10000000000 : ℝ)] ![(2178754111297/5000000000000 : ℝ), (1785874789807/4000000000000 : ℝ), (1177804801573/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5286157707/10000000000 : ℝ)|^4403 ≤ (2178754111297/5000000000000 : ℝ)^3379
        have hw : |(5286157707/10000000000 : ℝ)|=(5286157707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5385656677/10000000000 : ℝ)|^4403 ≤ (1785874789807/4000000000000 : ℝ)^3379
        have hw : |(5385656677/10000000000 : ℝ)|=(5385656677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1936924059/10000000000 : ℝ)|^4403 ≤ (1177804801573/10000000000000 : ℝ)^3379
        have hw : |(-1936924059/10000000000 : ℝ)|=(1936924059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1443_box_3 (p : ℝ) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4446909551/10000000000 : ℝ)*x 0 + (2115778299/5000000000 : ℝ)*x 1 + (4231556083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4446909551/10000000000 : ℝ)^4403 ≤ (8696469759899/25000000000000 : ℝ)^3379 := by
    have hnat : (4446909551 : ℕ)^4403*25000000000000^3379 ≤ 8696469759899^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4446909551 10000000000 8696469759899 25000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2115778299/5000000000 : ℝ)^4403 ≤ (32607063062123/100000000000000 : ℝ)^3379 := by
    have hnat : (2115778299 : ℕ)^4403*100000000000000^3379 ≤ 32607063062123^3379*5000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115778299 5000000000 32607063062123 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4231556083/10000000000 : ℝ)^4403 ≤ (32607057891067/100000000000000 : ℝ)^3379 := by
    have hnat : (4231556083 : ℕ)^4403*100000000000000^3379 ≤ 32607057891067^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4231556083 10000000000 32607057891067 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4403/1024 : ℝ)) 4403 3379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4446909551/10000000000 : ℝ), (2115778299/5000000000 : ℝ), (4231556083/10000000000 : ℝ)] ![(8696469759899/25000000000000 : ℝ), (32607063062123/100000000000000 : ℝ), (32607057891067/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4446909551/10000000000 : ℝ)|^4403 ≤ (8696469759899/25000000000000 : ℝ)^3379
        have hw : |(4446909551/10000000000 : ℝ)|=(4446909551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2115778299/5000000000 : ℝ)|^4403 ≤ (32607063062123/100000000000000 : ℝ)^3379
        have hw : |(2115778299/5000000000 : ℝ)|=(2115778299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4231556083/10000000000 : ℝ)|^4403 ≤ (32607057891067/100000000000000 : ℝ)^3379
        have hw : |(4231556083/10000000000 : ℝ)|=(4231556083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1443_box_4 (p : ℝ) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-265277341/1250000000 : ℝ)*x 0 + (2633362501/5000000000 : ℝ)*x 1 + (5266724783/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265277341/1250000000 : ℝ)^4403 ≤ (13267071844061/100000000000000 : ℝ)^3379 := by
    have hnat : (265277341 : ℕ)^4403*100000000000000^3379 ≤ 13267071844061^3379*1250000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265277341 1250000000 13267071844061 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633362501/5000000000 : ℝ)^4403 ≤ (5420808155169/12500000000000 : ℝ)^3379 := by
    have hnat : (2633362501 : ℕ)^4403*12500000000000^3379 ≤ 5420808155169^3379*5000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633362501 5000000000 5420808155169 12500000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266724783/10000000000 : ℝ)^4403 ≤ (21683231445811/50000000000000 : ℝ)^3379 := by
    have hnat : (5266724783 : ℕ)^4403*50000000000000^3379 ≤ 21683231445811^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266724783 10000000000 21683231445811 50000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4403/1024 : ℝ)) 4403 3379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-265277341/1250000000 : ℝ), (2633362501/5000000000 : ℝ), (5266724783/10000000000 : ℝ)] ![(13267071844061/100000000000000 : ℝ), (5420808155169/12500000000000 : ℝ), (21683231445811/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-265277341/1250000000 : ℝ)|^4403 ≤ (13267071844061/100000000000000 : ℝ)^3379
        have hw : |(-265277341/1250000000 : ℝ)|=(265277341/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633362501/5000000000 : ℝ)|^4403 ≤ (5420808155169/12500000000000 : ℝ)^3379
        have hw : |(2633362501/5000000000 : ℝ)|=(2633362501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266724783/10000000000 : ℝ)|^4403 ≤ (21683231445811/50000000000000 : ℝ)^3379
        have hw : |(5266724783/10000000000 : ℝ)|=(5266724783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1443_box_5 (p : ℝ) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2684672557/5000000000 : ℝ)*x 0 + (-992648753/5000000000 : ℝ)*x 1 + (5266725401/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684672557/5000000000 : ℝ)^4403 ≤ (11117687410757/25000000000000 : ℝ)^3379 := by
    have hnat : (2684672557 : ℕ)^4403*25000000000000^3379 ≤ 11117687410757^3379*5000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684672557 5000000000 11117687410757 25000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (992648753/5000000000 : ℝ)^4403 ≤ (486511232843/4000000000000 : ℝ)^3379 := by
    have hnat : (992648753 : ℕ)^4403*4000000000000^3379 ≤ 486511232843^3379*5000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      992648753 5000000000 486511232843 4000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266725401/10000000000 : ℝ)^4403 ≤ (43366469522367/100000000000000 : ℝ)^3379 := by
    have hnat : (5266725401 : ℕ)^4403*100000000000000^3379 ≤ 43366469522367^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266725401 10000000000 43366469522367 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4403/1024 : ℝ)) 4403 3379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684672557/5000000000 : ℝ), (-992648753/5000000000 : ℝ), (5266725401/10000000000 : ℝ)] ![(11117687410757/25000000000000 : ℝ), (486511232843/4000000000000 : ℝ), (43366469522367/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684672557/5000000000 : ℝ)|^4403 ≤ (11117687410757/25000000000000 : ℝ)^3379
        have hw : |(2684672557/5000000000 : ℝ)|=(2684672557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-992648753/5000000000 : ℝ)|^4403 ≤ (486511232843/4000000000000 : ℝ)^3379
        have hw : |(-992648753/5000000000 : ℝ)|=(992648753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266725401/10000000000 : ℝ)|^4403 ≤ (43366469522367/100000000000000 : ℝ)^3379
        have hw : |(5266725401/10000000000 : ℝ)|=(5266725401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1443_box_6 (p : ℝ) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1342336269/2500000000 : ℝ)*x 0 + (5266724387/10000000000 : ℝ)*x 1 + (-49632473/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1342336269/2500000000 : ℝ)^4403 ≤ (44470749232921/100000000000000 : ℝ)^3379 := by
    have hnat : (1342336269 : ℕ)^4403*100000000000000^3379 ≤ 44470749232921^3379*2500000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342336269 2500000000 44470749232921 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266724387/10000000000 : ℝ)^4403 ≤ (8673291728559/20000000000000 : ℝ)^3379 := by
    have hnat : (5266724387 : ℕ)^4403*20000000000000^3379 ≤ 8673291728559^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266724387 10000000000 8673291728559 20000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (49632473/250000000 : ℝ)^4403 ≤ (12162792109081/100000000000000 : ℝ)^3379 := by
    have hnat : (49632473 : ℕ)^4403*100000000000000^3379 ≤ 12162792109081^3379*250000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49632473 250000000 12162792109081 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4403/1024 : ℝ)) 4403 3379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1342336269/2500000000 : ℝ), (5266724387/10000000000 : ℝ), (-49632473/250000000 : ℝ)] ![(44470749232921/100000000000000 : ℝ), (8673291728559/20000000000000 : ℝ), (12162792109081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1342336269/2500000000 : ℝ)|^4403 ≤ (44470749232921/100000000000000 : ℝ)^3379
        have hw : |(1342336269/2500000000 : ℝ)|=(1342336269/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266724387/10000000000 : ℝ)|^4403 ≤ (8673291728559/20000000000000 : ℝ)^3379
        have hw : |(5266724387/10000000000 : ℝ)|=(5266724387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-49632473/250000000 : ℝ)|^4403 ≤ (12162792109081/100000000000000 : ℝ)^3379
        have hw : |(-49632473/250000000 : ℝ)|=(49632473/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1443_box_7 (p : ℝ) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4153796843/10000000000 : ℝ)*x 0 + (2189031503/5000000000 : ℝ)*x 1 + (1094515351/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4153796843/10000000000 : ℝ)^4403 ≤ (31828469624147/100000000000000 : ℝ)^3379 := by
    have hnat : (4153796843 : ℕ)^4403*100000000000000^3379 ≤ 31828469624147^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4153796843 10000000000 31828469624147 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2189031503/5000000000 : ℝ)^4403 ≤ (17042886653287/50000000000000 : ℝ)^3379 := by
    have hnat : (2189031503 : ℕ)^4403*50000000000000^3379 ≤ 17042886653287^3379*5000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2189031503 5000000000 17042886653287 50000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1094515351/2500000000 : ℝ)^4403 ≤ (34085757054301/100000000000000 : ℝ)^3379 := by
    have hnat : (1094515351 : ℕ)^4403*100000000000000^3379 ≤ 34085757054301^3379*2500000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094515351 2500000000 34085757054301 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4403/1024 : ℝ)) 4403 3379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4153796843/10000000000 : ℝ), (2189031503/5000000000 : ℝ), (1094515351/2500000000 : ℝ)] ![(31828469624147/100000000000000 : ℝ), (17042886653287/50000000000000 : ℝ), (34085757054301/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4153796843/10000000000 : ℝ)|^4403 ≤ (31828469624147/100000000000000 : ℝ)^3379
        have hw : |(4153796843/10000000000 : ℝ)|=(4153796843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2189031503/5000000000 : ℝ)|^4403 ≤ (17042886653287/50000000000000 : ℝ)^3379
        have hw : |(2189031503/5000000000 : ℝ)|=(2189031503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1094515351/2500000000 : ℝ)|^4403 ≤ (34085757054301/100000000000000 : ℝ)^3379
        have hw : |(1094515351/2500000000 : ℝ)|=(1094515351/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1443_box_8 (p : ℝ) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-256794431/1250000000 : ℝ)*x 0 + (5184398773/10000000000 : ℝ)*x 1 + (269981111/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (256794431/1250000000 : ℝ)^4403 ≤ (3179238756481/25000000000000 : ℝ)^3379 := by
    have hnat : (256794431 : ℕ)^4403*25000000000000^3379 ≤ 3179238756481^3379*1250000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256794431 1250000000 3179238756481 25000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5184398773/10000000000 : ℝ)^4403 ≤ (42485257165837/100000000000000 : ℝ)^3379 := by
    have hnat : (5184398773 : ℕ)^4403*100000000000000^3379 ≤ 42485257165837^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184398773 10000000000 42485257165837 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269981111/500000000 : ℝ)^4403 ≤ (22398893896043/50000000000000 : ℝ)^3379 := by
    have hnat : (269981111 : ℕ)^4403*50000000000000^3379 ≤ 22398893896043^3379*500000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269981111 500000000 22398893896043 50000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4403/1024 : ℝ)) 4403 3379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-256794431/1250000000 : ℝ), (5184398773/10000000000 : ℝ), (269981111/500000000 : ℝ)] ![(3179238756481/25000000000000 : ℝ), (42485257165837/100000000000000 : ℝ), (22398893896043/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-256794431/1250000000 : ℝ)|^4403 ≤ (3179238756481/25000000000000 : ℝ)^3379
        have hw : |(-256794431/1250000000 : ℝ)|=(256794431/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5184398773/10000000000 : ℝ)|^4403 ≤ (42485257165837/100000000000000 : ℝ)^3379
        have hw : |(5184398773/10000000000 : ℝ)|=(5184398773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269981111/500000000 : ℝ)|^4403 ≤ (22398893896043/50000000000000 : ℝ)^3379
        have hw : |(269981111/500000000 : ℝ)|=(269981111/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1443_box_9 (p : ℝ) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276385243/10000000000 : ℝ)*x 0 + (-1931118443/10000000000 : ℝ)*x 1 + (5399622429/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276385243/10000000000 : ℝ)^4403 ≤ (8694028450587/20000000000000 : ℝ)^3379 := by
    have hnat : (5276385243 : ℕ)^4403*20000000000000^3379 ≤ 8694028450587^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276385243 10000000000 8694028450587 20000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1931118443/10000000000 : ℝ)^4403 ≤ (11732067683811/100000000000000 : ℝ)^3379 := by
    have hnat : (1931118443 : ℕ)^4403*100000000000000^3379 ≤ 11732067683811^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1931118443 10000000000 11732067683811 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5399622429/10000000000 : ℝ)^4403 ≤ (22398895025761/50000000000000 : ℝ)^3379 := by
    have hnat : (5399622429 : ℕ)^4403*50000000000000^3379 ≤ 22398895025761^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399622429 10000000000 22398895025761 50000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4403/1024 : ℝ)) 4403 3379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276385243/10000000000 : ℝ), (-1931118443/10000000000 : ℝ), (5399622429/10000000000 : ℝ)] ![(8694028450587/20000000000000 : ℝ), (11732067683811/100000000000000 : ℝ), (22398895025761/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276385243/10000000000 : ℝ)|^4403 ≤ (8694028450587/20000000000000 : ℝ)^3379
        have hw : |(5276385243/10000000000 : ℝ)|=(5276385243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1931118443/10000000000 : ℝ)|^4403 ≤ (11732067683811/100000000000000 : ℝ)^3379
        have hw : |(-1931118443/10000000000 : ℝ)|=(1931118443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5399622429/10000000000 : ℝ)|^4403 ≤ (22398895025761/50000000000000 : ℝ)^3379
        have hw : |(5399622429/10000000000 : ℝ)|=(5399622429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1443_box_10 (p : ℝ) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2638192613/5000000000 : ℝ)*x 0 + (5399622641/10000000000 : ℝ)*x 1 + (-77244727/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638192613/5000000000 : ℝ)^4403 ≤ (8694028414087/20000000000000 : ℝ)^3379 := by
    have hnat : (2638192613 : ℕ)^4403*20000000000000^3379 ≤ 8694028414087^3379*5000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638192613 5000000000 8694028414087 20000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5399622641/10000000000 : ℝ)^4403 ≤ (4479779234339/10000000000000 : ℝ)^3379 := by
    have hnat : (5399622641 : ℕ)^4403*10000000000000^3379 ≤ 4479779234339^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399622641 10000000000 4479779234339 10000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (77244727/400000000 : ℝ)^4403 ≤ (733254097639/6250000000000 : ℝ)^3379 := by
    have hnat : (77244727 : ℕ)^4403*6250000000000^3379 ≤ 733254097639^3379*400000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      77244727 400000000 733254097639 6250000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4403/1024 : ℝ)) 4403 3379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638192613/5000000000 : ℝ), (5399622641/10000000000 : ℝ), (-77244727/400000000 : ℝ)] ![(8694028414087/20000000000000 : ℝ), (4479779234339/10000000000000 : ℝ), (733254097639/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638192613/5000000000 : ℝ)|^4403 ≤ (8694028414087/20000000000000 : ℝ)^3379
        have hw : |(2638192613/5000000000 : ℝ)|=(2638192613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5399622641/10000000000 : ℝ)|^4403 ≤ (4479779234339/10000000000000 : ℝ)^3379
        have hw : |(5399622641/10000000000 : ℝ)|=(5399622641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-77244727/400000000 : ℝ)|^4403 ≤ (733254097639/6250000000000 : ℝ)^3379
        have hw : |(-77244727/400000000 : ℝ)|=(77244727/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1443_box_11 (p : ℝ) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (70012043/156250000 : ℝ)*x 0 + (2107169443/5000000000 : ℝ)*x 1 + (4214338521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (70012043/156250000 : ℝ)^4403 ≤ (17565713148341/50000000000000 : ℝ)^3379 := by
    have hnat : (70012043 : ℕ)^4403*50000000000000^3379 ≤ 17565713148341^3379*156250000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70012043 156250000 17565713148341 50000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2107169443/5000000000 : ℝ)^4403 ≤ (4054286084003/12500000000000 : ℝ)^3379 := by
    have hnat : (2107169443 : ℕ)^4403*12500000000000^3379 ≤ 4054286084003^3379*5000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107169443 5000000000 4054286084003 12500000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4214338521/10000000000 : ℝ)^4403 ≤ (16217142505813/50000000000000 : ℝ)^3379 := by
    have hnat : (4214338521 : ℕ)^4403*50000000000000^3379 ≤ 16217142505813^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4214338521 10000000000 16217142505813 50000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4403/1024 : ℝ)) 4403 3379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(70012043/156250000 : ℝ), (2107169443/5000000000 : ℝ), (4214338521/10000000000 : ℝ)] ![(17565713148341/50000000000000 : ℝ), (4054286084003/12500000000000 : ℝ), (16217142505813/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(70012043/156250000 : ℝ)|^4403 ≤ (17565713148341/50000000000000 : ℝ)^3379
        have hw : |(70012043/156250000 : ℝ)|=(70012043/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2107169443/5000000000 : ℝ)|^4403 ≤ (4054286084003/12500000000000 : ℝ)^3379
        have hw : |(2107169443/5000000000 : ℝ)|=(2107169443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4214338521/10000000000 : ℝ)|^4403 ≤ (16217142505813/50000000000000 : ℝ)^3379
        have hw : |(4214338521/10000000000 : ℝ)|=(4214338521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1443_box_12 (p : ℝ) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-934094563/5000000000 : ℝ)*x 0 + (2732993133/5000000000 : ℝ)*x 1 + (5255592953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (934094563/5000000000 : ℝ)^4403 ≤ (5618187287211/50000000000000 : ℝ)^3379 := by
    have hnat : (934094563 : ℕ)^4403*50000000000000^3379 ≤ 5618187287211^3379*5000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      934094563 5000000000 5618187287211 50000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2732993133/5000000000 : ℝ)^4403 ≤ (455165616711/1000000000000 : ℝ)^3379 := by
    have hnat : (2732993133 : ℕ)^4403*1000000000000^3379 ≤ 455165616711^3379*5000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2732993133 5000000000 455165616711 1000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5255592953/10000000000 : ℝ)^4403 ≤ (43247063735801/100000000000000 : ℝ)^3379 := by
    have hnat : (5255592953 : ℕ)^4403*100000000000000^3379 ≤ 43247063735801^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255592953 10000000000 43247063735801 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4403/1024 : ℝ)) 4403 3379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-934094563/5000000000 : ℝ), (2732993133/5000000000 : ℝ), (5255592953/10000000000 : ℝ)] ![(5618187287211/50000000000000 : ℝ), (455165616711/1000000000000 : ℝ), (43247063735801/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-934094563/5000000000 : ℝ)|^4403 ≤ (5618187287211/50000000000000 : ℝ)^3379
        have hw : |(-934094563/5000000000 : ℝ)|=(934094563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2732993133/5000000000 : ℝ)|^4403 ≤ (455165616711/1000000000000 : ℝ)^3379
        have hw : |(2732993133/5000000000 : ℝ)|=(2732993133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5255592953/10000000000 : ℝ)|^4403 ≤ (43247063735801/100000000000000 : ℝ)^3379
        have hw : |(5255592953/10000000000 : ℝ)|=(5255592953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1443_box_13 (p : ℝ) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2688564933/5000000000 : ℝ)*x 0 + (-1989728313/10000000000 : ℝ)*x 1 + (5255591909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2688564933/5000000000 : ℝ)^4403 ≤ (22277391699307/50000000000000 : ℝ)^3379 := by
    have hnat : (2688564933 : ℕ)^4403*50000000000000^3379 ≤ 22277391699307^3379*5000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688564933 5000000000 22277391699307 50000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1989728313/10000000000 : ℝ)^4403 ≤ (6099082021497/50000000000000 : ℝ)^3379 := by
    have hnat : (1989728313 : ℕ)^4403*50000000000000^3379 ≤ 6099082021497^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1989728313 10000000000 6099082021497 50000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5255591909/10000000000 : ℝ)^4403 ≤ (5405881567691/12500000000000 : ℝ)^3379 := by
    have hnat : (5255591909 : ℕ)^4403*12500000000000^3379 ≤ 5405881567691^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255591909 10000000000 5405881567691 12500000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4403/1024 : ℝ)) 4403 3379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2688564933/5000000000 : ℝ), (-1989728313/10000000000 : ℝ), (5255591909/10000000000 : ℝ)] ![(22277391699307/50000000000000 : ℝ), (6099082021497/50000000000000 : ℝ), (5405881567691/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2688564933/5000000000 : ℝ)|^4403 ≤ (22277391699307/50000000000000 : ℝ)^3379
        have hw : |(2688564933/5000000000 : ℝ)|=(2688564933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1989728313/10000000000 : ℝ)|^4403 ≤ (6099082021497/50000000000000 : ℝ)^3379
        have hw : |(-1989728313/10000000000 : ℝ)|=(1989728313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5255591909/10000000000 : ℝ)|^4403 ≤ (5405881567691/12500000000000 : ℝ)^3379
        have hw : |(5255591909/10000000000 : ℝ)|=(5255591909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1443_box_14 (p : ℝ) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2688564983/5000000000 : ℝ)*x 0 + (5255592867/10000000000 : ℝ)*x 1 + (-1989726893/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2688564983/5000000000 : ℝ)^4403 ≤ (44554784478317/100000000000000 : ℝ)^3379 := by
    have hnat : (2688564983 : ℕ)^4403*100000000000000^3379 ≤ 44554784478317^3379*5000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688564983 5000000000 44554784478317 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5255592867/10000000000 : ℝ)^4403 ≤ (43247062813667/100000000000000 : ℝ)^3379 := by
    have hnat : (5255592867 : ℕ)^4403*100000000000000^3379 ≤ 43247062813667^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255592867 10000000000 43247062813667 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1989726893/10000000000 : ℝ)^4403 ≤ (12198152699431/100000000000000 : ℝ)^3379 := by
    have hnat : (1989726893 : ℕ)^4403*100000000000000^3379 ≤ 12198152699431^3379*10000000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1989726893 10000000000 12198152699431 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4403/1024 : ℝ)) 4403 3379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2688564983/5000000000 : ℝ), (5255592867/10000000000 : ℝ), (-1989726893/10000000000 : ℝ)] ![(44554784478317/100000000000000 : ℝ), (43247062813667/100000000000000 : ℝ), (12198152699431/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2688564983/5000000000 : ℝ)|^4403 ≤ (44554784478317/100000000000000 : ℝ)^3379
        have hw : |(2688564983/5000000000 : ℝ)|=(2688564983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5255592867/10000000000 : ℝ)|^4403 ≤ (43247062813667/100000000000000 : ℝ)^3379
        have hw : |(5255592867/10000000000 : ℝ)|=(5255592867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1989726893/10000000000 : ℝ)|^4403 ≤ (12198152699431/100000000000000 : ℝ)^3379
        have hw : |(-1989726893/10000000000 : ℝ)|=(1989726893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1443_box_15 (p : ℝ) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (128934669/312500000 : ℝ)*x 0 + (137242649/312500000 : ℝ)*x 1 + (1097941313/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (128934669/312500000 : ℝ)^4403 ≤ (7887577058231/25000000000000 : ℝ)^3379 := by
    have hnat : (128934669 : ℕ)^4403*25000000000000^3379 ≤ 7887577058231^3379*312500000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128934669 312500000 7887577058231 25000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (137242649/312500000 : ℝ)^4403 ≤ (1711242170991/5000000000000 : ℝ)^3379 := by
    have hnat : (137242649 : ℕ)^4403*5000000000000^3379 ≤ 1711242170991^3379*312500000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137242649 312500000 1711242170991 5000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1097941313/2500000000 : ℝ)^4403 ≤ (34224848334647/100000000000000 : ℝ)^3379 := by
    have hnat : (1097941313 : ℕ)^4403*100000000000000^3379 ≤ 34224848334647^3379*2500000000^4403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097941313 2500000000 34224848334647 100000000000000 4403 3379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4403/1024 : ℝ)) 4403 3379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(128934669/312500000 : ℝ), (137242649/312500000 : ℝ), (1097941313/2500000000 : ℝ)] ![(7887577058231/25000000000000 : ℝ), (1711242170991/5000000000000 : ℝ), (34224848334647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(128934669/312500000 : ℝ)|^4403 ≤ (7887577058231/25000000000000 : ℝ)^3379
        have hw : |(128934669/312500000 : ℝ)|=(128934669/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(137242649/312500000 : ℝ)|^4403 ≤ (1711242170991/5000000000000 : ℝ)^3379
        have hw : |(137242649/312500000 : ℝ)|=(137242649/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1097941313/2500000000 : ℝ)|^4403 ≤ (34224848334647/100000000000000 : ℝ)^3379
        have hw : |(1097941313/2500000000 : ℝ)|=(1097941313/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1443_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158721801/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3691/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11369/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(15727/25000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59141/100000 : ℝ) ∧ (3221/4000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84737/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3691/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11369/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3691/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11369/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3691/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11369/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3691/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11369/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3691/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11369/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3691/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11369/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11369/100000 : ℝ) ^ (2201/512 : ℝ) ≤ (8723932996387797/100000000000000000000 : ℝ) := by
    have hpowers : (11369/100000 : ℝ)^2201 ≤ (8723932996387797/100000000000000000000 : ℝ)^512 := by
      have hnat : (11369 : ℕ)^2201*100000000000000000000^512 ≤ 8723932996387797^512*100000^2201 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11369 100000 8723932996387797 100000000000000000000 2201 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11369/100000 : ℝ)) (X := (8723932996387797/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2201 512 (by norm_num) hpowers
    exact h
  have hpowhi : (3691/25000 : ℝ) ^ (2201/512 : ℝ) ≤ (13412846375437467/50000000000000000000 : ℝ) := by
    have hpowers : (3691/25000 : ℝ)^2201 ≤ (13412846375437467/50000000000000000000 : ℝ)^512 := by
      have hnat : (3691 : ℕ)^2201*50000000000000000000^512 ≤ 13412846375437467^512*25000^2201 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3691 25000 13412846375437467 50000000000000000000 2201 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3691/25000 : ℝ)) (X := (13412846375437467/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2201 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008723932996387797/50000000000000000000 : ℝ) ≤ (10000405847769391/10000000000000000 : ℝ) ^ (2201/512 : ℝ) := by
    have hpowers : (50008723932996387797/50000000000000000000 : ℝ)^512 ≤ (10000405847769391/10000000000000000 : ℝ)^2201 := by
      have hnat : (50008723932996387797 : ℕ)^512*10000000000000000^2201 ≤ 10000405847769391^2201*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008723932996387797 50000000000000000000 10000405847769391 10000000000000000 512 2201 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000405847769391/10000000000000000 : ℝ)) (X := (50008723932996387797/50000000000000000000 : ℝ)) (by norm_num) 2201 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100035549625747262731/100000000000000000000 : ℝ) ≤ (10000826848079453/10000000000000000 : ℝ) ^ (2201/512 : ℝ) := by
    have hpowers : (100035549625747262731/100000000000000000000 : ℝ)^512 ≤ (10000826848079453/10000000000000000 : ℝ)^2201 := by
      have hnat : (100035549625747262731 : ℕ)^512*10000000000000000^2201 ≤ 10000826848079453^2201*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100035549625747262731 100000000000000000000 10000826848079453 10000000000000000 512 2201 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000826848079453/10000000000000000 : ℝ)) (X := (100035549625747262731/100000000000000000000 : ℝ)) (by norm_num) 2201 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25013412846375437467/25000000000000000000 : ℝ) ≤ (2000249569677903/2000000000000000 : ℝ) ^ (2201/512 : ℝ) := by
    have hpowers : (25013412846375437467/25000000000000000000 : ℝ)^512 ≤ (2000249569677903/2000000000000000 : ℝ)^2201 := by
      have hnat : (25013412846375437467 : ℕ)^512*2000000000000000^2201 ≤ 2000249569677903^2201*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013412846375437467 25000000000000000000 2000249569677903 2000000000000000 512 2201 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000249569677903/2000000000000000 : ℝ)) (X := (25013412846375437467/25000000000000000000 : ℝ)) (by norm_num) 2201 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8723932996387797/100000000000000000000 : ℝ) ≤ ((33941805148126892689/33950000000000000000 : ℝ)+2*(210500155031/169750000000000 : ℝ)*(11369/100000 : ℝ))^(2201/512 : ℝ) := by
    rw [show (33941805148126892689/33950000000000000000 : ℝ)+2*(210500155031/169750000000000 : ℝ)*(11369/100000 : ℝ)=(10000405847769391/10000000000000000 : ℝ) by norm_num, show 1+2*(8723932996387797/100000000000000000000 : ℝ)=(50008723932996387797/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13412846375437467/50000000000000000000 : ℝ)+(8723932996387797/100000000000000000000 : ℝ) ≤ ((33941805148126892689/33950000000000000000 : ℝ)+(210500155031/169750000000000 : ℝ)*((3691/25000 : ℝ)+(11369/100000 : ℝ)))^(2201/512 : ℝ) := by
    rw [show (33941805148126892689/33950000000000000000 : ℝ)+(210500155031/169750000000000 : ℝ)*((3691/25000 : ℝ)+(11369/100000 : ℝ))=(10000826848079453/10000000000000000 : ℝ) by norm_num, show 1+(13412846375437467/50000000000000000000 : ℝ)+(8723932996387797/100000000000000000000 : ℝ)=(100035549625747262731/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13412846375437467/50000000000000000000 : ℝ) ≤ ((33941805148126892689/33950000000000000000 : ℝ)+2*(210500155031/169750000000000 : ℝ)*(3691/25000 : ℝ))^(2201/512 : ℝ) := by
    rw [show (33941805148126892689/33950000000000000000 : ℝ)+2*(210500155031/169750000000000 : ℝ)*(3691/25000 : ℝ)=(2000249569677903/2000000000000000 : ℝ) by norm_num, show 1+2*(13412846375437467/50000000000000000000 : ℝ)=(25013412846375437467/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (33941805148126892689/33950000000000000000 : ℝ)*(X 1 0+X 2 0)+(210500155031/169750000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2201/512 : ℝ)) (lo := (11369/100000 : ℝ)) (hi := (3691/25000 : ℝ)) (c := (33941805148126892689/33950000000000000000 : ℝ)) (alpha := (210500155031/169750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (33941805148126892689/33950000000000000000 : ℝ)*(X 0 1+X 2 1)+(210500155031/169750000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2201/512 : ℝ)) (lo := (11369/100000 : ℝ)) (hi := (3691/25000 : ℝ)) (c := (33941805148126892689/33950000000000000000 : ℝ)) (alpha := (210500155031/169750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (33941805148126892689/33950000000000000000 : ℝ)*(X 0 2+X 1 2)+(210500155031/169750000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2201/512 : ℝ)) (lo := (11369/100000 : ℝ)) (hi := (3691/25000 : ℝ)) (c := (33941805148126892689/33950000000000000000 : ℝ)) (alpha := (210500155031/169750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-360033993/2000000000 : ℝ)*X 0 0+(538565719/1000000000 : ℝ)*X 0 1+(215426267/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1443_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5286158479/10000000000 : ℝ)*X 1 0+(-1936924539/10000000000 : ℝ)*X 1 1+(5385655557/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1443_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5286157707/10000000000 : ℝ)*X 2 0+(5385656677/10000000000 : ℝ)*X 2 1+(-1936924059/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1443_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4446909551/10000000000 : ℝ)*X 0 0+(2115778299/5000000000 : ℝ)*X 0 1+(4231556083/10000000000 : ℝ)*X 0 2+(4446909551/10000000000 : ℝ)*X 1 0+(2115778299/5000000000 : ℝ)*X 1 1+(4231556083/10000000000 : ℝ)*X 1 2+(4446909551/10000000000 : ℝ)*X 2 0+(2115778299/5000000000 : ℝ)*X 2 1+(4231556083/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1443_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-265277341/1250000000 : ℝ)*X 0 0+(2633362501/5000000000 : ℝ)*X 0 1+(5266724783/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1443_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2684672557/5000000000 : ℝ)*X 1 0+(-992648753/5000000000 : ℝ)*X 1 1+(5266725401/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1443_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1342336269/2500000000 : ℝ)*X 2 0+(5266724387/10000000000 : ℝ)*X 2 1+(-49632473/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1443_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4153796843/10000000000 : ℝ)*X 0 0+(2189031503/5000000000 : ℝ)*X 0 1+(1094515351/2500000000 : ℝ)*X 0 2+(4153796843/10000000000 : ℝ)*X 1 0+(2189031503/5000000000 : ℝ)*X 1 1+(1094515351/2500000000 : ℝ)*X 1 2+(4153796843/10000000000 : ℝ)*X 2 0+(2189031503/5000000000 : ℝ)*X 2 1+(1094515351/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1443_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-256794431/1250000000 : ℝ)*X 0 0+(5184398773/10000000000 : ℝ)*X 0 1+(269981111/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1443_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5276385243/10000000000 : ℝ)*X 1 0+(-1931118443/10000000000 : ℝ)*X 1 1+(5399622429/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1443_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2638192613/5000000000 : ℝ)*X 2 0+(5399622641/10000000000 : ℝ)*X 2 1+(-77244727/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1443_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((70012043/156250000 : ℝ)*X 0 0+(2107169443/5000000000 : ℝ)*X 0 1+(4214338521/10000000000 : ℝ)*X 0 2+(70012043/156250000 : ℝ)*X 1 0+(2107169443/5000000000 : ℝ)*X 1 1+(4214338521/10000000000 : ℝ)*X 1 2+(70012043/156250000 : ℝ)*X 2 0+(2107169443/5000000000 : ℝ)*X 2 1+(4214338521/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1443_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-934094563/5000000000 : ℝ)*X 0 0+(2732993133/5000000000 : ℝ)*X 0 1+(5255592953/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1443_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2688564933/5000000000 : ℝ)*X 1 0+(-1989728313/10000000000 : ℝ)*X 1 1+(5255591909/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1443_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2688564983/5000000000 : ℝ)*X 2 0+(5255592867/10000000000 : ℝ)*X 2 1+(-1989726893/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1443_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((128934669/312500000 : ℝ)*X 0 0+(137242649/312500000 : ℝ)*X 0 1+(1097941313/2500000000 : ℝ)*X 0 2+(128934669/312500000 : ℝ)*X 1 0+(137242649/312500000 : ℝ)*X 1 1+(1097941313/2500000000 : ℝ)*X 1 2+(128934669/312500000 : ℝ)*X 2 0+(137242649/312500000 : ℝ)*X 2 1+(1097941313/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1443_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-15727/25000 : ℝ) ≤ (-4767082084263655812421029643881/7578125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (49917561/10000000000000 : ℝ)*(lower0) + (44982243/100000000000000 : ℝ)*(upper3) + (62126569/12500000000000 : ℝ)*(lower4) + (2923773/4000000000000 : ℝ)*(lower5) + (94748936650767/3125000000000 : ℝ)*(major0) + (94748936650767/3125000000000 : ℝ)*(major1) + (94748936650767/3125000000000 : ℝ)*(major2) + (25362896691/50000000000000 : ℝ)*(sp2) + (2087325874903123/50000000000000 : ℝ)*(sp4) + (521823174624543/12500000000000 : ℝ)*(sp5) + (1043652671074507/25000000000000 : ℝ)*(sp6) + (1910239144038281/100000000000000 : ℝ)*(sp7) + (9660285163/100000000000000 : ℝ)*(sp8) + (38006547533/50000000000000 : ℝ)*(sp13) + (1910239144038281/100000000000000 : ℝ)*(f.failure) + (417466141009141/10000000000000 : ℝ)*(f.sum) + (1669078071571/2425000000000000000000000000 : ℝ)*base66 + (128364252207906959/15156250000000000000000000000000 : ℝ)*base67 + (100273312516500709/15156250000000000000000000000000 : ℝ)*base69 + (112661603056969459/15156250000000000000000000000000 : ℝ)*base71 + (3972960441149/606250000000000000000000000 : ℝ)*base74 + (69372167107125709/15156250000000000000000000000000 : ℝ)*base75 + (102217418602281959/15156250000000000000000000000000 : ℝ)*base77 + (43746105798063209/15156250000000000000000000000000 : ℝ)*base79 + (1956762899973/1212500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (26735919/10000000000000000000000 : ℝ)*base90 + (26735919/10000000000000000000000 : ℝ)*base92 + (26735919/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (59141/100000 : ℝ) ≤ (35855937605879919327102835008339/60625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10686281/25000000000000 : ℝ)*(lower2) + (284031/1000000000000 : ℝ)*(upper4) + (133203943/100000000000000 : ℝ)*(lower5) + (1552034598390319/50000000000000 : ℝ)*(major0) + (1552034598390319/50000000000000 : ℝ)*(major1) + (1552034598390319/50000000000000 : ℝ)*(major2) + (4232748885663713/100000000000000 : ℝ)*(sp0) + (4232410068818149/100000000000000 : ℝ)*(sp1) + (2116375086460351/50000000000000 : ℝ)*(sp2) + (1955656251028389/100000000000000 : ℝ)*(sp3) + (7048718831/100000000000000 : ℝ)*(sp6) + (2063204827/20000000000000 : ℝ)*(sp7) + (416798791/5000000000000 : ℝ)*(sp8) + (43394102673/12500000000000 : ℝ)*(sp9) + (488916641763131/25000000000000 : ℝ)*(f.failure) + (1058189305409883/25000000000000 : ℝ)*(f.sum) + (89035311339969/16975000000000000000000000000 : ℝ)*base66 + (4800534077367722209/1697500000000000000000000000000000 : ℝ)*base68 + (9728469498517722209/1697500000000000000000000000000000 : ℝ)*base70 + (7757239799794777791/1697500000000000000000000000000000 : ℝ)*base71 + (39914164298219/16975000000000000000000000000 : ℝ)*base74 + (12245982612682722209/1697500000000000000000000000000000 : ℝ)*base76 + (10435894326137722209/1697500000000000000000000000000000 : ℝ)*base78 + (6235674454265222209/1697500000000000000000000000000000 : ℝ)*base80 + (31980505586219/16975000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (17718931/2500000000000000000000 : ℝ)*base89 + (17718931/2500000000000000000000 : ℝ)*base91 + (17718931/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (3221/4000 : ℝ) ≤ (683479569810548292938322418399737/848750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (20015147/100000000000000 : ℝ)*(lower3) + (63143237/50000000000000 : ℝ)*(upper4) + (53660433/100000000000000 : ℝ)*(lower5) + (3411165563073011/100000000000000 : ℝ)*(major0) + (3411165563073011/100000000000000 : ℝ)*(major1) + (3411165563073011/100000000000000 : ℝ)*(major2) + (2193016507/50000000000000 : ℝ)*(sp0) + (22060954083/25000000000000 : ℝ)*(sp1) + (225559935077/100000000000000 : ℝ)*(sp2) + (17810615157/25000000000000 : ℝ)*(sp3) + (4646336680022283/100000000000000 : ℝ)*(sp8) + (1161563205559741/25000000000000 : ℝ)*(sp9) + (4646115506120219/100000000000000 : ℝ)*(sp10) + (2149076222841263/100000000000000 : ℝ)*(sp11) + (2149147465301891/100000000000000 : ℝ)*(f.failure) + (4646341066055297/100000000000000 : ℝ)*(f.sum) + (4888275837777/1060937500000000000000000000 : ℝ)*base65 + (23679065250357683421/3395000000000000000000000000000000 : ℝ)*base68 + (14215784114377683421/3395000000000000000000000000000000 : ℝ)*base70 + (2256544305042683421/3395000000000000000000000000000000 : ℝ)*base72 + (19547301924183/4243750000000000000000000000 : ℝ)*base73 + (18744319513527683421/3395000000000000000000000000000000 : ℝ)*base76 + (374629403022316579/3395000000000000000000000000000000 : ℝ)*base77 + (5643155212512683421/3395000000000000000000000000000000 : ℝ)*base80 + (13881523949343/16975000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (48225691/10000000000000000000000 : ℝ)*base89 + (48225691/10000000000000000000000 : ℝ)*base91 + (48225691/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-84737/100000 : ℝ) ≤ (-719185548079882715248330485789429/848750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (187134703/100000000000000 : ℝ)*(lower1) + (62002033/12500000000000 : ℝ)*(lower2) + (32056559/50000000000000 : ℝ)*(lower3) + (273546921/100000000000000 : ℝ)*(upper5) + (1724407376627629/50000000000000 : ℝ)*(major0) + (1724407376627629/50000000000000 : ℝ)*(major1) + (1724407376627629/50000000000000 : ℝ)*(major2) + (1991988611/10000000000000 : ℝ)*(sp4) + (28805426117/5000000000000 : ℝ)*(sp5) + (174680442523/100000000000000 : ℝ)*(sp7) + (2376493386990531/50000000000000 : ℝ)*(sp12) + (74256727896013/1562500000000 : ℝ)*(sp13) + (1188251673466793/25000000000000 : ℝ)*(sp14) + (54317325590813/2500000000000 : ℝ)*(sp15) + (1086433852037521/50000000000000 : ℝ)*(f.failure) + (1188251673466793/25000000000000 : ℝ)*(f.sum) + (131493729284079/16975000000000000000000000000 : ℝ)*base66 + (19333578031420304381/1697500000000000000000000000000000 : ℝ)*base67 + (8264993060165304381/1697500000000000000000000000000000 : ℝ)*base69 + (9001699957997804381/1697500000000000000000000000000000 : ℝ)*base71 + (47660374615977/8487500000000000000000000000 : ℝ)*base74 + (7567316465795304381/1697500000000000000000000000000000 : ℝ)*base75 + (7490794454197804381/1697500000000000000000000000000000 : ℝ)*base77 + (5341008444550304381/1697500000000000000000000000000000 : ℝ)*base79 + (11594920046901/4243750000000000000000000000 : ℝ)*base82 + (47304679/5000000000000000000000 : ℝ)*base90 + (47304679/5000000000000000000000 : ℝ)*base92 + (47304679/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1443_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158721801/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3691/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11369/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15727/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(59141/100000 : ℝ) else (3221/4000 : ℝ) ≤ X j i ∧ X j i ≤ (84737/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1443_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1443_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158721801/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14767/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2273/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15727/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(59141/100000 : ℝ) else (3221/4000 : ℝ) ≤ X j i ∧ X j i ≤ (84737/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1443_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1443_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1443_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2201/512 : ℝ) ≤ p) (hpb : p ≤ (4403/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158721801/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14767/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2273/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15727/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(59141/100000 : ℝ) else (3221/4000 : ℝ) ≤ X j i ∧ X j i ≤ (84737/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1443_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
