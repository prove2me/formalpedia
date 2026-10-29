-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1483_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:14:04.510997+00:00
-- url     : https://prove2.me/submissions/f621a44c-7d04-4790-97f2-3214859f17f9

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
theorem support_rectangle_w1483_s6_0 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1911725291/10000000000 : ℝ)*x 0 + (5437033893/10000000000 : ℝ)*x 1 + (2608015181/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1911725291/10000000000 : ℝ)^4463 ≤ (11680516202863/100000000000000 : ℝ)^3439 := by
    have hnat : (1911725291 : ℕ)^4463*100000000000000^3439 ≤ 11680516202863^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1911725291 10000000000 11680516202863 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5437033893/10000000000 : ℝ)^4463 ≤ (9069705355417/20000000000000 : ℝ)^3439 := by
    have hnat : (5437033893 : ℕ)^4463*20000000000000^3439 ≤ 9069705355417^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437033893 10000000000 9069705355417 20000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2608015181/5000000000 : ℝ)^4463 ≤ (8594191400307/20000000000000 : ℝ)^3439 := by
    have hnat : (2608015181 : ℕ)^4463*20000000000000^3439 ≤ 8594191400307^3439*5000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608015181 5000000000 8594191400307 20000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1911725291/10000000000 : ℝ), (5437033893/10000000000 : ℝ), (2608015181/5000000000 : ℝ)] ![(11680516202863/100000000000000 : ℝ), (9069705355417/20000000000000 : ℝ), (8594191400307/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1911725291/10000000000 : ℝ)|^4463 ≤ (11680516202863/100000000000000 : ℝ)^3439
        have hw : |(-1911725291/10000000000 : ℝ)|=(1911725291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5437033893/10000000000 : ℝ)|^4463 ≤ (9069705355417/20000000000000 : ℝ)^3439
        have hw : |(5437033893/10000000000 : ℝ)|=(5437033893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2608015181/5000000000 : ℝ)|^4463 ≤ (8594191400307/20000000000000 : ℝ)^3439
        have hw : |(2608015181/5000000000 : ℝ)|=(2608015181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1483_s6_1 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (669144151/1250000000 : ℝ)*x 0 + (-253122649/1250000000 : ℝ)*x 1 + (521603057/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669144151/1250000000 : ℝ)^4463 ≤ (44442678382173/100000000000000 : ℝ)^3439 := by
    have hnat : (669144151 : ℕ)^4463*100000000000000^3439 ≤ 44442678382173^3439*1250000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669144151 1250000000 44442678382173 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (253122649/1250000000 : ℝ)^4463 ≤ (3146590593241/25000000000000 : ℝ)^3439 := by
    have hnat : (253122649 : ℕ)^4463*25000000000000^3439 ≤ 3146590593241^3439*1250000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      253122649 1250000000 3146590593241 25000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (521603057/1000000000 : ℝ)^4463 ≤ (42970959225321/100000000000000 : ℝ)^3439 := by
    have hnat : (521603057 : ℕ)^4463*100000000000000^3439 ≤ 42970959225321^3439*1000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521603057 1000000000 42970959225321 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669144151/1250000000 : ℝ), (-253122649/1250000000 : ℝ), (521603057/1000000000 : ℝ)] ![(44442678382173/100000000000000 : ℝ), (3146590593241/25000000000000 : ℝ), (42970959225321/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669144151/1250000000 : ℝ)|^4463 ≤ (44442678382173/100000000000000 : ℝ)^3439
        have hw : |(669144151/1250000000 : ℝ)|=(669144151/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-253122649/1250000000 : ℝ)|^4463 ≤ (3146590593241/25000000000000 : ℝ)^3439
        have hw : |(-253122649/1250000000 : ℝ)|=(253122649/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(521603057/1000000000 : ℝ)|^4463 ≤ (42970959225321/100000000000000 : ℝ)^3439
        have hw : |(521603057/1000000000 : ℝ)|=(521603057/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1483_s6_2 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353153127/10000000000 : ℝ)*x 0 + (1043206081/2000000000 : ℝ)*x 1 + (-2024981519/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353153127/10000000000 : ℝ)^4463 ≤ (22221338754731/50000000000000 : ℝ)^3439 := by
    have hnat : (5353153127 : ℕ)^4463*50000000000000^3439 ≤ 22221338754731^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353153127 10000000000 22221338754731 50000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043206081/2000000000 : ℝ)^4463 ≤ (2148547873063/5000000000000 : ℝ)^3439 := by
    have hnat : (1043206081 : ℕ)^4463*5000000000000^3439 ≤ 2148547873063^3439*2000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043206081 2000000000 2148547873063 5000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2024981519/10000000000 : ℝ)^4463 ≤ (6293182505321/50000000000000 : ℝ)^3439 := by
    have hnat : (2024981519 : ℕ)^4463*50000000000000^3439 ≤ 6293182505321^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2024981519 10000000000 6293182505321 50000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353153127/10000000000 : ℝ), (1043206081/2000000000 : ℝ), (-2024981519/10000000000 : ℝ)] ![(22221338754731/50000000000000 : ℝ), (2148547873063/5000000000000 : ℝ), (6293182505321/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353153127/10000000000 : ℝ)|^4463 ≤ (22221338754731/50000000000000 : ℝ)^3439
        have hw : |(5353153127/10000000000 : ℝ)|=(5353153127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043206081/2000000000 : ℝ)|^4463 ≤ (2148547873063/5000000000000 : ℝ)^3439
        have hw : |(1043206081/2000000000 : ℝ)|=(1043206081/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2024981519/10000000000 : ℝ)|^4463 ≤ (6293182505321/50000000000000 : ℝ)^3439
        have hw : |(-2024981519/10000000000 : ℝ)|=(2024981519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1483_s6_3 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070867751/2500000000 : ℝ)*x 0 + (2022064113/5000000000 : ℝ)*x 1 + (2267524841/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070867751/2500000000 : ℝ)^4463 ≤ (831953411733/2500000000000 : ℝ)^3439 := by
    have hnat : (1070867751 : ℕ)^4463*2500000000000^3439 ≤ 831953411733^3439*2500000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070867751 2500000000 831953411733 2500000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2022064113/5000000000 : ℝ)^4463 ≤ (3860670467069/12500000000000 : ℝ)^3439 := by
    have hnat : (2022064113 : ℕ)^4463*12500000000000^3439 ≤ 3860670467069^3439*5000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2022064113 5000000000 3860670467069 12500000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2267524841/5000000000 : ℝ)^4463 ≤ (35836499773247/100000000000000 : ℝ)^3439 := by
    have hnat : (2267524841 : ℕ)^4463*100000000000000^3439 ≤ 35836499773247^3439*5000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2267524841 5000000000 35836499773247 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070867751/2500000000 : ℝ), (2022064113/5000000000 : ℝ), (2267524841/5000000000 : ℝ)] ![(831953411733/2500000000000 : ℝ), (3860670467069/12500000000000 : ℝ), (35836499773247/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070867751/2500000000 : ℝ)|^4463 ≤ (831953411733/2500000000000 : ℝ)^3439
        have hw : |(1070867751/2500000000 : ℝ)|=(1070867751/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2022064113/5000000000 : ℝ)|^4463 ≤ (3860670467069/12500000000000 : ℝ)^3439
        have hw : |(2022064113/5000000000 : ℝ)|=(2022064113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2267524841/5000000000 : ℝ)|^4463 ≤ (35836499773247/100000000000000 : ℝ)^3439
        have hw : |(2267524841/5000000000 : ℝ)|=(2267524841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1483_s6_4 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-955877817/5000000000 : ℝ)*x 0 + (2608580757/5000000000 : ℝ)*x 1 + (5435894333/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (955877817/5000000000 : ℝ)^4463 ≤ (11680756800193/100000000000000 : ℝ)^3439 := by
    have hnat : (955877817 : ℕ)^4463*100000000000000^3439 ≤ 11680756800193^3439*5000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      955877817 5000000000 11680756800193 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2608580757/5000000000 : ℝ)^4463 ≤ (21491525426283/50000000000000 : ℝ)^3439 := by
    have hnat : (2608580757 : ℕ)^4463*50000000000000^3439 ≤ 21491525426283^3439*5000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608580757 5000000000 21491525426283 50000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5435894333/10000000000 : ℝ)^4463 ≤ (17709450131/39062500000 : ℝ)^3439 := by
    have hnat : (5435894333 : ℕ)^4463*39062500000^3439 ≤ 17709450131^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435894333 10000000000 17709450131 39062500000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-955877817/5000000000 : ℝ), (2608580757/5000000000 : ℝ), (5435894333/10000000000 : ℝ)] ![(11680756800193/100000000000000 : ℝ), (21491525426283/50000000000000 : ℝ), (17709450131/39062500000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-955877817/5000000000 : ℝ)|^4463 ≤ (11680756800193/100000000000000 : ℝ)^3439
        have hw : |(-955877817/5000000000 : ℝ)|=(955877817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2608580757/5000000000 : ℝ)|^4463 ≤ (21491525426283/50000000000000 : ℝ)^3439
        have hw : |(2608580757/5000000000 : ℝ)|=(2608580757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5435894333/10000000000 : ℝ)|^4463 ≤ (17709450131/39062500000 : ℝ)^3439
        have hw : |(5435894333/10000000000 : ℝ)|=(5435894333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1483_s6_5 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295405881/10000000000 : ℝ)*x 0 + (-1805117393/10000000000 : ℝ)*x 1 + (5435894321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295405881/10000000000 : ℝ)^4463 ≤ (5477687324399/12500000000000 : ℝ)^3439 := by
    have hnat : (5295405881 : ℕ)^4463*12500000000000^3439 ≤ 5477687324399^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295405881 10000000000 5477687324399 12500000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1805117393/10000000000 : ℝ)^4463 ≤ (10842309178937/100000000000000 : ℝ)^3439 := by
    have hnat : (1805117393 : ℕ)^4463*100000000000000^3439 ≤ 10842309178937^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1805117393 10000000000 10842309178937 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5435894321/10000000000 : ℝ)^4463 ≤ (22668096102739/50000000000000 : ℝ)^3439 := by
    have hnat : (5435894321 : ℕ)^4463*50000000000000^3439 ≤ 22668096102739^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435894321 10000000000 22668096102739 50000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295405881/10000000000 : ℝ), (-1805117393/10000000000 : ℝ), (5435894321/10000000000 : ℝ)] ![(5477687324399/12500000000000 : ℝ), (10842309178937/100000000000000 : ℝ), (22668096102739/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295405881/10000000000 : ℝ)|^4463 ≤ (5477687324399/12500000000000 : ℝ)^3439
        have hw : |(5295405881/10000000000 : ℝ)|=(5295405881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1805117393/10000000000 : ℝ)|^4463 ≤ (10842309178937/100000000000000 : ℝ)^3439
        have hw : |(-1805117393/10000000000 : ℝ)|=(1805117393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5435894321/10000000000 : ℝ)|^4463 ≤ (22668096102739/50000000000000 : ℝ)^3439
        have hw : |(5435894321/10000000000 : ℝ)|=(5435894321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1483_s6_6 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (82740717/156250000 : ℝ)*x 0 + (5435894327/10000000000 : ℝ)*x 1 + (-14440939/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (82740717/156250000 : ℝ)^4463 ≤ (43821498670369/100000000000000 : ℝ)^3439 := by
    have hnat : (82740717 : ℕ)^4463*100000000000000^3439 ≤ 43821498670369^3439*156250000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82740717 156250000 43821498670369 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5435894327/10000000000 : ℝ)^4463 ≤ (45336192270419/100000000000000 : ℝ)^3439 := by
    have hnat : (5435894327 : ℕ)^4463*100000000000000^3439 ≤ 45336192270419^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435894327 10000000000 45336192270419 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (14440939/80000000 : ℝ)^4463 ≤ (10842309038629/100000000000000 : ℝ)^3439 := by
    have hnat : (14440939 : ℕ)^4463*100000000000000^3439 ≤ 10842309038629^3439*80000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14440939 80000000 10842309038629 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(82740717/156250000 : ℝ), (5435894327/10000000000 : ℝ), (-14440939/80000000 : ℝ)] ![(43821498670369/100000000000000 : ℝ), (45336192270419/100000000000000 : ℝ), (10842309038629/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(82740717/156250000 : ℝ)|^4463 ≤ (43821498670369/100000000000000 : ℝ)^3439
        have hw : |(82740717/156250000 : ℝ)|=(82740717/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5435894327/10000000000 : ℝ)|^4463 ≤ (45336192270419/100000000000000 : ℝ)^3439
        have hw : |(5435894327/10000000000 : ℝ)|=(5435894327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-14440939/80000000 : ℝ)|^4463 ≤ (10842309038629/100000000000000 : ℝ)^3439
        have hw : |(-14440939/80000000 : ℝ)|=(14440939/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1483_s6_7 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070884531/2500000000 : ℝ)*x 0 + (4532536591/10000000000 : ℝ)*x 1 + (20233299/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070884531/2500000000 : ℝ)^4463 ≤ (33278813192167/100000000000000 : ℝ)^3439 := by
    have hnat : (1070884531 : ℕ)^4463*100000000000000^3439 ≤ 33278813192167^3439*2500000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070884531 2500000000 33278813192167 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4532536591/10000000000 : ℝ)^4463 ≤ (35810729998343/100000000000000 : ℝ)^3439 := by
    have hnat : (4532536591 : ℕ)^4463*100000000000000^3439 ≤ 35810729998343^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4532536591 10000000000 35810729998343 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (20233299/50000000 : ℝ)^4463 ≤ (30910456795577/100000000000000 : ℝ)^3439 := by
    have hnat : (20233299 : ℕ)^4463*100000000000000^3439 ≤ 30910456795577^3439*50000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20233299 50000000 30910456795577 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070884531/2500000000 : ℝ), (4532536591/10000000000 : ℝ), (20233299/50000000 : ℝ)] ![(33278813192167/100000000000000 : ℝ), (35810729998343/100000000000000 : ℝ), (30910456795577/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070884531/2500000000 : ℝ)|^4463 ≤ (33278813192167/100000000000000 : ℝ)^3439
        have hw : |(1070884531/2500000000 : ℝ)|=(1070884531/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4532536591/10000000000 : ℝ)|^4463 ≤ (35810729998343/100000000000000 : ℝ)^3439
        have hw : |(4532536591/10000000000 : ℝ)|=(4532536591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(20233299/50000000 : ℝ)|^4463 ≤ (30910456795577/100000000000000 : ℝ)^3439
        have hw : |(20233299/50000000 : ℝ)|=(20233299/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1483_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161066273/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7739/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10797/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10799/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3869/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7739/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10797/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7739/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10797/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7739/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10797/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7739/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10797/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7739/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10797/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7739/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10797/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10797/100000 : ℝ) ^ (4461/1024 : ℝ) ≤ (122932814015401/2000000000000000000 : ℝ) := by
    have hpowers : (10797/100000 : ℝ)^4461 ≤ (122932814015401/2000000000000000000 : ℝ)^1024 := by
      have hnat : (10797 : ℕ)^4461*2000000000000000000^1024 ≤ 122932814015401^1024*100000^4461 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10797 100000 122932814015401 2000000000000000000 4461 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10797/100000 : ℝ)) (X := (122932814015401/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4461 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7739/50000 : ℝ) ^ (4461/1024 : ℝ) ≤ (1475730412113271/5000000000000000000 : ℝ) := by
    have hpowers : (7739/50000 : ℝ)^4461 ≤ (1475730412113271/5000000000000000000 : ℝ)^1024 := by
      have hnat : (7739 : ℕ)^4461*5000000000000000000^1024 ≤ 1475730412113271^1024*50000^4461 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7739 50000 1475730412113271 5000000000000000000 4461 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7739/50000 : ℝ)) (X := (1475730412113271/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4461 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1000122932814015401/1000000000000000000 : ℝ) ≤ (625017635793617/625000000000000 : ℝ) ^ (4461/1024 : ℝ) := by
    have hpowers : (1000122932814015401/1000000000000000000 : ℝ)^1024 ≤ (625017635793617/625000000000000 : ℝ)^4461 := by
      have hnat : (1000122932814015401 : ℕ)^1024*625000000000000^4461 ≤ 625017635793617^4461*1000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000122932814015401 1000000000000000000 625017635793617 625000000000000 1024 4461 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625017635793617/625000000000000 : ℝ)) (X := (1000122932814015401/1000000000000000000 : ℝ)) (by norm_num) 4461 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10003566124894303547/10000000000000000000 : ℝ) ≤ (10000818473511833/10000000000000000 : ℝ) ^ (4461/1024 : ℝ) := by
    have hpowers : (10003566124894303547/10000000000000000000 : ℝ)^1024 ≤ (10000818473511833/10000000000000000 : ℝ)^4461 := by
      have hnat : (10003566124894303547 : ℕ)^1024*10000000000000000^4461 ≤ 10000818473511833^4461*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10003566124894303547 10000000000000000000 10000818473511833 10000000000000000 1024 4461 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000818473511833/10000000000000000 : ℝ)) (X := (10003566124894303547/10000000000000000000 : ℝ)) (by norm_num) 4461 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501475730412113271/2500000000000000000 : ℝ) ≤ (5000677387162897/5000000000000000 : ℝ) ^ (4461/1024 : ℝ) := by
    have hpowers : (2501475730412113271/2500000000000000000 : ℝ)^1024 ≤ (5000677387162897/5000000000000000 : ℝ)^4461 := by
      have hnat : (2501475730412113271 : ℕ)^1024*5000000000000000^4461 ≤ 5000677387162897^4461*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501475730412113271 2500000000000000000 5000677387162897 5000000000000000 1024 4461 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000677387162897/5000000000000000 : ℝ)) (X := (2501475730412113271/2500000000000000000 : ℝ)) (by norm_num) 4461 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(122932814015401/2000000000000000000 : ℝ) ≤ ((23399869985311032499/23405000000000000000 : ℝ)+2*(536300813961/468100000000000 : ℝ)*(10797/100000 : ℝ))^(4461/1024 : ℝ) := by
    rw [show (23399869985311032499/23405000000000000000 : ℝ)+2*(536300813961/468100000000000 : ℝ)*(10797/100000 : ℝ)=(625017635793617/625000000000000 : ℝ) by norm_num, show 1+2*(122932814015401/2000000000000000000 : ℝ)=(1000122932814015401/1000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1475730412113271/5000000000000000000 : ℝ)+(122932814015401/2000000000000000000 : ℝ) ≤ ((23399869985311032499/23405000000000000000 : ℝ)+(536300813961/468100000000000 : ℝ)*((7739/50000 : ℝ)+(10797/100000 : ℝ)))^(4461/1024 : ℝ) := by
    rw [show (23399869985311032499/23405000000000000000 : ℝ)+(536300813961/468100000000000 : ℝ)*((7739/50000 : ℝ)+(10797/100000 : ℝ))=(10000818473511833/10000000000000000 : ℝ) by norm_num, show 1+(1475730412113271/5000000000000000000 : ℝ)+(122932814015401/2000000000000000000 : ℝ)=(10003566124894303547/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1475730412113271/5000000000000000000 : ℝ) ≤ ((23399869985311032499/23405000000000000000 : ℝ)+2*(536300813961/468100000000000 : ℝ)*(7739/50000 : ℝ))^(4461/1024 : ℝ) := by
    rw [show (23399869985311032499/23405000000000000000 : ℝ)+2*(536300813961/468100000000000 : ℝ)*(7739/50000 : ℝ)=(5000677387162897/5000000000000000 : ℝ) by norm_num, show 1+2*(1475730412113271/5000000000000000000 : ℝ)=(2501475730412113271/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (23399869985311032499/23405000000000000000 : ℝ)*(X 1 0+X 2 0)+(536300813961/468100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4461/1024 : ℝ)) (lo := (10797/100000 : ℝ)) (hi := (7739/50000 : ℝ)) (c := (23399869985311032499/23405000000000000000 : ℝ)) (alpha := (536300813961/468100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (23399869985311032499/23405000000000000000 : ℝ)*(X 0 1+X 2 1)+(536300813961/468100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4461/1024 : ℝ)) (lo := (10797/100000 : ℝ)) (hi := (7739/50000 : ℝ)) (c := (23399869985311032499/23405000000000000000 : ℝ)) (alpha := (536300813961/468100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (23399869985311032499/23405000000000000000 : ℝ)*(X 0 2+X 1 2)+(536300813961/468100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4461/1024 : ℝ)) (lo := (10797/100000 : ℝ)) (hi := (7739/50000 : ℝ)) (c := (23399869985311032499/23405000000000000000 : ℝ)) (alpha := (536300813961/468100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1911725291/10000000000 : ℝ)*X 0 0+(5437033893/10000000000 : ℝ)*X 0 1+(2608015181/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((669144151/1250000000 : ℝ)*X 1 0+(-253122649/1250000000 : ℝ)*X 1 1+(521603057/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353153127/10000000000 : ℝ)*X 2 0+(1043206081/2000000000 : ℝ)*X 2 1+(-2024981519/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1070867751/2500000000 : ℝ)*X 0 0+(2022064113/5000000000 : ℝ)*X 0 1+(2267524841/5000000000 : ℝ)*X 0 2+(1070867751/2500000000 : ℝ)*X 1 0+(2022064113/5000000000 : ℝ)*X 1 1+(2267524841/5000000000 : ℝ)*X 1 2+(1070867751/2500000000 : ℝ)*X 2 0+(2022064113/5000000000 : ℝ)*X 2 1+(2267524841/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-955877817/5000000000 : ℝ)*X 0 0+(2608580757/5000000000 : ℝ)*X 0 1+(5435894333/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5295405881/10000000000 : ℝ)*X 1 0+(-1805117393/10000000000 : ℝ)*X 1 1+(5435894321/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((82740717/156250000 : ℝ)*X 2 0+(5435894327/10000000000 : ℝ)*X 2 1+(-14440939/80000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1070884531/2500000000 : ℝ)*X 0 0+(4532536591/10000000000 : ℝ)*X 0 1+(20233299/50000000 : ℝ)*X 0 2+(1070884531/2500000000 : ℝ)*X 1 0+(4532536591/10000000000 : ℝ)*X 1 1+(20233299/50000000 : ℝ)*X 1 2+(1070884531/2500000000 : ℝ)*X 2 0+(4532536591/10000000000 : ℝ)*X 2 1+(20233299/50000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5391627187711298436531747651/1170250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (202384001/50000000000000 : ℝ)*(base19) + (49604011/10000000000000 : ℝ)*(base23) + (138284161/100000000000000 : ℝ)*(upper3) + (92547809/100000000000000 : ℝ)*(lower4) + (3280915897751717/100000000000000 : ℝ)*(major0) + (3280915897751717/100000000000000 : ℝ)*(major1) + (3280915897751717/100000000000000 : ℝ)*(major2) + (2262413689338773/50000000000000 : ℝ)*(sp0) + (2262416886151173/50000000000000 : ℝ)*(sp1) + (4524832462392127/100000000000000 : ℝ)*(sp2) + (2036991202258319/100000000000000 : ℝ)*(sp3) + (3399196401/50000000000000 : ℝ)*(sp4) + (1218638111/100000000000000 : ℝ)*(sp6) + (6262599961/100000000000000 : ℝ)*(sp7) + (50924936621457/2500000000000 : ℝ)*(f.failure) + (1131208544267587/25000000000000 : ℝ)*(f.sum) + (110671669556793/23405000000000000000000000000 : ℝ)*base66 + (9886957157806400783/2340500000000000000000000000000000 : ℝ)*base67 + (41877750870693900783/2340500000000000000000000000000000 : ℝ)*base69 + (10902177299352099217/2340500000000000000000000000000000 : ℝ)*base72 + (14558941683443/5851250000000000000000000000 : ℝ)*base73 + (21339220898762900783/2340500000000000000000000000000000 : ℝ)*base75 + (5858406186576599217/2340500000000000000000000000000000 : ℝ)*base78 + (7671840256503400783/2340500000000000000000000000000000 : ℝ)*base79 + (162100504868937/23405000000000000000000000000 : ℝ)*base81 + (1680239/250000000000000000000 : ℝ)*base90 + (1680239/250000000000000000000 : ℝ)*base92 + (1680239/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (78033176160749541496547349/18285156250000000000000000000000 : ℝ) := by norm_num
    linear_combination (695701529/100000000000000 : ℝ)*(base19) + (779566717/100000000000000 : ℝ)*(base23) + (111021983/50000000000000 : ℝ)*(lower1) + (89995437/100000000000000 : ℝ)*(upper3) + (16522263/50000000000000 : ℝ)*(lower4) + (22097817/25000000000000 : ℝ)*(upper5) + (414369209681257/12500000000000 : ℝ)*(major0) + (414369209681257/12500000000000 : ℝ)*(major1) + (414369209681257/12500000000000 : ℝ)*(major2) + (1413963097/100000000000000 : ℝ)*(sp2) + (2285888484338337/50000000000000 : ℝ)*(sp4) + (2285888136487573/50000000000000 : ℝ)*(sp5) + (4571774775146861/100000000000000 : ℝ)*(sp6) + (1029065121985549/50000000000000 : ℝ)*(sp7) + (1029065121985549/50000000000000 : ℝ)*(f.failure) + (2285888484338337/50000000000000 : ℝ)*(f.sum) + (14312375493809/5851250000000000000000000000 : ℝ)*base65 + (751443548552396243/292562500000000000000000000000000 : ℝ)*base67 + (1655175697219396243/292562500000000000000000000000000 : ℝ)*base69 + (14016351498119103757/292562500000000000000000000000000 : ℝ)*base72 + (11170993233279/5851250000000000000000000000 : ℝ)*base73 + (15929400297110396243/292562500000000000000000000000000 : ℝ)*base75 + (1057334995647083743/292562500000000000000000000000000 : ℝ)*base77 + (3472451097885146243/292562500000000000000000000000000 : ℝ)*base79 + (13360158071053/11702500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (62711123/5000000000000000000000 : ℝ)*base90 + (62711123/5000000000000000000000 : ℝ)*base92 + (62711123/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1483_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161066273/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7739/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10797/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10799/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3869/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1483_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1483_box_0 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-169276413/1000000000 : ℝ)*x 0 + (5405974131/10000000000 : ℝ)*x 1 + (168936707/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (169276413/1000000000 : ℝ)^4463 ≤ (9974762691831/100000000000000 : ℝ)^3439 := by
    have hnat : (169276413 : ℕ)^4463*100000000000000^3439 ≤ 9974762691831^3439*1000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169276413 1000000000 9974762691831 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5405974131/10000000000 : ℝ)^4463 ≤ (45012615984733/100000000000000 : ℝ)^3439 := by
    have hnat : (5405974131 : ℕ)^4463*100000000000000^3439 ≤ 45012615984733^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405974131 10000000000 45012615984733 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (168936707/312500000 : ℝ)^4463 ≤ (45012621311969/100000000000000 : ℝ)^3439 := by
    have hnat : (168936707 : ℕ)^4463*100000000000000^3439 ≤ 45012621311969^3439*312500000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168936707 312500000 45012621311969 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-169276413/1000000000 : ℝ), (5405974131/10000000000 : ℝ), (168936707/312500000 : ℝ)] ![(9974762691831/100000000000000 : ℝ), (45012615984733/100000000000000 : ℝ), (45012621311969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-169276413/1000000000 : ℝ)|^4463 ≤ (9974762691831/100000000000000 : ℝ)^3439
        have hw : |(-169276413/1000000000 : ℝ)|=(169276413/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5405974131/10000000000 : ℝ)|^4463 ≤ (45012615984733/100000000000000 : ℝ)^3439
        have hw : |(5405974131/10000000000 : ℝ)|=(5405974131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(168936707/312500000 : ℝ)|^4463 ≤ (45012621311969/100000000000000 : ℝ)^3439
        have hw : |(168936707/312500000 : ℝ)|=(168936707/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1483_box_1 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5270295899/10000000000 : ℝ)*x 0 + (-940366119/5000000000 : ℝ)*x 1 + (5405974331/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5270295899/10000000000 : ℝ)^4463 ≤ (43552021388547/100000000000000 : ℝ)^3439 := by
    have hnat : (5270295899 : ℕ)^4463*100000000000000^3439 ≤ 43552021388547^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5270295899 10000000000 43552021388547 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (940366119/5000000000 : ℝ)^4463 ≤ (2287072089039/20000000000000 : ℝ)^3439 := by
    have hnat : (940366119 : ℕ)^4463*20000000000000^3439 ≤ 2287072089039^3439*5000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      940366119 5000000000 2287072089039 20000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5405974331/10000000000 : ℝ)^4463 ≤ (45012618145883/100000000000000 : ℝ)^3439 := by
    have hnat : (5405974331 : ℕ)^4463*100000000000000^3439 ≤ 45012618145883^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405974331 10000000000 45012618145883 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5270295899/10000000000 : ℝ), (-940366119/5000000000 : ℝ), (5405974331/10000000000 : ℝ)] ![(43552021388547/100000000000000 : ℝ), (2287072089039/20000000000000 : ℝ), (45012618145883/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5270295899/10000000000 : ℝ)|^4463 ≤ (43552021388547/100000000000000 : ℝ)^3439
        have hw : |(5270295899/10000000000 : ℝ)|=(5270295899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-940366119/5000000000 : ℝ)|^4463 ≤ (2287072089039/20000000000000 : ℝ)^3439
        have hw : |(-940366119/5000000000 : ℝ)|=(940366119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5405974331/10000000000 : ℝ)|^4463 ≤ (45012618145883/100000000000000 : ℝ)^3439
        have hw : |(5405974331/10000000000 : ℝ)|=(5405974331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1483_box_2 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1054059239/2000000000 : ℝ)*x 0 + (2702987059/5000000000 : ℝ)*x 1 + (-58772879/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1054059239/2000000000 : ℝ)^4463 ≤ (43552024562933/100000000000000 : ℝ)^3439 := by
    have hnat : (1054059239 : ℕ)^4463*100000000000000^3439 ≤ 43552024562933^3439*2000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054059239 2000000000 43552024562933 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2702987059/5000000000 : ℝ)^4463 ≤ (22506307922129/50000000000000 : ℝ)^3439 := by
    have hnat : (2702987059 : ℕ)^4463*50000000000000^3439 ≤ 22506307922129^3439*5000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702987059 5000000000 22506307922129 50000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (58772879/312500000 : ℝ)^4463 ≤ (5717679788607/50000000000000 : ℝ)^3439 := by
    have hnat : (58772879 : ℕ)^4463*50000000000000^3439 ≤ 5717679788607^3439*312500000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58772879 312500000 5717679788607 50000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1054059239/2000000000 : ℝ), (2702987059/5000000000 : ℝ), (-58772879/312500000 : ℝ)] ![(43552024562933/100000000000000 : ℝ), (22506307922129/50000000000000 : ℝ), (5717679788607/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1054059239/2000000000 : ℝ)|^4463 ≤ (43552024562933/100000000000000 : ℝ)^3439
        have hw : |(1054059239/2000000000 : ℝ)|=(1054059239/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2702987059/5000000000 : ℝ)|^4463 ≤ (22506307922129/50000000000000 : ℝ)^3439
        have hw : |(2702987059/5000000000 : ℝ)|=(2702987059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-58772879/312500000 : ℝ)|^4463 ≤ (5717679788607/50000000000000 : ℝ)^3439
        have hw : |(-58772879/312500000 : ℝ)|=(58772879/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1483_box_3 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4487920283/10000000000 : ℝ)*x 0 + (2094212013/5000000000 : ℝ)*x 1 + (418842447/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4487920283/10000000000 : ℝ)^4463 ≤ (35353934527307/100000000000000 : ℝ)^3439 := by
    have hnat : (4487920283 : ℕ)^4463*100000000000000^3439 ≤ 35353934527307^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4487920283 10000000000 35353934527307 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2094212013/5000000000 : ℝ)^4463 ≤ (32323030506523/100000000000000 : ℝ)^3439 := by
    have hnat : (2094212013 : ℕ)^4463*100000000000000^3439 ≤ 32323030506523^3439*5000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2094212013 5000000000 32323030506523 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (418842447/1000000000 : ℝ)^4463 ≤ (8080758738309/25000000000000 : ℝ)^3439 := by
    have hnat : (418842447 : ℕ)^4463*25000000000000^3439 ≤ 8080758738309^3439*1000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      418842447 1000000000 8080758738309 25000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4487920283/10000000000 : ℝ), (2094212013/5000000000 : ℝ), (418842447/1000000000 : ℝ)] ![(35353934527307/100000000000000 : ℝ), (32323030506523/100000000000000 : ℝ), (8080758738309/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4487920283/10000000000 : ℝ)|^4463 ≤ (35353934527307/100000000000000 : ℝ)^3439
        have hw : |(4487920283/10000000000 : ℝ)|=(4487920283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2094212013/5000000000 : ℝ)|^4463 ≤ (32323030506523/100000000000000 : ℝ)^3439
        have hw : |(2094212013/5000000000 : ℝ)|=(2094212013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(418842447/1000000000 : ℝ)|^4463 ≤ (8080758738309/25000000000000 : ℝ)^3439
        have hw : |(418842447/1000000000 : ℝ)|=(418842447/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1483_box_4 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1068075857/5000000000 : ℝ)*x 0 + (1310640523/2500000000 : ℝ)*x 1 + (2621281373/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068075857/5000000000 : ℝ)^4463 ≤ (3372583414739/25000000000000 : ℝ)^3439 := by
    have hnat : (1068075857 : ℕ)^4463*25000000000000^3439 ≤ 3372583414739^3439*5000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068075857 5000000000 3372583414739 25000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310640523/2500000000 : ℝ)^4463 ≤ (4325482966199/10000000000000 : ℝ)^3439 := by
    have hnat : (1310640523 : ℕ)^4463*10000000000000^3439 ≤ 4325482966199^3439*2500000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310640523 2500000000 4325482966199 10000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621281373/5000000000 : ℝ)^4463 ≤ (43254836664657/100000000000000 : ℝ)^3439 := by
    have hnat : (2621281373 : ℕ)^4463*100000000000000^3439 ≤ 43254836664657^3439*5000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621281373 5000000000 43254836664657 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1068075857/5000000000 : ℝ), (1310640523/2500000000 : ℝ), (2621281373/5000000000 : ℝ)] ![(3372583414739/25000000000000 : ℝ), (4325482966199/10000000000000 : ℝ), (43254836664657/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1068075857/5000000000 : ℝ)|^4463 ≤ (3372583414739/25000000000000 : ℝ)^3439
        have hw : |(-1068075857/5000000000 : ℝ)|=(1068075857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310640523/2500000000 : ℝ)|^4463 ≤ (4325482966199/10000000000000 : ℝ)^3439
        have hw : |(1310640523/2500000000 : ℝ)|=(1310640523/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621281373/5000000000 : ℝ)|^4463 ≤ (43254836664657/100000000000000 : ℝ)^3439
        have hw : |(2621281373/5000000000 : ℝ)|=(2621281373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1483_box_5 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5384324759/10000000000 : ℝ)*x 0 + (-1947672661/10000000000 : ℝ)*x 1 + (1310640679/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5384324759/10000000000 : ℝ)^4463 ≤ (22389408923613/50000000000000 : ℝ)^3439 := by
    have hnat : (5384324759 : ℕ)^4463*50000000000000^3439 ≤ 22389408923613^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384324759 10000000000 22389408923613 50000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1947672661/10000000000 : ℝ)^4463 ≤ (2991586449629/25000000000000 : ℝ)^3439 := by
    have hnat : (1947672661 : ℕ)^4463*25000000000000^3439 ≤ 2991586449629^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1947672661 10000000000 2991586449629 25000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310640679/2500000000 : ℝ)^4463 ≤ (21627418171717/50000000000000 : ℝ)^3439 := by
    have hnat : (1310640679 : ℕ)^4463*50000000000000^3439 ≤ 21627418171717^3439*2500000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310640679 2500000000 21627418171717 50000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5384324759/10000000000 : ℝ), (-1947672661/10000000000 : ℝ), (1310640679/2500000000 : ℝ)] ![(22389408923613/50000000000000 : ℝ), (2991586449629/25000000000000 : ℝ), (21627418171717/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5384324759/10000000000 : ℝ)|^4463 ≤ (22389408923613/50000000000000 : ℝ)^3439
        have hw : |(5384324759/10000000000 : ℝ)|=(5384324759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1947672661/10000000000 : ℝ)|^4463 ≤ (2991586449629/25000000000000 : ℝ)^3439
        have hw : |(-1947672661/10000000000 : ℝ)|=(1947672661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310640679/2500000000 : ℝ)|^4463 ≤ (21627418171717/50000000000000 : ℝ)^3439
        have hw : |(1310640679/2500000000 : ℝ)|=(1310640679/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1483_box_6 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5384324821/10000000000 : ℝ)*x 0 + (262128121/500000000 : ℝ)*x 1 + (-1947672973/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5384324821/10000000000 : ℝ)^4463 ≤ (44778818516383/100000000000000 : ℝ)^3439 := by
    have hnat : (5384324821 : ℕ)^4463*100000000000000^3439 ≤ 44778818516383^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384324821 10000000000 44778818516383 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (262128121/500000000 : ℝ)^4463 ≤ (43254833174031/100000000000000 : ℝ)^3439 := by
    have hnat : (262128121 : ℕ)^4463*100000000000000^3439 ≤ 43254833174031^3439*500000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262128121 500000000 43254833174031 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1947672973/10000000000 : ℝ)^4463 ≤ (5983174143099/50000000000000 : ℝ)^3439 := by
    have hnat : (1947672973 : ℕ)^4463*50000000000000^3439 ≤ 5983174143099^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1947672973 10000000000 5983174143099 50000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5384324821/10000000000 : ℝ), (262128121/500000000 : ℝ), (-1947672973/10000000000 : ℝ)] ![(44778818516383/100000000000000 : ℝ), (43254833174031/100000000000000 : ℝ), (5983174143099/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5384324821/10000000000 : ℝ)|^4463 ≤ (44778818516383/100000000000000 : ℝ)^3439
        have hw : |(5384324821/10000000000 : ℝ)|=(5384324821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(262128121/500000000 : ℝ)|^4463 ≤ (43254833174031/100000000000000 : ℝ)^3439
        have hw : |(262128121/500000000 : ℝ)|=(262128121/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1947672973/10000000000 : ℝ)|^4463 ≤ (5983174143099/50000000000000 : ℝ)^3439
        have hw : |(-1947672973/10000000000 : ℝ)|=(1947672973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1483_box_7 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4076748403/10000000000 : ℝ)*x 0 + (4393871877/10000000000 : ℝ)*x 1 + (1098468009/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4076748403/10000000000 : ℝ)^4463 ≤ (31209053577647/100000000000000 : ℝ)^3439 := by
    have hnat : (4076748403 : ℕ)^4463*100000000000000^3439 ≤ 31209053577647^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4076748403 10000000000 31209053577647 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4393871877/10000000000 : ℝ)^4463 ≤ (1074858512439/3125000000000 : ℝ)^3439 := by
    have hnat : (4393871877 : ℕ)^4463*3125000000000^3439 ≤ 1074858512439^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4393871877 10000000000 1074858512439 3125000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1098468009/2500000000 : ℝ)^4463 ≤ (859886850333/2500000000000 : ℝ)^3439 := by
    have hnat : (1098468009 : ℕ)^4463*2500000000000^3439 ≤ 859886850333^3439*2500000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098468009 2500000000 859886850333 2500000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4076748403/10000000000 : ℝ), (4393871877/10000000000 : ℝ), (1098468009/2500000000 : ℝ)] ![(31209053577647/100000000000000 : ℝ), (1074858512439/3125000000000 : ℝ), (859886850333/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4076748403/10000000000 : ℝ)|^4463 ≤ (31209053577647/100000000000000 : ℝ)^3439
        have hw : |(4076748403/10000000000 : ℝ)|=(4076748403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4393871877/10000000000 : ℝ)|^4463 ≤ (1074858512439/3125000000000 : ℝ)^3439
        have hw : |(4393871877/10000000000 : ℝ)|=(4393871877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1098468009/2500000000 : ℝ)|^4463 ≤ (859886850333/2500000000000 : ℝ)^3439
        have hw : |(1098468009/2500000000 : ℝ)|=(1098468009/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1483_box_8 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1021309461/5000000000 : ℝ)*x 0 + (5128408863/10000000000 : ℝ)*x 1 + (2713255563/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1021309461/5000000000 : ℝ)^4463 ≤ (12728817572967/100000000000000 : ℝ)^3439 := by
    have hnat : (1021309461 : ℕ)^4463*100000000000000^3439 ≤ 12728817572967^3439*5000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1021309461 5000000000 12728817572967 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5128408863/10000000000 : ℝ)^4463 ≤ (10509130835097/25000000000000 : ℝ)^3439 := by
    have hnat : (5128408863 : ℕ)^4463*25000000000000^3439 ≤ 10509130835097^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5128408863 10000000000 10509130835097 25000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2713255563/5000000000 : ℝ)^4463 ≤ (22617329532481/50000000000000 : ℝ)^3439 := by
    have hnat : (2713255563 : ℕ)^4463*50000000000000^3439 ≤ 22617329532481^3439*5000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713255563 5000000000 22617329532481 50000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1021309461/5000000000 : ℝ), (5128408863/10000000000 : ℝ), (2713255563/5000000000 : ℝ)] ![(12728817572967/100000000000000 : ℝ), (10509130835097/25000000000000 : ℝ), (22617329532481/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1021309461/5000000000 : ℝ)|^4463 ≤ (12728817572967/100000000000000 : ℝ)^3439
        have hw : |(-1021309461/5000000000 : ℝ)|=(1021309461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5128408863/10000000000 : ℝ)|^4463 ≤ (10509130835097/25000000000000 : ℝ)^3439
        have hw : |(5128408863/10000000000 : ℝ)|=(5128408863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2713255563/5000000000 : ℝ)|^4463 ≤ (22617329532481/50000000000000 : ℝ)^3439
        have hw : |(2713255563/5000000000 : ℝ)|=(2713255563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1483_box_9 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5255957883/10000000000 : ℝ)*x 0 + (-936032843/5000000000 : ℝ)*x 1 + (5426511139/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5255957883/10000000000 : ℝ)^4463 ≤ (21699159425543/50000000000000 : ℝ)^3439 := by
    have hnat : (5255957883 : ℕ)^4463*50000000000000^3439 ≤ 21699159425543^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255957883 10000000000 21699159425543 50000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (936032843/5000000000 : ℝ)^4463 ≤ (568351096219/5000000000000 : ℝ)^3439 := by
    have hnat : (936032843 : ℕ)^4463*5000000000000^3439 ≤ 568351096219^3439*5000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      936032843 5000000000 568351096219 5000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5426511139/10000000000 : ℝ)^4463 ≤ (11308664801399/25000000000000 : ℝ)^3439 := by
    have hnat : (5426511139 : ℕ)^4463*25000000000000^3439 ≤ 11308664801399^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426511139 10000000000 11308664801399 25000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5255957883/10000000000 : ℝ), (-936032843/5000000000 : ℝ), (5426511139/10000000000 : ℝ)] ![(21699159425543/50000000000000 : ℝ), (568351096219/5000000000000 : ℝ), (11308664801399/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5255957883/10000000000 : ℝ)|^4463 ≤ (21699159425543/50000000000000 : ℝ)^3439
        have hw : |(5255957883/10000000000 : ℝ)|=(5255957883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-936032843/5000000000 : ℝ)|^4463 ≤ (568351096219/5000000000000 : ℝ)^3439
        have hw : |(-936032843/5000000000 : ℝ)|=(936032843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5426511139/10000000000 : ℝ)|^4463 ≤ (11308664801399/25000000000000 : ℝ)^3439
        have hw : |(5426511139/10000000000 : ℝ)|=(5426511139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1483_box_10 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5255957911/10000000000 : ℝ)*x 0 + (2713255561/5000000000 : ℝ)*x 1 + (-234008209/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5255957911/10000000000 : ℝ)^4463 ≤ (21699159575561/50000000000000 : ℝ)^3439 := by
    have hnat : (5255957911 : ℕ)^4463*50000000000000^3439 ≤ 21699159575561^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255957911 10000000000 21699159575561 50000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2713255561/5000000000 : ℝ)^4463 ≤ (4523465902169/10000000000000 : ℝ)^3439 := by
    have hnat : (2713255561 : ℕ)^4463*10000000000000^3439 ≤ 4523465902169^3439*5000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713255561 5000000000 4523465902169 10000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (234008209/1250000000 : ℝ)^4463 ≤ (11367021814061/100000000000000 : ℝ)^3439 := by
    have hnat : (234008209 : ℕ)^4463*100000000000000^3439 ≤ 11367021814061^3439*1250000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      234008209 1250000000 11367021814061 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5255957911/10000000000 : ℝ), (2713255561/5000000000 : ℝ), (-234008209/1250000000 : ℝ)] ![(21699159575561/50000000000000 : ℝ), (4523465902169/10000000000000 : ℝ), (11367021814061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5255957911/10000000000 : ℝ)|^4463 ≤ (21699159575561/50000000000000 : ℝ)^3439
        have hw : |(5255957911/10000000000 : ℝ)|=(5255957911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2713255561/5000000000 : ℝ)|^4463 ≤ (4523465902169/10000000000000 : ℝ)^3439
        have hw : |(2713255561/5000000000 : ℝ)|=(2713255561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-234008209/1250000000 : ℝ)|^4463 ≤ (11367021814061/100000000000000 : ℝ)^3439
        have hw : |(-234008209/1250000000 : ℝ)|=(234008209/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1483_box_11 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (283652453/625000000 : ℝ)*x 0 + (4162573053/10000000000 : ℝ)*x 1 + (4162573033/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (283652453/625000000 : ℝ)^4463 ≤ (71742527693/200000000000 : ℝ)^3439 := by
    have hnat : (283652453 : ℕ)^4463*200000000000^3439 ≤ 71742527693^3439*625000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283652453 625000000 71742527693 200000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4162573053/10000000000 : ℝ)^4463 ≤ (32064368165619/100000000000000 : ℝ)^3439 := by
    have hnat : (4162573053 : ℕ)^4463*100000000000000^3439 ≤ 32064368165619^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4162573053 10000000000 32064368165619 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4162573033/10000000000 : ℝ)^4463 ≤ (16032183982843/50000000000000 : ℝ)^3439 := by
    have hnat : (4162573033 : ℕ)^4463*50000000000000^3439 ≤ 16032183982843^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4162573033 10000000000 16032183982843 50000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(283652453/625000000 : ℝ), (4162573053/10000000000 : ℝ), (4162573033/10000000000 : ℝ)] ![(71742527693/200000000000 : ℝ), (32064368165619/100000000000000 : ℝ), (16032183982843/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(283652453/625000000 : ℝ)|^4463 ≤ (71742527693/200000000000 : ℝ)^3439
        have hw : |(283652453/625000000 : ℝ)|=(283652453/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4162573053/10000000000 : ℝ)|^4463 ≤ (32064368165619/100000000000000 : ℝ)^3439
        have hw : |(4162573053/10000000000 : ℝ)|=(4162573053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4162573033/10000000000 : ℝ)|^4463 ≤ (16032183982843/50000000000000 : ℝ)^3439
        have hw : |(4162573033/10000000000 : ℝ)|=(4162573033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1483_box_12 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1786410677/10000000000 : ℝ)*x 0 + (5516353361/10000000000 : ℝ)*x 1 + (5227565907/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1786410677/10000000000 : ℝ)^4463 ≤ (2139343511201/20000000000000 : ℝ)^3439 := by
    have hnat : (1786410677 : ℕ)^4463*20000000000000^3439 ≤ 2139343511201^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1786410677 10000000000 2139343511201 20000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5516353361/10000000000 : ℝ)^4463 ≤ (46208955118829/100000000000000 : ℝ)^3439 := by
    have hnat : (5516353361 : ℕ)^4463*100000000000000^3439 ≤ 46208955118829^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5516353361 10000000000 46208955118829 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5227565907/10000000000 : ℝ)^4463 ≤ (4309432730733/10000000000000 : ℝ)^3439 := by
    have hnat : (5227565907 : ℕ)^4463*10000000000000^3439 ≤ 4309432730733^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5227565907 10000000000 4309432730733 10000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1786410677/10000000000 : ℝ), (5516353361/10000000000 : ℝ), (5227565907/10000000000 : ℝ)] ![(2139343511201/20000000000000 : ℝ), (46208955118829/100000000000000 : ℝ), (4309432730733/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1786410677/10000000000 : ℝ)|^4463 ≤ (2139343511201/20000000000000 : ℝ)^3439
        have hw : |(-1786410677/10000000000 : ℝ)|=(1786410677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5516353361/10000000000 : ℝ)|^4463 ≤ (46208955118829/100000000000000 : ℝ)^3439
        have hw : |(5516353361/10000000000 : ℝ)|=(5516353361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5227565907/10000000000 : ℝ)|^4463 ≤ (4309432730733/10000000000000 : ℝ)^3439
        have hw : |(5227565907/10000000000 : ℝ)|=(5227565907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1483_box_13 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (168587131/312500000 : ℝ)*x 0 + (-244204143/1250000000 : ℝ)*x 1 + (5227565863/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (168587131/312500000 : ℝ)^4463 ≤ (44891780754631/100000000000000 : ℝ)^3439 := by
    have hnat : (168587131 : ℕ)^4463*100000000000000^3439 ≤ 44891780754631^3439*312500000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168587131 312500000 44891780754631 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (244204143/1250000000 : ℝ)^4463 ≤ (12013892394751/100000000000000 : ℝ)^3439 := by
    have hnat : (244204143 : ℕ)^4463*100000000000000^3439 ≤ 12013892394751^3439*1250000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      244204143 1250000000 12013892394751 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5227565863/10000000000 : ℝ)^4463 ≤ (10773581709151/25000000000000 : ℝ)^3439 := by
    have hnat : (5227565863 : ℕ)^4463*25000000000000^3439 ≤ 10773581709151^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5227565863 10000000000 10773581709151 25000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(168587131/312500000 : ℝ), (-244204143/1250000000 : ℝ), (5227565863/10000000000 : ℝ)] ![(44891780754631/100000000000000 : ℝ), (12013892394751/100000000000000 : ℝ), (10773581709151/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(168587131/312500000 : ℝ)|^4463 ≤ (44891780754631/100000000000000 : ℝ)^3439
        have hw : |(168587131/312500000 : ℝ)|=(168587131/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-244204143/1250000000 : ℝ)|^4463 ≤ (12013892394751/100000000000000 : ℝ)^3439
        have hw : |(-244204143/1250000000 : ℝ)|=(244204143/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5227565863/10000000000 : ℝ)|^4463 ≤ (10773581709151/25000000000000 : ℝ)^3439
        have hw : |(5227565863/10000000000 : ℝ)|=(5227565863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1483_box_14 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5394788273/10000000000 : ℝ)*x 0 + (5227565993/10000000000 : ℝ)*x 1 + (-97681643/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5394788273/10000000000 : ℝ)^4463 ≤ (44891781629357/100000000000000 : ℝ)^3439 := by
    have hnat : (5394788273 : ℕ)^4463*100000000000000^3439 ≤ 44891781629357^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394788273 10000000000 44891781629357 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5227565993/10000000000 : ℝ)^4463 ≤ (8618865645477/20000000000000 : ℝ)^3439 := by
    have hnat : (5227565993 : ℕ)^4463*20000000000000^3439 ≤ 8618865645477^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5227565993 10000000000 8618865645477 20000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (97681643/500000000 : ℝ)^4463 ≤ (12013890128261/100000000000000 : ℝ)^3439 := by
    have hnat : (97681643 : ℕ)^4463*100000000000000^3439 ≤ 12013890128261^3439*500000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      97681643 500000000 12013890128261 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5394788273/10000000000 : ℝ), (5227565993/10000000000 : ℝ), (-97681643/500000000 : ℝ)] ![(44891781629357/100000000000000 : ℝ), (8618865645477/20000000000000 : ℝ), (12013890128261/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5394788273/10000000000 : ℝ)|^4463 ≤ (44891781629357/100000000000000 : ℝ)^3439
        have hw : |(5394788273/10000000000 : ℝ)|=(5394788273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5227565993/10000000000 : ℝ)|^4463 ≤ (8618865645477/20000000000000 : ℝ)^3439
        have hw : |(5227565993/10000000000 : ℝ)|=(5227565993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-97681643/500000000 : ℝ)|^4463 ≤ (12013890128261/100000000000000 : ℝ)^3439
        have hw : |(-97681643/500000000 : ℝ)|=(97681643/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1483_box_15 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4038155219/10000000000 : ℝ)*x 0 + (4412704799/10000000000 : ℝ)*x 1 + (2206351831/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4038155219/10000000000 : ℝ)^4463 ≤ (30826177599251/100000000000000 : ℝ)^3439 := by
    have hnat : (4038155219 : ℕ)^4463*100000000000000^3439 ≤ 30826177599251^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4038155219 10000000000 30826177599251 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4412704799/10000000000 : ℝ)^4463 ≤ (8646729244809/25000000000000 : ℝ)^3439 := by
    have hnat : (4412704799 : ℕ)^4463*25000000000000^3439 ≤ 8646729244809^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4412704799 10000000000 8646729244809 25000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2206351831/5000000000 : ℝ)^4463 ≤ (34586905413797/100000000000000 : ℝ)^3439 := by
    have hnat : (2206351831 : ℕ)^4463*100000000000000^3439 ≤ 34586905413797^3439*5000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2206351831 5000000000 34586905413797 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4038155219/10000000000 : ℝ), (4412704799/10000000000 : ℝ), (2206351831/5000000000 : ℝ)] ![(30826177599251/100000000000000 : ℝ), (8646729244809/25000000000000 : ℝ), (34586905413797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4038155219/10000000000 : ℝ)|^4463 ≤ (30826177599251/100000000000000 : ℝ)^3439
        have hw : |(4038155219/10000000000 : ℝ)|=(4038155219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4412704799/10000000000 : ℝ)|^4463 ≤ (8646729244809/25000000000000 : ℝ)^3439
        have hw : |(4412704799/10000000000 : ℝ)|=(4412704799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2206351831/5000000000 : ℝ)|^4463 ≤ (34586905413797/100000000000000 : ℝ)^3439
        have hw : |(2206351831/5000000000 : ℝ)|=(2206351831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1483_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161066273/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3869/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10799/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(12741/20000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(14623/25000 : ℝ) ∧ (40001/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (85813/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3869/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10799/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3869/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10799/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3869/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10799/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3869/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10799/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3869/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10799/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3869/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10799/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10799/100000 : ℝ) ^ (4461/1024 : ℝ) ≤ (6151602417831753/100000000000000000000 : ℝ) := by
    have hpowers : (10799/100000 : ℝ)^4461 ≤ (6151602417831753/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10799 : ℕ)^4461*100000000000000000000^1024 ≤ 6151602417831753^1024*100000^4461 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10799 100000 6151602417831753 100000000000000000000 4461 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10799/100000 : ℝ)) (X := (6151602417831753/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4461 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3869/25000 : ℝ) ^ (4461/1024 : ℝ) ≤ (7374499363289293/25000000000000000000 : ℝ) := by
    have hpowers : (3869/25000 : ℝ)^4461 ≤ (7374499363289293/25000000000000000000 : ℝ)^1024 := by
      have hnat : (3869 : ℕ)^4461*25000000000000000000^1024 ≤ 7374499363289293^1024*25000^4461 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3869 25000 7374499363289293 25000000000000000000 4461 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3869/25000 : ℝ)) (X := (7374499363289293/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4461 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006151602417831753/50000000000000000000 : ℝ) ≤ (2000056480092741/2000000000000000 : ℝ) ^ (4461/1024 : ℝ) := by
    have hpowers : (50006151602417831753/50000000000000000000 : ℝ)^1024 ≤ (2000056480092741/2000000000000000 : ℝ)^4461 := by
      have hnat : (50006151602417831753 : ℕ)^1024*2000000000000000^4461 ≤ 2000056480092741^4461*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006151602417831753 50000000000000000000 2000056480092741 2000000000000000 1024 4461 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000056480092741/2000000000000000 : ℝ)) (X := (50006151602417831753/50000000000000000000 : ℝ)) (by norm_num) 4461 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (4001425983994839557/4000000000000000000 : ℝ) ≤ (5000409103093353/5000000000000000 : ℝ) ^ (4461/1024 : ℝ) := by
    have hpowers : (4001425983994839557/4000000000000000000 : ℝ)^1024 ≤ (5000409103093353/5000000000000000 : ℝ)^4461 := by
      have hnat : (4001425983994839557 : ℕ)^1024*5000000000000000^4461 ≤ 5000409103093353^4461*4000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4001425983994839557 4000000000000000000 5000409103093353 5000000000000000 1024 4461 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000409103093353/5000000000000000 : ℝ)) (X := (4001425983994839557/4000000000000000000 : ℝ)) (by norm_num) 4461 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507374499363289293/12500000000000000000 : ℝ) ≤ (10001354011909707/10000000000000000 : ℝ) ^ (4461/1024 : ℝ) := by
    have hpowers : (12507374499363289293/12500000000000000000 : ℝ)^1024 ≤ (10001354011909707/10000000000000000 : ℝ)^4461 := by
      have hnat : (12507374499363289293 : ℕ)^1024*10000000000000000^4461 ≤ 10001354011909707^4461*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507374499363289293 12500000000000000000 10001354011909707 10000000000000000 1024 4461 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001354011909707/10000000000000000 : ℝ)) (X := (12507374499363289293/12500000000000000000 : ℝ)) (by norm_num) 4461 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6151602417831753/100000000000000000000 : ℝ) ≤ ((15586582818321124229/15590000000000000000 : ℝ)+2*(178601907667/155900000000000 : ℝ)*(10799/100000 : ℝ))^(4461/1024 : ℝ) := by
    rw [show (15586582818321124229/15590000000000000000 : ℝ)+2*(178601907667/155900000000000 : ℝ)*(10799/100000 : ℝ)=(2000056480092741/2000000000000000 : ℝ) by norm_num, show 1+2*(6151602417831753/100000000000000000000 : ℝ)=(50006151602417831753/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7374499363289293/25000000000000000000 : ℝ)+(6151602417831753/100000000000000000000 : ℝ) ≤ ((15586582818321124229/15590000000000000000 : ℝ)+(178601907667/155900000000000 : ℝ)*((3869/25000 : ℝ)+(10799/100000 : ℝ)))^(4461/1024 : ℝ) := by
    rw [show (15586582818321124229/15590000000000000000 : ℝ)+(178601907667/155900000000000 : ℝ)*((3869/25000 : ℝ)+(10799/100000 : ℝ))=(5000409103093353/5000000000000000 : ℝ) by norm_num, show 1+(7374499363289293/25000000000000000000 : ℝ)+(6151602417831753/100000000000000000000 : ℝ)=(4001425983994839557/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7374499363289293/25000000000000000000 : ℝ) ≤ ((15586582818321124229/15590000000000000000 : ℝ)+2*(178601907667/155900000000000 : ℝ)*(3869/25000 : ℝ))^(4461/1024 : ℝ) := by
    rw [show (15586582818321124229/15590000000000000000 : ℝ)+2*(178601907667/155900000000000 : ℝ)*(3869/25000 : ℝ)=(10001354011909707/10000000000000000 : ℝ) by norm_num, show 1+2*(7374499363289293/25000000000000000000 : ℝ)=(12507374499363289293/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (15586582818321124229/15590000000000000000 : ℝ)*(X 1 0+X 2 0)+(178601907667/155900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4461/1024 : ℝ)) (lo := (10799/100000 : ℝ)) (hi := (3869/25000 : ℝ)) (c := (15586582818321124229/15590000000000000000 : ℝ)) (alpha := (178601907667/155900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (15586582818321124229/15590000000000000000 : ℝ)*(X 0 1+X 2 1)+(178601907667/155900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4461/1024 : ℝ)) (lo := (10799/100000 : ℝ)) (hi := (3869/25000 : ℝ)) (c := (15586582818321124229/15590000000000000000 : ℝ)) (alpha := (178601907667/155900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (15586582818321124229/15590000000000000000 : ℝ)*(X 0 2+X 1 2)+(178601907667/155900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4461/1024 : ℝ)) (lo := (10799/100000 : ℝ)) (hi := (3869/25000 : ℝ)) (c := (15586582818321124229/15590000000000000000 : ℝ)) (alpha := (178601907667/155900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-169276413/1000000000 : ℝ)*X 0 0+(5405974131/10000000000 : ℝ)*X 0 1+(168936707/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5270295899/10000000000 : ℝ)*X 1 0+(-940366119/5000000000 : ℝ)*X 1 1+(5405974331/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1054059239/2000000000 : ℝ)*X 2 0+(2702987059/5000000000 : ℝ)*X 2 1+(-58772879/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4487920283/10000000000 : ℝ)*X 0 0+(2094212013/5000000000 : ℝ)*X 0 1+(418842447/1000000000 : ℝ)*X 0 2+(4487920283/10000000000 : ℝ)*X 1 0+(2094212013/5000000000 : ℝ)*X 1 1+(418842447/1000000000 : ℝ)*X 1 2+(4487920283/10000000000 : ℝ)*X 2 0+(2094212013/5000000000 : ℝ)*X 2 1+(418842447/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1068075857/5000000000 : ℝ)*X 0 0+(1310640523/2500000000 : ℝ)*X 0 1+(2621281373/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5384324759/10000000000 : ℝ)*X 1 0+(-1947672661/10000000000 : ℝ)*X 1 1+(1310640679/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5384324821/10000000000 : ℝ)*X 2 0+(262128121/500000000 : ℝ)*X 2 1+(-1947672973/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4076748403/10000000000 : ℝ)*X 0 0+(4393871877/10000000000 : ℝ)*X 0 1+(1098468009/2500000000 : ℝ)*X 0 2+(4076748403/10000000000 : ℝ)*X 1 0+(4393871877/10000000000 : ℝ)*X 1 1+(1098468009/2500000000 : ℝ)*X 1 2+(4076748403/10000000000 : ℝ)*X 2 0+(4393871877/10000000000 : ℝ)*X 2 1+(1098468009/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1021309461/5000000000 : ℝ)*X 0 0+(5128408863/10000000000 : ℝ)*X 0 1+(2713255563/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5255957883/10000000000 : ℝ)*X 1 0+(-936032843/5000000000 : ℝ)*X 1 1+(5426511139/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5255957911/10000000000 : ℝ)*X 2 0+(2713255561/5000000000 : ℝ)*X 2 1+(-234008209/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((283652453/625000000 : ℝ)*X 0 0+(4162573053/10000000000 : ℝ)*X 0 1+(4162573033/10000000000 : ℝ)*X 0 2+(283652453/625000000 : ℝ)*X 1 0+(4162573053/10000000000 : ℝ)*X 1 1+(4162573033/10000000000 : ℝ)*X 1 2+(283652453/625000000 : ℝ)*X 2 0+(4162573053/10000000000 : ℝ)*X 2 1+(4162573033/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1786410677/10000000000 : ℝ)*X 0 0+(5516353361/10000000000 : ℝ)*X 0 1+(5227565907/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((168587131/312500000 : ℝ)*X 1 0+(-244204143/1250000000 : ℝ)*X 1 1+(5227565863/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5394788273/10000000000 : ℝ)*X 2 0+(5227565993/10000000000 : ℝ)*X 2 1+(-97681643/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4038155219/10000000000 : ℝ)*X 0 0+(4412704799/10000000000 : ℝ)*X 0 1+(2206351831/5000000000 : ℝ)*X 0 2+(4038155219/10000000000 : ℝ)*X 1 0+(4412704799/10000000000 : ℝ)*X 1 1+(2206351831/5000000000 : ℝ)*X 1 2+(4038155219/10000000000 : ℝ)*X 2 0+(4412704799/10000000000 : ℝ)*X 2 1+(2206351831/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-12741/20000 : ℝ) ≤ (-62070241980999619085490379951497/97437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (39157207/100000000000000 : ℝ)*(upper1) + (22423623/25000000000000 : ℝ)*(lower4) + (1469597/5000000000000 : ℝ)*(upper5) + (272531134766131/12500000000000 : ℝ)*(major0) + (272531134766131/12500000000000 : ℝ)*(major1) + (272531134766131/12500000000000 : ℝ)*(major2) + (7051756341/100000000000000 : ℝ)*(sp2) + (1611484507/100000000000000 : ℝ)*(sp3) + (757022707002787/25000000000000 : ℝ)*(sp4) + (1514035387600509/50000000000000 : ℝ)*(sp5) + (302809053920269/10000000000000 : ℝ)*(sp6) + (676816580517453/50000000000000 : ℝ)*(sp7) + (6762947883/100000000000000 : ℝ)*(sp12) + (13407879007/50000000000000 : ℝ)*(sp13) + (676817386259707/50000000000000 : ℝ)*(f.failure) + (3028097590959031/100000000000000 : ℝ)*(f.sum) + (1194129064431/487187500000000000000000000 : ℝ)*base65 + (1103132359330762999/194875000000000000000000000000000 : ℝ)*base67 + (221614893049762999/194875000000000000000000000000000 : ℝ)*base69 + (971057864760987001/194875000000000000000000000000000 : ℝ)*base72 + (29854865665583/3897500000000000000000000000 : ℝ)*base73 + (1154398199285112001/194875000000000000000000000000000 : ℝ)*base76 + (689196138368387999/194875000000000000000000000000000 : ℝ)*base77 + (258893781533137999/194875000000000000000000000000000 : ℝ)*base79 + (1936405680743/974375000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (16562011/5000000000000000000000 : ℝ)*base89 + (16562011/5000000000000000000000 : ℝ)*base91 + (16562011/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (14623/25000 : ℝ) ≤ (455962634767728050342770700183583/779500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (94547029/100000000000000 : ℝ)*(lower3) + (16043233/100000000000000 : ℝ)*(upper4) + (5840519/12500000000000 : ℝ)*(upper5) + (2254517964705403/100000000000000 : ℝ)*(major0) + (2254517964705403/100000000000000 : ℝ)*(major1) + (2254517964705403/100000000000000 : ℝ)*(major2) + (772447616999881/25000000000000 : ℝ)*(sp0) + (3089790052911513/100000000000000 : ℝ)*(sp1) + (386219711236119/12500000000000 : ℝ)*(sp2) + (174968063073809/12500000000000 : ℝ)*(sp3) + (565012153/25000000000000 : ℝ)*(sp5) + (1030407661/100000000000000 : ℝ)*(sp7) + (34623071173/100000000000000 : ℝ)*(sp10) + (1844960601/100000000000000 : ℝ)*(sp12) + (1399745534998133/100000000000000 : ℝ)*(f.failure) + (24718338503681/800000000000 : ℝ)*(f.sum) + (25534503161011/7795000000000000000000000000 : ℝ)*base65 + (10720011173635390713/1559000000000000000000000000000000 : ℝ)*base68 + (8008213526690390713/1559000000000000000000000000000000 : ℝ)*base70 + (7255843143355390713/1559000000000000000000000000000000 : ℝ)*base72 + (1742035784029/1948750000000000000000000000 : ℝ)*base73 + (11714290015498390713/1559000000000000000000000000000000 : ℝ)*base76 + (7933333950687390713/1559000000000000000000000000000000 : ℝ)*base78 + (11632005652518390713/1559000000000000000000000000000000 : ℝ)*base80 + (3103910289779/7795000000000000000000000000 : ℝ)*base82 + (44268309/10000000000000000000000 : ℝ)*base89 + (44268309/10000000000000000000000 : ℝ)*base91 + (44268309/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (40001/50000 : ℝ) ≤ (311815861949377752852220754175411/389750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1119951/12500000000000 : ℝ)*(lower3) + (8628391/100000000000000 : ℝ)*(upper4) + (3422601/50000000000000 : ℝ)*(lower5) + (1225846540473649/50000000000000 : ℝ)*(major0) + (1225846540473649/50000000000000 : ℝ)*(major1) + (1225846540473649/50000000000000 : ℝ)*(major2) + (218914107/100000000000000 : ℝ)*(sp0) + (838135433/12500000000000 : ℝ)*(sp1) + (3085933827/50000000000000 : ℝ)*(sp2) + (7957417/200000000000 : ℝ)*(sp3) + (838638440009119/25000000000000 : ℝ)*(sp8) + (1677273636933559/50000000000000 : ℝ)*(sp9) + (209659237942683/6250000000000 : ℝ)*(sp10) + (761080090488529/50000000000000 : ℝ)*(sp11) + (761082079842779/50000000000000 : ℝ)*(f.failure) + (1677276989475291/50000000000000 : ℝ)*(f.sum) + (3255249055919/1948750000000000000000000000 : ℝ)*base65 + (44674736837741621/779500000000000000000000000000000 : ℝ)*base67 + (1323964585607241621/779500000000000000000000000000000 : ℝ)*base69 + (4424302241205241621/779500000000000000000000000000000 : ℝ)*base71 + (4918815152741/1948750000000000000000000000 : ℝ)*base74 + (5555139505468241621/779500000000000000000000000000000 : ℝ)*base75 + (5472016804269241621/779500000000000000000000000000000 : ℝ)*base77 + (1339384027889241621/779500000000000000000000000000000 : ℝ)*base79 + (3702322743237/974375000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (60507333/5000000000000000000000 : ℝ)*base90 + (60507333/5000000000000000000000 : ℝ)*base92 + (60507333/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-85813/100000 : ℝ) ≤ (-334447717281915027584040805997961/389750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (88960373/50000000000000 : ℝ)*(lower2) + (167354219/100000000000000 : ℝ)*(upper3) + (4548293/100000000000000 : ℝ)*(upper5) + (2490072658322297/100000000000000 : ℝ)*(major0) + (2490072658322297/100000000000000 : ℝ)*(major1) + (2490072658322297/100000000000000 : ℝ)*(major2) + (452946971/20000000000000 : ℝ)*(sp0) + (148694657097/100000000000000 : ℝ)*(sp5) + (5460184447/100000000000000 : ℝ)*(sp6) + (23692328029/50000000000000 : ℝ)*(sp7) + (865688516155249/25000000000000 : ℝ)*(sp12) + (1731303817349377/50000000000000 : ℝ)*(sp13) + (865687717292851/25000000000000 : ℝ)*(sp14) + (1545945213261879/100000000000000 : ℝ)*(sp15) + (1545992597917937/100000000000000 : ℝ)*(f.failure) + (3462756329355851/100000000000000 : ℝ)*(f.sum) + (329874800733/974375000000000000000000000 : ℝ)*base65 + (8308742575964465987/1559000000000000000000000000000000 : ℝ)*base68 + (4540136117365534013/1559000000000000000000000000000000 : ℝ)*base69 + (6547240196526465987/1559000000000000000000000000000000 : ℝ)*base72 + (55579237949631/7795000000000000000000000000 : ℝ)*base74 + (4894506684092465987/1559000000000000000000000000000000 : ℝ)*base76 + (17145208214918465987/1559000000000000000000000000000000 : ℝ)*base78 + (7637347301173465987/1559000000000000000000000000000000 : ℝ)*base80 + (8439989348587/3897500000000000000000000000 : ℝ)*base81 + (27561199/10000000000000000000000 : ℝ)*base90 + (27561199/10000000000000000000000 : ℝ)*base92 + (27561199/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1483_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161066273/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3869/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10799/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12741/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(14623/25000 : ℝ) else (40001/50000 : ℝ) ≤ X j i ∧ X j i ≤ (85813/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1483_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1483_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161066273/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7739/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10797/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12741/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(14623/25000 : ℝ) else (40001/50000 : ℝ) ≤ X j i ∧ X j i ≤ (85813/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1483_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1483_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161066273/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7739/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10797/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12741/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(14623/25000 : ℝ) else (40001/50000 : ℝ) ≤ X j i ∧ X j i ≤ (85813/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1483_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
