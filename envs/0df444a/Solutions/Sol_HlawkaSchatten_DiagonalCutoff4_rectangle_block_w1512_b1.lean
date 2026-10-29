-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1512_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:55:39.243991+00:00
-- url     : https://prove2.me/submissions/31d81721-7615-4b74-8033-f0b1b7699f09

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
theorem support_rectangle_w1512_s3_0 (p : ℝ) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4521/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-933759919/5000000000 : ℝ)*x 0 + (2718252773/5000000000 : ℝ)*x 1 + (5214693067/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (933759919/5000000000 : ℝ)^4521 ≤ (11425503396513/100000000000000 : ℝ)^3497 := by
    have hnat : (933759919 : ℕ)^4521*100000000000000^3497 ≤ 11425503396513^3497*5000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      933759919 5000000000 11425503396513 100000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2718252773/5000000000 : ℝ)^4521 ≤ (22739743081731/50000000000000 : ℝ)^3497 := by
    have hnat : (2718252773 : ℕ)^4521*50000000000000^3497 ≤ 22739743081731^3497*5000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718252773 5000000000 22739743081731 50000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5214693067/10000000000 : ℝ)^4521 ≤ (43095010426349/100000000000000 : ℝ)^3497 := by
    have hnat : (5214693067 : ℕ)^4521*100000000000000^3497 ≤ 43095010426349^3497*10000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5214693067 10000000000 43095010426349 100000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4521/1024 : ℝ)) 4521 3497 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-933759919/5000000000 : ℝ), (2718252773/5000000000 : ℝ), (5214693067/10000000000 : ℝ)] ![(11425503396513/100000000000000 : ℝ), (22739743081731/50000000000000 : ℝ), (43095010426349/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-933759919/5000000000 : ℝ)|^4521 ≤ (11425503396513/100000000000000 : ℝ)^3497
        have hw : |(-933759919/5000000000 : ℝ)|=(933759919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2718252773/5000000000 : ℝ)|^4521 ≤ (22739743081731/50000000000000 : ℝ)^3497
        have hw : |(2718252773/5000000000 : ℝ)|=(2718252773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5214693067/10000000000 : ℝ)|^4521 ≤ (43095010426349/100000000000000 : ℝ)^3497
        have hw : |(5214693067/10000000000 : ℝ)|=(5214693067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1512_s3_1 (p : ℝ) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4521/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352446873/10000000000 : ℝ)*x 0 + (-1981198781/10000000000 : ℝ)*x 1 + (5214693159/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352446873/10000000000 : ℝ)^4521 ≤ (44572440325517/100000000000000 : ℝ)^3497 := by
    have hnat : (5352446873 : ℕ)^4521*100000000000000^3497 ≤ 44572440325517^3497*10000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352446873 10000000000 44572440325517 100000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1981198781/10000000000 : ℝ)^4521 ≤ (12332548254301/100000000000000 : ℝ)^3497 := by
    have hnat : (1981198781 : ℕ)^4521*100000000000000^3497 ≤ 12332548254301^3497*10000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1981198781 10000000000 12332548254301 100000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5214693159/10000000000 : ℝ)^4521 ≤ (10773752852321/25000000000000 : ℝ)^3497 := by
    have hnat : (5214693159 : ℕ)^4521*25000000000000^3497 ≤ 10773752852321^3497*10000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5214693159 10000000000 10773752852321 25000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4521/1024 : ℝ)) 4521 3497 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352446873/10000000000 : ℝ), (-1981198781/10000000000 : ℝ), (5214693159/10000000000 : ℝ)] ![(44572440325517/100000000000000 : ℝ), (12332548254301/100000000000000 : ℝ), (10773752852321/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352446873/10000000000 : ℝ)|^4521 ≤ (44572440325517/100000000000000 : ℝ)^3497
        have hw : |(5352446873/10000000000 : ℝ)|=(5352446873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1981198781/10000000000 : ℝ)|^4521 ≤ (12332548254301/100000000000000 : ℝ)^3497
        have hw : |(-1981198781/10000000000 : ℝ)|=(1981198781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5214693159/10000000000 : ℝ)|^4521 ≤ (10773752852321/25000000000000 : ℝ)^3497
        have hw : |(5214693159/10000000000 : ℝ)|=(5214693159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1512_s3_2 (p : ℝ) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4521/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352447/10000000 : ℝ)*x 0 + (5214693071/10000000000 : ℝ)*x 1 + (-247649841/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352447/10000000 : ℝ)^4521 ≤ (22286220846397/50000000000000 : ℝ)^3497 := by
    have hnat : (5352447 : ℕ)^4521*50000000000000^3497 ≤ 22286220846397^3497*10000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352447 10000000 22286220846397 50000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5214693071/10000000000 : ℝ)^4521 ≤ (8619002093817/20000000000000 : ℝ)^3497 := by
    have hnat : (5214693071 : ℕ)^4521*20000000000000^3497 ≤ 8619002093817^3497*10000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5214693071 10000000000 8619002093817 20000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (247649841/1250000000 : ℝ)^4521 ≤ (12332547827781/100000000000000 : ℝ)^3497 := by
    have hnat : (247649841 : ℕ)^4521*100000000000000^3497 ≤ 12332547827781^3497*1250000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      247649841 1250000000 12332547827781 100000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4521/1024 : ℝ)) 4521 3497 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352447/10000000 : ℝ), (5214693071/10000000000 : ℝ), (-247649841/1250000000 : ℝ)] ![(22286220846397/50000000000000 : ℝ), (8619002093817/20000000000000 : ℝ), (12332547827781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352447/10000000 : ℝ)|^4521 ≤ (22286220846397/50000000000000 : ℝ)^3497
        have hw : |(5352447/10000000 : ℝ)|=(5352447/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5214693071/10000000000 : ℝ)|^4521 ≤ (8619002093817/20000000000000 : ℝ)^3497
        have hw : |(5214693071/10000000000 : ℝ)|=(5214693071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-247649841/1250000000 : ℝ)|^4521 ≤ (12332547827781/100000000000000 : ℝ)^3497
        have hw : |(-247649841/1250000000 : ℝ)|=(247649841/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1512_s3_3 (p : ℝ) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4521/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2134730491/5000000000 : ℝ)*x 0 + (2012129537/5000000000 : ℝ)*x 1 + (4527238173/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2134730491/5000000000 : ℝ)^4521 ≤ (33276526796589/100000000000000 : ℝ)^3497 := by
    have hnat : (2134730491 : ℕ)^4521*100000000000000^3497 ≤ 33276526796589^3497*5000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2134730491 5000000000 33276526796589 100000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2012129537/5000000000 : ℝ)^4521 ≤ (30826847234521/100000000000000 : ℝ)^3497 := by
    have hnat : (2012129537 : ℕ)^4521*100000000000000^3497 ≤ 30826847234521^3497*5000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2012129537 5000000000 30826847234521 100000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4527238173/10000000000 : ℝ)^4521 ≤ (4487078244333/12500000000000 : ℝ)^3497 := by
    have hnat : (4527238173 : ℕ)^4521*12500000000000^3497 ≤ 4487078244333^3497*10000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4527238173 10000000000 4487078244333 12500000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4521/1024 : ℝ)) 4521 3497 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2134730491/5000000000 : ℝ), (2012129537/5000000000 : ℝ), (4527238173/10000000000 : ℝ)] ![(33276526796589/100000000000000 : ℝ), (30826847234521/100000000000000 : ℝ), (4487078244333/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2134730491/5000000000 : ℝ)|^4521 ≤ (33276526796589/100000000000000 : ℝ)^3497
        have hw : |(2134730491/5000000000 : ℝ)|=(2134730491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2012129537/5000000000 : ℝ)|^4521 ≤ (30826847234521/100000000000000 : ℝ)^3497
        have hw : |(2012129537/5000000000 : ℝ)|=(2012129537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4527238173/10000000000 : ℝ)|^4521 ≤ (4487078244333/12500000000000 : ℝ)^3497
        have hw : |(4527238173/10000000000 : ℝ)|=(4527238173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1512_s3_4 (p : ℝ) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4521/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-933775501/5000000000 : ℝ)*x 0 + (5215867529/10000000000 : ℝ)*x 1 + (679415307/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (933775501/5000000000 : ℝ)^4521 ≤ (11425749888753/100000000000000 : ℝ)^3497 := by
    have hnat : (933775501 : ℕ)^4521*100000000000000^3497 ≤ 11425749888753^3497*5000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      933775501 5000000000 11425749888753 100000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5215867529/10000000000 : ℝ)^4521 ≤ (43107558885553/100000000000000 : ℝ)^3497 := by
    have hnat : (5215867529 : ℕ)^4521*100000000000000^3497 ≤ 43107558885553^3497*10000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215867529 10000000000 43107558885553 100000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (679415307/1250000000 : ℝ)^4521 ≤ (45466691215211/100000000000000 : ℝ)^3497 := by
    have hnat : (679415307 : ℕ)^4521*100000000000000^3497 ≤ 45466691215211^3497*1250000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      679415307 1250000000 45466691215211 100000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4521/1024 : ℝ)) 4521 3497 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-933775501/5000000000 : ℝ), (5215867529/10000000000 : ℝ), (679415307/1250000000 : ℝ)] ![(11425749888753/100000000000000 : ℝ), (43107558885553/100000000000000 : ℝ), (45466691215211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-933775501/5000000000 : ℝ)|^4521 ≤ (11425749888753/100000000000000 : ℝ)^3497
        have hw : |(-933775501/5000000000 : ℝ)|=(933775501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5215867529/10000000000 : ℝ)|^4521 ≤ (43107558885553/100000000000000 : ℝ)^3497
        have hw : |(5215867529/10000000000 : ℝ)|=(5215867529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(679415307/1250000000 : ℝ)|^4521 ≤ (45466691215211/100000000000000 : ℝ)^3497
        have hw : |(679415307/1250000000 : ℝ)|=(679415307/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1512_s3_5 (p : ℝ) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4521/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323554211/2500000000 : ℝ)*x 0 + (-880284703/5000000000 : ℝ)*x 1 + (5435322423/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323554211/2500000000 : ℝ)^4521 ≤ (43946539052539/100000000000000 : ℝ)^3497 := by
    have hnat : (1323554211 : ℕ)^4521*100000000000000^3497 ≤ 43946539052539^3497*2500000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323554211 2500000000 43946539052539 100000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (880284703/5000000000 : ℝ)^4521 ≤ (10586770081237/100000000000000 : ℝ)^3497 := by
    have hnat : (880284703 : ℕ)^4521*100000000000000^3497 ≤ 10586770081237^3497*5000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      880284703 5000000000 10586770081237 100000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5435322423/10000000000 : ℝ)^4521 ≤ (11366672714583/25000000000000 : ℝ)^3497 := by
    have hnat : (5435322423 : ℕ)^4521*25000000000000^3497 ≤ 11366672714583^3497*10000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435322423 10000000000 11366672714583 25000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4521/1024 : ℝ)) 4521 3497 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323554211/2500000000 : ℝ), (-880284703/5000000000 : ℝ), (5435322423/10000000000 : ℝ)] ![(43946539052539/100000000000000 : ℝ), (10586770081237/100000000000000 : ℝ), (11366672714583/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323554211/2500000000 : ℝ)|^4521 ≤ (43946539052539/100000000000000 : ℝ)^3497
        have hw : |(1323554211/2500000000 : ℝ)|=(1323554211/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-880284703/5000000000 : ℝ)|^4521 ≤ (10586770081237/100000000000000 : ℝ)^3497
        have hw : |(-880284703/5000000000 : ℝ)|=(880284703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5435322423/10000000000 : ℝ)|^4521 ≤ (11366672714583/25000000000000 : ℝ)^3497
        have hw : |(5435322423/10000000000 : ℝ)|=(5435322423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1512_s3_6 (p : ℝ) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4521/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294216809/10000000000 : ℝ)*x 0 + (5435322479/10000000000 : ℝ)*x 1 + (-55017793/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294216809/10000000000 : ℝ)^4521 ≤ (8789307735387/20000000000000 : ℝ)^3497 := by
    have hnat : (5294216809 : ℕ)^4521*20000000000000^3497 ≤ 8789307735387^3497*10000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294216809 10000000000 8789307735387 20000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5435322479/10000000000 : ℝ)^4521 ≤ (5683336432993/12500000000000 : ℝ)^3497 := by
    have hnat : (5435322479 : ℕ)^4521*12500000000000^3497 ≤ 5683336432993^3497*10000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435322479 10000000000 5683336432993 12500000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (55017793/312500000 : ℝ)^4521 ≤ (2117353969603/20000000000000 : ℝ)^3497 := by
    have hnat : (55017793 : ℕ)^4521*20000000000000^3497 ≤ 2117353969603^3497*312500000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55017793 312500000 2117353969603 20000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4521/1024 : ℝ)) 4521 3497 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294216809/10000000000 : ℝ), (5435322479/10000000000 : ℝ), (-55017793/312500000 : ℝ)] ![(8789307735387/20000000000000 : ℝ), (5683336432993/12500000000000 : ℝ), (2117353969603/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294216809/10000000000 : ℝ)|^4521 ≤ (8789307735387/20000000000000 : ℝ)^3497
        have hw : |(5294216809/10000000000 : ℝ)|=(5294216809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5435322479/10000000000 : ℝ)|^4521 ≤ (5683336432993/12500000000000 : ℝ)^3497
        have hw : |(5435322479/10000000000 : ℝ)|=(5435322479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-55017793/312500000 : ℝ)|^4521 ≤ (2117353969603/20000000000000 : ℝ)^3497
        have hw : |(-55017793/312500000 : ℝ)|=(55017793/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1512_s3_7 (p : ℝ) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4521/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (853906469/2000000000 : ℝ)*x 0 + (904915027/2000000000 : ℝ)*x 1 + (4026942443/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (853906469/2000000000 : ℝ)^4521 ≤ (16638622938931/50000000000000 : ℝ)^3497 := by
    have hnat : (853906469 : ℕ)^4521*50000000000000^3497 ≤ 16638622938931^3497*2000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      853906469 2000000000 16638622938931 50000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (904915027/2000000000 : ℝ)^4521 ≤ (8967332486997/25000000000000 : ℝ)^3497 := by
    have hnat : (904915027 : ℕ)^4521*25000000000000^3497 ≤ 8967332486997^3497*2000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      904915027 2000000000 8967332486997 25000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4026942443/10000000000 : ℝ)^4521 ≤ (7713356041569/25000000000000 : ℝ)^3497 := by
    have hnat : (4026942443 : ℕ)^4521*25000000000000^3497 ≤ 7713356041569^3497*10000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4026942443 10000000000 7713356041569 25000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4521/1024 : ℝ)) 4521 3497 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(853906469/2000000000 : ℝ), (904915027/2000000000 : ℝ), (4026942443/10000000000 : ℝ)] ![(16638622938931/50000000000000 : ℝ), (8967332486997/25000000000000 : ℝ), (7713356041569/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(853906469/2000000000 : ℝ)|^4521 ≤ (16638622938931/50000000000000 : ℝ)^3497
        have hw : |(853906469/2000000000 : ℝ)|=(853906469/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(904915027/2000000000 : ℝ)|^4521 ≤ (8967332486997/25000000000000 : ℝ)^3497
        have hw : |(904915027/2000000000 : ℝ)|=(904915027/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4026942443/10000000000 : ℝ)|^4521 ≤ (7713356041569/25000000000000 : ℝ)^3497
        have hw : |(4026942443/10000000000 : ℝ)|=(4026942443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1512_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4521/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (81689629/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3999/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10443/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10853/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (311/2000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3999/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10443/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3999/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10443/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3999/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10443/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3999/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10443/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3999/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10443/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3999/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10443/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10443/100000 : ℝ) ^ (4519/1024 : ℝ) ≤ (4677261291770011/100000000000000000000 : ℝ) := by
    have hpowers : (10443/100000 : ℝ)^4519 ≤ (4677261291770011/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10443 : ℕ)^4519*100000000000000000000^1024 ≤ 4677261291770011^1024*100000^4519 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10443 100000 4677261291770011 100000000000000000000 4519 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10443/100000 : ℝ)) (X := (4677261291770011/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4519 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3999/25000 : ℝ) ^ (4519/1024 : ℝ) ≤ (30706752101290763/100000000000000000000 : ℝ) := by
    have hpowers : (3999/25000 : ℝ)^4519 ≤ (30706752101290763/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3999 : ℕ)^4519*100000000000000000000^1024 ≤ 30706752101290763^1024*25000^4519 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3999 25000 30706752101290763 100000000000000000000 4519 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3999/25000 : ℝ)) (X := (30706752101290763/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4519 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004677261291770011/50000000000000000000 : ℝ) ≤ (10000211964696457/10000000000000000 : ℝ) ^ (4519/1024 : ℝ) := by
    have hpowers : (50004677261291770011/50000000000000000000 : ℝ)^1024 ≤ (10000211964696457/10000000000000000 : ℝ)^4519 := by
      have hnat : (50004677261291770011 : ℕ)^1024*10000000000000000^4519 ≤ 10000211964696457^4519*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004677261291770011 50000000000000000000 10000211964696457 10000000000000000 1024 4519 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000211964696457/10000000000000000 : ℝ)) (X := (50004677261291770011/50000000000000000000 : ℝ)) (by norm_num) 4519 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50017692006696530387/50000000000000000000 : ℝ) ≤ (10000801687828093/10000000000000000 : ℝ) ^ (4519/1024 : ℝ) := by
    have hpowers : (50017692006696530387/50000000000000000000 : ℝ)^1024 ≤ (10000801687828093/10000000000000000 : ℝ)^4519 := by
      have hnat : (50017692006696530387 : ℕ)^1024*10000000000000000^4519 ≤ 10000801687828093^4519*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50017692006696530387 50000000000000000000 10000801687828093 10000000000000000 1024 4519 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000801687828093/10000000000000000 : ℝ)) (X := (50017692006696530387/50000000000000000000 : ℝ)) (by norm_num) 4519 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50030706752101290763/50000000000000000000 : ℝ) ≤ (10001391410959729/10000000000000000 : ℝ) ^ (4519/1024 : ℝ) := by
    have hpowers : (50030706752101290763/50000000000000000000 : ℝ)^1024 ≤ (10001391410959729/10000000000000000 : ℝ)^4519 := by
      have hnat : (50030706752101290763 : ℕ)^1024*10000000000000000^4519 ≤ 10001391410959729^4519*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030706752101290763 50000000000000000000 10001391410959729 10000000000000000 1024 4519 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001391410959729/10000000000000000 : ℝ)) (X := (50030706752101290763/50000000000000000000 : ℝ)) (by norm_num) 4519 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4677261291770011/100000000000000000000 : ℝ) ≤ ((246750489256142561/246800000000000000 : ℝ)+2*(16381198101/15425000000000 : ℝ)*(10443/100000 : ℝ))^(4519/1024 : ℝ) := by
    rw [show (246750489256142561/246800000000000000 : ℝ)+2*(16381198101/15425000000000 : ℝ)*(10443/100000 : ℝ)=(10000211964696457/10000000000000000 : ℝ) by norm_num, show 1+2*(4677261291770011/100000000000000000000 : ℝ)=(50004677261291770011/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30706752101290763/100000000000000000000 : ℝ)+(4677261291770011/100000000000000000000 : ℝ) ≤ ((246750489256142561/246800000000000000 : ℝ)+(16381198101/15425000000000 : ℝ)*((3999/25000 : ℝ)+(10443/100000 : ℝ)))^(4519/1024 : ℝ) := by
    rw [show (246750489256142561/246800000000000000 : ℝ)+(16381198101/15425000000000 : ℝ)*((3999/25000 : ℝ)+(10443/100000 : ℝ))=(10000801687828093/10000000000000000 : ℝ) by norm_num, show 1+(30706752101290763/100000000000000000000 : ℝ)+(4677261291770011/100000000000000000000 : ℝ)=(50017692006696530387/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30706752101290763/100000000000000000000 : ℝ) ≤ ((246750489256142561/246800000000000000 : ℝ)+2*(16381198101/15425000000000 : ℝ)*(3999/25000 : ℝ))^(4519/1024 : ℝ) := by
    rw [show (246750489256142561/246800000000000000 : ℝ)+2*(16381198101/15425000000000 : ℝ)*(3999/25000 : ℝ)=(10001391410959729/10000000000000000 : ℝ) by norm_num, show 1+2*(30706752101290763/100000000000000000000 : ℝ)=(50030706752101290763/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (246750489256142561/246800000000000000 : ℝ)*(X 1 0+X 2 0)+(16381198101/15425000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4519/1024 : ℝ)) (lo := (10443/100000 : ℝ)) (hi := (3999/25000 : ℝ)) (c := (246750489256142561/246800000000000000 : ℝ)) (alpha := (16381198101/15425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (246750489256142561/246800000000000000 : ℝ)*(X 0 1+X 2 1)+(16381198101/15425000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4519/1024 : ℝ)) (lo := (10443/100000 : ℝ)) (hi := (3999/25000 : ℝ)) (c := (246750489256142561/246800000000000000 : ℝ)) (alpha := (16381198101/15425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (246750489256142561/246800000000000000 : ℝ)*(X 0 2+X 1 2)+(16381198101/15425000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4519/1024 : ℝ)) (lo := (10443/100000 : ℝ)) (hi := (3999/25000 : ℝ)) (c := (246750489256142561/246800000000000000 : ℝ)) (alpha := (16381198101/15425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-933759919/5000000000 : ℝ)*X 0 0+(2718252773/5000000000 : ℝ)*X 0 1+(5214693067/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1512_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352446873/10000000000 : ℝ)*X 1 0+(-1981198781/10000000000 : ℝ)*X 1 1+(5214693159/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1512_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352447/10000000 : ℝ)*X 2 0+(5214693071/10000000000 : ℝ)*X 2 1+(-247649841/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1512_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2134730491/5000000000 : ℝ)*X 0 0+(2012129537/5000000000 : ℝ)*X 0 1+(4527238173/10000000000 : ℝ)*X 0 2+(2134730491/5000000000 : ℝ)*X 1 0+(2012129537/5000000000 : ℝ)*X 1 1+(4527238173/10000000000 : ℝ)*X 1 2+(2134730491/5000000000 : ℝ)*X 2 0+(2012129537/5000000000 : ℝ)*X 2 1+(4527238173/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1512_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-933775501/5000000000 : ℝ)*X 0 0+(5215867529/10000000000 : ℝ)*X 0 1+(679415307/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1512_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1323554211/2500000000 : ℝ)*X 1 0+(-880284703/5000000000 : ℝ)*X 1 1+(5435322423/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1512_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5294216809/10000000000 : ℝ)*X 2 0+(5435322479/10000000000 : ℝ)*X 2 1+(-55017793/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1512_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((853906469/2000000000 : ℝ)*X 0 0+(904915027/2000000000 : ℝ)*X 0 1+(4026942443/10000000000 : ℝ)*X 0 2+(853906469/2000000000 : ℝ)*X 1 0+(904915027/2000000000 : ℝ)*X 1 1+(4026942443/10000000000 : ℝ)*X 1 2+(853906469/2000000000 : ℝ)*X 2 0+(904915027/2000000000 : ℝ)*X 2 1+(4026942443/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1512_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7547302187829872465568009/1542500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1271513297/100000000000000 : ℝ)*(base19) + (145936889/12500000000000 : ℝ)*(base23) + (48593427/20000000000000 : ℝ)*(upper3) + (56465599/50000000000000 : ℝ)*(upper4) + (161901107/100000000000000 : ℝ)*(upper5) + (812065126676123/25000000000000 : ℝ)*(major0) + (812065126676123/25000000000000 : ℝ)*(major1) + (812065126676123/25000000000000 : ℝ)*(major2) + (4508330499209259/100000000000000 : ℝ)*(sp0) + (4508347673461661/100000000000000 : ℝ)*(sp1) + (2254173888739923/50000000000000 : ℝ)*(sp2) + (1553251682951/78125000000 : ℝ)*(sp3) + (18445765699/100000000000000 : ℝ)*(sp4) + (9751159989/100000000000000 : ℝ)*(sp7) + (1988171905337269/100000000000000 : ℝ)*(f.failure) + (2254174472487479/50000000000000 : ℝ)*(f.sum) + (7635584577857/3085000000000000000000000000 : ℝ)*base66 + (20298108249860997/6170000000000000000000000000000 : ℝ)*base68 + (5826473475340997/6170000000000000000000000000000 : ℝ)*base70 + (16731964233520997/6170000000000000000000000000000 : ℝ)*base72 + (3203421123861/1542500000000000000000000000 : ℝ)*base74 + (102613616097680997/6170000000000000000000000000000 : ℝ)*base76 + (3145764673489003/6170000000000000000000000000000 : ℝ)*base77 + (86034577045630997/6170000000000000000000000000000 : ℝ)*base80 + (15089604625947/3085000000000000000000000000 : ℝ)*base82 + (24483201/5000000000000000000000 : ℝ)*base89 + (24483201/5000000000000000000000 : ℝ)*base91 + (24483201/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15040315721285727757593/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (484303189/50000000000000 : ℝ)*(base19) + (507177549/50000000000000 : ℝ)*(base23) + (119353533/100000000000000 : ℝ)*(upper3) + (809187/2500000000000 : ℝ)*(lower4) + (126053493/100000000000000 : ℝ)*(upper5) + (410391130048207/12500000000000 : ℝ)*(major0) + (410391130048207/12500000000000 : ℝ)*(major1) + (410391130048207/12500000000000 : ℝ)*(major2) + (13948593547/100000000000000 : ℝ)*(sp1) + (15288320969/100000000000000 : ℝ)*(sp2) + (911348778766861/20000000000000 : ℝ)*(sp4) + (227836448831719/5000000000000 : ℝ)*(sp5) + (2278363795579119/50000000000000 : ℝ)*(sp6) + (1004756993199729/50000000000000 : ℝ)*(sp7) + (1004756993199729/50000000000000 : ℝ)*(f.failure) + (911348778766861/20000000000000 : ℝ)*(f.sum) + (601629974753/385625000000000000000000000 : ℝ)*base65 + (14116700081924873/3085000000000000000000000000000 : ℝ)*base68 + (8002781388160127/3085000000000000000000000000000 : ℝ)*base69 + (5546061322234873/3085000000000000000000000000000 : ℝ)*base72 + (12553653578869/3085000000000000000000000000 : ℝ)*base73 + (16644809554644873/3085000000000000000000000000000 : ℝ)*base76 + (1060287119969873/3085000000000000000000000000000 : ℝ)*base78 + (10069837336315127/3085000000000000000000000000000 : ℝ)*base79 + (10359335886117/1542500000000000000000000000 : ℝ)*base81 + (15089459/2500000000000000000000 : ℝ)*base90 + (15089459/2500000000000000000000 : ℝ)*base92 + (15089459/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1512_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4521/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (81689629/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3999/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10443/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10853/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (311/2000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1512_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1512_s4_0 (p : ℝ) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4521/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1867957409/10000000000 : ℝ)*x 0 + (135840721/250000000 : ℝ)*x 1 + (1043456143/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1867957409/10000000000 : ℝ)^4521 ≤ (457158579311/4000000000000 : ℝ)^3497 := by
    have hnat : (1867957409 : ℕ)^4521*4000000000000^3497 ≤ 457158579311^3497*10000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1867957409 10000000000 457158579311 4000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (135840721/250000000 : ℝ)^4521 ≤ (2840523526311/6250000000000 : ℝ)^3497 := by
    have hnat : (135840721 : ℕ)^4521*6250000000000^3497 ≤ 2840523526311^3497*250000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135840721 250000000 2840523526311 6250000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043456143/2000000000 : ℝ)^4521 ≤ (43122659071831/100000000000000 : ℝ)^3497 := by
    have hnat : (1043456143 : ℕ)^4521*100000000000000^3497 ≤ 43122659071831^3497*2000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043456143 2000000000 43122659071831 100000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4521/1024 : ℝ)) 4521 3497 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1867957409/10000000000 : ℝ), (135840721/250000000 : ℝ), (1043456143/2000000000 : ℝ)] ![(457158579311/4000000000000 : ℝ), (2840523526311/6250000000000 : ℝ), (43122659071831/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1867957409/10000000000 : ℝ)|^4521 ≤ (457158579311/4000000000000 : ℝ)^3497
        have hw : |(-1867957409/10000000000 : ℝ)|=(1867957409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(135840721/250000000 : ℝ)|^4521 ≤ (2840523526311/6250000000000 : ℝ)^3497
        have hw : |(135840721/250000000 : ℝ)|=(135840721/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043456143/2000000000 : ℝ)|^4521 ≤ (43122659071831/100000000000000 : ℝ)^3497
        have hw : |(1043456143/2000000000 : ℝ)|=(1043456143/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1512_s4_1 (p : ℝ) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4521/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351694541/10000000000 : ℝ)*x 0 + (-1978769901/10000000000 : ℝ)*x 1 + (2608640113/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351694541/10000000000 : ℝ)^4521 ≤ (2785271307063/6250000000000 : ℝ)^3497 := by
    have hnat : (5351694541 : ℕ)^4521*6250000000000^3497 ≤ 2785271307063^3497*10000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351694541 10000000000 2785271307063 6250000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1978769901/10000000000 : ℝ)^4521 ≤ (12313005232269/100000000000000 : ℝ)^3497 := by
    have hnat : (1978769901 : ℕ)^4521*100000000000000^3497 ≤ 12313005232269^3497*10000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1978769901 10000000000 12313005232269 100000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2608640113/5000000000 : ℝ)^4521 ≤ (43122653846557/100000000000000 : ℝ)^3497 := by
    have hnat : (2608640113 : ℕ)^4521*100000000000000^3497 ≤ 43122653846557^3497*5000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608640113 5000000000 43122653846557 100000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4521/1024 : ℝ)) 4521 3497 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351694541/10000000000 : ℝ), (-1978769901/10000000000 : ℝ), (2608640113/5000000000 : ℝ)] ![(2785271307063/6250000000000 : ℝ), (12313005232269/100000000000000 : ℝ), (43122653846557/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351694541/10000000000 : ℝ)|^4521 ≤ (2785271307063/6250000000000 : ℝ)^3497
        have hw : |(5351694541/10000000000 : ℝ)|=(5351694541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1978769901/10000000000 : ℝ)|^4521 ≤ (12313005232269/100000000000000 : ℝ)^3497
        have hw : |(-1978769901/10000000000 : ℝ)|=(1978769901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2608640113/5000000000 : ℝ)|^4521 ≤ (43122653846557/100000000000000 : ℝ)^3497
        have hw : |(2608640113/5000000000 : ℝ)|=(2608640113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1512_s4_2 (p : ℝ) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4521/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (535169417/1000000000 : ℝ)*x 0 + (2608640363/5000000000 : ℝ)*x 1 + (-1978769733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535169417/1000000000 : ℝ)^4521 ≤ (44564336919/100000000000 : ℝ)^3497 := by
    have hnat : (535169417 : ℕ)^4521*100000000000^3497 ≤ 44564336919^3497*1000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535169417 1000000000 44564336919 100000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2608640363/5000000000 : ℝ)^4521 ≤ (43122659189373/100000000000000 : ℝ)^3497 := by
    have hnat : (2608640363 : ℕ)^4521*100000000000000^3497 ≤ 43122659189373^3497*5000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608640363 5000000000 43122659189373 100000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1978769733/10000000000 : ℝ)^4521 ≤ (12313003880767/100000000000000 : ℝ)^3497 := by
    have hnat : (1978769733 : ℕ)^4521*100000000000000^3497 ≤ 12313003880767^3497*10000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1978769733 10000000000 12313003880767 100000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4521/1024 : ℝ)) 4521 3497 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535169417/1000000000 : ℝ), (2608640363/5000000000 : ℝ), (-1978769733/10000000000 : ℝ)] ![(44564336919/100000000000 : ℝ), (43122659189373/100000000000000 : ℝ), (12313003880767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535169417/1000000000 : ℝ)|^4521 ≤ (44564336919/100000000000 : ℝ)^3497
        have hw : |(535169417/1000000000 : ℝ)|=(535169417/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2608640363/5000000000 : ℝ)|^4521 ≤ (43122659189373/100000000000000 : ℝ)^3497
        have hw : |(2608640363/5000000000 : ℝ)|=(2608640363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1978769733/10000000000 : ℝ)|^4521 ≤ (12313003880767/100000000000000 : ℝ)^3497
        have hw : |(-1978769733/10000000000 : ℝ)|=(1978769733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1512_s4_3 (p : ℝ) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4521/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (853946959/2000000000 : ℝ)*x 0 + (2015211499/5000000000 : ℝ)*x 1 + (90420229/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (853946959/2000000000 : ℝ)^4521 ≤ (6655857172351/20000000000000 : ℝ)^3497 := by
    have hnat : (853946959 : ℕ)^4521*20000000000000^3497 ≤ 6655857172351^3497*2000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      853946959 2000000000 6655857172351 20000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2015211499/5000000000 : ℝ)^4521 ≤ (7721976101301/25000000000000 : ℝ)^3497 := by
    have hnat : (2015211499 : ℕ)^4521*25000000000000^3497 ≤ 7721976101301^3497*5000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2015211499 5000000000 7721976101301 25000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (90420229/200000000 : ℝ)^4521 ≤ (4479101214273/12500000000000 : ℝ)^3497 := by
    have hnat : (90420229 : ℕ)^4521*12500000000000^3497 ≤ 4479101214273^3497*200000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90420229 200000000 4479101214273 12500000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4521/1024 : ℝ)) 4521 3497 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(853946959/2000000000 : ℝ), (2015211499/5000000000 : ℝ), (90420229/200000000 : ℝ)] ![(6655857172351/20000000000000 : ℝ), (7721976101301/25000000000000 : ℝ), (4479101214273/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(853946959/2000000000 : ℝ)|^4521 ≤ (6655857172351/20000000000000 : ℝ)^3497
        have hw : |(853946959/2000000000 : ℝ)|=(853946959/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2015211499/5000000000 : ℝ)|^4521 ≤ (7721976101301/25000000000000 : ℝ)^3497
        have hw : |(2015211499/5000000000 : ℝ)|=(2015211499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(90420229/200000000 : ℝ)|^4521 ≤ (4479101214273/12500000000000 : ℝ)^3497
        have hw : |(90420229/200000000 : ℝ)|=(90420229/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1512_s4_4 (p : ℝ) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4521/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1867986813/10000000000 : ℝ)*x 0 + (1043679603/2000000000 : ℝ)*x 1 + (5432503177/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1867986813/10000000000 : ℝ)^4521 ≤ (2285839414037/20000000000000 : ℝ)^3497 := by
    have hnat : (1867986813 : ℕ)^4521*20000000000000^3497 ≤ 2285839414037^3497*10000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1867986813 10000000000 2285839414037 20000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043679603/2000000000 : ℝ)^4521 ≤ (21567299251251/50000000000000 : ℝ)^3497 := by
    have hnat : (1043679603 : ℕ)^4521*50000000000000^3497 ≤ 21567299251251^3497*2000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043679603 2000000000 21567299251251 50000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5432503177/10000000000 : ℝ)^4521 ≤ (45436204405487/100000000000000 : ℝ)^3497 := by
    have hnat : (5432503177 : ℕ)^4521*100000000000000^3497 ≤ 45436204405487^3497*10000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432503177 10000000000 45436204405487 100000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4521/1024 : ℝ)) 4521 3497 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1867986813/10000000000 : ℝ), (1043679603/2000000000 : ℝ), (5432503177/10000000000 : ℝ)] ![(2285839414037/20000000000000 : ℝ), (21567299251251/50000000000000 : ℝ), (45436204405487/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1867986813/10000000000 : ℝ)|^4521 ≤ (2285839414037/20000000000000 : ℝ)^3497
        have hw : |(-1867986813/10000000000 : ℝ)|=(1867986813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043679603/2000000000 : ℝ)|^4521 ≤ (21567299251251/50000000000000 : ℝ)^3497
        have hw : |(1043679603/2000000000 : ℝ)|=(1043679603/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5432503177/10000000000 : ℝ)|^4521 ≤ (45436204405487/100000000000000 : ℝ)^3497
        have hw : |(5432503177/10000000000 : ℝ)|=(5432503177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1512_s4_5 (p : ℝ) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4521/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (529489989/1000000000 : ℝ)*x 0 + (-440886821/2500000000 : ℝ)*x 1 + (5432503193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529489989/1000000000 : ℝ)^4521 ≤ (43953869322741/100000000000000 : ℝ)^3497 := by
    have hnat : (529489989 : ℕ)^4521*100000000000000^3497 ≤ 43953869322741^3497*1000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529489989 1000000000 43953869322741 100000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (440886821/2500000000 : ℝ)^4521 ≤ (10609926084441/100000000000000 : ℝ)^3497 := by
    have hnat : (440886821 : ℕ)^4521*100000000000000^3497 ≤ 10609926084441^3497*2500000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      440886821 2500000000 10609926084441 100000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5432503193/10000000000 : ℝ)^4521 ≤ (45436204578493/100000000000000 : ℝ)^3497 := by
    have hnat : (5432503193 : ℕ)^4521*100000000000000^3497 ≤ 45436204578493^3497*10000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432503193 10000000000 45436204578493 100000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4521/1024 : ℝ)) 4521 3497 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529489989/1000000000 : ℝ), (-440886821/2500000000 : ℝ), (5432503193/10000000000 : ℝ)] ![(43953869322741/100000000000000 : ℝ), (10609926084441/100000000000000 : ℝ), (45436204578493/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529489989/1000000000 : ℝ)|^4521 ≤ (43953869322741/100000000000000 : ℝ)^3497
        have hw : |(529489989/1000000000 : ℝ)|=(529489989/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-440886821/2500000000 : ℝ)|^4521 ≤ (10609926084441/100000000000000 : ℝ)^3497
        have hw : |(-440886821/2500000000 : ℝ)|=(440886821/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5432503193/10000000000 : ℝ)|^4521 ≤ (45436204578493/100000000000000 : ℝ)^3497
        have hw : |(5432503193/10000000000 : ℝ)|=(5432503193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1512_s4_6 (p : ℝ) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4521/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323724997/2500000000 : ℝ)*x 0 + (108650063/200000000 : ℝ)*x 1 + (-220443401/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323724997/2500000000 : ℝ)^4521 ≤ (43953870374471/100000000000000 : ℝ)^3497 := by
    have hnat : (1323724997 : ℕ)^4521*100000000000000^3497 ≤ 43953870374471^3497*2500000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323724997 2500000000 43953870374471 100000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (108650063/200000000 : ℝ)^4521 ≤ (45436204113539/100000000000000 : ℝ)^3497 := by
    have hnat : (108650063 : ℕ)^4521*100000000000000^3497 ≤ 45436204113539^3497*200000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108650063 200000000 45436204113539 100000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (220443401/1250000000 : ℝ)^4521 ≤ (10609925493319/100000000000000 : ℝ)^3497 := by
    have hnat : (220443401 : ℕ)^4521*100000000000000^3497 ≤ 10609925493319^3497*1250000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220443401 1250000000 10609925493319 100000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4521/1024 : ℝ)) 4521 3497 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323724997/2500000000 : ℝ), (108650063/200000000 : ℝ), (-220443401/1250000000 : ℝ)] ![(43953870374471/100000000000000 : ℝ), (45436204113539/100000000000000 : ℝ), (10609925493319/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323724997/2500000000 : ℝ)|^4521 ≤ (43953870374471/100000000000000 : ℝ)^3497
        have hw : |(1323724997/2500000000 : ℝ)|=(1323724997/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(108650063/200000000 : ℝ)|^4521 ≤ (45436204113539/100000000000000 : ℝ)^3497
        have hw : |(108650063/200000000 : ℝ)|=(108650063/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-220443401/1250000000 : ℝ)|^4521 ≤ (10609925493319/100000000000000 : ℝ)^3497
        have hw : |(-220443401/1250000000 : ℝ)|=(220443401/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1512_s4_7 (p : ℝ) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4521/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2134900749/5000000000 : ℝ)*x 0 + (4518477101/10000000000 : ℝ)*x 1 + (4032975749/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2134900749/5000000000 : ℝ)^4521 ≤ (1331198319983/4000000000000 : ℝ)^3497 := by
    have hnat : (2134900749 : ℕ)^4521*4000000000000^3497 ≤ 1331198319983^3497*5000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2134900749 5000000000 1331198319983 4000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4518477101/10000000000 : ℝ)^4521 ≤ (17903421562677/50000000000000 : ℝ)^3497 := by
    have hnat : (4518477101 : ℕ)^4521*50000000000000^3497 ≤ 17903421562677^3497*10000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4518477101 10000000000 17903421562677 50000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4032975749/10000000000 : ℝ)^4521 ≤ (30913198865147/100000000000000 : ℝ)^3497 := by
    have hnat : (4032975749 : ℕ)^4521*100000000000000^3497 ≤ 30913198865147^3497*10000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4032975749 10000000000 30913198865147 100000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4521/1024 : ℝ)) 4521 3497 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2134900749/5000000000 : ℝ), (4518477101/10000000000 : ℝ), (4032975749/10000000000 : ℝ)] ![(1331198319983/4000000000000 : ℝ), (17903421562677/50000000000000 : ℝ), (30913198865147/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2134900749/5000000000 : ℝ)|^4521 ≤ (1331198319983/4000000000000 : ℝ)^3497
        have hw : |(2134900749/5000000000 : ℝ)|=(2134900749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4518477101/10000000000 : ℝ)|^4521 ≤ (17903421562677/50000000000000 : ℝ)^3497
        have hw : |(4518477101/10000000000 : ℝ)|=(4518477101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4032975749/10000000000 : ℝ)|^4521 ≤ (30913198865147/100000000000000 : ℝ)^3497
        have hw : |(4032975749/10000000000 : ℝ)|=(4032975749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1512_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4521/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (81689629/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (311/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10853/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2727/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1549/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (311/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10853/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (311/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10853/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (311/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10853/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (311/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10853/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (311/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10853/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (311/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10853/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10853/100000 : ℝ) ^ (4519/1024 : ℝ) ≤ (5543683125676227/100000000000000000000 : ℝ) := by
    have hpowers : (10853/100000 : ℝ)^4519 ≤ (5543683125676227/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10853 : ℕ)^4519*100000000000000000000^1024 ≤ 5543683125676227^1024*100000^4519 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10853 100000 5543683125676227 100000000000000000000 4519 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10853/100000 : ℝ)) (X := (5543683125676227/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4519 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (311/2000 : ℝ) ^ (4519/1024 : ℝ) ≤ (27104210731345851/100000000000000000000 : ℝ) := by
    have hpowers : (311/2000 : ℝ)^4519 ≤ (27104210731345851/100000000000000000000 : ℝ)^1024 := by
      have hnat : (311 : ℕ)^4519*100000000000000000000^1024 ≤ 27104210731345851^1024*2000^4519 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        311 2000 27104210731345851 100000000000000000000 4519 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (311/2000 : ℝ)) (X := (27104210731345851/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4519 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005543683125676227/50000000000000000000 : ℝ) ≤ (625015701726453/625000000000000 : ℝ) ^ (4519/1024 : ℝ) := by
    have hpowers : (50005543683125676227/50000000000000000000 : ℝ)^1024 ≤ (625015701726453/625000000000000 : ℝ)^4519 := by
      have hnat : (50005543683125676227 : ℕ)^1024*625000000000000^4519 ≤ 625015701726453^4519*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005543683125676227 50000000000000000000 625015701726453 625000000000000 1024 4519 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625015701726453/625000000000000 : ℝ)) (X := (50005543683125676227/50000000000000000000 : ℝ)) (by norm_num) 4519 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50016323946928511039/50000000000000000000 : ℝ) ≤ (1250092462999053/1250000000000000 : ℝ) ^ (4519/1024 : ℝ) := by
    have hpowers : (50016323946928511039/50000000000000000000 : ℝ)^1024 ≤ (1250092462999053/1250000000000000 : ℝ)^4519 := by
      have hnat : (50016323946928511039 : ℕ)^1024*1250000000000000^4519 ≤ 1250092462999053^4519*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50016323946928511039 50000000000000000000 1250092462999053 1250000000000000 1024 4519 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250092462999053/1250000000000000 : ℝ)) (X := (50016323946928511039/50000000000000000000 : ℝ)) (by norm_num) 4519 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50027104210731345851/50000000000000000000 : ℝ) ≤ (3125383806363/3125000000000 : ℝ) ^ (4519/1024 : ℝ) := by
    have hpowers : (50027104210731345851/50000000000000000000 : ℝ)^1024 ≤ (3125383806363/3125000000000 : ℝ)^4519 := by
      have hnat : (50027104210731345851 : ℕ)^1024*3125000000000^4519 ≤ 3125383806363^4519*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027104210731345851 50000000000000000000 3125383806363 3125000000000 1024 4519 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3125383806363/3125000000000 : ℝ)) (X := (50027104210731345851/50000000000000000000 : ℝ)) (by norm_num) 4519 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5543683125676227/100000000000000000000 : ℝ) ≤ ((58700721435096327/58712500000000000 : ℝ)+2*(61059546147/58712500000000 : ℝ)*(10853/100000 : ℝ))^(4519/1024 : ℝ) := by
    rw [show (58700721435096327/58712500000000000 : ℝ)+2*(61059546147/58712500000000 : ℝ)*(10853/100000 : ℝ)=(625015701726453/625000000000000 : ℝ) by norm_num, show 1+2*(5543683125676227/100000000000000000000 : ℝ)=(50005543683125676227/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27104210731345851/100000000000000000000 : ℝ)+(5543683125676227/100000000000000000000 : ℝ) ≤ ((58700721435096327/58712500000000000 : ℝ)+(61059546147/58712500000000 : ℝ)*((311/2000 : ℝ)+(10853/100000 : ℝ)))^(4519/1024 : ℝ) := by
    rw [show (58700721435096327/58712500000000000 : ℝ)+(61059546147/58712500000000 : ℝ)*((311/2000 : ℝ)+(10853/100000 : ℝ))=(1250092462999053/1250000000000000 : ℝ) by norm_num, show 1+(27104210731345851/100000000000000000000 : ℝ)+(5543683125676227/100000000000000000000 : ℝ)=(50016323946928511039/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27104210731345851/100000000000000000000 : ℝ) ≤ ((58700721435096327/58712500000000000 : ℝ)+2*(61059546147/58712500000000 : ℝ)*(311/2000 : ℝ))^(4519/1024 : ℝ) := by
    rw [show (58700721435096327/58712500000000000 : ℝ)+2*(61059546147/58712500000000 : ℝ)*(311/2000 : ℝ)=(3125383806363/3125000000000 : ℝ) by norm_num, show 1+2*(27104210731345851/100000000000000000000 : ℝ)=(50027104210731345851/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (58700721435096327/58712500000000000 : ℝ)*(X 1 0+X 2 0)+(61059546147/58712500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4519/1024 : ℝ)) (lo := (10853/100000 : ℝ)) (hi := (311/2000 : ℝ)) (c := (58700721435096327/58712500000000000 : ℝ)) (alpha := (61059546147/58712500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (58700721435096327/58712500000000000 : ℝ)*(X 0 1+X 2 1)+(61059546147/58712500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4519/1024 : ℝ)) (lo := (10853/100000 : ℝ)) (hi := (311/2000 : ℝ)) (c := (58700721435096327/58712500000000000 : ℝ)) (alpha := (61059546147/58712500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (58700721435096327/58712500000000000 : ℝ)*(X 0 2+X 1 2)+(61059546147/58712500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4519/1024 : ℝ)) (lo := (10853/100000 : ℝ)) (hi := (311/2000 : ℝ)) (c := (58700721435096327/58712500000000000 : ℝ)) (alpha := (61059546147/58712500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1867957409/10000000000 : ℝ)*X 0 0+(135840721/250000000 : ℝ)*X 0 1+(1043456143/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1512_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351694541/10000000000 : ℝ)*X 1 0+(-1978769901/10000000000 : ℝ)*X 1 1+(2608640113/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1512_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((535169417/1000000000 : ℝ)*X 2 0+(2608640363/5000000000 : ℝ)*X 2 1+(-1978769733/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1512_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((853946959/2000000000 : ℝ)*X 0 0+(2015211499/5000000000 : ℝ)*X 0 1+(90420229/200000000 : ℝ)*X 0 2+(853946959/2000000000 : ℝ)*X 1 0+(2015211499/5000000000 : ℝ)*X 1 1+(90420229/200000000 : ℝ)*X 1 2+(853946959/2000000000 : ℝ)*X 2 0+(2015211499/5000000000 : ℝ)*X 2 1+(90420229/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1512_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1867986813/10000000000 : ℝ)*X 0 0+(1043679603/2000000000 : ℝ)*X 0 1+(5432503177/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1512_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((529489989/1000000000 : ℝ)*X 1 0+(-440886821/2500000000 : ℝ)*X 1 1+(5432503193/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1512_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1323724997/2500000000 : ℝ)*X 2 0+(108650063/200000000 : ℝ)*X 2 1+(-220443401/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1512_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2134900749/5000000000 : ℝ)*X 0 0+(4518477101/10000000000 : ℝ)*X 0 1+(4032975749/10000000000 : ℝ)*X 0 2+(2134900749/5000000000 : ℝ)*X 1 0+(4518477101/10000000000 : ℝ)*X 1 1+(4032975749/10000000000 : ℝ)*X 1 2+(2134900749/5000000000 : ℝ)*X 2 0+(4518477101/10000000000 : ℝ)*X 2 1+(4032975749/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1512_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (29738053616815136851304667/2935625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1934096633/100000000000000 : ℝ)*(base19) + (282527017/20000000000000 : ℝ)*(base23) + (26896403/25000000000000 : ℝ)*(lower2) + (169444529/100000000000000 : ℝ)*(upper3) + (65690557/50000000000000 : ℝ)*(upper5) + (104072243426299/3125000000000 : ℝ)*(major0) + (104072243426299/3125000000000 : ℝ)*(major1) + (104072243426299/3125000000000 : ℝ)*(major2) + (4622205372842377/100000000000000 : ℝ)*(sp0) + (2311114021821251/50000000000000 : ℝ)*(sp1) + (92444571302081/2000000000000 : ℝ)*(sp2) + (2038380640848349/100000000000000 : ℝ)*(sp3) + (12302448379/50000000000000 : ℝ)*(sp4) + (504921081/4000000000000 : ℝ)*(sp7) + (1019196631937687/50000000000000 : ℝ)*(f.failure) + (924445995547827/20000000000000 : ℝ)*(f.sum) + (40387594026581/11742500000000000000000000000 : ℝ)*base66 + (17974058471365243/2935625000000000000000000000000 : ℝ)*base67 + (531012080932449/91738281250000000000000000000 : ℝ)*base69 + (3858412108758993/2935625000000000000000000000000 : ℝ)*base71 + (49840418958343/23485000000000000000000000000 : ℝ)*base73 + (2757817703271493/2935625000000000000000000000000 : ℝ)*base75 + (2363371824894757/2935625000000000000000000000000 : ℝ)*base78 + (18959193040041007/2935625000000000000000000000000 : ℝ)*base80 + (85405976017657/23485000000000000000000000000 : ℝ)*base82 + (2148123/2500000000000000000000 : ℝ)*base89 + (2148123/2500000000000000000000 : ℝ)*base91 + (2148123/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (142641289936572722782887/23485000000000000000000000000 : ℝ) := by norm_num
    linear_combination (457694553/50000000000000 : ℝ)*(base19) + (1201714367/100000000000000 : ℝ)*(base23) + (12761993/12500000000000 : ℝ)*(upper3) + (17665831/20000000000000 : ℝ)*(lower4) + (166539673/100000000000000 : ℝ)*(upper5) + (3365164363536529/100000000000000 : ℝ)*(major0) + (3365164363536529/100000000000000 : ℝ)*(major1) + (3365164363536529/100000000000000 : ℝ)*(major2) + (3757506783/25000000000000 : ℝ)*(sp1) + (18112387191/100000000000000 : ℝ)*(sp2) + (467060294822923/10000000000000 : ℝ)*(sp4) + (72977921918953/1562500000000 : ℝ)*(sp5) + (583822954265959/12500000000000 : ℝ)*(sp6) + (1029862788193263/50000000000000 : ℝ)*(sp7) + (1029862788193263/50000000000000 : ℝ)*(f.failure) + (467060294822923/10000000000000 : ℝ)*(f.sum) + (33385507651763/11742500000000000000000000000 : ℝ)*base66 + (1394387141401983/5871250000000000000000000000000 : ℝ)*base67 + (13760495735193017/5871250000000000000000000000000 : ℝ)*base70 + (21189691058358017/5871250000000000000000000000000 : ℝ)*base72 + (50704865640547/11742500000000000000000000000 : ℝ)*base73 + (29982010162474483/5871250000000000000000000000000 : ℝ)*base75 + (5237429151430517/5871250000000000000000000000000 : ℝ)*base78 + (16079739556211983/5871250000000000000000000000000 : ℝ)*base79 + (118646004029471/23485000000000000000000000000 : ℝ)*base82 + (9769427/2500000000000000000000 : ℝ)*base89 + (9769427/2500000000000000000000 : ℝ)*base91 + (9769427/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1512_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4521/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (81689629/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (311/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10853/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2727/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1512_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1512_s5_0 (p : ℝ) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4521/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1868011867/10000000000 : ℝ)*x 0 + (1086655161/2000000000 : ℝ)*x 1 + (2608798829/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1868011867/10000000000 : ℝ)^4521 ≤ (11429395249679/100000000000000 : ℝ)^3497 := by
    have hnat : (1868011867 : ℕ)^4521*100000000000000^3497 ≤ 11429395249679^3497*10000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1868011867 10000000000 11429395249679 100000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1086655161/2000000000 : ℝ)^4521 ≤ (45444558904581/100000000000000 : ℝ)^3497 := by
    have hnat : (1086655161 : ℕ)^4521*100000000000000^3497 ≤ 45444558904581^3497*2000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086655161 2000000000 45444558904581 100000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2608798829/5000000000 : ℝ)^4521 ≤ (8625209167627/20000000000000 : ℝ)^3497 := by
    have hnat : (2608798829 : ℕ)^4521*20000000000000^3497 ≤ 8625209167627^3497*5000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608798829 5000000000 8625209167627 20000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4521/1024 : ℝ)) 4521 3497 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1868011867/10000000000 : ℝ), (1086655161/2000000000 : ℝ), (2608798829/5000000000 : ℝ)] ![(11429395249679/100000000000000 : ℝ), (45444558904581/100000000000000 : ℝ), (8625209167627/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1868011867/10000000000 : ℝ)|^4521 ≤ (11429395249679/100000000000000 : ℝ)^3497
        have hw : |(-1868011867/10000000000 : ℝ)|=(1868011867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1086655161/2000000000 : ℝ)|^4521 ≤ (45444558904581/100000000000000 : ℝ)^3497
        have hw : |(1086655161/2000000000 : ℝ)|=(1086655161/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2608798829/5000000000 : ℝ)|^4521 ≤ (8625209167627/20000000000000 : ℝ)^3497
        have hw : |(2608798829/5000000000 : ℝ)|=(2608798829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1512_s5_1 (p : ℝ) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4521/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675800749/5000000000 : ℝ)*x 0 + (-49461819/250000000 : ℝ)*x 1 + (2608798829/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675800749/5000000000 : ℝ)^4521 ≤ (11140834814801/25000000000000 : ℝ)^3497 := by
    have hnat : (2675800749 : ℕ)^4521*25000000000000^3497 ≤ 11140834814801^3497*5000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675800749 5000000000 11140834814801 25000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (49461819/250000000 : ℝ)^4521 ≤ (3077653721697/25000000000000 : ℝ)^3497 := by
    have hnat : (49461819 : ℕ)^4521*25000000000000^3497 ≤ 3077653721697^3497*250000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49461819 250000000 3077653721697 25000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2608798829/5000000000 : ℝ)^4521 ≤ (8625209167627/20000000000000 : ℝ)^3497 := by
    have hnat : (2608798829 : ℕ)^4521*20000000000000^3497 ≤ 8625209167627^3497*5000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608798829 5000000000 8625209167627 20000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4521/1024 : ℝ)) 4521 3497 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675800749/5000000000 : ℝ), (-49461819/250000000 : ℝ), (2608798829/5000000000 : ℝ)] ![(11140834814801/25000000000000 : ℝ), (3077653721697/25000000000000 : ℝ), (8625209167627/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675800749/5000000000 : ℝ)|^4521 ≤ (11140834814801/25000000000000 : ℝ)^3497
        have hw : |(2675800749/5000000000 : ℝ)|=(2675800749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-49461819/250000000 : ℝ)|^4521 ≤ (3077653721697/25000000000000 : ℝ)^3497
        have hw : |(-49461819/250000000 : ℝ)|=(49461819/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2608798829/5000000000 : ℝ)|^4521 ≤ (8625209167627/20000000000000 : ℝ)^3497
        have hw : |(2608798829/5000000000 : ℝ)|=(2608798829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1512_s5_2 (p : ℝ) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4521/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675800749/5000000000 : ℝ)*x 0 + (2608798829/5000000000 : ℝ)*x 1 + (-49461819/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675800749/5000000000 : ℝ)^4521 ≤ (11140834814801/25000000000000 : ℝ)^3497 := by
    have hnat : (2675800749 : ℕ)^4521*25000000000000^3497 ≤ 11140834814801^3497*5000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675800749 5000000000 11140834814801 25000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2608798829/5000000000 : ℝ)^4521 ≤ (8625209167627/20000000000000 : ℝ)^3497 := by
    have hnat : (2608798829 : ℕ)^4521*20000000000000^3497 ≤ 8625209167627^3497*5000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608798829 5000000000 8625209167627 20000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (49461819/250000000 : ℝ)^4521 ≤ (3077653721697/25000000000000 : ℝ)^3497 := by
    have hnat : (49461819 : ℕ)^4521*25000000000000^3497 ≤ 3077653721697^3497*250000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49461819 250000000 3077653721697 25000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4521/1024 : ℝ)) 4521 3497 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675800749/5000000000 : ℝ), (2608798829/5000000000 : ℝ), (-49461819/250000000 : ℝ)] ![(11140834814801/25000000000000 : ℝ), (8625209167627/20000000000000 : ℝ), (3077653721697/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675800749/5000000000 : ℝ)|^4521 ≤ (11140834814801/25000000000000 : ℝ)^3497
        have hw : |(2675800749/5000000000 : ℝ)|=(2675800749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2608798829/5000000000 : ℝ)|^4521 ≤ (8625209167627/20000000000000 : ℝ)^3497
        have hw : |(2608798829/5000000000 : ℝ)|=(2608798829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-49461819/250000000 : ℝ)|^4521 ≤ (3077653721697/25000000000000 : ℝ)^3497
        have hw : |(-49461819/250000000 : ℝ)|=(49461819/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1512_s5_3 (p : ℝ) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4521/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4269768121/10000000000 : ℝ)*x 0 + (2015589519/5000000000 : ℝ)*x 1 + (904049521/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4269768121/10000000000 : ℝ)^4521 ≤ (2079976354583/6250000000000 : ℝ)^3497 := by
    have hnat : (4269768121 : ℕ)^4521*6250000000000^3497 ≤ 2079976354583^3497*10000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4269768121 10000000000 2079976354583 6250000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2015589519/5000000000 : ℝ)^4521 ≤ (15447697647357/50000000000000 : ℝ)^3497 := by
    have hnat : (2015589519 : ℕ)^4521*50000000000000^3497 ≤ 15447697647357^3497*5000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2015589519 5000000000 15447697647357 50000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (904049521/2000000000 : ℝ)^4521 ≤ (35824983015263/100000000000000 : ℝ)^3497 := by
    have hnat : (904049521 : ℕ)^4521*100000000000000^3497 ≤ 35824983015263^3497*2000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      904049521 2000000000 35824983015263 100000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4521/1024 : ℝ)) 4521 3497 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4269768121/10000000000 : ℝ), (2015589519/5000000000 : ℝ), (904049521/2000000000 : ℝ)] ![(2079976354583/6250000000000 : ℝ), (15447697647357/50000000000000 : ℝ), (35824983015263/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4269768121/10000000000 : ℝ)|^4521 ≤ (2079976354583/6250000000000 : ℝ)^3497
        have hw : |(4269768121/10000000000 : ℝ)|=(4269768121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2015589519/5000000000 : ℝ)|^4521 ≤ (15447697647357/50000000000000 : ℝ)^3497
        have hw : |(2015589519/5000000000 : ℝ)|=(2015589519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(904049521/2000000000 : ℝ)|^4521 ≤ (35824983015263/100000000000000 : ℝ)^3497
        have hw : |(904049521/2000000000 : ℝ)|=(904049521/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1512_s5_4 (p : ℝ) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4521/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1868040571/10000000000 : ℝ)*x 0 + (5218709077/10000000000 : ℝ)*x 1 + (217286257/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1868040571/10000000000 : ℝ)^4521 ≤ (11429622301973/100000000000000 : ℝ)^3497 := by
    have hnat : (1868040571 : ℕ)^4521*100000000000000^3497 ≤ 11429622301973^3497*10000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1868040571 10000000000 11429622301973 100000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5218709077/10000000000 : ℝ)^4521 ≤ (10784480658479/25000000000000 : ℝ)^3497 := by
    have hnat : (5218709077 : ℕ)^4521*25000000000000^3497 ≤ 10784480658479^3497*10000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218709077 10000000000 10784480658479 25000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (217286257/400000000 : ℝ)^4521 ≤ (4543245505667/10000000000000 : ℝ)^3497 := by
    have hnat : (217286257 : ℕ)^4521*10000000000000^3497 ≤ 4543245505667^3497*400000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217286257 400000000 4543245505667 10000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4521/1024 : ℝ)) 4521 3497 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1868040571/10000000000 : ℝ), (5218709077/10000000000 : ℝ), (217286257/400000000 : ℝ)] ![(11429622301973/100000000000000 : ℝ), (10784480658479/25000000000000 : ℝ), (4543245505667/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1868040571/10000000000 : ℝ)|^4521 ≤ (11429622301973/100000000000000 : ℝ)^3497
        have hw : |(-1868040571/10000000000 : ℝ)|=(1868040571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5218709077/10000000000 : ℝ)|^4521 ≤ (10784480658479/25000000000000 : ℝ)^3497
        have hw : |(5218709077/10000000000 : ℝ)|=(5218709077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(217286257/400000000 : ℝ)|^4521 ≤ (4543245505667/10000000000000 : ℝ)^3497
        have hw : |(217286257/400000000 : ℝ)|=(217286257/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1512_s5_5 (p : ℝ) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4521/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294983111/10000000000 : ℝ)*x 0 + (-440978333/2500000000 : ℝ)*x 1 + (5432157277/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294983111/10000000000 : ℝ)^4521 ≤ (43954762447571/100000000000000 : ℝ)^3497 := by
    have hnat : (5294983111 : ℕ)^4521*100000000000000^3497 ≤ 43954762447571^3497*10000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294983111 10000000000 43954762447571 100000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (440978333/2500000000 : ℝ)^4521 ≤ (10612773267299/100000000000000 : ℝ)^3497 := by
    have hnat : (440978333 : ℕ)^4521*100000000000000^3497 ≤ 10612773267299^3497*2500000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      440978333 2500000000 10612773267299 100000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5432157277/10000000000 : ℝ)^4521 ≤ (45432464269063/100000000000000 : ℝ)^3497 := by
    have hnat : (5432157277 : ℕ)^4521*100000000000000^3497 ≤ 45432464269063^3497*10000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432157277 10000000000 45432464269063 100000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4521/1024 : ℝ)) 4521 3497 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294983111/10000000000 : ℝ), (-440978333/2500000000 : ℝ), (5432157277/10000000000 : ℝ)] ![(43954762447571/100000000000000 : ℝ), (10612773267299/100000000000000 : ℝ), (45432464269063/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294983111/10000000000 : ℝ)|^4521 ≤ (43954762447571/100000000000000 : ℝ)^3497
        have hw : |(5294983111/10000000000 : ℝ)|=(5294983111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-440978333/2500000000 : ℝ)|^4521 ≤ (10612773267299/100000000000000 : ℝ)^3497
        have hw : |(-440978333/2500000000 : ℝ)|=(440978333/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5432157277/10000000000 : ℝ)|^4521 ≤ (45432464269063/100000000000000 : ℝ)^3497
        have hw : |(5432157277/10000000000 : ℝ)|=(5432157277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1512_s5_6 (p : ℝ) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4521/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (529498331/1000000000 : ℝ)*x 0 + (2716078399/5000000000 : ℝ)*x 1 + (-440978431/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529498331/1000000000 : ℝ)^4521 ≤ (43954764583237/100000000000000 : ℝ)^3497 := by
    have hnat : (529498331 : ℕ)^4521*100000000000000^3497 ≤ 43954764583237^3497*1000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529498331 1000000000 43954764583237 100000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2716078399/5000000000 : ℝ)^4521 ≤ (9086491817959/20000000000000 : ℝ)^3497 := by
    have hnat : (2716078399 : ℕ)^4521*20000000000000^3497 ≤ 9086491817959^3497*5000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716078399 5000000000 9086491817959 20000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (440978431/2500000000 : ℝ)^4521 ≤ (10612776316433/100000000000000 : ℝ)^3497 := by
    have hnat : (440978431 : ℕ)^4521*100000000000000^3497 ≤ 10612776316433^3497*2500000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      440978431 2500000000 10612776316433 100000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4521/1024 : ℝ)) 4521 3497 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529498331/1000000000 : ℝ), (2716078399/5000000000 : ℝ), (-440978431/2500000000 : ℝ)] ![(43954764583237/100000000000000 : ℝ), (9086491817959/20000000000000 : ℝ), (10612776316433/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529498331/1000000000 : ℝ)|^4521 ≤ (43954764583237/100000000000000 : ℝ)^3497
        have hw : |(529498331/1000000000 : ℝ)|=(529498331/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2716078399/5000000000 : ℝ)|^4521 ≤ (9086491817959/20000000000000 : ℝ)^3497
        have hw : |(2716078399/5000000000 : ℝ)|=(2716078399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-440978431/2500000000 : ℝ)|^4521 ≤ (10612776316433/100000000000000 : ℝ)^3497
        have hw : |(-440978431/2500000000 : ℝ)|=(440978431/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1512_s5_7 (p : ℝ) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4521/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2134917047/5000000000 : ℝ)*x 0 + (2258864841/5000000000 : ℝ)*x 1 + (4033715281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2134917047/5000000000 : ℝ)^4521 ≤ (133121145827/400000000000 : ℝ)^3497 := by
    have hnat : (2134917047 : ℕ)^4521*400000000000^3497 ≤ 133121145827^3497*5000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2134917047 5000000000 133121145827 400000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2258864841/5000000000 : ℝ)^4521 ≤ (17899592993997/50000000000000 : ℝ)^3497 := by
    have hnat : (2258864841 : ℕ)^4521*50000000000000^3497 ≤ 17899592993997^3497*5000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2258864841 5000000000 17899592993997 50000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4033715281/10000000000 : ℝ)^4521 ≤ (15460263773273/50000000000000 : ℝ)^3497 := by
    have hnat : (4033715281 : ℕ)^4521*50000000000000^3497 ≤ 15460263773273^3497*10000000000^4521 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4033715281 10000000000 15460263773273 50000000000000 4521 3497 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4521/1024 : ℝ)) 4521 3497 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2134917047/5000000000 : ℝ), (2258864841/5000000000 : ℝ), (4033715281/10000000000 : ℝ)] ![(133121145827/400000000000 : ℝ), (17899592993997/50000000000000 : ℝ), (15460263773273/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2134917047/5000000000 : ℝ)|^4521 ≤ (133121145827/400000000000 : ℝ)^3497
        have hw : |(2134917047/5000000000 : ℝ)|=(2134917047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2258864841/5000000000 : ℝ)|^4521 ≤ (17899592993997/50000000000000 : ℝ)^3497
        have hw : |(2258864841/5000000000 : ℝ)|=(2258864841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4033715281/10000000000 : ℝ)|^4521 ≤ (15460263773273/50000000000000 : ℝ)^3497
        have hw : |(4033715281/10000000000 : ℝ)|=(4033715281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1512_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4521/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (81689629/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2727/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2183/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15483/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2727/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2727/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2727/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2727/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2727/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2727/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2727/25000 : ℝ) ^ (4519/1024 : ℝ) ≤ (141718507637699/2500000000000000000 : ℝ) := by
    have hpowers : (2727/25000 : ℝ)^4519 ≤ (141718507637699/2500000000000000000 : ℝ)^1024 := by
      have hnat : (2727 : ℕ)^4519*2500000000000000000^1024 ≤ 141718507637699^1024*25000^4519 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2727 25000 141718507637699 2500000000000000000 4519 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2727/25000 : ℝ)) (X := (141718507637699/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4519 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1549/10000 : ℝ) ^ (4519/1024 : ℝ) ≤ (2664571028830921/10000000000000000000 : ℝ) := by
    have hpowers : (1549/10000 : ℝ)^4519 ≤ (2664571028830921/10000000000000000000 : ℝ)^1024 := by
      have hnat : (1549 : ℕ)^4519*10000000000000000000^1024 ≤ 2664571028830921^1024*10000^4519 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1549 10000 2664571028830921 10000000000000000000 4519 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1549/10000 : ℝ)) (X := (2664571028830921/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4519 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1250141718507637699/1250000000000000000 : ℝ) ≤ (400010275787733/400000000000000 : ℝ) ^ (4519/1024 : ℝ) := by
    have hpowers : (1250141718507637699/1250000000000000000 : ℝ)^1024 ≤ (400010275787733/400000000000000 : ℝ)^4519 := by
      have hnat : (1250141718507637699 : ℕ)^1024*400000000000000^4519 ≤ 400010275787733^4519*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250141718507637699 1250000000000000000 400010275787733 400000000000000 1024 4519 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400010275787733/400000000000000 : ℝ)) (X := (1250141718507637699/1250000000000000000 : ℝ)) (by norm_num) 4519 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10003231445059381717/10000000000000000000 : ℝ) ≤ (2000146430021093/2000000000000000 : ℝ) ^ (4519/1024 : ℝ) := by
    have hpowers : (10003231445059381717/10000000000000000000 : ℝ)^1024 ≤ (2000146430021093/2000000000000000 : ℝ)^4519 := by
      have hnat : (10003231445059381717 : ℕ)^1024*2000000000000000^4519 ≤ 2000146430021093^4519*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10003231445059381717 10000000000000000000 2000146430021093 2000000000000000 1024 4519 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000146430021093/2000000000000000 : ℝ)) (X := (10003231445059381717/10000000000000000000 : ℝ)) (by norm_num) 4519 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5002664571028830921/5000000000000000000 : ℝ) ≤ (2000241481103521/2000000000000000 : ℝ) ^ (4519/1024 : ℝ) := by
    have hpowers : (5002664571028830921/5000000000000000000 : ℝ)^1024 ≤ (2000241481103521/2000000000000000 : ℝ)^4519 := by
      have hnat : (5002664571028830921 : ℕ)^1024*2000000000000000^4519 ≤ 2000241481103521^4519*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002664571028830921 5000000000000000000 2000241481103521 2000000000000000 1024 4519 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000241481103521/2000000000000000 : ℝ)) (X := (5002664571028830921/5000000000000000000 : ℝ)) (by norm_num) 4519 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(141718507637699/2500000000000000000 : ℝ) ≤ ((157968306618667479/158000000000000000 : ℝ)+2*(819405883/790000000000 : ℝ)*(2727/25000 : ℝ))^(4519/1024 : ℝ) := by
    rw [show (157968306618667479/158000000000000000 : ℝ)+2*(819405883/790000000000 : ℝ)*(2727/25000 : ℝ)=(400010275787733/400000000000000 : ℝ) by norm_num, show 1+2*(141718507637699/2500000000000000000 : ℝ)=(1250141718507637699/1250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2664571028830921/10000000000000000000 : ℝ)+(141718507637699/2500000000000000000 : ℝ) ≤ ((157968306618667479/158000000000000000 : ℝ)+(819405883/790000000000 : ℝ)*((1549/10000 : ℝ)+(2727/25000 : ℝ)))^(4519/1024 : ℝ) := by
    rw [show (157968306618667479/158000000000000000 : ℝ)+(819405883/790000000000 : ℝ)*((1549/10000 : ℝ)+(2727/25000 : ℝ))=(2000146430021093/2000000000000000 : ℝ) by norm_num, show 1+(2664571028830921/10000000000000000000 : ℝ)+(141718507637699/2500000000000000000 : ℝ)=(10003231445059381717/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2664571028830921/10000000000000000000 : ℝ) ≤ ((157968306618667479/158000000000000000 : ℝ)+2*(819405883/790000000000 : ℝ)*(1549/10000 : ℝ))^(4519/1024 : ℝ) := by
    rw [show (157968306618667479/158000000000000000 : ℝ)+2*(819405883/790000000000 : ℝ)*(1549/10000 : ℝ)=(2000241481103521/2000000000000000 : ℝ) by norm_num, show 1+2*(2664571028830921/10000000000000000000 : ℝ)=(5002664571028830921/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (157968306618667479/158000000000000000 : ℝ)*(X 1 0+X 2 0)+(819405883/790000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4519/1024 : ℝ)) (lo := (2727/25000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (157968306618667479/158000000000000000 : ℝ)) (alpha := (819405883/790000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (157968306618667479/158000000000000000 : ℝ)*(X 0 1+X 2 1)+(819405883/790000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4519/1024 : ℝ)) (lo := (2727/25000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (157968306618667479/158000000000000000 : ℝ)) (alpha := (819405883/790000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (157968306618667479/158000000000000000 : ℝ)*(X 0 2+X 1 2)+(819405883/790000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4519/1024 : ℝ)) (lo := (2727/25000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (157968306618667479/158000000000000000 : ℝ)) (alpha := (819405883/790000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1868011867/10000000000 : ℝ)*X 0 0+(1086655161/2000000000 : ℝ)*X 0 1+(2608798829/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1512_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675800749/5000000000 : ℝ)*X 1 0+(-49461819/250000000 : ℝ)*X 1 1+(2608798829/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1512_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675800749/5000000000 : ℝ)*X 2 0+(2608798829/5000000000 : ℝ)*X 2 1+(-49461819/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1512_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4269768121/10000000000 : ℝ)*X 0 0+(2015589519/5000000000 : ℝ)*X 0 1+(904049521/2000000000 : ℝ)*X 0 2+(4269768121/10000000000 : ℝ)*X 1 0+(2015589519/5000000000 : ℝ)*X 1 1+(904049521/2000000000 : ℝ)*X 1 2+(4269768121/10000000000 : ℝ)*X 2 0+(2015589519/5000000000 : ℝ)*X 2 1+(904049521/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1512_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1868040571/10000000000 : ℝ)*X 0 0+(5218709077/10000000000 : ℝ)*X 0 1+(217286257/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1512_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5294983111/10000000000 : ℝ)*X 1 0+(-440978333/2500000000 : ℝ)*X 1 1+(5432157277/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1512_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((529498331/1000000000 : ℝ)*X 2 0+(2716078399/5000000000 : ℝ)*X 2 1+(-440978431/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1512_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2134917047/5000000000 : ℝ)*X 0 0+(2258864841/5000000000 : ℝ)*X 0 1+(4033715281/10000000000 : ℝ)*X 0 2+(2134917047/5000000000 : ℝ)*X 1 0+(2258864841/5000000000 : ℝ)*X 1 1+(4033715281/10000000000 : ℝ)*X 1 2+(2134917047/5000000000 : ℝ)*X 2 0+(2258864841/5000000000 : ℝ)*X 2 1+(4033715281/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1512_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3120313950886475004808911/395000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1384959147/100000000000000 : ℝ)*(base19) + (1293136671/100000000000000 : ℝ)*(base23) + (4913973/10000000000000 : ℝ)*(lower2) + (196531803/100000000000000 : ℝ)*(upper3) + (129415643/100000000000000 : ℝ)*(upper5) + (167032640030601/5000000000000 : ℝ)*(major0) + (167032640030601/5000000000000 : ℝ)*(major1) + (167032640030601/5000000000000 : ℝ)*(major2) + (2318280456142573/50000000000000 : ℝ)*(sp0) + (4636581237526413/100000000000000 : ℝ)*(sp1) + (4636581329348889/100000000000000 : ℝ)*(sp2) + (1022356169130983/50000000000000 : ℝ)*(sp3) + (10855100207/50000000000000 : ℝ)*(sp4) + (83017271/800000000000 : ℝ)*(sp7) + (51118067885521/2500000000000 : ℝ)*(f.failure) + (115914565562139/2500000000000 : ℝ)*(f.sum) + (9489605483/1975000000000000000000000 : ℝ)*base66 + (10569562484015121/790000000000000000000000000000 : ℝ)*base68 + (2247040035045121/790000000000000000000000000000 : ℝ)*base70 + (5141385539775121/790000000000000000000000000000 : ℝ)*base72 + (253530906171/39500000000000000000000000 : ℝ)*base74 + (7015790296485121/790000000000000000000000000000 : ℝ)*base76 + (5229604087695121/790000000000000000000000000000 : ℝ)*base78 + (6507107211675121/790000000000000000000000000000 : ℝ)*base80 + (14441421843/15800000000000000000000000 : ℝ)*base82 + (38291/125000000000000000000 : ℝ)*base90 + (38291/125000000000000000000 : ℝ)*base92 + (38291/125000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (42933532341635796821152353/3950000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (505287071/50000000000000 : ℝ)*(base19) + (1741887699/100000000000000 : ℝ)*(base23) + (12536783/2500000000000 : ℝ)*(lower1) + (179650757/50000000000000 : ℝ)*(upper3) + (250282041/100000000000000 : ℝ)*(lower4) + (1687753793902223/50000000000000 : ℝ)*(major0) + (1687753793902223/50000000000000 : ℝ)*(major1) + (1687753793902223/50000000000000 : ℝ)*(major2) + (1544260469/20000000000000 : ℝ)*(sp2) + (4796481031/100000000000000 : ℝ)*(sp3) + (234247921533471/5000000000000 : ℝ)*(sp4) + (4684957420095279/100000000000000 : ℝ)*(sp5) + (4684948967479377/100000000000000 : ℝ)*(sp6) + (103302579307507/5000000000000 : ℝ)*(sp7) + (206605638263117/10000000000000 : ℝ)*(f.failure) + (234247921533471/5000000000000 : ℝ)*(f.sum) + (157585008553/79000000000000000000000000 : ℝ)*base66 + (53772603626494183/7900000000000000000000000000000 : ℝ)*base68 + (129914261942794183/7900000000000000000000000000000 : ℝ)*base70 + (31803571694294183/7900000000000000000000000000000 : ℝ)*base72 + (106801043367/39500000000000000000000000 : ℝ)*base74 + (42612719028494183/7900000000000000000000000000000 : ℝ)*base76 + (76685665611194183/7900000000000000000000000000000 : ℝ)*base78 + (238134410002894183/7900000000000000000000000000000 : ℝ)*base80 + (831394246177/79000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (2113593/500000000000000000000 : ℝ)*base89 + (2113593/500000000000000000000 : ℝ)*base91 + (2113593/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1512_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4521/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (81689629/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2727/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2183/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1512_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1512_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4521/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (81689629/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3999/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10443/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2183/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1512_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1512_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1512_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4519/1024 : ℝ) ≤ p) (hpb : p ≤ (4521/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (81689629/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3999/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10443/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2183/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1512_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
