-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1191_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:53:19.481085+00:00
-- url     : https://prove2.me/submissions/cb5c5c8e-8147-4214-acf6-602683a22507

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
theorem support_rectangle_w1191_s9_0 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-107183867/500000000 : ℝ)*x 0 + (5392089849/10000000000 : ℝ)*x 1 + (5266544371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107183867/500000000 : ℝ)^131 ≤ (13030723266407/100000000000000 : ℝ)^99 := by
    have hnat : (107183867 : ℕ)^131*100000000000000^99 ≤ 13030723266407^99*500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107183867 500000000 13030723266407 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392089849/10000000000 : ℝ)^131 ≤ (44162367871173/100000000000000 : ℝ)^99 := by
    have hnat : (5392089849 : ℕ)^131*100000000000000^99 ≤ 44162367871173^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392089849 10000000000 44162367871173 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266544371/10000000000 : ℝ)^131 ≤ (10701727211981/25000000000000 : ℝ)^99 := by
    have hnat : (5266544371 : ℕ)^131*25000000000000^99 ≤ 10701727211981^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266544371 10000000000 10701727211981 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-107183867/500000000 : ℝ), (5392089849/10000000000 : ℝ), (5266544371/10000000000 : ℝ)] ![(13030723266407/100000000000000 : ℝ), (44162367871173/100000000000000 : ℝ), (10701727211981/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-107183867/500000000 : ℝ)|^131 ≤ (13030723266407/100000000000000 : ℝ)^99
        have hw : |(-107183867/500000000 : ℝ)|=(107183867/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392089849/10000000000 : ℝ)|^131 ≤ (44162367871173/100000000000000 : ℝ)^99
        have hw : |(5392089849/10000000000 : ℝ)|=(5392089849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266544371/10000000000 : ℝ)|^131 ≤ (10701727211981/25000000000000 : ℝ)^99
        have hw : |(5266544371/10000000000 : ℝ)|=(5266544371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s9_1 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2672272209/5000000000 : ℝ)*x 0 + (-2207342897/10000000000 : ℝ)*x 1 + (2633272403/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672272209/5000000000 : ℝ)^131 ≤ (43647827398361/100000000000000 : ℝ)^99 := by
    have hnat : (2672272209 : ℕ)^131*100000000000000^99 ≤ 43647827398361^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672272209 5000000000 43647827398361 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2207342897/10000000000 : ℝ)^131 ≤ (1354525905977/10000000000000 : ℝ)^99 := by
    have hnat : (2207342897 : ℕ)^131*10000000000000^99 ≤ 1354525905977^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2207342897 10000000000 1354525905977 10000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633272403/5000000000 : ℝ)^131 ≤ (42806913526497/100000000000000 : ℝ)^99 := by
    have hnat : (2633272403 : ℕ)^131*100000000000000^99 ≤ 42806913526497^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633272403 5000000000 42806913526497 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672272209/5000000000 : ℝ), (-2207342897/10000000000 : ℝ), (2633272403/5000000000 : ℝ)] ![(43647827398361/100000000000000 : ℝ), (1354525905977/10000000000000 : ℝ), (42806913526497/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672272209/5000000000 : ℝ)|^131 ≤ (43647827398361/100000000000000 : ℝ)^99
        have hw : |(2672272209/5000000000 : ℝ)|=(2672272209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2207342897/10000000000 : ℝ)|^131 ≤ (1354525905977/10000000000000 : ℝ)^99
        have hw : |(-2207342897/10000000000 : ℝ)|=(2207342897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633272403/5000000000 : ℝ)|^131 ≤ (42806913526497/100000000000000 : ℝ)^99
        have hw : |(2633272403/5000000000 : ℝ)|=(2633272403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s9_2 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (534454473/1000000000 : ℝ)*x 0 + (5266544449/10000000000 : ℝ)*x 1 + (-441468591/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534454473/1000000000 : ℝ)^131 ≤ (10911957692503/25000000000000 : ℝ)^99 := by
    have hnat : (534454473 : ℕ)^131*25000000000000^99 ≤ 10911957692503^99*1000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534454473 1000000000 10911957692503 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266544449/10000000000 : ℝ)^131 ≤ (1070172742171/2500000000000 : ℝ)^99 := by
    have hnat : (5266544449 : ℕ)^131*2500000000000^99 ≤ 1070172742171^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266544449 10000000000 1070172742171 2500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (441468591/2000000000 : ℝ)^131 ≤ (1693157441341/12500000000000 : ℝ)^99 := by
    have hnat : (441468591 : ℕ)^131*12500000000000^99 ≤ 1693157441341^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441468591 2000000000 1693157441341 12500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534454473/1000000000 : ℝ), (5266544449/10000000000 : ℝ), (-441468591/2000000000 : ℝ)] ![(10911957692503/25000000000000 : ℝ), (1070172742171/2500000000000 : ℝ), (1693157441341/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534454473/1000000000 : ℝ)|^131 ≤ (10911957692503/25000000000000 : ℝ)^99
        have hw : |(534454473/1000000000 : ℝ)|=(534454473/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266544449/10000000000 : ℝ)|^131 ≤ (1070172742171/2500000000000 : ℝ)^99
        have hw : |(5266544449/10000000000 : ℝ)|=(5266544449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-441468591/2000000000 : ℝ)|^131 ≤ (1693157441341/12500000000000 : ℝ)^99
        have hw : |(-441468591/2000000000 : ℝ)|=(441468591/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s9_3 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5447273/12500000 : ℝ)*x 0 + (846705361/2000000000 : ℝ)*x 1 + (89713957/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5447273/12500000 : ℝ)^131 ≤ (666345157903/2000000000000 : ℝ)^99 := by
    have hnat : (5447273 : ℕ)^131*2000000000000^99 ≤ 666345157903^99*12500000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5447273 12500000 666345157903 2000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (846705361/2000000000 : ℝ)^131 ≤ (16032839311619/50000000000000 : ℝ)^99 := by
    have hnat : (846705361 : ℕ)^131*50000000000000^99 ≤ 16032839311619^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      846705361 2000000000 16032839311619 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (89713957/200000000 : ℝ)^131 ≤ (4327132932737/12500000000000 : ℝ)^99 := by
    have hnat : (89713957 : ℕ)^131*12500000000000^99 ≤ 4327132932737^99*200000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89713957 200000000 4327132932737 12500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5447273/12500000 : ℝ), (846705361/2000000000 : ℝ), (89713957/200000000 : ℝ)] ![(666345157903/2000000000000 : ℝ), (16032839311619/50000000000000 : ℝ), (4327132932737/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5447273/12500000 : ℝ)|^131 ≤ (666345157903/2000000000000 : ℝ)^99
        have hw : |(5447273/12500000 : ℝ)|=(5447273/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(846705361/2000000000 : ℝ)|^131 ≤ (16032839311619/50000000000000 : ℝ)^99
        have hw : |(846705361/2000000000 : ℝ)|=(846705361/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(89713957/200000000 : ℝ)|^131 ≤ (4327132932737/12500000000000 : ℝ)^99
        have hw : |(89713957/200000000 : ℝ)|=(89713957/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s9_4 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-428736319/2000000000 : ℝ)*x 0 + (1316715127/2500000000 : ℝ)*x 1 + (2695886473/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (428736319/2000000000 : ℝ)^131 ≤ (6515378745761/50000000000000 : ℝ)^99 := by
    have hnat : (428736319 : ℕ)^131*50000000000000^99 ≤ 6515378745761^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      428736319 2000000000 6515378745761 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316715127/2500000000 : ℝ)^131 ≤ (21405154521219/50000000000000 : ℝ)^99 := by
    have hnat : (1316715127 : ℕ)^131*50000000000000^99 ≤ 21405154521219^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316715127 2500000000 21405154521219 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695886473/5000000000 : ℝ)^131 ≤ (22079466724983/50000000000000 : ℝ)^99 := by
    have hnat : (2695886473 : ℕ)^131*50000000000000^99 ≤ 22079466724983^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695886473 5000000000 22079466724983 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-428736319/2000000000 : ℝ), (1316715127/2500000000 : ℝ), (2695886473/5000000000 : ℝ)] ![(6515378745761/50000000000000 : ℝ), (21405154521219/50000000000000 : ℝ), (22079466724983/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-428736319/2000000000 : ℝ)|^131 ≤ (6515378745761/50000000000000 : ℝ)^99
        have hw : |(-428736319/2000000000 : ℝ)|=(428736319/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316715127/2500000000 : ℝ)|^131 ≤ (21405154521219/50000000000000 : ℝ)^99
        have hw : |(1316715127/2500000000 : ℝ)|=(1316715127/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695886473/5000000000 : ℝ)|^131 ≤ (22079466724983/50000000000000 : ℝ)^99
        have hw : |(2695886473/5000000000 : ℝ)|=(2695886473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s9_5 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (21789139/50000000 : ℝ)*x 0 + (2242531983/5000000000 : ℝ)*x 1 + (4234163137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21789139/50000000 : ℝ)^131 ≤ (1041167280987/3125000000000 : ℝ)^99 := by
    have hnat : (21789139 : ℕ)^131*3125000000000^99 ≤ 1041167280987^99*50000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21789139 50000000 1041167280987 3125000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2242531983/5000000000 : ℝ)^131 ≤ (34610590602411/100000000000000 : ℝ)^99 := by
    have hnat : (2242531983 : ℕ)^131*100000000000000^99 ≤ 34610590602411^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2242531983 5000000000 34610590602411 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4234163137/10000000000 : ℝ)^131 ≤ (1282882255543/4000000000000 : ℝ)^99 := by
    have hnat : (4234163137 : ℕ)^131*4000000000000^99 ≤ 1282882255543^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4234163137 10000000000 1282882255543 4000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(21789139/50000000 : ℝ), (2242531983/5000000000 : ℝ), (4234163137/10000000000 : ℝ)] ![(1041167280987/3125000000000 : ℝ), (34610590602411/100000000000000 : ℝ), (1282882255543/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(21789139/50000000 : ℝ)|^131 ≤ (1041167280987/3125000000000 : ℝ)^99
        have hw : |(21789139/50000000 : ℝ)|=(21789139/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2242531983/5000000000 : ℝ)|^131 ≤ (34610590602411/100000000000000 : ℝ)^99
        have hw : |(2242531983/5000000000 : ℝ)|=(2242531983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4234163137/10000000000 : ℝ)|^131 ≤ (1282882255543/4000000000000 : ℝ)^99
        have hw : |(4234163137/10000000000 : ℝ)|=(4234163137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1191_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37607663/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3519/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1427/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (11417/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3519/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3519/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1427/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3519/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1427/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3519/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1427/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3519/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1427/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3519/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1427/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3519/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1427/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1427/12500 : ℝ) ^ (8383/2048 : ℝ) ≤ (13872603461285487/100000000000000000000 : ℝ) := by
    have hpowers : (1427/12500 : ℝ)^8383 ≤ (13872603461285487/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1427 : ℕ)^8383*100000000000000000000^2048 ≤ 13872603461285487^2048*12500^8383 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1427 12500 13872603461285487 100000000000000000000 8383 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1427/12500 : ℝ)) (X := (13872603461285487/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8383 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3519/25000 : ℝ) ^ (8383/2048 : ℝ) ≤ (1021769103862273/3125000000000000000 : ℝ) := by
    have hpowers : (3519/25000 : ℝ)^8383 ≤ (1021769103862273/3125000000000000000 : ℝ)^2048 := by
      have hnat : (3519 : ℕ)^8383*3125000000000000000^2048 ≤ 1021769103862273^2048*25000^8383 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3519 25000 1021769103862273 3125000000000000000 8383 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3519/25000 : ℝ)) (X := (1021769103862273/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 8383 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013872603461285487/50000000000000000000 : ℝ) ≤ (1250084719414003/1250000000000000 : ℝ) ^ (8383/2048 : ℝ) := by
    have hpowers : (50013872603461285487/50000000000000000000 : ℝ)^2048 ≤ (1250084719414003/1250000000000000 : ℝ)^8383 := by
      have hnat : (50013872603461285487 : ℕ)^2048*1250000000000000^8383 ≤ 1250084719414003^8383*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013872603461285487 50000000000000000000 1250084719414003 1250000000000000 2048 8383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250084719414003/1250000000000000 : ℝ)) (X := (50013872603461285487/50000000000000000000 : ℝ)) (by norm_num) 8383 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046569214784878223/100000000000000000000 : ℝ) ≤ (2500284376042003/2500000000000000 : ℝ) ^ (8383/2048 : ℝ) := by
    have hpowers : (100046569214784878223/100000000000000000000 : ℝ)^2048 ≤ (2500284376042003/2500000000000000 : ℝ)^8383 := by
      have hnat : (100046569214784878223 : ℕ)^2048*2500000000000000^8383 ≤ 2500284376042003^8383*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046569214784878223 100000000000000000000 2500284376042003 2500000000000000 2048 8383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500284376042003/2500000000000000 : ℝ)) (X := (100046569214784878223/100000000000000000000 : ℝ)) (by norm_num) 8383 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (1563521769103862273/1562500000000000000 : ℝ) ≤ (312549914157/312500000000 : ℝ) ^ (8383/2048 : ℝ) := by
    have hpowers : (1563521769103862273/1562500000000000000 : ℝ)^2048 ≤ (312549914157/312500000000 : ℝ)^8383 := by
      have hnat : (1563521769103862273 : ℕ)^2048*312500000000^8383 ≤ 312549914157^8383*1562500000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1563521769103862273 1562500000000000000 312549914157 312500000000 2048 8383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312549914157/312500000000 : ℝ)) (X := (1563521769103862273/1562500000000000000 : ℝ)) (by norm_num) 8383 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13872603461285487/100000000000000000000 : ℝ) ≤ ((830978307601564557/831250000000000000 : ℝ)+2*(114937213997/66500000000000 : ℝ)*(1427/12500 : ℝ))^(8383/2048 : ℝ) := by
    rw [show (830978307601564557/831250000000000000 : ℝ)+2*(114937213997/66500000000000 : ℝ)*(1427/12500 : ℝ)=(1250084719414003/1250000000000000 : ℝ) by norm_num, show 1+2*(13872603461285487/100000000000000000000 : ℝ)=(50013872603461285487/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1021769103862273/3125000000000000000 : ℝ)+(13872603461285487/100000000000000000000 : ℝ) ≤ ((830978307601564557/831250000000000000 : ℝ)+(114937213997/66500000000000 : ℝ)*((3519/25000 : ℝ)+(1427/12500 : ℝ)))^(8383/2048 : ℝ) := by
    rw [show (830978307601564557/831250000000000000 : ℝ)+(114937213997/66500000000000 : ℝ)*((3519/25000 : ℝ)+(1427/12500 : ℝ))=(2500284376042003/2500000000000000 : ℝ) by norm_num, show 1+(1021769103862273/3125000000000000000 : ℝ)+(13872603461285487/100000000000000000000 : ℝ)=(100046569214784878223/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1021769103862273/3125000000000000000 : ℝ) ≤ ((830978307601564557/831250000000000000 : ℝ)+2*(114937213997/66500000000000 : ℝ)*(3519/25000 : ℝ))^(8383/2048 : ℝ) := by
    rw [show (830978307601564557/831250000000000000 : ℝ)+2*(114937213997/66500000000000 : ℝ)*(3519/25000 : ℝ)=(312549914157/312500000000 : ℝ) by norm_num, show 1+2*(1021769103862273/3125000000000000000 : ℝ)=(1563521769103862273/1562500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (830978307601564557/831250000000000000 : ℝ)*(X 1 0+X 2 0)+(114937213997/66500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8383/2048 : ℝ)) (lo := (1427/12500 : ℝ)) (hi := (3519/25000 : ℝ)) (c := (830978307601564557/831250000000000000 : ℝ)) (alpha := (114937213997/66500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (830978307601564557/831250000000000000 : ℝ)*(X 0 1+X 2 1)+(114937213997/66500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8383/2048 : ℝ)) (lo := (1427/12500 : ℝ)) (hi := (3519/25000 : ℝ)) (c := (830978307601564557/831250000000000000 : ℝ)) (alpha := (114937213997/66500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (830978307601564557/831250000000000000 : ℝ)*(X 0 2+X 1 2)+(114937213997/66500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8383/2048 : ℝ)) (lo := (1427/12500 : ℝ)) (hi := (3519/25000 : ℝ)) (c := (830978307601564557/831250000000000000 : ℝ)) (alpha := (114937213997/66500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-107183867/500000000 : ℝ)*X 0 0+(5392089849/10000000000 : ℝ)*X 0 1+(5266544371/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s9_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672272209/5000000000 : ℝ)*X 1 0+(-2207342897/10000000000 : ℝ)*X 1 1+(2633272403/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s9_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534454473/1000000000 : ℝ)*X 2 0+(5266544449/10000000000 : ℝ)*X 2 1+(-441468591/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s9_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5447273/12500000 : ℝ)*X 0 0+(846705361/2000000000 : ℝ)*X 0 1+(89713957/200000000 : ℝ)*X 0 2+(5447273/12500000 : ℝ)*X 1 0+(846705361/2000000000 : ℝ)*X 1 1+(89713957/200000000 : ℝ)*X 1 2+(5447273/12500000 : ℝ)*X 2 0+(846705361/2000000000 : ℝ)*X 2 1+(89713957/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s9_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-428736319/2000000000 : ℝ)*X 0 0+(1316715127/2500000000 : ℝ)*X 0 1+(2695886473/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s9_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((21789139/50000000 : ℝ)*X 0 0+(2242531983/5000000000 : ℝ)*X 0 1+(4234163137/10000000000 : ℝ)*X 0 2+(21789139/50000000 : ℝ)*X 1 0+(2242531983/5000000000 : ℝ)*X 1 1+(4234163137/10000000000 : ℝ)*X 1 2+(21789139/50000000 : ℝ)*X 2 0+(2242531983/5000000000 : ℝ)*X 2 1+(4234163137/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s9_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1096465138125567266984793/5195312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1055892493/100000000000000 : ℝ)*(base19) + (724972181/50000000000000 : ℝ)*(base23) + (201717963/100000000000000 : ℝ)*(upper3) + (7583163/20000000000000 : ℝ)*(upper4) + (141523949/100000000000000 : ℝ)*(upper5) + (93210416176637/1562500000000 : ℝ)*(major0) + (93210416176637/1562500000000 : ℝ)*(major1) + (93210416176637/1562500000000 : ℝ)*(major2) + (1991322325906653/25000000000000 : ℝ)*(sp0) + (497833732482483/6250000000000 : ℝ)*(sp1) + (3982669662833929/50000000000000 : ℝ)*(sp2) + (495696921268321/12500000000000 : ℝ)*(sp3) + (6433998201/12500000000000 : ℝ)*(sp4) + (1711781577/10000000000000 : ℝ)*(sp5) + (3965592487962339/100000000000000 : ℝ)*(f.failure) + (7965340775612221/100000000000000 : ℝ)*(f.sum) + (1302961780087/415625000000000000000000000 : ℝ)*base65 + (89670464851291/5798339843750000000000000000 : ℝ)*base67 + (5343653174324623/742187500000000000000000000000 : ℝ)*base69 + (2051934232194437/185546875000000000000000000000 : ℝ)*base71 + (4221103254099/831250000000000000000000000 : ℝ)*base73 + (478043716769127/742187500000000000000000000000 : ℝ)*base76 + (5069673333841999/371093750000000000000000000000 : ℝ)*base77 + (18753788016199623/742187500000000000000000000000 : ℝ)*base79 + (4007259163701/831250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (1803757/2500000000000000000000 : ℝ)*base89 + (1803757/2500000000000000000000 : ℝ)*base91 + (1803757/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1191_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37607663/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3519/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1427/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11417/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3519/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1191_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1191_box_0 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-504594721/2500000000 : ℝ)*x 0 + (5375598749/10000000000 : ℝ)*x 1 + (5375598729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (504594721/2500000000 : ℝ)^131 ≤ (6016267036329/50000000000000 : ℝ)^99 := by
    have hnat : (504594721 : ℕ)^131*50000000000000^99 ≤ 6016267036329^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      504594721 2500000000 6016267036329 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5375598749/10000000000 : ℝ)^131 ≤ (5497966632747/12500000000000 : ℝ)^99 := by
    have hnat : (5375598749 : ℕ)^131*12500000000000^99 ≤ 5497966632747^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375598749 10000000000 5497966632747 12500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5375598729/10000000000 : ℝ)^131 ≤ (43983732845439/100000000000000 : ℝ)^99 := by
    have hnat : (5375598729 : ℕ)^131*100000000000000^99 ≤ 43983732845439^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375598729 10000000000 43983732845439 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-504594721/2500000000 : ℝ), (5375598749/10000000000 : ℝ), (5375598729/10000000000 : ℝ)] ![(6016267036329/50000000000000 : ℝ), (5497966632747/12500000000000 : ℝ), (43983732845439/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-504594721/2500000000 : ℝ)|^131 ≤ (6016267036329/50000000000000 : ℝ)^99
        have hw : |(-504594721/2500000000 : ℝ)|=(504594721/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5375598749/10000000000 : ℝ)|^131 ≤ (5497966632747/12500000000000 : ℝ)^99
        have hw : |(5375598749/10000000000 : ℝ)|=(5375598749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5375598729/10000000000 : ℝ)|^131 ≤ (43983732845439/100000000000000 : ℝ)^99
        have hw : |(5375598729/10000000000 : ℝ)|=(5375598729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_box_1 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2648206733/5000000000 : ℝ)*x 0 + (-106294299/500000000 : ℝ)*x 1 + (1343899709/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2648206733/5000000000 : ℝ)^131 ≤ (21564227631183/50000000000000 : ℝ)^99 := by
    have hnat : (2648206733 : ℕ)^131*50000000000000^99 ≤ 21564227631183^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2648206733 5000000000 21564227631183 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (106294299/500000000 : ℝ)^131 ≤ (6443905363633/50000000000000 : ℝ)^99 := by
    have hnat : (106294299 : ℕ)^131*50000000000000^99 ≤ 6443905363633^99*500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106294299 500000000 6443905363633 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1343899709/2500000000 : ℝ)^131 ≤ (4398373400391/10000000000000 : ℝ)^99 := by
    have hnat : (1343899709 : ℕ)^131*10000000000000^99 ≤ 4398373400391^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343899709 2500000000 4398373400391 10000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2648206733/5000000000 : ℝ), (-106294299/500000000 : ℝ), (1343899709/2500000000 : ℝ)] ![(21564227631183/50000000000000 : ℝ), (6443905363633/50000000000000 : ℝ), (4398373400391/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2648206733/5000000000 : ℝ)|^131 ≤ (21564227631183/50000000000000 : ℝ)^99
        have hw : |(2648206733/5000000000 : ℝ)|=(2648206733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-106294299/500000000 : ℝ)|^131 ≤ (6443905363633/50000000000000 : ℝ)^99
        have hw : |(-106294299/500000000 : ℝ)|=(106294299/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1343899709/2500000000 : ℝ)|^131 ≤ (4398373400391/10000000000000 : ℝ)^99
        have hw : |(1343899709/2500000000 : ℝ)|=(1343899709/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_box_2 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5296413081/10000000000 : ℝ)*x 0 + (671949889/1250000000 : ℝ)*x 1 + (-2125886123/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5296413081/10000000000 : ℝ)^131 ≤ (43128451113983/100000000000000 : ℝ)^99 := by
    have hnat : (5296413081 : ℕ)^131*100000000000000^99 ≤ 43128451113983^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296413081 10000000000 43128451113983 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (671949889/1250000000 : ℝ)^131 ≤ (8796747398423/20000000000000 : ℝ)^99 := by
    have hnat : (671949889 : ℕ)^131*20000000000000^99 ≤ 8796747398423^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671949889 1250000000 8796747398423 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2125886123/10000000000 : ℝ)^131 ≤ (1610976484299/12500000000000 : ℝ)^99 := by
    have hnat : (2125886123 : ℕ)^131*12500000000000^99 ≤ 1610976484299^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125886123 10000000000 1610976484299 12500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5296413081/10000000000 : ℝ), (671949889/1250000000 : ℝ), (-2125886123/10000000000 : ℝ)] ![(43128451113983/100000000000000 : ℝ), (8796747398423/20000000000000 : ℝ), (1610976484299/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5296413081/10000000000 : ℝ)|^131 ≤ (43128451113983/100000000000000 : ℝ)^99
        have hw : |(5296413081/10000000000 : ℝ)|=(5296413081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(671949889/1250000000 : ℝ)|^131 ≤ (8796747398423/20000000000000 : ℝ)^99
        have hw : |(671949889/1250000000 : ℝ)|=(671949889/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2125886123/10000000000 : ℝ)|^131 ≤ (1610976484299/12500000000000 : ℝ)^99
        have hw : |(-2125886123/10000000000 : ℝ)|=(2125886123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_box_3 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4464846563/10000000000 : ℝ)*x 0 + (1076594541/2500000000 : ℝ)*x 1 + (4306378211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4464846563/10000000000 : ℝ)^131 ≤ (1720214867857/5000000000000 : ℝ)^99 := by
    have hnat : (4464846563 : ℕ)^131*5000000000000^99 ≤ 1720214867857^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4464846563 10000000000 1720214867857 5000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1076594541/2500000000 : ℝ)^131 ≤ (3279785108077/10000000000000 : ℝ)^99 := by
    have hnat : (1076594541 : ℕ)^131*10000000000000^99 ≤ 3279785108077^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076594541 2500000000 3279785108077 10000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4306378211/10000000000 : ℝ)^131 ≤ (3279785155443/10000000000000 : ℝ)^99 := by
    have hnat : (4306378211 : ℕ)^131*10000000000000^99 ≤ 3279785155443^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4306378211 10000000000 3279785155443 10000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4464846563/10000000000 : ℝ), (1076594541/2500000000 : ℝ), (4306378211/10000000000 : ℝ)] ![(1720214867857/5000000000000 : ℝ), (3279785108077/10000000000000 : ℝ), (3279785155443/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4464846563/10000000000 : ℝ)|^131 ≤ (1720214867857/5000000000000 : ℝ)^99
        have hw : |(4464846563/10000000000 : ℝ)|=(4464846563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1076594541/2500000000 : ℝ)|^131 ≤ (3279785108077/10000000000000 : ℝ)^99
        have hw : |(1076594541/2500000000 : ℝ)|=(1076594541/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4306378211/10000000000 : ℝ)|^131 ≤ (3279785155443/10000000000000 : ℝ)^99
        have hw : |(4306378211/10000000000 : ℝ)|=(4306378211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_box_4 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1135175583/5000000000 : ℝ)*x 0 + (264086859/500000000 : ℝ)*x 1 + (2640868297/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1135175583/5000000000 : ℝ)^131 ≤ (140592286191/1000000000000 : ℝ)^99 := by
    have hnat : (1135175583 : ℕ)^131*1000000000000^99 ≤ 140592286191^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1135175583 5000000000 140592286191 1000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (264086859/500000000 : ℝ)^131 ≤ (42970388837157/100000000000000 : ℝ)^99 := by
    have hnat : (264086859 : ℕ)^131*100000000000000^99 ≤ 42970388837157^99*500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264086859 500000000 42970388837157 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2640868297/5000000000 : ℝ)^131 ≤ (8594076505731/20000000000000 : ℝ)^99 := by
    have hnat : (2640868297 : ℕ)^131*20000000000000^99 ≤ 8594076505731^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640868297 5000000000 8594076505731 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1135175583/5000000000 : ℝ), (264086859/500000000 : ℝ), (2640868297/5000000000 : ℝ)] ![(140592286191/1000000000000 : ℝ), (42970388837157/100000000000000 : ℝ), (8594076505731/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1135175583/5000000000 : ℝ)|^131 ≤ (140592286191/1000000000000 : ℝ)^99
        have hw : |(-1135175583/5000000000 : ℝ)|=(1135175583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(264086859/500000000 : ℝ)|^131 ≤ (42970388837157/100000000000000 : ℝ)^99
        have hw : |(264086859/500000000 : ℝ)|=(264086859/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2640868297/5000000000 : ℝ)|^131 ≤ (8594076505731/20000000000000 : ℝ)^99
        have hw : |(2640868297/5000000000 : ℝ)|=(2640868297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_box_5 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2681327099/5000000000 : ℝ)*x 0 + (-67592229/312500000 : ℝ)*x 1 + (2640868289/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681327099/5000000000 : ℝ)^131 ≤ (10960909793107/25000000000000 : ℝ)^99 := by
    have hnat : (2681327099 : ℕ)^131*25000000000000^99 ≤ 10960909793107^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681327099 5000000000 10960909793107 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (67592229/312500000 : ℝ)^131 ≤ (2637195691769/20000000000000 : ℝ)^99 := by
    have hnat : (67592229 : ℕ)^131*20000000000000^99 ≤ 2637195691769^99*312500000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67592229 312500000 2637195691769 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2640868289/5000000000 : ℝ)^131 ≤ (4297038235641/10000000000000 : ℝ)^99 := by
    have hnat : (2640868289 : ℕ)^131*10000000000000^99 ≤ 4297038235641^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640868289 5000000000 4297038235641 10000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681327099/5000000000 : ℝ), (-67592229/312500000 : ℝ), (2640868289/5000000000 : ℝ)] ![(10960909793107/25000000000000 : ℝ), (2637195691769/20000000000000 : ℝ), (4297038235641/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681327099/5000000000 : ℝ)|^131 ≤ (10960909793107/25000000000000 : ℝ)^99
        have hw : |(2681327099/5000000000 : ℝ)|=(2681327099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-67592229/312500000 : ℝ)|^131 ≤ (2637195691769/20000000000000 : ℝ)^99
        have hw : |(-67592229/312500000 : ℝ)|=(67592229/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2640868289/5000000000 : ℝ)|^131 ≤ (4297038235641/10000000000000 : ℝ)^99
        have hw : |(2640868289/5000000000 : ℝ)|=(2640868289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_box_6 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (670331781/1250000000 : ℝ)*x 0 + (5281736703/10000000000 : ℝ)*x 1 + (-1081475547/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (670331781/1250000000 : ℝ)^131 ≤ (43843639713347/100000000000000 : ℝ)^99 := by
    have hnat : (670331781 : ℕ)^131*100000000000000^99 ≤ 43843639713347^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      670331781 1250000000 43843639713347 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5281736703/10000000000 : ℝ)^131 ≤ (134282449069/312500000000 : ℝ)^99 := by
    have hnat : (5281736703 : ℕ)^131*312500000000^99 ≤ 134282449069^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281736703 10000000000 134282449069 312500000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081475547/5000000000 : ℝ)^131 ≤ (3296494142803/25000000000000 : ℝ)^99 := by
    have hnat : (1081475547 : ℕ)^131*25000000000000^99 ≤ 3296494142803^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081475547 5000000000 3296494142803 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(670331781/1250000000 : ℝ), (5281736703/10000000000 : ℝ), (-1081475547/5000000000 : ℝ)] ![(43843639713347/100000000000000 : ℝ), (134282449069/312500000000 : ℝ), (3296494142803/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(670331781/1250000000 : ℝ)|^131 ≤ (43843639713347/100000000000000 : ℝ)^99
        have hw : |(670331781/1250000000 : ℝ)|=(670331781/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5281736703/10000000000 : ℝ)|^131 ≤ (134282449069/312500000000 : ℝ)^99
        have hw : |(5281736703/10000000000 : ℝ)|=(5281736703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1081475547/5000000000 : ℝ)|^131 ≤ (3296494142803/25000000000000 : ℝ)^99
        have hw : |(-1081475547/5000000000 : ℝ)|=(1081475547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_box_7 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4250407431/10000000000 : ℝ)*x 0 + (551697177/1250000000 : ℝ)*x 1 + (4413577161/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4250407431/10000000000 : ℝ)^131 ≤ (8058743227173/25000000000000 : ℝ)^99 := by
    have hnat : (4250407431 : ℕ)^131*25000000000000^99 ≤ 8058743227173^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4250407431 10000000000 8058743227173 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (551697177/1250000000 : ℝ)^131 ≤ (27106011869/80000000000 : ℝ)^99 := by
    have hnat : (551697177 : ℕ)^131*80000000000^99 ≤ 27106011869^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551697177 1250000000 27106011869 80000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4413577161/10000000000 : ℝ)^131 ≤ (8470628061471/25000000000000 : ℝ)^99 := by
    have hnat : (4413577161 : ℕ)^131*25000000000000^99 ≤ 8470628061471^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4413577161 10000000000 8470628061471 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4250407431/10000000000 : ℝ), (551697177/1250000000 : ℝ), (4413577161/10000000000 : ℝ)] ![(8058743227173/25000000000000 : ℝ), (27106011869/80000000000 : ℝ), (8470628061471/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4250407431/10000000000 : ℝ)|^131 ≤ (8058743227173/25000000000000 : ℝ)^99
        have hw : |(4250407431/10000000000 : ℝ)|=(4250407431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(551697177/1250000000 : ℝ)|^131 ≤ (27106011869/80000000000 : ℝ)^99
        have hw : |(551697177/1250000000 : ℝ)|=(551697177/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4413577161/10000000000 : ℝ)|^131 ≤ (8470628061471/25000000000000 : ℝ)^99
        have hw : |(4413577161/10000000000 : ℝ)|=(4413577161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_box_8 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-2217605327/10000000000 : ℝ)*x 0 + (1304452171/2500000000 : ℝ)*x 1 + (1346302499/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2217605327/10000000000 : ℝ)^131 ≤ (6814326037953/50000000000000 : ℝ)^99 := by
    have hnat : (2217605327 : ℕ)^131*50000000000000^99 ≤ 6814326037953^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2217605327 10000000000 6814326037953 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1304452171/2500000000 : ℝ)^131 ≤ (1691341017749/4000000000000 : ℝ)^99 := by
    have hnat : (1304452171 : ℕ)^131*4000000000000^99 ≤ 1691341017749^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304452171 2500000000 1691341017749 4000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1346302499/2500000000 : ℝ)^131 ≤ (44087822462421/100000000000000 : ℝ)^99 := by
    have hnat : (1346302499 : ℕ)^131*100000000000000^99 ≤ 44087822462421^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346302499 2500000000 44087822462421 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2217605327/10000000000 : ℝ), (1304452171/2500000000 : ℝ), (1346302499/2500000000 : ℝ)] ![(6814326037953/50000000000000 : ℝ), (1691341017749/4000000000000 : ℝ), (44087822462421/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2217605327/10000000000 : ℝ)|^131 ≤ (6814326037953/50000000000000 : ℝ)^99
        have hw : |(-2217605327/10000000000 : ℝ)|=(2217605327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1304452171/2500000000 : ℝ)|^131 ≤ (1691341017749/4000000000000 : ℝ)^99
        have hw : |(1304452171/2500000000 : ℝ)|=(1304452171/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1346302499/2500000000 : ℝ)|^131 ≤ (44087822462421/100000000000000 : ℝ)^99
        have hw : |(1346302499/2500000000 : ℝ)|=(1346302499/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_box_9 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (528962729/1000000000 : ℝ)*x 0 + (-1061011319/5000000000 : ℝ)*x 1 + (2692604983/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528962729/1000000000 : ℝ)^131 ≤ (538191865247/1250000000000 : ℝ)^99 := by
    have hnat : (528962729 : ℕ)^131*1250000000000^99 ≤ 538191865247^99*1000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528962729 1000000000 538191865247 1250000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1061011319/5000000000 : ℝ)^131 ≤ (6428414314983/50000000000000 : ℝ)^99 := by
    have hnat : (1061011319 : ℕ)^131*50000000000000^99 ≤ 6428414314983^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061011319 5000000000 6428414314983 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2692604983/5000000000 : ℝ)^131 ≤ (44087822137429/100000000000000 : ℝ)^99 := by
    have hnat : (2692604983 : ℕ)^131*100000000000000^99 ≤ 44087822137429^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692604983 5000000000 44087822137429 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528962729/1000000000 : ℝ), (-1061011319/5000000000 : ℝ), (2692604983/5000000000 : ℝ)] ![(538191865247/1250000000000 : ℝ), (6428414314983/50000000000000 : ℝ), (44087822137429/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528962729/1000000000 : ℝ)|^131 ≤ (538191865247/1250000000000 : ℝ)^99
        have hw : |(528962729/1000000000 : ℝ)|=(528962729/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1061011319/5000000000 : ℝ)|^131 ≤ (6428414314983/50000000000000 : ℝ)^99
        have hw : |(-1061011319/5000000000 : ℝ)|=(1061011319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2692604983/5000000000 : ℝ)|^131 ≤ (44087822137429/100000000000000 : ℝ)^99
        have hw : |(2692604983/5000000000 : ℝ)|=(2692604983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_box_10 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1322406823/2500000000 : ℝ)*x 0 + (5385209987/10000000000 : ℝ)*x 1 + (-2122022607/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322406823/2500000000 : ℝ)^131 ≤ (43055349241301/100000000000000 : ℝ)^99 := by
    have hnat : (1322406823 : ℕ)^131*100000000000000^99 ≤ 43055349241301^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322406823 2500000000 43055349241301 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5385209987/10000000000 : ℝ)^131 ≤ (44087822364923/100000000000000 : ℝ)^99 := by
    have hnat : (5385209987 : ℕ)^131*100000000000000^99 ≤ 44087822364923^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385209987 10000000000 44087822364923 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2122022607/10000000000 : ℝ)^131 ≤ (6428414190717/50000000000000 : ℝ)^99 := by
    have hnat : (2122022607 : ℕ)^131*50000000000000^99 ≤ 6428414190717^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122022607 10000000000 6428414190717 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322406823/2500000000 : ℝ), (5385209987/10000000000 : ℝ), (-2122022607/10000000000 : ℝ)] ![(43055349241301/100000000000000 : ℝ), (44087822364923/100000000000000 : ℝ), (6428414190717/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322406823/2500000000 : ℝ)|^131 ≤ (43055349241301/100000000000000 : ℝ)^99
        have hw : |(1322406823/2500000000 : ℝ)|=(1322406823/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5385209987/10000000000 : ℝ)|^131 ≤ (44087822364923/100000000000000 : ℝ)^99
        have hw : |(5385209987/10000000000 : ℝ)|=(5385209987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2122022607/10000000000 : ℝ)|^131 ≤ (6428414190717/50000000000000 : ℝ)^99
        have hw : |(-2122022607/10000000000 : ℝ)|=(2122022607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_box_11 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2243265603/5000000000 : ℝ)*x 0 + (4295395337/10000000000 : ℝ)*x 1 + (4295395353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2243265603/5000000000 : ℝ)^131 ≤ (17312786832393/50000000000000 : ℝ)^99 := by
    have hnat : (2243265603 : ℕ)^131*50000000000000^99 ≤ 17312786832393^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2243265603 5000000000 17312786832393 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4295395337/10000000000 : ℝ)^131 ≤ (32687213079551/100000000000000 : ℝ)^99 := by
    have hnat : (4295395337 : ℕ)^131*100000000000000^99 ≤ 32687213079551^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4295395337 10000000000 32687213079551 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4295395353/10000000000 : ℝ)^131 ≤ (4085901655083/12500000000000 : ℝ)^99 := by
    have hnat : (4295395353 : ℕ)^131*12500000000000^99 ≤ 4085901655083^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4295395353 10000000000 4085901655083 12500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2243265603/5000000000 : ℝ), (4295395337/10000000000 : ℝ), (4295395353/10000000000 : ℝ)] ![(17312786832393/50000000000000 : ℝ), (32687213079551/100000000000000 : ℝ), (4085901655083/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2243265603/5000000000 : ℝ)|^131 ≤ (17312786832393/50000000000000 : ℝ)^99
        have hw : |(2243265603/5000000000 : ℝ)|=(2243265603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4295395337/10000000000 : ℝ)|^131 ≤ (32687213079551/100000000000000 : ℝ)^99
        have hw : |(4295395337/10000000000 : ℝ)|=(4295395337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4295395353/10000000000 : ℝ)|^131 ≤ (4085901655083/12500000000000 : ℝ)^99
        have hw : |(4295395353/10000000000 : ℝ)|=(4295395353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_box_12 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1035707037/5000000000 : ℝ)*x 0 + (543828337/1000000000 : ℝ)*x 1 + (1054735611/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1035707037/5000000000 : ℝ)^131 ≤ (12452664619123/100000000000000 : ℝ)^99 := by
    have hnat : (1035707037 : ℕ)^131*100000000000000^99 ≤ 12452664619123^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035707037 5000000000 12452664619123 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (543828337/1000000000 : ℝ)^131 ≤ (11165921130287/25000000000000 : ℝ)^99 := by
    have hnat : (543828337 : ℕ)^131*25000000000000^99 ≤ 11165921130287^99*1000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543828337 1000000000 11165921130287 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1054735611/2000000000 : ℝ)^131 ≤ (42883650849559/100000000000000 : ℝ)^99 := by
    have hnat : (1054735611 : ℕ)^131*100000000000000^99 ≤ 42883650849559^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054735611 2000000000 42883650849559 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1035707037/5000000000 : ℝ), (543828337/1000000000 : ℝ), (1054735611/2000000000 : ℝ)] ![(12452664619123/100000000000000 : ℝ), (11165921130287/25000000000000 : ℝ), (42883650849559/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1035707037/5000000000 : ℝ)|^131 ≤ (12452664619123/100000000000000 : ℝ)^99
        have hw : |(-1035707037/5000000000 : ℝ)|=(1035707037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(543828337/1000000000 : ℝ)|^131 ≤ (11165921130287/25000000000000 : ℝ)^99
        have hw : |(543828337/1000000000 : ℝ)|=(543828337/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1054735611/2000000000 : ℝ)|^131 ≤ (42883650849559/100000000000000 : ℝ)^99
        have hw : |(1054735611/2000000000 : ℝ)|=(1054735611/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_box_13 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (536834053/1000000000 : ℝ)*x 0 + (-33844923/156250000 : ℝ)*x 1 + (5273678003/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536834053/1000000000 : ℝ)^131 ≤ (21952583353761/50000000000000 : ℝ)^99 := by
    have hnat : (536834053 : ℕ)^131*50000000000000^99 ≤ 21952583353761^99*1000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536834053 1000000000 21952583353761 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (33844923/156250000 : ℝ)^131 ≤ (13211182981313/100000000000000 : ℝ)^99 := by
    have hnat : (33844923 : ℕ)^131*100000000000000^99 ≤ 13211182981313^99*156250000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33844923 156250000 13211182981313 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5273678003/10000000000 : ℝ)^131 ≤ (42883650290037/100000000000000 : ℝ)^99 := by
    have hnat : (5273678003 : ℕ)^131*100000000000000^99 ≤ 42883650290037^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5273678003 10000000000 42883650290037 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(536834053/1000000000 : ℝ), (-33844923/156250000 : ℝ), (5273678003/10000000000 : ℝ)] ![(21952583353761/50000000000000 : ℝ), (13211182981313/100000000000000 : ℝ), (42883650290037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(536834053/1000000000 : ℝ)|^131 ≤ (21952583353761/50000000000000 : ℝ)^99
        have hw : |(536834053/1000000000 : ℝ)|=(536834053/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-33844923/156250000 : ℝ)|^131 ≤ (13211182981313/100000000000000 : ℝ)^99
        have hw : |(-33844923/156250000 : ℝ)|=(33844923/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5273678003/10000000000 : ℝ)|^131 ≤ (42883650290037/100000000000000 : ℝ)^99
        have hw : |(5273678003/10000000000 : ℝ)|=(5273678003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_box_14 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5368341381/10000000000 : ℝ)*x 0 + (2636838173/5000000000 : ℝ)*x 1 + (-2166076141/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368341381/10000000000 : ℝ)^131 ≤ (10976293979283/25000000000000 : ℝ)^99 := by
    have hnat : (5368341381 : ℕ)^131*25000000000000^99 ≤ 10976293979283^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368341381 10000000000 10976293979283 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2636838173/5000000000 : ℝ)^131 ≤ (42883632460637/100000000000000 : ℝ)^99 := by
    have hnat : (2636838173 : ℕ)^131*100000000000000^99 ≤ 42883632460637^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636838173 5000000000 42883632460637 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2166076141/10000000000 : ℝ)^131 ≤ (2642238321751/20000000000000 : ℝ)^99 := by
    have hnat : (2166076141 : ℕ)^131*20000000000000^99 ≤ 2642238321751^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2166076141 10000000000 2642238321751 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368341381/10000000000 : ℝ), (2636838173/5000000000 : ℝ), (-2166076141/10000000000 : ℝ)] ![(10976293979283/25000000000000 : ℝ), (42883632460637/100000000000000 : ℝ), (2642238321751/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368341381/10000000000 : ℝ)|^131 ≤ (10976293979283/25000000000000 : ℝ)^99
        have hw : |(5368341381/10000000000 : ℝ)|=(5368341381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2636838173/5000000000 : ℝ)|^131 ≤ (42883632460637/100000000000000 : ℝ)^99
        have hw : |(2636838173/5000000000 : ℝ)|=(2636838173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2166076141/10000000000 : ℝ)|^131 ≤ (2642238321751/20000000000000 : ℝ)^99
        have hw : |(-2166076141/10000000000 : ℝ)|=(2166076141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_box_15 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (211588159/500000000 : ℝ)*x 0 + (4422776709/10000000000 : ℝ)*x 1 + (442277721/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211588159/500000000 : ℝ)^131 ≤ (16024001978413/50000000000000 : ℝ)^99 := by
    have hnat : (211588159 : ℕ)^131*50000000000000^99 ≤ 16024001978413^99*500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211588159 500000000 16024001978413 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4422776709/10000000000 : ℝ)^131 ≤ (33975995469087/100000000000000 : ℝ)^99 := by
    have hnat : (4422776709 : ℕ)^131*100000000000000^99 ≤ 33975995469087^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4422776709 10000000000 33975995469087 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (442277721/1000000000 : ℝ)^131 ≤ (16988000280911/50000000000000 : ℝ)^99 := by
    have hnat : (442277721 : ℕ)^131*50000000000000^99 ≤ 16988000280911^99*1000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442277721 1000000000 16988000280911 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(211588159/500000000 : ℝ), (4422776709/10000000000 : ℝ), (442277721/1000000000 : ℝ)] ![(16024001978413/50000000000000 : ℝ), (33975995469087/100000000000000 : ℝ), (16988000280911/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(211588159/500000000 : ℝ)|^131 ≤ (16024001978413/50000000000000 : ℝ)^99
        have hw : |(211588159/500000000 : ℝ)|=(211588159/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4422776709/10000000000 : ℝ)|^131 ≤ (33975995469087/100000000000000 : ℝ)^99
        have hw : |(4422776709/10000000000 : ℝ)|=(4422776709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(442277721/1000000000 : ℝ)|^131 ≤ (16988000280911/50000000000000 : ℝ)^99
        have hw : |(442277721/1000000000 : ℝ)|=(442277721/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1191_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37607663/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3519/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11417/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(31119/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59337/100000 : ℝ) ∧ (79957/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (41617/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3519/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11417/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3519/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11417/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3519/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11417/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3519/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11417/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3519/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11417/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3519/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11417/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11417/100000 : ℝ) ^ (8383/2048 : ℝ) ≤ (1734697277990013/12500000000000000000 : ℝ) := by
    have hpowers : (11417/100000 : ℝ)^8383 ≤ (1734697277990013/12500000000000000000 : ℝ)^2048 := by
      have hnat : (11417 : ℕ)^8383*12500000000000000000^2048 ≤ 1734697277990013^2048*100000^8383 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11417 100000 1734697277990013 12500000000000000000 8383 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11417/100000 : ℝ)) (X := (1734697277990013/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8383 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3519/25000 : ℝ) ^ (8383/2048 : ℝ) ≤ (1021769103862273/3125000000000000000 : ℝ) := by
    have hpowers : (3519/25000 : ℝ)^8383 ≤ (1021769103862273/3125000000000000000 : ℝ)^2048 := by
      have hnat : (3519 : ℕ)^8383*3125000000000000000^2048 ≤ 1021769103862273^2048*25000^8383 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3519 25000 1021769103862273 3125000000000000000 8383 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3519/25000 : ℝ)) (X := (1021769103862273/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 8383 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251734697277990013/6250000000000000000 : ℝ) ≤ (5000338999165947/5000000000000000 : ℝ) ^ (8383/2048 : ℝ) := by
    have hpowers : (6251734697277990013/6250000000000000000 : ℝ)^2048 ≤ (5000338999165947/5000000000000000 : ℝ)^8383 := by
      have hnat : (6251734697277990013 : ℕ)^2048*5000000000000000^8383 ≤ 5000338999165947^8383*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251734697277990013 6250000000000000000 5000338999165947 5000000000000000 2048 8383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000338999165947/5000000000000000 : ℝ)) (X := (6251734697277990013/6250000000000000000 : ℝ)) (by norm_num) 8383 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (2501164354738687821/2500000000000000000 : ℝ) ≤ (39066943850237/39062500000000 : ℝ) ^ (8383/2048 : ℝ) := by
    have hpowers : (2501164354738687821/2500000000000000000 : ℝ)^2048 ≤ (39066943850237/39062500000000 : ℝ)^8383 := by
      have hnat : (2501164354738687821 : ℕ)^2048*39062500000000^8383 ≤ 39066943850237^8383*2500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501164354738687821 2500000000000000000 39066943850237 39062500000000 2048 8383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (39066943850237/39062500000000 : ℝ)) (X := (2501164354738687821/2500000000000000000 : ℝ)) (by norm_num) 8383 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (1563521769103862273/1562500000000000000 : ℝ) ≤ (200031945059789/200000000000000 : ℝ) ^ (8383/2048 : ℝ) := by
    have hpowers : (1563521769103862273/1562500000000000000 : ℝ)^2048 ≤ (200031945059789/200000000000000 : ℝ)^8383 := by
      have hnat : (1563521769103862273 : ℕ)^2048*200000000000000^8383 ≤ 200031945059789^8383*1562500000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1563521769103862273 1562500000000000000 200031945059789 200000000000000 2048 8383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200031945059789/200000000000000 : ℝ)) (X := (1563521769103862273/1562500000000000000 : ℝ)) (by norm_num) 8383 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1734697277990013/12500000000000000000 : ℝ) ≤ ((13290653833569594647/13295000000000000000 : ℝ)+2*(229813664389/132950000000000 : ℝ)*(11417/100000 : ℝ))^(8383/2048 : ℝ) := by
    rw [show (13290653833569594647/13295000000000000000 : ℝ)+2*(229813664389/132950000000000 : ℝ)*(11417/100000 : ℝ)=(5000338999165947/5000000000000000 : ℝ) by norm_num, show 1+2*(1734697277990013/12500000000000000000 : ℝ)=(6251734697277990013/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1021769103862273/3125000000000000000 : ℝ)+(1734697277990013/12500000000000000000 : ℝ) ≤ ((13290653833569594647/13295000000000000000 : ℝ)+(229813664389/132950000000000 : ℝ)*((3519/25000 : ℝ)+(11417/100000 : ℝ)))^(8383/2048 : ℝ) := by
    rw [show (13290653833569594647/13295000000000000000 : ℝ)+(229813664389/132950000000000 : ℝ)*((3519/25000 : ℝ)+(11417/100000 : ℝ))=(39066943850237/39062500000000 : ℝ) by norm_num, show 1+(1021769103862273/3125000000000000000 : ℝ)+(1734697277990013/12500000000000000000 : ℝ)=(2501164354738687821/2500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1021769103862273/3125000000000000000 : ℝ) ≤ ((13290653833569594647/13295000000000000000 : ℝ)+2*(229813664389/132950000000000 : ℝ)*(3519/25000 : ℝ))^(8383/2048 : ℝ) := by
    rw [show (13290653833569594647/13295000000000000000 : ℝ)+2*(229813664389/132950000000000 : ℝ)*(3519/25000 : ℝ)=(200031945059789/200000000000000 : ℝ) by norm_num, show 1+2*(1021769103862273/3125000000000000000 : ℝ)=(1563521769103862273/1562500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13290653833569594647/13295000000000000000 : ℝ)*(X 1 0+X 2 0)+(229813664389/132950000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8383/2048 : ℝ)) (lo := (11417/100000 : ℝ)) (hi := (3519/25000 : ℝ)) (c := (13290653833569594647/13295000000000000000 : ℝ)) (alpha := (229813664389/132950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13290653833569594647/13295000000000000000 : ℝ)*(X 0 1+X 2 1)+(229813664389/132950000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8383/2048 : ℝ)) (lo := (11417/100000 : ℝ)) (hi := (3519/25000 : ℝ)) (c := (13290653833569594647/13295000000000000000 : ℝ)) (alpha := (229813664389/132950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13290653833569594647/13295000000000000000 : ℝ)*(X 0 2+X 1 2)+(229813664389/132950000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8383/2048 : ℝ)) (lo := (11417/100000 : ℝ)) (hi := (3519/25000 : ℝ)) (c := (13290653833569594647/13295000000000000000 : ℝ)) (alpha := (229813664389/132950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-504594721/2500000000 : ℝ)*X 0 0+(5375598749/10000000000 : ℝ)*X 0 1+(5375598729/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2648206733/5000000000 : ℝ)*X 1 0+(-106294299/500000000 : ℝ)*X 1 1+(1343899709/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5296413081/10000000000 : ℝ)*X 2 0+(671949889/1250000000 : ℝ)*X 2 1+(-2125886123/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4464846563/10000000000 : ℝ)*X 0 0+(1076594541/2500000000 : ℝ)*X 0 1+(4306378211/10000000000 : ℝ)*X 0 2+(4464846563/10000000000 : ℝ)*X 1 0+(1076594541/2500000000 : ℝ)*X 1 1+(4306378211/10000000000 : ℝ)*X 1 2+(4464846563/10000000000 : ℝ)*X 2 0+(1076594541/2500000000 : ℝ)*X 2 1+(4306378211/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1135175583/5000000000 : ℝ)*X 0 0+(264086859/500000000 : ℝ)*X 0 1+(2640868297/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2681327099/5000000000 : ℝ)*X 1 0+(-67592229/312500000 : ℝ)*X 1 1+(2640868289/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((670331781/1250000000 : ℝ)*X 2 0+(5281736703/10000000000 : ℝ)*X 2 1+(-1081475547/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4250407431/10000000000 : ℝ)*X 0 0+(551697177/1250000000 : ℝ)*X 0 1+(4413577161/10000000000 : ℝ)*X 0 2+(4250407431/10000000000 : ℝ)*X 1 0+(551697177/1250000000 : ℝ)*X 1 1+(4413577161/10000000000 : ℝ)*X 1 2+(4250407431/10000000000 : ℝ)*X 2 0+(551697177/1250000000 : ℝ)*X 2 1+(4413577161/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2217605327/10000000000 : ℝ)*X 0 0+(1304452171/2500000000 : ℝ)*X 0 1+(1346302499/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((528962729/1000000000 : ℝ)*X 1 0+(-1061011319/5000000000 : ℝ)*X 1 1+(2692604983/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1322406823/2500000000 : ℝ)*X 2 0+(5385209987/10000000000 : ℝ)*X 2 1+(-2122022607/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2243265603/5000000000 : ℝ)*X 0 0+(4295395337/10000000000 : ℝ)*X 0 1+(4295395353/10000000000 : ℝ)*X 0 2+(2243265603/5000000000 : ℝ)*X 1 0+(4295395337/10000000000 : ℝ)*X 1 1+(4295395353/10000000000 : ℝ)*X 1 2+(2243265603/5000000000 : ℝ)*X 2 0+(4295395337/10000000000 : ℝ)*X 2 1+(4295395353/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1035707037/5000000000 : ℝ)*X 0 0+(543828337/1000000000 : ℝ)*X 0 1+(1054735611/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((536834053/1000000000 : ℝ)*X 1 0+(-33844923/156250000 : ℝ)*X 1 1+(5273678003/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5368341381/10000000000 : ℝ)*X 2 0+(2636838173/5000000000 : ℝ)*X 2 1+(-2166076141/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((211588159/500000000 : ℝ)*X 0 0+(4422776709/10000000000 : ℝ)*X 0 1+(442277721/1000000000 : ℝ)*X 0 2+(211588159/500000000 : ℝ)*X 1 0+(4422776709/10000000000 : ℝ)*X 1 1+(442277721/1000000000 : ℝ)*X 1 2+(211588159/500000000 : ℝ)*X 2 0+(4422776709/10000000000 : ℝ)*X 2 1+(442277721/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31119/50000 : ℝ) ≤ (-103427101392185125821584540738049/166187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (412351/20000000000000 : ℝ)*(upper1) + (237259/2500000000000 : ℝ)*(lower2) + (2456061/2000000000000 : ℝ)*(upper4) + (1980710949939611/50000000000000 : ℝ)*(major0) + (1980710949939611/50000000000000 : ℝ)*(major1) + (1980710949939611/50000000000000 : ℝ)*(major2) + (13404702131/50000000000000 : ℝ)*(sp1) + (216919653/2000000000000 : ℝ)*(sp2) + (9863113931/100000000000000 : ℝ)*(sp3) + (5310177721947167/100000000000000 : ℝ)*(sp4) + (2655087304947047/50000000000000 : ℝ)*(sp5) + (1062038114663141/20000000000000 : ℝ)*(sp6) + (2633377579678793/100000000000000 : ℝ)*(sp7) + (23697351189/100000000000000 : ℝ)*(sp8) + (658346860698181/25000000000000 : ℝ)*(f.failure) + (1327550354824589/25000000000000 : ℝ)*(f.sum) + (101889582068529/13295000000000000000000000000 : ℝ)*base66 + (1075929148176237683/664750000000000000000000000000000 : ℝ)*base68 + (51271963434237683/664750000000000000000000000000000 : ℝ)*base70 + (19030256779273237683/664750000000000000000000000000000 : ℝ)*base72 + (718828261673/1661875000000000000000000000 : ℝ)*base74 + (744469887833737683/664750000000000000000000000000000 : ℝ)*base76 + (6003357624266737683/664750000000000000000000000000000 : ℝ)*base78 + (312911037558512317/664750000000000000000000000000000 : ℝ)*base79 + (5287358847493/6647500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (1738997/625000000000000000000 : ℝ)*base90 + (1738997/625000000000000000000 : ℝ)*base92 + (1738997/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (59337/100000 : ℝ) ≤ (3944577320872984728439133174757/6647500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7750073/10000000000000 : ℝ)*(lower0) + (105915021/100000000000000 : ℝ)*(upper2) + (3048303/4000000000000 : ℝ)*(lower4) + (40263697005623/1000000000000 : ℝ)*(major0) + (40263697005623/1000000000000 : ℝ)*(major1) + (40263697005623/1000000000000 : ℝ)*(major2) + (5356396078235851/100000000000000 : ℝ)*(sp0) + (5356389839236279/100000000000000 : ℝ)*(sp1) + (2678193100630899/50000000000000 : ℝ)*(sp2) + (1338277076633161/50000000000000 : ℝ)*(sp3) + (1946675861/25000000000000 : ℝ)*(sp5) + (456987117/4000000000000 : ℝ)*(sp6) + (7868523159/100000000000000 : ℝ)*(sp7) + (1547703873/100000000000000 : ℝ)*(sp12) + (1338281010894741/50000000000000 : ℝ)*(f.failure) + (1339099406484931/25000000000000 : ℝ)*(f.sum) + (131469343790331/2659000000000000000000000000 : ℝ)*base66 + (91130934384905081/13295000000000000000000000000000 : ℝ)*base67 + (17202630098575081/13295000000000000000000000000000 : ℝ)*base69 + (715321488247194919/13295000000000000000000000000000 : ℝ)*base72 + (634519025611/132950000000000000000000000 : ℝ)*base74 + (85561458715385081/13295000000000000000000000000000 : ℝ)*base75 + (130681053383765081/13295000000000000000000000000000 : ℝ)*base77 + (42505915122484919/13295000000000000000000000000000 : ℝ)*base80 + (150131143897/2659000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (1999717/1250000000000000000000 : ℝ)*base90 + (1999717/1250000000000000000000 : ℝ)*base92 + (1999717/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (79957/100000 : ℝ) ≤ (265765216661203703694765632546811/332375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10988739/50000000000000 : ℝ)*(lower3) + (9096587/100000000000000 : ℝ)*(upper4) + (1589263/50000000000000 : ℝ)*(lower5) + (2246905041467929/50000000000000 : ℝ)*(major0) + (2246905041467929/50000000000000 : ℝ)*(major1) + (2246905041467929/50000000000000 : ℝ)*(major2) + (32219649/10000000000000 : ℝ)*(sp0) + (567849357/12500000000000 : ℝ)*(sp1) + (8093880301/50000000000000 : ℝ)*(sp2) + (9718055039/100000000000000 : ℝ)*(sp3) + (5973669874580231/100000000000000 : ℝ)*(sp8) + (1194733130796373/20000000000000 : ℝ)*(sp9) + (5973654009016119/100000000000000 : ℝ)*(sp10) + (29872871015691/1000000000000 : ℝ)*(sp11) + (149364840981207/5000000000000 : ℝ)*(f.failure) + (5973670196776721/100000000000000 : ℝ)*(f.sum) + (4569309184647/1661875000000000000000000000 : ℝ)*base66 + (7113102730296176063/664750000000000000000000000000000 : ℝ)*base67 + (7705842897426063/664750000000000000000000000000000 : ℝ)*base69 + (4921511455500573937/664750000000000000000000000000000 : ℝ)*base72 + (30281630750727/6647500000000000000000000000 : ℝ)*base73 + (895676287077426063/664750000000000000000000000000000 : ℝ)*base75 + (133003286619573937/664750000000000000000000000000000 : ℝ)*base78 + (6634583198616926063/664750000000000000000000000000000 : ℝ)*base79 + (46521296387/6647500000000000000000000000 : ℝ)*base81 + (310759/125000000000000000000 : ℝ)*base90 + (310759/125000000000000000000 : ℝ)*base92 + (310759/125000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-41617/50000 : ℝ) ≤ (-34579904876788588588319645073321/41546875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1060779681/100000000000000 : ℝ)*(lower0) + (799236117/100000000000000 : ℝ)*(lower1) + (160490413/50000000000000 : ℝ)*(lower3) + (498483289/100000000000000 : ℝ)*(lower4) + (566132001019819/12500000000000 : ℝ)*(major0) + (566132001019819/12500000000000 : ℝ)*(major1) + (566132001019819/12500000000000 : ℝ)*(major2) + (632675083593/100000000000000 : ℝ)*(sp5) + (2418154831463/100000000000000 : ℝ)*(sp6) + (292684302883/100000000000000 : ℝ)*(sp7) + (759391108512487/12500000000000 : ℝ)*(sp12) + (6074496193016303/100000000000000 : ℝ)*(sp13) + (6072710713268433/100000000000000 : ℝ)*(sp14) + (75260853772897/2500000000000 : ℝ)*(sp15) + (752681708804691/25000000000000 : ℝ)*(f.failure) + (759391108512487/12500000000000 : ℝ)*(f.sum) + (5406088559899/13295000000000000000000000000 : ℝ)*base66 + (527886249504591107/166187500000000000000000000000000 : ℝ)*base68 + (575444703881153607/166187500000000000000000000000000 : ℝ)*base70 + (526124198175278607/166187500000000000000000000000000 : ℝ)*base72 + (1816602999269/830937500000000000000000000 : ℝ)*base74 + (679189807218466107/166187500000000000000000000000000 : ℝ)*base76 + (1290654703538033893/166187500000000000000000000000000 : ℝ)*base77 + (602893778919153607/166187500000000000000000000000000 : ℝ)*base80 + (8558198934751/3323750000000000000000000000 : ℝ)*base82 + (1947133/625000000000000000000 : ℝ)*base89 + (1947133/625000000000000000000 : ℝ)*base91 + (1947133/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1191_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37607663/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3519/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11417/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31119/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(59337/100000 : ℝ) else (79957/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41617/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1191_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1191_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37607663/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3519/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1427/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31119/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(59337/100000 : ℝ) else (79957/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41617/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1191_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1191_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37607663/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3519/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1427/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31119/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(59337/100000 : ℝ) else (79957/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41617/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1191_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
