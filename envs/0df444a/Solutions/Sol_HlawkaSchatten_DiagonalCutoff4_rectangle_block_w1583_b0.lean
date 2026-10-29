-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1583_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:30:45.828679+00:00
-- url     : https://prove2.me/submissions/57ae1393-a2c8-4302-a4ad-9b8afb69e7db

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
theorem support_rectangle_w1583_s0_0 (p : ℝ) (hpa : (4661/1024 : ℝ) ≤ p) (hpb : p ≤ (4663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1613049989/10000000000 : ℝ)*x 0 + (2930107183/5000000000 : ℝ)*x 1 + (4884528193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1613049989/10000000000 : ℝ)^4663 ≤ (2413365569779/25000000000000 : ℝ)^3639 := by
    have hnat : (1613049989 : ℕ)^4663*25000000000000^3639 ≤ 2413365569779^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1613049989 10000000000 2413365569779 25000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2930107183/5000000000 : ℝ)^4663 ≤ (6302535587109/12500000000000 : ℝ)^3639 := by
    have hnat : (2930107183 : ℕ)^4663*12500000000000^3639 ≤ 6302535587109^3639*5000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2930107183 5000000000 6302535587109 12500000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4884528193/10000000000 : ℝ)^4663 ≤ (39926253013399/100000000000000 : ℝ)^3639 := by
    have hnat : (4884528193 : ℕ)^4663*100000000000000^3639 ≤ 39926253013399^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4884528193 10000000000 39926253013399 100000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4663/1024 : ℝ)) 4663 3639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1613049989/10000000000 : ℝ), (2930107183/5000000000 : ℝ), (4884528193/10000000000 : ℝ)] ![(2413365569779/25000000000000 : ℝ), (6302535587109/12500000000000 : ℝ), (39926253013399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1613049989/10000000000 : ℝ)|^4663 ≤ (2413365569779/25000000000000 : ℝ)^3639
        have hw : |(-1613049989/10000000000 : ℝ)|=(1613049989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2930107183/5000000000 : ℝ)|^4663 ≤ (6302535587109/12500000000000 : ℝ)^3639
        have hw : |(2930107183/5000000000 : ℝ)|=(2930107183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4884528193/10000000000 : ℝ)|^4663 ≤ (39926253013399/100000000000000 : ℝ)^3639
        have hw : |(4884528193/10000000000 : ℝ)|=(4884528193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1583_s0_1 (p : ℝ) (hpa : (4661/1024 : ℝ) ≤ p) (hpb : p ≤ (4663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5462712229/10000000000 : ℝ)*x 0 + (-2155155459/10000000000 : ℝ)*x 1 + (4884528131/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5462712229/10000000000 : ℝ)^4663 ≤ (23040191412641/50000000000000 : ℝ)^3639 := by
    have hnat : (5462712229 : ℕ)^4663*50000000000000^3639 ≤ 23040191412641^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5462712229 10000000000 23040191412641 50000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2155155459/10000000000 : ℝ)^4663 ≤ (1749170598741/12500000000000 : ℝ)^3639 := by
    have hnat : (2155155459 : ℕ)^4663*12500000000000^3639 ≤ 1749170598741^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155155459 10000000000 1749170598741 12500000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4884528131/10000000000 : ℝ)^4663 ≤ (39926252364001/100000000000000 : ℝ)^3639 := by
    have hnat : (4884528131 : ℕ)^4663*100000000000000^3639 ≤ 39926252364001^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4884528131 10000000000 39926252364001 100000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4663/1024 : ℝ)) 4663 3639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5462712229/10000000000 : ℝ), (-2155155459/10000000000 : ℝ), (4884528131/10000000000 : ℝ)] ![(23040191412641/50000000000000 : ℝ), (1749170598741/12500000000000 : ℝ), (39926252364001/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5462712229/10000000000 : ℝ)|^4663 ≤ (23040191412641/50000000000000 : ℝ)^3639
        have hw : |(5462712229/10000000000 : ℝ)|=(5462712229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2155155459/10000000000 : ℝ)|^4663 ≤ (1749170598741/12500000000000 : ℝ)^3639
        have hw : |(-2155155459/10000000000 : ℝ)|=(2155155459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4884528131/10000000000 : ℝ)|^4663 ≤ (39926252364001/100000000000000 : ℝ)^3639
        have hw : |(4884528131/10000000000 : ℝ)|=(4884528131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1583_s0_2 (p : ℝ) (hpa : (4661/1024 : ℝ) ≤ p) (hpb : p ≤ (4663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5462712301/10000000000 : ℝ)*x 0 + (4884528027/10000000000 : ℝ)*x 1 + (-2155155497/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5462712301/10000000000 : ℝ)^4663 ≤ (2304019180177/5000000000000 : ℝ)^3639 := by
    have hnat : (5462712301 : ℕ)^4663*5000000000000^3639 ≤ 2304019180177^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5462712301 10000000000 2304019180177 5000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4884528027/10000000000 : ℝ)^4663 ≤ (623847676167/1562500000000 : ℝ)^3639 := by
    have hnat : (4884528027 : ℕ)^4663*1562500000000^3639 ≤ 623847676167^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4884528027 10000000000 623847676167 1562500000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2155155497/10000000000 : ℝ)^4663 ≤ (13993365106091/100000000000000 : ℝ)^3639 := by
    have hnat : (2155155497 : ℕ)^4663*100000000000000^3639 ≤ 13993365106091^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155155497 10000000000 13993365106091 100000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4663/1024 : ℝ)) 4663 3639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5462712301/10000000000 : ℝ), (4884528027/10000000000 : ℝ), (-2155155497/10000000000 : ℝ)] ![(2304019180177/5000000000000 : ℝ), (623847676167/1562500000000 : ℝ), (13993365106091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5462712301/10000000000 : ℝ)|^4663 ≤ (2304019180177/5000000000000 : ℝ)^3639
        have hw : |(5462712301/10000000000 : ℝ)|=(5462712301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4884528027/10000000000 : ℝ)|^4663 ≤ (623847676167/1562500000000 : ℝ)^3639
        have hw : |(4884528027/10000000000 : ℝ)|=(4884528027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2155155497/10000000000 : ℝ)|^4663 ≤ (13993365106091/100000000000000 : ℝ)^3639
        have hw : |(-2155155497/10000000000 : ℝ)|=(2155155497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1583_s0_3 (p : ℝ) (hpa : (4661/1024 : ℝ) ≤ p) (hpb : p ≤ (4663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2063255831/5000000000 : ℝ)*x 0 + (618789433/2000000000 : ℝ)*x 1 + (5417525897/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2063255831/5000000000 : ℝ)^4663 ≤ (16083468072711/50000000000000 : ℝ)^3639 := by
    have hnat : (2063255831 : ℕ)^4663*50000000000000^3639 ≤ 16083468072711^3639*5000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2063255831 5000000000 16083468072711 50000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (618789433/2000000000 : ℝ)^4663 ≤ (11120268400471/50000000000000 : ℝ)^3639 := by
    have hnat : (618789433 : ℕ)^4663*50000000000000^3639 ≤ 11120268400471^3639*2000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      618789433 2000000000 11120268400471 50000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5417525897/10000000000 : ℝ)^4663 ≤ (22796263518467/50000000000000 : ℝ)^3639 := by
    have hnat : (5417525897 : ℕ)^4663*50000000000000^3639 ≤ 22796263518467^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417525897 10000000000 22796263518467 50000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4663/1024 : ℝ)) 4663 3639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2063255831/5000000000 : ℝ), (618789433/2000000000 : ℝ), (5417525897/10000000000 : ℝ)] ![(16083468072711/50000000000000 : ℝ), (11120268400471/50000000000000 : ℝ), (22796263518467/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2063255831/5000000000 : ℝ)|^4663 ≤ (16083468072711/50000000000000 : ℝ)^3639
        have hw : |(2063255831/5000000000 : ℝ)|=(2063255831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(618789433/2000000000 : ℝ)|^4663 ≤ (11120268400471/50000000000000 : ℝ)^3639
        have hw : |(618789433/2000000000 : ℝ)|=(618789433/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5417525897/10000000000 : ℝ)|^4663 ≤ (22796263518467/50000000000000 : ℝ)^3639
        have hw : |(5417525897/10000000000 : ℝ)|=(5417525897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1583_s0_4 (p : ℝ) (hpa : (4661/1024 : ℝ) ≤ p) (hpb : p ≤ (4663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-323201497/2000000000 : ℝ)*x 0 + (4909044559/10000000000 : ℝ)*x 1 + (5834833117/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (323201497/2000000000 : ℝ)^4663 ≤ (302379628573/3125000000000 : ℝ)^3639 := by
    have hnat : (323201497 : ℕ)^4663*3125000000000^3639 ≤ 302379628573^3639*2000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323201497 2000000000 302379628573 3125000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4909044559/10000000000 : ℝ)^4663 ≤ (80366445061/200000000000 : ℝ)^3639 := by
    have hnat : (4909044559 : ℕ)^4663*200000000000^3639 ≤ 80366445061^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4909044559 10000000000 80366445061 200000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5834833117/10000000000 : ℝ)^4663 ≤ (50140629345243/100000000000000 : ℝ)^3639 := by
    have hnat : (5834833117 : ℕ)^4663*100000000000000^3639 ≤ 50140629345243^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5834833117 10000000000 50140629345243 100000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4663/1024 : ℝ)) 4663 3639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-323201497/2000000000 : ℝ), (4909044559/10000000000 : ℝ), (5834833117/10000000000 : ℝ)] ![(302379628573/3125000000000 : ℝ), (80366445061/200000000000 : ℝ), (50140629345243/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-323201497/2000000000 : ℝ)|^4663 ≤ (302379628573/3125000000000 : ℝ)^3639
        have hw : |(-323201497/2000000000 : ℝ)|=(323201497/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4909044559/10000000000 : ℝ)|^4663 ≤ (80366445061/200000000000 : ℝ)^3639
        have hw : |(4909044559/10000000000 : ℝ)|=(4909044559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5834833117/10000000000 : ℝ)|^4663 ≤ (50140629345243/100000000000000 : ℝ)^3639
        have hw : |(5834833117/10000000000 : ℝ)|=(5834833117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1583_s0_5 (p : ℝ) (hpa : (4661/1024 : ℝ) ≤ p) (hpb : p ≤ (4663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5195970601/10000000000 : ℝ)*x 0 + (-1204850053/10000000000 : ℝ)*x 1 + (2917416601/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5195970601/10000000000 : ℝ)^4663 ≤ (43217180613349/100000000000000 : ℝ)^3639 := by
    have hnat : (5195970601 : ℕ)^4663*100000000000000^3639 ≤ 43217180613349^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195970601 10000000000 43217180613349 100000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1204850053/10000000000 : ℝ)^4663 ≤ (1660547272657/25000000000000 : ℝ)^3639 := by
    have hnat : (1204850053 : ℕ)^4663*25000000000000^3639 ≤ 1660547272657^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1204850053 10000000000 1660547272657 25000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2917416601/5000000000 : ℝ)^4663 ≤ (50140630281217/100000000000000 : ℝ)^3639 := by
    have hnat : (2917416601 : ℕ)^4663*100000000000000^3639 ≤ 50140630281217^3639*5000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2917416601 5000000000 50140630281217 100000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4663/1024 : ℝ)) 4663 3639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5195970601/10000000000 : ℝ), (-1204850053/10000000000 : ℝ), (2917416601/5000000000 : ℝ)] ![(43217180613349/100000000000000 : ℝ), (1660547272657/25000000000000 : ℝ), (50140630281217/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5195970601/10000000000 : ℝ)|^4663 ≤ (43217180613349/100000000000000 : ℝ)^3639
        have hw : |(5195970601/10000000000 : ℝ)|=(5195970601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1204850053/10000000000 : ℝ)|^4663 ≤ (1660547272657/25000000000000 : ℝ)^3639
        have hw : |(-1204850053/10000000000 : ℝ)|=(1204850053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2917416601/5000000000 : ℝ)|^4663 ≤ (50140630281217/100000000000000 : ℝ)^3639
        have hw : |(2917416601/5000000000 : ℝ)|=(2917416601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1583_s0_6 (p : ℝ) (hpa : (4661/1024 : ℝ) ≤ p) (hpb : p ≤ (4663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2597985281/5000000000 : ℝ)*x 0 + (2917416547/5000000000 : ℝ)*x 1 + (-1204850281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2597985281/5000000000 : ℝ)^4663 ≤ (4321718019769/10000000000000 : ℝ)^3639 := by
    have hnat : (2597985281 : ℕ)^4663*10000000000000^3639 ≤ 4321718019769^3639*5000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2597985281 5000000000 4321718019769 10000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2917416547/5000000000 : ℝ)^4663 ≤ (50140629091979/100000000000000 : ℝ)^3639 := by
    have hnat : (2917416547 : ℕ)^4663*100000000000000^3639 ≤ 50140629091979^3639*5000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2917416547 5000000000 50140629091979 100000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1204850281/10000000000 : ℝ)^4663 ≤ (6642190701261/100000000000000 : ℝ)^3639 := by
    have hnat : (1204850281 : ℕ)^4663*100000000000000^3639 ≤ 6642190701261^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1204850281 10000000000 6642190701261 100000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4663/1024 : ℝ)) 4663 3639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2597985281/5000000000 : ℝ), (2917416547/5000000000 : ℝ), (-1204850281/10000000000 : ℝ)] ![(4321718019769/10000000000000 : ℝ), (50140629091979/100000000000000 : ℝ), (6642190701261/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2597985281/5000000000 : ℝ)|^4663 ≤ (4321718019769/10000000000000 : ℝ)^3639
        have hw : |(2597985281/5000000000 : ℝ)|=(2597985281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2917416547/5000000000 : ℝ)|^4663 ≤ (50140629091979/100000000000000 : ℝ)^3639
        have hw : |(2917416547/5000000000 : ℝ)|=(2917416547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1204850281/10000000000 : ℝ)|^4663 ≤ (6642190701261/100000000000000 : ℝ)^3639
        have hw : |(-1204850281/10000000000 : ℝ)|=(1204850281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1583_s0_7 (p : ℝ) (hpa : (4661/1024 : ℝ) ≤ p) (hpb : p ≤ (4663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4133555329/10000000000 : ℝ)*x 0 + (5359140559/10000000000 : ℝ)*x 1 + (3154391829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4133555329/10000000000 : ℝ)^4663 ≤ (2014831892241/6250000000000 : ℝ)^3639 := by
    have hnat : (4133555329 : ℕ)^4663*6250000000000^3639 ≤ 2014831892241^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4133555329 10000000000 2014831892241 6250000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5359140559/10000000000 : ℝ)^4663 ≤ (44963862319019/100000000000000 : ℝ)^3639 := by
    have hnat : (5359140559 : ℕ)^4663*100000000000000^3639 ≤ 44963862319019^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5359140559 10000000000 44963862319019 100000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3154391829/10000000000 : ℝ)^4663 ≤ (22798827378359/100000000000000 : ℝ)^3639 := by
    have hnat : (3154391829 : ℕ)^4663*100000000000000^3639 ≤ 22798827378359^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3154391829 10000000000 22798827378359 100000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4663/1024 : ℝ)) 4663 3639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4133555329/10000000000 : ℝ), (5359140559/10000000000 : ℝ), (3154391829/10000000000 : ℝ)] ![(2014831892241/6250000000000 : ℝ), (44963862319019/100000000000000 : ℝ), (22798827378359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4133555329/10000000000 : ℝ)|^4663 ≤ (2014831892241/6250000000000 : ℝ)^3639
        have hw : |(4133555329/10000000000 : ℝ)|=(4133555329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5359140559/10000000000 : ℝ)|^4663 ≤ (44963862319019/100000000000000 : ℝ)^3639
        have hw : |(5359140559/10000000000 : ℝ)|=(5359140559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3154391829/10000000000 : ℝ)|^4663 ≤ (22798827378359/100000000000000 : ℝ)^3639
        have hw : |(3154391829/10000000000 : ℝ)|=(3154391829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1583_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4661/1024 : ℝ) ≤ p) (hpb : p ≤ (4663/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21134259/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (3697/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (24597/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4661/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4661 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4661*1^1024 ≤ 0^1024*1^4661 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4661 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4661 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4661/1024 : ℝ) ≤ (193011626101961481/12500000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4661 ≤ (193011626101961481/12500000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4661*12500000000000000000^1024 ≤ 193011626101961481^1024*5^4661 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 193011626101961481 12500000000000000000 4661 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (193011626101961481/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4661 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4661/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4661 := by
      have hnat : (1 : ℕ)^1024*1^4661 ≤ 1^4661*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4661 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4661 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12693011626101961481/12500000000000000000 : ℝ) ≤ (1003372049441739/1000000000000000 : ℝ) ^ (4661/1024 : ℝ) := by
    have hpowers : (12693011626101961481/12500000000000000000 : ℝ)^1024 ≤ (1003372049441739/1000000000000000 : ℝ)^4661 := by
      have hnat : (12693011626101961481 : ℕ)^1024*1000000000000000^4661 ≤ 1003372049441739^4661*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12693011626101961481 12500000000000000000 1003372049441739 1000000000000000 1024 4661 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1003372049441739/1000000000000000 : ℝ)) (X := (12693011626101961481/12500000000000000000 : ℝ)) (by norm_num) 4661 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6443011626101961481/6250000000000000000 : ℝ) ≤ (503372049441739/500000000000000 : ℝ) ^ (4661/1024 : ℝ) := by
    have hpowers : (6443011626101961481/6250000000000000000 : ℝ)^1024 ≤ (503372049441739/500000000000000 : ℝ)^4661 := by
      have hnat : (6443011626101961481 : ℕ)^1024*500000000000000^4661 ≤ 503372049441739^4661*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6443011626101961481 6250000000000000000 503372049441739 500000000000000 1024 4661 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (503372049441739/500000000000000 : ℝ)) (X := (6443011626101961481/6250000000000000000 : ℝ)) (by norm_num) 4661 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(3372049441739/400000000000000 : ℝ)*(0 : ℝ))^(4661/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(3372049441739/400000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(193011626101961481/12500000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(3372049441739/400000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4661/1024 : ℝ) := by
    rw [show (1 : ℝ)+(3372049441739/400000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(1003372049441739/1000000000000000 : ℝ) by norm_num, show 1+(193011626101961481/12500000000000000000 : ℝ)+(0 : ℝ)=(12693011626101961481/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(193011626101961481/12500000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(3372049441739/400000000000000 : ℝ)*(2/5 : ℝ))^(4661/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(3372049441739/400000000000000 : ℝ)*(2/5 : ℝ)=(503372049441739/500000000000000 : ℝ) by norm_num, show 1+2*(193011626101961481/12500000000000000000 : ℝ)=(6443011626101961481/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(3372049441739/400000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4661/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (3372049441739/400000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(3372049441739/400000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4661/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (3372049441739/400000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(3372049441739/400000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4661/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (3372049441739/400000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1613049989/10000000000 : ℝ)*X 0 0+(2930107183/5000000000 : ℝ)*X 0 1+(4884528193/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1583_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5462712229/10000000000 : ℝ)*X 1 0+(-2155155459/10000000000 : ℝ)*X 1 1+(4884528131/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1583_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5462712301/10000000000 : ℝ)*X 2 0+(4884528027/10000000000 : ℝ)*X 2 1+(-2155155497/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1583_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2063255831/5000000000 : ℝ)*X 0 0+(618789433/2000000000 : ℝ)*X 0 1+(5417525897/10000000000 : ℝ)*X 0 2+(2063255831/5000000000 : ℝ)*X 1 0+(618789433/2000000000 : ℝ)*X 1 1+(5417525897/10000000000 : ℝ)*X 1 2+(2063255831/5000000000 : ℝ)*X 2 0+(618789433/2000000000 : ℝ)*X 2 1+(5417525897/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1583_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-323201497/2000000000 : ℝ)*X 0 0+(4909044559/10000000000 : ℝ)*X 0 1+(5834833117/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1583_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5195970601/10000000000 : ℝ)*X 1 0+(-1204850053/10000000000 : ℝ)*X 1 1+(2917416601/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1583_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2597985281/5000000000 : ℝ)*X 2 0+(2917416547/5000000000 : ℝ)*X 2 1+(-1204850281/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1583_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4133555329/10000000000 : ℝ)*X 0 0+(5359140559/10000000000 : ℝ)*X 0 1+(3154391829/10000000000 : ℝ)*X 0 2+(4133555329/10000000000 : ℝ)*X 1 0+(5359140559/10000000000 : ℝ)*X 1 1+(3154391829/10000000000 : ℝ)*X 1 2+(4133555329/10000000000 : ℝ)*X 2 0+(5359140559/10000000000 : ℝ)*X 2 1+(3154391829/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1583_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6320141739608484141/1000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7280417/12500000000000 : ℝ)*(base1) + (1227109649/100000000000000 : ℝ)*(base19) + (38769327/3125000000000 : ℝ)*(base23) + (160972117/100000000000000 : ℝ)*(upper3) + (153085097/100000000000000 : ℝ)*(upper5) + (181912903459421/25000000000000 : ℝ)*(major0) + (181912903459421/25000000000000 : ℝ)*(major1) + (181912903459421/25000000000000 : ℝ)*(major2) + (25623101902683/2500000000000 : ℝ)*(sp0) + (512463668061871/50000000000000 : ℝ)*(sp1) + (1024927322614927/100000000000000 : ℝ)*(sp2) + (430372438672073/100000000000000 : ℝ)*(sp3) + (4545369407/100000000000000 : ℝ)*(sp4) + (78274207/4000000000000 : ℝ)*(sp7) + (53796806721323/12500000000000 : ℝ)*(f.failure) + (1024928563233391/100000000000000 : ℝ)*(f.sum) + (10014419956881/5000000000000000000000000000 : ℝ)*base66 + (9637575143119/10000000000000000000000000000 : ℝ)*base67 + (25980250823119/10000000000000000000000000000 : ℝ)*base69 + (15071551983119/10000000000000000000000000000 : ℝ)*base71 + (1733901286881/5000000000000000000000000000 : ℝ)*base74 + (5020367406881/10000000000000000000000000000 : ℝ)*base76 + (31786790893119/10000000000000000000000000000 : ℝ)*base77 + (7961358816881/10000000000000000000000000000 : ℝ)*base80 + (1253710988119/5000000000000000000000000000 : ℝ)*base81 + (145343/156250000000000000000 : ℝ)*base90 + (145343/156250000000000000000 : ℝ)*base92 + (145343/156250000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (100018514876216462070459/10000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2139902931/100000000000000 : ℝ)*(base19) + (1072361733/50000000000000 : ℝ)*(base23) + (17769023/10000000000000 : ℝ)*(base32) + (336823899/100000000000000 : ℝ)*(upper3) + (200878797/100000000000000 : ℝ)*(upper5) + (766862836738827/100000000000000 : ℝ)*(major0) + (766862836738827/100000000000000 : ℝ)*(major1) + (766862836738827/100000000000000 : ℝ)*(major2) + (1186277407/20000000000000 : ℝ)*(sp1) + (3091607117/50000000000000 : ℝ)*(sp2) + (1080159144114467/100000000000000 : ℝ)*(sp4) + (1080151072824501/100000000000000 : ℝ)*(sp5) + (1080150816176767/100000000000000 : ℝ)*(sp6) + (226783009138953/50000000000000 : ℝ)*(sp7) + (56695774496017/12500000000000 : ℝ)*(f.failure) + (1080159144114467/100000000000000 : ℝ)*(f.sum) + (124815879847/20000000000000000000000000000 : ℝ)*base66 + (88375715420153/40000000000000000000000000000 : ℝ)*base67 + (93636652819847/40000000000000000000000000000 : ℝ)*base70 + (27312408100153/40000000000000000000000000000 : ℝ)*base71 + (16153358980153/20000000000000000000000000000 : ℝ)*base73 + (52423058739847/40000000000000000000000000000 : ℝ)*base76 + (62902766779847/40000000000000000000000000000 : ℝ)*base78 + (10197419099847/40000000000000000000000000000 : ℝ)*base80 + (27280589279847/20000000000000000000000000000 : ℝ)*base82 + (558903/156250000000000000000 : ℝ)*base89 + (558903/156250000000000000000 : ℝ)*base91 + (558903/156250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1583_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4661/1024 : ℝ) ≤ p) (hpb : p ≤ (4663/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21134259/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3697/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (24597/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1583_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1583_s1_0 (p : ℝ) (hpa : (4661/1024 : ℝ) ≤ p) (hpb : p ≤ (4663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1748396043/10000000000 : ℝ)*x 0 + (1105517793/2000000000 : ℝ)*x 1 + (1282463709/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1748396043/10000000000 : ℝ)^4663 ≤ (21406797119/200000000000 : ℝ)^3639 := by
    have hnat : (1748396043 : ℕ)^4663*200000000000^3639 ≤ 21406797119^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1748396043 10000000000 21406797119 200000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1105517793/2000000000 : ℝ)^4663 ≤ (2339140648763/5000000000000 : ℝ)^3639 := by
    have hnat : (1105517793 : ℕ)^4663*5000000000000^3639 ≤ 2339140648763^3639*2000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1105517793 2000000000 2339140648763 5000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1282463709/2500000000 : ℝ)^4663 ≤ (21256894220477/50000000000000 : ℝ)^3639 := by
    have hnat : (1282463709 : ℕ)^4663*50000000000000^3639 ≤ 21256894220477^3639*2500000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1282463709 2500000000 21256894220477 50000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4663/1024 : ℝ)) 4663 3639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1748396043/10000000000 : ℝ), (1105517793/2000000000 : ℝ), (1282463709/2500000000 : ℝ)] ![(21406797119/200000000000 : ℝ), (2339140648763/5000000000000 : ℝ), (21256894220477/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1748396043/10000000000 : ℝ)|^4663 ≤ (21406797119/200000000000 : ℝ)^3639
        have hw : |(-1748396043/10000000000 : ℝ)|=(1748396043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1105517793/2000000000 : ℝ)|^4663 ≤ (2339140648763/5000000000000 : ℝ)^3639
        have hw : |(1105517793/2000000000 : ℝ)|=(1105517793/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1282463709/2500000000 : ℝ)|^4663 ≤ (21256894220477/50000000000000 : ℝ)^3639
        have hw : |(1282463709/2500000000 : ℝ)|=(1282463709/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1583_s1_1 (p : ℝ) (hpa : (4661/1024 : ℝ) ≤ p) (hpb : p ≤ (4663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (16794571/31250000 : ℝ)*x 0 + (-1956159459/10000000000 : ℝ)*x 1 + (5129854461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16794571/31250000 : ℝ)^4663 ≤ (4512650628269/10000000000000 : ℝ)^3639 := by
    have hnat : (16794571 : ℕ)^4663*10000000000000^3639 ≤ 4512650628269^3639*31250000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16794571 31250000 4512650628269 10000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1956159459/10000000000 : ℝ)^4663 ≤ (772481827243/6250000000000 : ℝ)^3639 := by
    have hnat : (1956159459 : ℕ)^4663*6250000000000^3639 ≤ 772481827243^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1956159459 10000000000 772481827243 6250000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5129854461/10000000000 : ℝ)^4663 ≤ (8502756891721/20000000000000 : ℝ)^3639 := by
    have hnat : (5129854461 : ℕ)^4663*20000000000000^3639 ≤ 8502756891721^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5129854461 10000000000 8502756891721 20000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4663/1024 : ℝ)) 4663 3639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(16794571/31250000 : ℝ), (-1956159459/10000000000 : ℝ), (5129854461/10000000000 : ℝ)] ![(4512650628269/10000000000000 : ℝ), (772481827243/6250000000000 : ℝ), (8502756891721/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(16794571/31250000 : ℝ)|^4663 ≤ (4512650628269/10000000000000 : ℝ)^3639
        have hw : |(16794571/31250000 : ℝ)|=(16794571/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1956159459/10000000000 : ℝ)|^4663 ≤ (772481827243/6250000000000 : ℝ)^3639
        have hw : |(-1956159459/10000000000 : ℝ)|=(1956159459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5129854461/10000000000 : ℝ)|^4663 ≤ (8502756891721/20000000000000 : ℝ)^3639
        have hw : |(5129854461/10000000000 : ℝ)|=(5129854461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1583_s1_2 (p : ℝ) (hpa : (4661/1024 : ℝ) ≤ p) (hpb : p ≤ (4663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2687131181/5000000000 : ℝ)*x 0 + (2564927393/5000000000 : ℝ)*x 1 + (-195615951/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2687131181/5000000000 : ℝ)^4663 ≤ (45126502430753/100000000000000 : ℝ)^3639 := by
    have hnat : (2687131181 : ℕ)^4663*100000000000000^3639 ≤ 45126502430753^3639*5000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687131181 5000000000 45126502430753 100000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2564927393/5000000000 : ℝ)^4663 ≤ (1700551516399/4000000000000 : ℝ)^3639 := by
    have hnat : (2564927393 : ℕ)^4663*4000000000000^3639 ≤ 1700551516399^3639*5000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2564927393 5000000000 1700551516399 4000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (195615951/1000000000 : ℝ)^4663 ≤ (15449637061/125000000000 : ℝ)^3639 := by
    have hnat : (195615951 : ℕ)^4663*125000000000^3639 ≤ 15449637061^3639*1000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      195615951 1000000000 15449637061 125000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4663/1024 : ℝ)) 4663 3639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2687131181/5000000000 : ℝ), (2564927393/5000000000 : ℝ), (-195615951/1000000000 : ℝ)] ![(45126502430753/100000000000000 : ℝ), (1700551516399/4000000000000 : ℝ), (15449637061/125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2687131181/5000000000 : ℝ)|^4663 ≤ (45126502430753/100000000000000 : ℝ)^3639
        have hw : |(2687131181/5000000000 : ℝ)|=(2687131181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2564927393/5000000000 : ℝ)|^4663 ≤ (1700551516399/4000000000000 : ℝ)^3639
        have hw : |(2564927393/5000000000 : ℝ)|=(2564927393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-195615951/1000000000 : ℝ)|^4663 ≤ (15449637061/125000000000 : ℝ)^3639
        have hw : |(-195615951/1000000000 : ℝ)|=(195615951/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1583_s1_3 (p : ℝ) (hpa : (4661/1024 : ℝ) ≤ p) (hpb : p ≤ (4663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4223731683/10000000000 : ℝ)*x 0 + (754264353/2000000000 : ℝ)*x 1 + (1179629743/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4223731683/10000000000 : ℝ)^4663 ≤ (16570620541159/50000000000000 : ℝ)^3639 := by
    have hnat : (4223731683 : ℕ)^4663*50000000000000^3639 ≤ 16570620541159^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4223731683 10000000000 16570620541159 50000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (754264353/2000000000 : ℝ)^4663 ≤ (28662929942559/100000000000000 : ℝ)^3639 := by
    have hnat : (754264353 : ℕ)^4663*100000000000000^3639 ≤ 28662929942559^3639*2000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      754264353 2000000000 28662929942559 100000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1179629743/2500000000 : ℝ)^4663 ≤ (19097914477247/50000000000000 : ℝ)^3639 := by
    have hnat : (1179629743 : ℕ)^4663*50000000000000^3639 ≤ 19097914477247^3639*2500000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1179629743 2500000000 19097914477247 50000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4663/1024 : ℝ)) 4663 3639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4223731683/10000000000 : ℝ), (754264353/2000000000 : ℝ), (1179629743/2500000000 : ℝ)] ![(16570620541159/50000000000000 : ℝ), (28662929942559/100000000000000 : ℝ), (19097914477247/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4223731683/10000000000 : ℝ)|^4663 ≤ (16570620541159/50000000000000 : ℝ)^3639
        have hw : |(4223731683/10000000000 : ℝ)|=(4223731683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(754264353/2000000000 : ℝ)|^4663 ≤ (28662929942559/100000000000000 : ℝ)^3639
        have hw : |(754264353/2000000000 : ℝ)|=(754264353/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1179629743/2500000000 : ℝ)|^4663 ≤ (19097914477247/50000000000000 : ℝ)^3639
        have hw : |(1179629743/2500000000 : ℝ)|=(1179629743/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1583_s1_4 (p : ℝ) (hpa : (4661/1024 : ℝ) ≤ p) (hpb : p ≤ (4663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-874295717/5000000000 : ℝ)*x 0 + (2566943201/5000000000 : ℝ)*x 1 + (5523499037/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (874295717/5000000000 : ℝ)^4663 ≤ (10704931328211/100000000000000 : ℝ)^3639 := by
    have hnat : (874295717 : ℕ)^4663*100000000000000^3639 ≤ 10704931328211^3639*5000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      874295717 5000000000 10704931328211 100000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2566943201/5000000000 : ℝ)^4663 ≤ (21278303392903/50000000000000 : ℝ)^3639 := by
    have hnat : (2566943201 : ℕ)^4663*50000000000000^3639 ≤ 21278303392903^3639*5000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2566943201 5000000000 21278303392903 50000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5523499037/10000000000 : ℝ)^4663 ≤ (11684615468939/25000000000000 : ℝ)^3639 := by
    have hnat : (5523499037 : ℕ)^4663*25000000000000^3639 ≤ 11684615468939^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5523499037 10000000000 11684615468939 25000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4663/1024 : ℝ)) 4663 3639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-874295717/5000000000 : ℝ), (2566943201/5000000000 : ℝ), (5523499037/10000000000 : ℝ)] ![(10704931328211/100000000000000 : ℝ), (21278303392903/50000000000000 : ℝ), (11684615468939/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-874295717/5000000000 : ℝ)|^4663 ≤ (10704931328211/100000000000000 : ℝ)^3639
        have hw : |(-874295717/5000000000 : ℝ)|=(874295717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2566943201/5000000000 : ℝ)|^4663 ≤ (21278303392903/50000000000000 : ℝ)^3639
        have hw : |(2566943201/5000000000 : ℝ)|=(2566943201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5523499037/10000000000 : ℝ)|^4663 ≤ (11684615468939/25000000000000 : ℝ)^3639
        have hw : |(5523499037/10000000000 : ℝ)|=(5523499037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1583_s1_5 (p : ℝ) (hpa : (4661/1024 : ℝ) ≤ p) (hpb : p ≤ (4663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1053740653/2000000000 : ℝ)*x 0 + (-195314367/1250000000 : ℝ)*x 1 + (1380874937/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1053740653/2000000000 : ℝ)^4663 ≤ (4399388229769/10000000000000 : ℝ)^3639 := by
    have hnat : (1053740653 : ℕ)^4663*10000000000000^3639 ≤ 4399388229769^3639*2000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053740653 2000000000 4399388229769 10000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (195314367/1250000000 : ℝ)^4663 ≤ (231691202763/2500000000000 : ℝ)^3639 := by
    have hnat : (195314367 : ℕ)^4663*2500000000000^3639 ≤ 231691202763^3639*1250000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      195314367 1250000000 231691202763 2500000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1380874937/2500000000 : ℝ)^4663 ≤ (365144293633/781250000000 : ℝ)^3639 := by
    have hnat : (1380874937 : ℕ)^4663*781250000000^3639 ≤ 365144293633^3639*2500000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1380874937 2500000000 365144293633 781250000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4663/1024 : ℝ)) 4663 3639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1053740653/2000000000 : ℝ), (-195314367/1250000000 : ℝ), (1380874937/2500000000 : ℝ)] ![(4399388229769/10000000000000 : ℝ), (231691202763/2500000000000 : ℝ), (365144293633/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1053740653/2000000000 : ℝ)|^4663 ≤ (4399388229769/10000000000000 : ℝ)^3639
        have hw : |(1053740653/2000000000 : ℝ)|=(1053740653/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-195314367/1250000000 : ℝ)|^4663 ≤ (231691202763/2500000000000 : ℝ)^3639
        have hw : |(-195314367/1250000000 : ℝ)|=(195314367/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1380874937/2500000000 : ℝ)|^4663 ≤ (365144293633/781250000000 : ℝ)^3639
        have hw : |(1380874937/2500000000 : ℝ)|=(1380874937/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1583_s1_6 (p : ℝ) (hpa : (4661/1024 : ℝ) ≤ p) (hpb : p ≤ (4663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5268702389/10000000000 : ℝ)*x 0 + (5523500093/10000000000 : ℝ)*x 1 + (-390628919/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5268702389/10000000000 : ℝ)^4663 ≤ (21996936462373/50000000000000 : ℝ)^3639 := by
    have hnat : (5268702389 : ℕ)^4663*50000000000000^3639 ≤ 21996936462373^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5268702389 10000000000 21996936462373 50000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5523500093/10000000000 : ℝ)^4663 ≤ (46738473325807/100000000000000 : ℝ)^3639 := by
    have hnat : (5523500093 : ℕ)^4663*100000000000000^3639 ≤ 46738473325807^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5523500093 10000000000 46738473325807 100000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (390628919/2500000000 : ℝ)^4663 ≤ (2316913433679/25000000000000 : ℝ)^3639 := by
    have hnat : (390628919 : ℕ)^4663*25000000000000^3639 ≤ 2316913433679^3639*2500000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      390628919 2500000000 2316913433679 25000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4663/1024 : ℝ)) 4663 3639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5268702389/10000000000 : ℝ), (5523500093/10000000000 : ℝ), (-390628919/2500000000 : ℝ)] ![(21996936462373/50000000000000 : ℝ), (46738473325807/100000000000000 : ℝ), (2316913433679/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5268702389/10000000000 : ℝ)|^4663 ≤ (21996936462373/50000000000000 : ℝ)^3639
        have hw : |(5268702389/10000000000 : ℝ)|=(5268702389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5523500093/10000000000 : ℝ)|^4663 ≤ (46738473325807/100000000000000 : ℝ)^3639
        have hw : |(5523500093/10000000000 : ℝ)|=(5523500093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-390628919/2500000000 : ℝ)|^4663 ≤ (2316913433679/25000000000000 : ℝ)^3639
        have hw : |(-390628919/2500000000 : ℝ)|=(390628919/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1583_s1_7 (p : ℝ) (hpa : (4661/1024 : ℝ) ≤ p) (hpb : p ≤ (4663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4224196153/10000000000 : ℝ)*x 0 + (941783761/2000000000 : ℝ)*x 1 + (3781060747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4224196153/10000000000 : ℝ)^4663 ≤ (33145911117947/100000000000000 : ℝ)^3639 := by
    have hnat : (4224196153 : ℕ)^4663*100000000000000^3639 ≤ 33145911117947^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4224196153 10000000000 33145911117947 100000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (941783761/2000000000 : ℝ)^4663 ≤ (38096277414571/100000000000000 : ℝ)^3639 := by
    have hnat : (941783761 : ℕ)^4663*100000000000000^3639 ≤ 38096277414571^3639*2000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      941783761 2000000000 38096277414571 100000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3781060747/10000000000 : ℝ)^4663 ≤ (28757811452231/100000000000000 : ℝ)^3639 := by
    have hnat : (3781060747 : ℕ)^4663*100000000000000^3639 ≤ 28757811452231^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3781060747 10000000000 28757811452231 100000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4663/1024 : ℝ)) 4663 3639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4224196153/10000000000 : ℝ), (941783761/2000000000 : ℝ), (3781060747/10000000000 : ℝ)] ![(33145911117947/100000000000000 : ℝ), (38096277414571/100000000000000 : ℝ), (28757811452231/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4224196153/10000000000 : ℝ)|^4663 ≤ (33145911117947/100000000000000 : ℝ)^3639
        have hw : |(4224196153/10000000000 : ℝ)|=(4224196153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(941783761/2000000000 : ℝ)|^4663 ≤ (38096277414571/100000000000000 : ℝ)^3639
        have hw : |(941783761/2000000000 : ℝ)|=(941783761/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3781060747/10000000000 : ℝ)|^4663 ≤ (28757811452231/100000000000000 : ℝ)^3639
        have hw : |(3781060747/10000000000 : ℝ)|=(3781060747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1583_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4661/1024 : ℝ) ≤ p) (hpb : p ≤ (4663/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21134259/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (24597/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3697/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2303/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17639/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (24597/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3697/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (24597/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3697/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (24597/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3697/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (24597/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3697/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (24597/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3697/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (24597/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3697/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3697/100000 : ℝ) ^ (4661/1024 : ℝ) ≤ (30282905964653/100000000000000000000 : ℝ) := by
    have hpowers : (3697/100000 : ℝ)^4661 ≤ (30282905964653/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3697 : ℕ)^4661*100000000000000000000^1024 ≤ 30282905964653^1024*100000^4661 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3697 100000 30282905964653 100000000000000000000 4661 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3697/100000 : ℝ)) (X := (30282905964653/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4661 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (24597/100000 : ℝ) ^ (4661/1024 : ℝ) ≤ (168827436901961751/100000000000000000000 : ℝ) := by
    have hpowers : (24597/100000 : ℝ)^4661 ≤ (168827436901961751/100000000000000000000 : ℝ)^1024 := by
      have hnat : (24597 : ℕ)^4661*100000000000000000000^1024 ≤ 168827436901961751^1024*100000^4661 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24597 100000 168827436901961751 100000000000000000000 4661 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (24597/100000 : ℝ)) (X := (168827436901961751/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4661 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000030282905964653/50000000000000000000 : ℝ) ≤ (10000001330602377/10000000000000000 : ℝ) ^ (4661/1024 : ℝ) := by
    have hpowers : (50000030282905964653/50000000000000000000 : ℝ)^1024 ≤ (10000001330602377/10000000000000000 : ℝ)^4661 := by
      have hnat : (50000030282905964653 : ℕ)^1024*10000000000000000^4661 ≤ 10000001330602377^4661*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000030282905964653 50000000000000000000 10000001330602377 10000000000000000 1024 4661 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000001330602377/10000000000000000 : ℝ)) (X := (50000030282905964653/50000000000000000000 : ℝ)) (by norm_num) 4661 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25042214429951981601/25000000000000000000 : ℝ) ≤ (5001853641980123/5000000000000000 : ℝ) ^ (4661/1024 : ℝ) := by
    have hpowers : (25042214429951981601/25000000000000000000 : ℝ)^1024 ≤ (5001853641980123/5000000000000000 : ℝ)^4661 := by
      have hnat : (25042214429951981601 : ℕ)^1024*5000000000000000^4661 ≤ 5001853641980123^4661*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25042214429951981601 25000000000000000000 5001853641980123 5000000000000000 1024 4661 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001853641980123/5000000000000000 : ℝ)) (X := (25042214429951981601/25000000000000000000 : ℝ)) (by norm_num) 4661 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50168827436901961751/50000000000000000000 : ℝ) ≤ (2001482647463623/2000000000000000 : ℝ) ^ (4661/1024 : ℝ) := by
    have hpowers : (50168827436901961751/50000000000000000000 : ℝ)^1024 ≤ (2001482647463623/2000000000000000 : ℝ)^4661 := by
      have hnat : (50168827436901961751 : ℕ)^1024*2000000000000000^4661 ≤ 2001482647463623^4661*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50168827436901961751 50000000000000000000 2001482647463623 2000000000000000 1024 4661 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2001482647463623/2000000000000000 : ℝ)) (X := (50168827436901961751/50000000000000000000 : ℝ)) (by norm_num) 4661 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(30282905964653/100000000000000000000 : ℝ) ≤ ((104486312995230797957/104500000000000000000 : ℝ)+2*(3705953357869/2090000000000000 : ℝ)*(3697/100000 : ℝ))^(4661/1024 : ℝ) := by
    rw [show (104486312995230797957/104500000000000000000 : ℝ)+2*(3705953357869/2090000000000000 : ℝ)*(3697/100000 : ℝ)=(10000001330602377/10000000000000000 : ℝ) by norm_num, show 1+2*(30282905964653/100000000000000000000 : ℝ)=(50000030282905964653/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(168827436901961751/100000000000000000000 : ℝ)+(30282905964653/100000000000000000000 : ℝ) ≤ ((104486312995230797957/104500000000000000000 : ℝ)+(3705953357869/2090000000000000 : ℝ)*((24597/100000 : ℝ)+(3697/100000 : ℝ)))^(4661/1024 : ℝ) := by
    rw [show (104486312995230797957/104500000000000000000 : ℝ)+(3705953357869/2090000000000000 : ℝ)*((24597/100000 : ℝ)+(3697/100000 : ℝ))=(5001853641980123/5000000000000000 : ℝ) by norm_num, show 1+(168827436901961751/100000000000000000000 : ℝ)+(30282905964653/100000000000000000000 : ℝ)=(25042214429951981601/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(168827436901961751/100000000000000000000 : ℝ) ≤ ((104486312995230797957/104500000000000000000 : ℝ)+2*(3705953357869/2090000000000000 : ℝ)*(24597/100000 : ℝ))^(4661/1024 : ℝ) := by
    rw [show (104486312995230797957/104500000000000000000 : ℝ)+2*(3705953357869/2090000000000000 : ℝ)*(24597/100000 : ℝ)=(2001482647463623/2000000000000000 : ℝ) by norm_num, show 1+2*(168827436901961751/100000000000000000000 : ℝ)=(50168827436901961751/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (104486312995230797957/104500000000000000000 : ℝ)*(X 1 0+X 2 0)+(3705953357869/2090000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4661/1024 : ℝ)) (lo := (3697/100000 : ℝ)) (hi := (24597/100000 : ℝ)) (c := (104486312995230797957/104500000000000000000 : ℝ)) (alpha := (3705953357869/2090000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (104486312995230797957/104500000000000000000 : ℝ)*(X 0 1+X 2 1)+(3705953357869/2090000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4661/1024 : ℝ)) (lo := (3697/100000 : ℝ)) (hi := (24597/100000 : ℝ)) (c := (104486312995230797957/104500000000000000000 : ℝ)) (alpha := (3705953357869/2090000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (104486312995230797957/104500000000000000000 : ℝ)*(X 0 2+X 1 2)+(3705953357869/2090000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4661/1024 : ℝ)) (lo := (3697/100000 : ℝ)) (hi := (24597/100000 : ℝ)) (c := (104486312995230797957/104500000000000000000 : ℝ)) (alpha := (3705953357869/2090000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1748396043/10000000000 : ℝ)*X 0 0+(1105517793/2000000000 : ℝ)*X 0 1+(1282463709/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1583_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((16794571/31250000 : ℝ)*X 1 0+(-1956159459/10000000000 : ℝ)*X 1 1+(5129854461/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1583_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2687131181/5000000000 : ℝ)*X 2 0+(2564927393/5000000000 : ℝ)*X 2 1+(-195615951/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1583_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4223731683/10000000000 : ℝ)*X 0 0+(754264353/2000000000 : ℝ)*X 0 1+(1179629743/2500000000 : ℝ)*X 0 2+(4223731683/10000000000 : ℝ)*X 1 0+(754264353/2000000000 : ℝ)*X 1 1+(1179629743/2500000000 : ℝ)*X 1 2+(4223731683/10000000000 : ℝ)*X 2 0+(754264353/2000000000 : ℝ)*X 2 1+(1179629743/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1583_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-874295717/5000000000 : ℝ)*X 0 0+(2566943201/5000000000 : ℝ)*X 0 1+(5523499037/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1583_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1053740653/2000000000 : ℝ)*X 1 0+(-195314367/1250000000 : ℝ)*X 1 1+(1380874937/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1583_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5268702389/10000000000 : ℝ)*X 2 0+(5523500093/10000000000 : ℝ)*X 2 1+(-390628919/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1583_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4224196153/10000000000 : ℝ)*X 0 0+(941783761/2000000000 : ℝ)*X 0 1+(3781060747/10000000000 : ℝ)*X 0 2+(4224196153/10000000000 : ℝ)*X 1 0+(941783761/2000000000 : ℝ)*X 1 1+(3781060747/10000000000 : ℝ)*X 1 2+(4224196153/10000000000 : ℝ)*X 2 0+(941783761/2000000000 : ℝ)*X 2 1+(3781060747/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1583_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18775646864174917590721978557/2612500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2120125061/100000000000000 : ℝ)*(base19) + (231451039/12500000000000 : ℝ)*(base23) + (244324801/100000000000000 : ℝ)*(upper3) + (27148409/50000000000000 : ℝ)*(upper4) + (27577517/25000000000000 : ℝ)*(upper5) + (892510624765267/50000000000000 : ℝ)*(major0) + (892510624765267/50000000000000 : ℝ)*(major1) + (892510624765267/50000000000000 : ℝ)*(major2) + (628565444102049/25000000000000 : ℝ)*(sp0) + (1257138642211237/50000000000000 : ℝ)*(sp1) + (2514277552939223/100000000000000 : ℝ)*(sp2) + (263938538585763/25000000000000 : ℝ)*(sp3) + (881406967/5000000000000 : ℝ)*(sp4) + (8700608791/100000000000000 : ℝ)*(sp7) + (1055762854951843/100000000000000 : ℝ)*(f.failure) + (157142462784221/6250000000000 : ℝ)*(f.sum) + (104948484796273/52250000000000000000000000000 : ℝ)*base65 + (950707046360299499/275000000000000000000000000000000 : ℝ)*base68 + (2844029109410299499/275000000000000000000000000000000 : ℝ)*base70 + (1153919251039700501/275000000000000000000000000000000 : ℝ)*base71 + (118369188955773/52250000000000000000000000000 : ℝ)*base73 + (232933005860299499/275000000000000000000000000000000 : ℝ)*base76 + (1566945996610299499/275000000000000000000000000000000 : ℝ)*base78 + (1870446602689700501/275000000000000000000000000000000 : ℝ)*base79 + (189022196768727/52250000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (7489337/1250000000000000000000 : ℝ)*base89 + (7489337/1250000000000000000000 : ℝ)*base91 + (7489337/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1996193209683243936695565453/237500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1474173183/100000000000000 : ℝ)*(base19) + (80970751/6250000000000 : ℝ)*(base23) + (35217291/25000000000000 : ℝ)*(upper2) + (34402167/10000000000000 : ℝ)*(upper3) + (120963157/100000000000000 : ℝ)*(upper5) + (911099188989473/50000000000000 : ℝ)*(major0) + (911099188989473/50000000000000 : ℝ)*(major1) + (911099188989473/50000000000000 : ℝ)*(major2) + (12660648201/100000000000000 : ℝ)*(sp1) + (2339773303/20000000000000 : ℝ)*(sp2) + (1283322478760791/50000000000000 : ℝ)*(sp4) + (1283315411350099/50000000000000 : ℝ)*(sp5) + (51332639262461/2000000000000 : ℝ)*(sp6) + (1077751518268837/100000000000000 : ℝ)*(sp7) + (1077751518268837/100000000000000 : ℝ)*(f.failure) + (1283322478760791/50000000000000 : ℝ)*(f.sum) + (5262254022617/4750000000000000000000000000 : ℝ)*base65 + (66005736408563429/25000000000000000000000000000000 : ℝ)*base67 + (162208014191436571/25000000000000000000000000000000 : ℝ)*base70 + (104169001141436571/25000000000000000000000000000000 : ℝ)*base72 + (21448906328867/4750000000000000000000000000 : ℝ)*base73 + (44715719966436571/25000000000000000000000000000000 : ℝ)*base76 + (6030543391436571/25000000000000000000000000000000 : ℝ)*base78 + (202455574508563429/25000000000000000000000000000000 : ℝ)*base79 + (21216365978383/4750000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (7786783/1250000000000000000000 : ℝ)*base89 + (7786783/1250000000000000000000 : ℝ)*base91 + (7786783/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1583_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4661/1024 : ℝ) ≤ p) (hpb : p ≤ (4663/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21134259/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (24597/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3697/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2303/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17639/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1583_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1583_s2_0 (p : ℝ) (hpa : (4661/1024 : ℝ) ≤ p) (hpb : p ≤ (4663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-220732179/1250000000 : ℝ)*x 0 + (2719129431/5000000000 : ℝ)*x 1 + (5207791183/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (220732179/1250000000 : ℝ)^4663 ≤ (10840566432643/100000000000000 : ℝ)^3639 := by
    have hnat : (220732179 : ℕ)^4663*100000000000000^3639 ≤ 10840566432643^3639*1250000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220732179 1250000000 10840566432643 100000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2719129431/5000000000 : ℝ)^4663 ≤ (22908114813721/50000000000000 : ℝ)^3639 := by
    have hnat : (2719129431 : ℕ)^4663*50000000000000^3639 ≤ 22908114813721^3639*5000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719129431 5000000000 22908114813721 50000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5207791183/10000000000 : ℝ)^4663 ≤ (4334320392199/10000000000000 : ℝ)^3639 := by
    have hnat : (5207791183 : ℕ)^4663*10000000000000^3639 ≤ 4334320392199^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5207791183 10000000000 4334320392199 10000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4663/1024 : ℝ)) 4663 3639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-220732179/1250000000 : ℝ), (2719129431/5000000000 : ℝ), (5207791183/10000000000 : ℝ)] ![(10840566432643/100000000000000 : ℝ), (22908114813721/50000000000000 : ℝ), (4334320392199/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-220732179/1250000000 : ℝ)|^4663 ≤ (10840566432643/100000000000000 : ℝ)^3639
        have hw : |(-220732179/1250000000 : ℝ)|=(220732179/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2719129431/5000000000 : ℝ)|^4663 ≤ (22908114813721/50000000000000 : ℝ)^3639
        have hw : |(2719129431/5000000000 : ℝ)|=(2719129431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5207791183/10000000000 : ℝ)|^4663 ≤ (4334320392199/10000000000000 : ℝ)^3639
        have hw : |(5207791183/10000000000 : ℝ)|=(5207791183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1583_s2_1 (p : ℝ) (hpa : (4661/1024 : ℝ) ≤ p) (hpb : p ≤ (4663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675557597/5000000000 : ℝ)*x 0 + (-1884080621/10000000000 : ℝ)*x 1 + (5207791931/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675557597/5000000000 : ℝ)^4663 ≤ (44877599217641/100000000000000 : ℝ)^3639 := by
    have hnat : (2675557597 : ℕ)^4663*100000000000000^3639 ≤ 44877599217641^3639*5000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675557597 5000000000 44877599217641 100000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1884080621/10000000000 : ℝ)^4663 ≤ (73619930429/625000000000 : ℝ)^3639 := by
    have hnat : (1884080621 : ℕ)^4663*625000000000^3639 ≤ 73619930429^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1884080621 10000000000 73619930429 625000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5207791931/10000000000 : ℝ)^4663 ≤ (1733728475969/4000000000000 : ℝ)^3639 := by
    have hnat : (5207791931 : ℕ)^4663*4000000000000^3639 ≤ 1733728475969^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5207791931 10000000000 1733728475969 4000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4663/1024 : ℝ)) 4663 3639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675557597/5000000000 : ℝ), (-1884080621/10000000000 : ℝ), (5207791931/10000000000 : ℝ)] ![(44877599217641/100000000000000 : ℝ), (73619930429/625000000000 : ℝ), (1733728475969/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675557597/5000000000 : ℝ)|^4663 ≤ (44877599217641/100000000000000 : ℝ)^3639
        have hw : |(2675557597/5000000000 : ℝ)|=(2675557597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1884080621/10000000000 : ℝ)|^4663 ≤ (73619930429/625000000000 : ℝ)^3639
        have hw : |(-1884080621/10000000000 : ℝ)|=(1884080621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5207791931/10000000000 : ℝ)|^4663 ≤ (1733728475969/4000000000000 : ℝ)^3639
        have hw : |(5207791931/10000000000 : ℝ)|=(5207791931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1583_s2_2 (p : ℝ) (hpa : (4661/1024 : ℝ) ≤ p) (hpb : p ≤ (4663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334444729/625000000 : ℝ)*x 0 + (5207790751/10000000000 : ℝ)*x 1 + (-1884081561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334444729/625000000 : ℝ)^4663 ≤ (8975520853703/20000000000000 : ℝ)^3639 := by
    have hnat : (334444729 : ℕ)^4663*20000000000000^3639 ≤ 8975520853703^3639*625000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334444729 625000000 8975520853703 20000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5207790751/10000000000 : ℝ)^4663 ≤ (338618744647/781250000000 : ℝ)^3639 := by
    have hnat : (5207790751 : ℕ)^4663*781250000000^3639 ≤ 338618744647^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5207790751 10000000000 338618744647 781250000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1884081561/10000000000 : ℝ)^4663 ≤ (11779196399197/100000000000000 : ℝ)^3639 := by
    have hnat : (1884081561 : ℕ)^4663*100000000000000^3639 ≤ 11779196399197^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1884081561 10000000000 11779196399197 100000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4663/1024 : ℝ)) 4663 3639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334444729/625000000 : ℝ), (5207790751/10000000000 : ℝ), (-1884081561/10000000000 : ℝ)] ![(8975520853703/20000000000000 : ℝ), (338618744647/781250000000 : ℝ), (11779196399197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334444729/625000000 : ℝ)|^4663 ≤ (8975520853703/20000000000000 : ℝ)^3639
        have hw : |(334444729/625000000 : ℝ)|=(334444729/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5207790751/10000000000 : ℝ)|^4663 ≤ (338618744647/781250000000 : ℝ)^3639
        have hw : |(5207790751/10000000000 : ℝ)|=(5207790751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1884081561/10000000000 : ℝ)|^4663 ≤ (11779196399197/100000000000000 : ℝ)^3639
        have hw : |(-1884081561/10000000000 : ℝ)|=(1884081561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1583_s2_3 (p : ℝ) (hpa : (4661/1024 : ℝ) ≤ p) (hpb : p ≤ (4663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4236411197/10000000000 : ℝ)*x 0 + (992276577/2500000000 : ℝ)*x 1 + (4517959359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4236411197/10000000000 : ℝ)^4663 ≤ (33268779691609/100000000000000 : ℝ)^3639 := by
    have hnat : (4236411197 : ℕ)^4663*100000000000000^3639 ≤ 33268779691609^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4236411197 10000000000 33268779691609 100000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (992276577/2500000000 : ℝ)^4663 ≤ (6120634859467/20000000000000 : ℝ)^3639 := by
    have hnat : (992276577 : ℕ)^4663*20000000000000^3639 ≤ 6120634859467^3639*2500000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      992276577 2500000000 6120634859467 20000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4517959359/10000000000 : ℝ)^4663 ≤ (36128045996459/100000000000000 : ℝ)^3639 := by
    have hnat : (4517959359 : ℕ)^4663*100000000000000^3639 ≤ 36128045996459^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4517959359 10000000000 36128045996459 100000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4663/1024 : ℝ)) 4663 3639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4236411197/10000000000 : ℝ), (992276577/2500000000 : ℝ), (4517959359/10000000000 : ℝ)] ![(33268779691609/100000000000000 : ℝ), (6120634859467/20000000000000 : ℝ), (36128045996459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4236411197/10000000000 : ℝ)|^4663 ≤ (33268779691609/100000000000000 : ℝ)^3639
        have hw : |(4236411197/10000000000 : ℝ)|=(4236411197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(992276577/2500000000 : ℝ)|^4663 ≤ (6120634859467/20000000000000 : ℝ)^3639
        have hw : |(992276577/2500000000 : ℝ)|=(992276577/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4517959359/10000000000 : ℝ)|^4663 ≤ (36128045996459/100000000000000 : ℝ)^3639
        have hw : |(4517959359/10000000000 : ℝ)|=(4517959359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1583_s2_4 (p : ℝ) (hpa : (4661/1024 : ℝ) ≤ p) (hpb : p ≤ (4663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1765895129/10000000000 : ℝ)*x 0 + (5209152997/10000000000 : ℝ)*x 1 + (2718442987/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1765895129/10000000000 : ℝ)^4663 ≤ (10840862975721/100000000000000 : ℝ)^3639 := by
    have hnat : (1765895129 : ℕ)^4663*100000000000000^3639 ≤ 10840862975721^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1765895129 10000000000 10840862975721 100000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5209152997/10000000000 : ℝ)^4663 ≤ (8671545573299/20000000000000 : ℝ)^3639 := by
    have hnat : (5209152997 : ℕ)^4663*20000000000000^3639 ≤ 8671545573299^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5209152997 10000000000 8671545573299 20000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2718442987/5000000000 : ℝ)^4663 ≤ (45801409139157/100000000000000 : ℝ)^3639 := by
    have hnat : (2718442987 : ℕ)^4663*100000000000000^3639 ≤ 45801409139157^3639*5000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718442987 5000000000 45801409139157 100000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4663/1024 : ℝ)) 4663 3639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1765895129/10000000000 : ℝ), (5209152997/10000000000 : ℝ), (2718442987/5000000000 : ℝ)] ![(10840862975721/100000000000000 : ℝ), (8671545573299/20000000000000 : ℝ), (45801409139157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1765895129/10000000000 : ℝ)|^4663 ≤ (10840862975721/100000000000000 : ℝ)^3639
        have hw : |(-1765895129/10000000000 : ℝ)|=(1765895129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5209152997/10000000000 : ℝ)|^4663 ≤ (8671545573299/20000000000000 : ℝ)^3639
        have hw : |(5209152997/10000000000 : ℝ)|=(5209152997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2718442987/5000000000 : ℝ)|^4663 ≤ (45801409139157/100000000000000 : ℝ)^3639
        have hw : |(2718442987/5000000000 : ℝ)|=(2718442987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1583_s2_5 (p : ℝ) (hpa : (4661/1024 : ℝ) ≤ p) (hpb : p ≤ (4663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (264502179/500000000 : ℝ)*x 0 + (-6464793/39062500 : ℝ)*x 1 + (2718443537/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (264502179/500000000 : ℝ)^4663 ≤ (44222347425953/100000000000000 : ℝ)^3639 := by
    have hnat : (264502179 : ℕ)^4663*100000000000000^3639 ≤ 44222347425953^3639*500000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264502179 500000000 44222347425953 100000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6464793/39062500 : ℝ)^4663 ≤ (9976231544207/100000000000000 : ℝ)^3639 := by
    have hnat : (6464793 : ℕ)^4663*100000000000000^3639 ≤ 9976231544207^3639*39062500^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6464793 39062500 9976231544207 100000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2718443537/5000000000 : ℝ)^4663 ≤ (22900710506683/50000000000000 : ℝ)^3639 := by
    have hnat : (2718443537 : ℕ)^4663*50000000000000^3639 ≤ 22900710506683^3639*5000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718443537 5000000000 22900710506683 50000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4663/1024 : ℝ)) 4663 3639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(264502179/500000000 : ℝ), (-6464793/39062500 : ℝ), (2718443537/5000000000 : ℝ)] ![(44222347425953/100000000000000 : ℝ), (9976231544207/100000000000000 : ℝ), (22900710506683/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(264502179/500000000 : ℝ)|^4663 ≤ (44222347425953/100000000000000 : ℝ)^3639
        have hw : |(264502179/500000000 : ℝ)|=(264502179/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6464793/39062500 : ℝ)|^4663 ≤ (9976231544207/100000000000000 : ℝ)^3639
        have hw : |(-6464793/39062500 : ℝ)|=(6464793/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2718443537/5000000000 : ℝ)|^4663 ≤ (22900710506683/50000000000000 : ℝ)^3639
        have hw : |(2718443537/5000000000 : ℝ)|=(2718443537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1583_s2_6 (p : ℝ) (hpa : (4661/1024 : ℝ) ≤ p) (hpb : p ≤ (4663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1322511051/2500000000 : ℝ)*x 0 + (5436888197/10000000000 : ℝ)*x 1 + (-827492287/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322511051/2500000000 : ℝ)^4663 ≤ (44222354110169/100000000000000 : ℝ)^3639 := by
    have hnat : (1322511051 : ℕ)^4663*100000000000000^3639 ≤ 44222354110169^3639*2500000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322511051 2500000000 44222354110169 100000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5436888197/10000000000 : ℝ)^4663 ≤ (22900716567927/50000000000000 : ℝ)^3639 := by
    have hnat : (5436888197 : ℕ)^4663*50000000000000^3639 ≤ 22900716567927^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436888197 10000000000 22900716567927 50000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (827492287/5000000000 : ℝ)^4663 ≤ (9976212743431/100000000000000 : ℝ)^3639 := by
    have hnat : (827492287 : ℕ)^4663*100000000000000^3639 ≤ 9976212743431^3639*5000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      827492287 5000000000 9976212743431 100000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4663/1024 : ℝ)) 4663 3639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322511051/2500000000 : ℝ), (5436888197/10000000000 : ℝ), (-827492287/5000000000 : ℝ)] ![(44222354110169/100000000000000 : ℝ), (22900716567927/50000000000000 : ℝ), (9976212743431/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322511051/2500000000 : ℝ)|^4663 ≤ (44222354110169/100000000000000 : ℝ)^3639
        have hw : |(1322511051/2500000000 : ℝ)|=(1322511051/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5436888197/10000000000 : ℝ)|^4663 ≤ (22900716567927/50000000000000 : ℝ)^3639
        have hw : |(5436888197/10000000000 : ℝ)|=(5436888197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-827492287/5000000000 : ℝ)|^4663 ≤ (9976212743431/100000000000000 : ℝ)^3639
        have hw : |(-827492287/5000000000 : ℝ)|=(827492287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1583_s2_7 (p : ℝ) (hpa : (4661/1024 : ℝ) ≤ p) (hpb : p ≤ (4663/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4236502607/10000000000 : ℝ)*x 0 + (225735889/500000000 : ℝ)*x 1 + (3972374389/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4236502607/10000000000 : ℝ)^4663 ≤ (16634849770951/50000000000000 : ℝ)^3639 := by
    have hnat : (4236502607 : ℕ)^4663*50000000000000^3639 ≤ 16634849770951^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4236502607 10000000000 16634849770951 50000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (225735889/500000000 : ℝ)^4663 ≤ (14099544433/39062500000 : ℝ)^3639 := by
    have hnat : (225735889 : ℕ)^4663*39062500000^3639 ≤ 14099544433^3639*500000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225735889 500000000 14099544433 39062500000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3972374389/10000000000 : ℝ)^4663 ≤ (30635466689337/100000000000000 : ℝ)^3639 := by
    have hnat : (3972374389 : ℕ)^4663*100000000000000^3639 ≤ 30635466689337^3639*10000000000^4663 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3972374389 10000000000 30635466689337 100000000000000 4663 3639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4663/1024 : ℝ)) 4663 3639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4236502607/10000000000 : ℝ), (225735889/500000000 : ℝ), (3972374389/10000000000 : ℝ)] ![(16634849770951/50000000000000 : ℝ), (14099544433/39062500000 : ℝ), (30635466689337/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4236502607/10000000000 : ℝ)|^4663 ≤ (16634849770951/50000000000000 : ℝ)^3639
        have hw : |(4236502607/10000000000 : ℝ)|=(4236502607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(225735889/500000000 : ℝ)|^4663 ≤ (14099544433/39062500000 : ℝ)^3639
        have hw : |(225735889/500000000 : ℝ)|=(225735889/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3972374389/10000000000 : ℝ)|^4663 ≤ (30635466689337/100000000000000 : ℝ)^3639
        have hw : |(3972374389/10000000000 : ℝ)|=(3972374389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1583_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4661/1024 : ℝ) ≤ p) (hpb : p ≤ (4663/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21134259/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17639/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2303/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (10891/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15779/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17639/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2303/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17639/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2303/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17639/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2303/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17639/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2303/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17639/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2303/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17639/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2303/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2303/25000 : ℝ) ^ (4661/1024 : ℝ) ≤ (1931923417147327/100000000000000000000 : ℝ) := by
    have hpowers : (2303/25000 : ℝ)^4661 ≤ (1931923417147327/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2303 : ℕ)^4661*100000000000000000000^1024 ≤ 1931923417147327^1024*25000^4661 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2303 25000 1931923417147327 100000000000000000000 4661 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2303/25000 : ℝ)) (X := (1931923417147327/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4661 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17639/100000 : ℝ) ^ (4661/1024 : ℝ) ≤ (37164813823337507/100000000000000000000 : ℝ) := by
    have hpowers : (17639/100000 : ℝ)^4661 ≤ (37164813823337507/100000000000000000000 : ℝ)^1024 := by
      have hnat : (17639 : ℕ)^4661*100000000000000000000^1024 ≤ 37164813823337507^1024*100000^4661 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17639 100000 37164813823337507 100000000000000000000 4661 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17639/100000 : ℝ)) (X := (37164813823337507/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4661 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001931923417147327/50000000000000000000 : ℝ) ≤ (2000016977127289/2000000000000000 : ℝ) ^ (4661/1024 : ℝ) := by
    have hpowers : (50001931923417147327/50000000000000000000 : ℝ)^1024 ≤ (2000016977127289/2000000000000000 : ℝ)^4661 := by
      have hnat : (50001931923417147327 : ℕ)^1024*2000000000000000^4661 ≤ 2000016977127289^4661*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001931923417147327 50000000000000000000 2000016977127289 2000000000000000 1024 4661 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000016977127289/2000000000000000 : ℝ)) (X := (50001931923417147327/50000000000000000000 : ℝ)) (by norm_num) 4661 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50019548368620242417/50000000000000000000 : ℝ) ≤ (5000429403062967/5000000000000000 : ℝ) ^ (4661/1024 : ℝ) := by
    have hpowers : (50019548368620242417/50000000000000000000 : ℝ)^1024 ≤ (5000429403062967/5000000000000000 : ℝ)^4661 := by
      have hnat : (50019548368620242417 : ℕ)^1024*5000000000000000^4661 ≤ 5000429403062967^4661*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50019548368620242417 50000000000000000000 5000429403062967 5000000000000000 1024 4661 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000429403062967/5000000000000000 : ℝ)) (X := (50019548368620242417/50000000000000000000 : ℝ)) (by norm_num) 4661 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50037164813823337507/50000000000000000000 : ℝ) ≤ (10001632726615423/10000000000000000 : ℝ) ^ (4661/1024 : ℝ) := by
    have hpowers : (50037164813823337507/50000000000000000000 : ℝ)^1024 ≤ (10001632726615423/10000000000000000 : ℝ)^4661 := by
      have hnat : (50037164813823337507 : ℕ)^1024*10000000000000000^4661 ≤ 10001632726615423^4661*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50037164813823337507 50000000000000000000 10001632726615423 10000000000000000 1024 4661 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001632726615423/10000000000000000 : ℝ)) (X := (50037164813823337507/50000000000000000000 : ℝ)) (by norm_num) 4661 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1931923417147327/100000000000000000000 : ℝ) ≤ ((84256456620159976679/84270000000000000000 : ℝ)+2*(773920489489/842700000000000 : ℝ)*(2303/25000 : ℝ))^(4661/1024 : ℝ) := by
    rw [show (84256456620159976679/84270000000000000000 : ℝ)+2*(773920489489/842700000000000 : ℝ)*(2303/25000 : ℝ)=(2000016977127289/2000000000000000 : ℝ) by norm_num, show 1+2*(1931923417147327/100000000000000000000 : ℝ)=(50001931923417147327/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(37164813823337507/100000000000000000000 : ℝ)+(1931923417147327/100000000000000000000 : ℝ) ≤ ((84256456620159976679/84270000000000000000 : ℝ)+(773920489489/842700000000000 : ℝ)*((17639/100000 : ℝ)+(2303/25000 : ℝ)))^(4661/1024 : ℝ) := by
    rw [show (84256456620159976679/84270000000000000000 : ℝ)+(773920489489/842700000000000 : ℝ)*((17639/100000 : ℝ)+(2303/25000 : ℝ))=(5000429403062967/5000000000000000 : ℝ) by norm_num, show 1+(37164813823337507/100000000000000000000 : ℝ)+(1931923417147327/100000000000000000000 : ℝ)=(50019548368620242417/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(37164813823337507/100000000000000000000 : ℝ) ≤ ((84256456620159976679/84270000000000000000 : ℝ)+2*(773920489489/842700000000000 : ℝ)*(17639/100000 : ℝ))^(4661/1024 : ℝ) := by
    rw [show (84256456620159976679/84270000000000000000 : ℝ)+2*(773920489489/842700000000000 : ℝ)*(17639/100000 : ℝ)=(10001632726615423/10000000000000000 : ℝ) by norm_num, show 1+2*(37164813823337507/100000000000000000000 : ℝ)=(50037164813823337507/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (84256456620159976679/84270000000000000000 : ℝ)*(X 1 0+X 2 0)+(773920489489/842700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4661/1024 : ℝ)) (lo := (2303/25000 : ℝ)) (hi := (17639/100000 : ℝ)) (c := (84256456620159976679/84270000000000000000 : ℝ)) (alpha := (773920489489/842700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (84256456620159976679/84270000000000000000 : ℝ)*(X 0 1+X 2 1)+(773920489489/842700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4661/1024 : ℝ)) (lo := (2303/25000 : ℝ)) (hi := (17639/100000 : ℝ)) (c := (84256456620159976679/84270000000000000000 : ℝ)) (alpha := (773920489489/842700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (84256456620159976679/84270000000000000000 : ℝ)*(X 0 2+X 1 2)+(773920489489/842700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4661/1024 : ℝ)) (lo := (2303/25000 : ℝ)) (hi := (17639/100000 : ℝ)) (c := (84256456620159976679/84270000000000000000 : ℝ)) (alpha := (773920489489/842700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-220732179/1250000000 : ℝ)*X 0 0+(2719129431/5000000000 : ℝ)*X 0 1+(5207791183/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1583_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675557597/5000000000 : ℝ)*X 1 0+(-1884080621/10000000000 : ℝ)*X 1 1+(5207791931/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1583_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((334444729/625000000 : ℝ)*X 2 0+(5207790751/10000000000 : ℝ)*X 2 1+(-1884081561/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1583_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4236411197/10000000000 : ℝ)*X 0 0+(992276577/2500000000 : ℝ)*X 0 1+(4517959359/10000000000 : ℝ)*X 0 2+(4236411197/10000000000 : ℝ)*X 1 0+(992276577/2500000000 : ℝ)*X 1 1+(4517959359/10000000000 : ℝ)*X 1 2+(4236411197/10000000000 : ℝ)*X 2 0+(992276577/2500000000 : ℝ)*X 2 1+(4517959359/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1583_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1765895129/10000000000 : ℝ)*X 0 0+(5209152997/10000000000 : ℝ)*X 0 1+(2718442987/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1583_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((264502179/500000000 : ℝ)*X 1 0+(-6464793/39062500 : ℝ)*X 1 1+(2718443537/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1583_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1322511051/2500000000 : ℝ)*X 2 0+(5436888197/10000000000 : ℝ)*X 2 1+(-827492287/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1583_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4236502607/10000000000 : ℝ)*X 0 0+(225735889/500000000 : ℝ)*X 0 1+(3972374389/10000000000 : ℝ)*X 0 2+(4236502607/10000000000 : ℝ)*X 1 0+(225735889/500000000 : ℝ)*X 1 1+(3972374389/10000000000 : ℝ)*X 1 2+(4236502607/10000000000 : ℝ)*X 2 0+(225735889/500000000 : ℝ)*X 2 1+(3972374389/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1583_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5239462967366505702726067287/1404500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12555117/50000000000000 : ℝ)*(base23) + (8496287/50000000000000 : ℝ)*(lower2) + (35692017/50000000000000 : ℝ)*(upper4) + (67619211/50000000000000 : ℝ)*(lower5) + (3080510506455749/100000000000000 : ℝ)*(major0) + (3080510506455749/100000000000000 : ℝ)*(major1) + (3080510506455749/100000000000000 : ℝ)*(major2) + (2169509004848457/50000000000000 : ℝ)*(sp0) + (1084758044185319/25000000000000 : ℝ)*(sp1) + (4339015430051739/100000000000000 : ℝ)*(sp2) + (182198393244529/10000000000000 : ℝ)*(sp3) + (14167044361/100000000000000 : ℝ)*(sp4) + (16721579303/100000000000000 : ℝ)*(sp6) + (4779375497/100000000000000 : ℝ)*(sp7) + (910994355910393/50000000000000 : ℝ)*(f.failure) + (1084758044185319/25000000000000 : ℝ)*(f.sum) + (1054442583644659/42135000000000000000000000000 : ℝ)*base66 + (20023412921785525857/2809000000000000000000000000000000 : ℝ)*base67 + (21806174114599525857/2809000000000000000000000000000000 : ℝ)*base69 + (45236146952093525857/2809000000000000000000000000000000 : ℝ)*base71 + (86035473739579/42135000000000000000000000000 : ℝ)*base74 + (3718343111879525857/2809000000000000000000000000000000 : ℝ)*base75 + (2976702735217525857/2809000000000000000000000000000000 : ℝ)*base77 + (5230654607730525857/2809000000000000000000000000000000 : ℝ)*base79 + (100177890898909/42135000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (4796213/625000000000000000000 : ℝ)*base90 + (4796213/625000000000000000000 : ℝ)*base92 + (4796213/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11868636762779200475925936429/702250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (443996869/50000000000000 : ℝ)*(base23) + (109945081/50000000000000 : ℝ)*(lower2) + (298099609/100000000000000 : ℝ)*(upper3) + (51931053/50000000000000 : ℝ)*(lower4) + (37827959/100000000000000 : ℝ)*(upper5) + (1558741131146583/50000000000000 : ℝ)*(major0) + (1558741131146583/50000000000000 : ℝ)*(major1) + (1558741131146583/50000000000000 : ℝ)*(major2) + (8071854961/100000000000000 : ℝ)*(sp1) + (59122812527/100000000000000 : ℝ)*(sp2) + (2195554027550917/50000000000000 : ℝ)*(sp4) + (2195549991623437/50000000000000 : ℝ)*(sp5) + (4391048044295569/100000000000000 : ℝ)*(sp6) + (46096397653053/2500000000000 : ℝ)*(sp7) + (46096397653053/2500000000000 : ℝ)*(f.failure) + (2195554027550917/50000000000000 : ℝ)*(f.sum) + (351110069157/3511250000000000000000000000 : ℝ)*base65 + (2103545014165412619/1404500000000000000000000000000000 : ℝ)*base67 + (15134677337924412619/1404500000000000000000000000000000 : ℝ)*base69 + (9245956875833412619/1404500000000000000000000000000000 : ℝ)*base71 + (29985038123843/14045000000000000000000000000 : ℝ)*base73 + (1815312191294912619/1404500000000000000000000000000000 : ℝ)*base75 + (3506736376908412619/1404500000000000000000000000000000 : ℝ)*base77 + (10851135661691412619/1404500000000000000000000000000000 : ℝ)*base79 + (9248331581843/14045000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (132273/31250000000000000000 : ℝ)*base90 + (132273/31250000000000000000 : ℝ)*base92 + (132273/31250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1583_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4661/1024 : ℝ) ≤ p) (hpb : p ≤ (4663/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21134259/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17639/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2303/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10891/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15779/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1583_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1583_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4661/1024 : ℝ) ≤ p) (hpb : p ≤ (4663/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21134259/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10891/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15779/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1583_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1583_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1583_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4661/1024 : ℝ) ≤ p) (hpb : p ≤ (4663/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21134259/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10891/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15779/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1583_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
