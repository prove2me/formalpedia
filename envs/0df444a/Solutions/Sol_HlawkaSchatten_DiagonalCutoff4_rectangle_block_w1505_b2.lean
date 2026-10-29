-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1505_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:53:43.569018+00:00
-- url     : https://prove2.me/submissions/d0ac6509-6d97-43d0-b08f-e8d2cc5ee76e

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
theorem support_rectangle_w1505_s6_0 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-375681499/2000000000 : ℝ)*x 0 + (5434145533/10000000000 : ℝ)*x 1 + (1304318893/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (375681499/2000000000 : ℝ)^4507 ≤ (11489058328497/100000000000000 : ℝ)^3483 := by
    have hnat : (375681499 : ℕ)^4507*100000000000000^3483 ≤ 11489058328497^3483*2000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      375681499 2000000000 11489058328497 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5434145533/10000000000 : ℝ)^4507 ≤ (11355336746293/25000000000000 : ℝ)^3483 := by
    have hnat : (5434145533 : ℕ)^4507*25000000000000^3483 ≤ 11355336746293^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434145533 10000000000 11355336746293 25000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1304318893/2500000000 : ℝ)^4507 ≤ (43089594675641/100000000000000 : ℝ)^3483 := by
    have hnat : (1304318893 : ℕ)^4507*100000000000000^3483 ≤ 43089594675641^3483*2500000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304318893 2500000000 43089594675641 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-375681499/2000000000 : ℝ), (5434145533/10000000000 : ℝ), (1304318893/2500000000 : ℝ)] ![(11489058328497/100000000000000 : ℝ), (11355336746293/25000000000000 : ℝ), (43089594675641/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-375681499/2000000000 : ℝ)|^4507 ≤ (11489058328497/100000000000000 : ℝ)^3483
        have hw : |(-375681499/2000000000 : ℝ)|=(375681499/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5434145533/10000000000 : ℝ)|^4507 ≤ (11355336746293/25000000000000 : ℝ)^3483
        have hw : |(5434145533/10000000000 : ℝ)|=(5434145533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1304318893/2500000000 : ℝ)|^4507 ≤ (43089594675641/100000000000000 : ℝ)^3483
        have hw : |(1304318893/2500000000 : ℝ)|=(1304318893/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1505_s6_1 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351977231/10000000000 : ℝ)*x 0 + (-994746803/5000000000 : ℝ)*x 1 + (2608637831/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351977231/10000000000 : ℝ)^4507 ≤ (22267302496801/50000000000000 : ℝ)^3483 := by
    have hnat : (5351977231 : ℕ)^4507*50000000000000^3483 ≤ 22267302496801^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351977231 10000000000 22267302496801 50000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (994746803/5000000000 : ℝ)^4507 ≤ (12375799347831/100000000000000 : ℝ)^3483 := by
    have hnat : (994746803 : ℕ)^4507*100000000000000^3483 ≤ 12375799347831^3483*5000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      994746803 5000000000 12375799347831 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2608637831/5000000000 : ℝ)^4507 ≤ (21544797818743/50000000000000 : ℝ)^3483 := by
    have hnat : (2608637831 : ℕ)^4507*50000000000000^3483 ≤ 21544797818743^3483*5000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608637831 5000000000 21544797818743 50000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351977231/10000000000 : ℝ), (-994746803/5000000000 : ℝ), (2608637831/5000000000 : ℝ)] ![(22267302496801/50000000000000 : ℝ), (12375799347831/100000000000000 : ℝ), (21544797818743/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351977231/10000000000 : ℝ)|^4507 ≤ (22267302496801/50000000000000 : ℝ)^3483
        have hw : |(5351977231/10000000000 : ℝ)|=(5351977231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-994746803/5000000000 : ℝ)|^4507 ≤ (12375799347831/100000000000000 : ℝ)^3483
        have hw : |(-994746803/5000000000 : ℝ)|=(994746803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2608637831/5000000000 : ℝ)|^4507 ≤ (21544797818743/50000000000000 : ℝ)^3483
        have hw : |(2608637831/5000000000 : ℝ)|=(2608637831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1505_s6_2 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351977299/10000000000 : ℝ)*x 0 + (521727561/1000000000 : ℝ)*x 1 + (-124343349/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351977299/10000000000 : ℝ)^4507 ≤ (11133651431449/25000000000000 : ℝ)^3483 := by
    have hnat : (5351977299 : ℕ)^4507*25000000000000^3483 ≤ 11133651431449^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351977299 10000000000 11133651431449 25000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (521727561/1000000000 : ℝ)^4507 ≤ (43089595081753/100000000000000 : ℝ)^3483 := by
    have hnat : (521727561 : ℕ)^4507*100000000000000^3483 ≤ 43089595081753^3483*1000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521727561 1000000000 43089595081753 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (124343349/625000000 : ℝ)^4507 ≤ (12375799170743/100000000000000 : ℝ)^3483 := by
    have hnat : (124343349 : ℕ)^4507*100000000000000^3483 ≤ 12375799170743^3483*625000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      124343349 625000000 12375799170743 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351977299/10000000000 : ℝ), (521727561/1000000000 : ℝ), (-124343349/625000000 : ℝ)] ![(11133651431449/25000000000000 : ℝ), (43089595081753/100000000000000 : ℝ), (12375799170743/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351977299/10000000000 : ℝ)|^4507 ≤ (11133651431449/25000000000000 : ℝ)^3483
        have hw : |(5351977299/10000000000 : ℝ)|=(5351977299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(521727561/1000000000 : ℝ)|^4507 ≤ (43089595081753/100000000000000 : ℝ)^3483
        have hw : |(521727561/1000000000 : ℝ)|=(521727561/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-124343349/625000000 : ℝ)|^4507 ≤ (12375799170743/100000000000000 : ℝ)^3483
        have hw : |(-124343349/625000000 : ℝ)|=(124343349/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1505_s6_3 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4273043279/10000000000 : ℝ)*x 0 + (806870437/2000000000 : ℝ)*x 1 + (2261849227/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4273043279/10000000000 : ℝ)^4507 ≤ (16639653240043/50000000000000 : ℝ)^3483 := by
    have hnat : (4273043279 : ℕ)^4507*50000000000000^3483 ≤ 16639653240043^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4273043279 10000000000 16639653240043 50000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (806870437/2000000000 : ℝ)^4507 ≤ (247150515613/800000000000 : ℝ)^3483 := by
    have hnat : (806870437 : ℕ)^4507*800000000000^3483 ≤ 247150515613^3483*2000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      806870437 2000000000 247150515613 800000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2261849227/5000000000 : ℝ)^4507 ≤ (17913439530347/50000000000000 : ℝ)^3483 := by
    have hnat : (2261849227 : ℕ)^4507*50000000000000^3483 ≤ 17913439530347^3483*5000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2261849227 5000000000 17913439530347 50000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4273043279/10000000000 : ℝ), (806870437/2000000000 : ℝ), (2261849227/5000000000 : ℝ)] ![(16639653240043/50000000000000 : ℝ), (247150515613/800000000000 : ℝ), (17913439530347/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4273043279/10000000000 : ℝ)|^4507 ≤ (16639653240043/50000000000000 : ℝ)^3483
        have hw : |(4273043279/10000000000 : ℝ)|=(4273043279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(806870437/2000000000 : ℝ)|^4507 ≤ (247150515613/800000000000 : ℝ)^3483
        have hw : |(806870437/2000000000 : ℝ)|=(806870437/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2261849227/5000000000 : ℝ)|^4507 ≤ (17913439530347/50000000000000 : ℝ)^3483
        have hw : |(2261849227/5000000000 : ℝ)|=(2261849227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1505_s6_4 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1878436739/10000000000 : ℝ)*x 0 + (5218390387/10000000000 : ℝ)*x 1 + (2716511259/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1878436739/10000000000 : ℝ)^4507 ≤ (11489289783447/100000000000000 : ℝ)^3483 := by
    have hnat : (1878436739 : ℕ)^4507*100000000000000^3483 ≤ 11489289783447^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1878436739 10000000000 11489289783447 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5218390387/10000000000 : ℝ)^4507 ≤ (43101509267233/100000000000000 : ℝ)^3483 := by
    have hnat : (5218390387 : ℕ)^4507*100000000000000^3483 ≤ 43101509267233^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218390387 10000000000 43101509267233 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2716511259/5000000000 : ℝ)^4507 ≤ (709518764557/1562500000000 : ℝ)^3483 := by
    have hnat : (2716511259 : ℕ)^4507*1562500000000^3483 ≤ 709518764557^3483*5000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716511259 5000000000 709518764557 1562500000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1878436739/10000000000 : ℝ), (5218390387/10000000000 : ℝ), (2716511259/5000000000 : ℝ)] ![(11489289783447/100000000000000 : ℝ), (43101509267233/100000000000000 : ℝ), (709518764557/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1878436739/10000000000 : ℝ)|^4507 ≤ (11489289783447/100000000000000 : ℝ)^3483
        have hw : |(-1878436739/10000000000 : ℝ)|=(1878436739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5218390387/10000000000 : ℝ)|^4507 ≤ (43101509267233/100000000000000 : ℝ)^3483
        have hw : |(5218390387/10000000000 : ℝ)|=(5218390387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2716511259/5000000000 : ℝ)|^4507 ≤ (709518764557/1562500000000 : ℝ)^3483
        have hw : |(2716511259/5000000000 : ℝ)|=(2716511259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1505_s6_5 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323776813/2500000000 : ℝ)*x 0 + (-886873343/5000000000 : ℝ)*x 1 + (5433022529/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323776813/2500000000 : ℝ)^4507 ≤ (43923212802899/100000000000000 : ℝ)^3483 := by
    have hnat : (1323776813 : ℕ)^4507*100000000000000^3483 ≤ 43923212802899^3483*2500000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323776813 2500000000 43923212802899 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (886873343/5000000000 : ℝ)^4507 ≤ (10667586126151/100000000000000 : ℝ)^3483 := by
    have hnat : (886873343 : ℕ)^4507*100000000000000^3483 ≤ 10667586126151^3483*5000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      886873343 5000000000 10667586126151 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5433022529/10000000000 : ℝ)^4507 ≤ (9081840210123/20000000000000 : ℝ)^3483 := by
    have hnat : (5433022529 : ℕ)^4507*20000000000000^3483 ≤ 9081840210123^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433022529 10000000000 9081840210123 20000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323776813/2500000000 : ℝ), (-886873343/5000000000 : ℝ), (5433022529/10000000000 : ℝ)] ![(43923212802899/100000000000000 : ℝ), (10667586126151/100000000000000 : ℝ), (9081840210123/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323776813/2500000000 : ℝ)|^4507 ≤ (43923212802899/100000000000000 : ℝ)^3483
        have hw : |(1323776813/2500000000 : ℝ)|=(1323776813/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-886873343/5000000000 : ℝ)|^4507 ≤ (10667586126151/100000000000000 : ℝ)^3483
        have hw : |(-886873343/5000000000 : ℝ)|=(886873343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5433022529/10000000000 : ℝ)|^4507 ≤ (9081840210123/20000000000000 : ℝ)^3483
        have hw : |(5433022529/10000000000 : ℝ)|=(5433022529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1505_s6_6 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1059021453/2000000000 : ℝ)*x 0 + (5433022519/10000000000 : ℝ)*x 1 + (-443436671/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059021453/2000000000 : ℝ)^4507 ≤ (43923212942439/100000000000000 : ℝ)^3483 := by
    have hnat : (1059021453 : ℕ)^4507*100000000000000^3483 ≤ 43923212942439^3483*2000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059021453 2000000000 43923212942439 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5433022519/10000000000 : ℝ)^4507 ≤ (45409200942463/100000000000000 : ℝ)^3483 := by
    have hnat : (5433022519 : ℕ)^4507*100000000000000^3483 ≤ 45409200942463^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433022519 10000000000 45409200942463 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (443436671/2500000000 : ℝ)^4507 ≤ (10667586110587/100000000000000 : ℝ)^3483 := by
    have hnat : (443436671 : ℕ)^4507*100000000000000^3483 ≤ 10667586110587^3483*2500000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      443436671 2500000000 10667586110587 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1059021453/2000000000 : ℝ), (5433022519/10000000000 : ℝ), (-443436671/2500000000 : ℝ)] ![(43923212942439/100000000000000 : ℝ), (45409200942463/100000000000000 : ℝ), (10667586110587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1059021453/2000000000 : ℝ)|^4507 ≤ (43923212942439/100000000000000 : ℝ)^3483
        have hw : |(1059021453/2000000000 : ℝ)|=(1059021453/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5433022519/10000000000 : ℝ)|^4507 ≤ (45409200942463/100000000000000 : ℝ)^3483
        have hw : |(5433022519/10000000000 : ℝ)|=(5433022519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-443436671/2500000000 : ℝ)|^4507 ≤ (10667586110587/100000000000000 : ℝ)^3483
        have hw : |(-443436671/2500000000 : ℝ)|=(443436671/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1505_s6_7 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4273109271/10000000000 : ℝ)*x 0 + (904236609/2000000000 : ℝ)*x 1 + (504610767/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4273109271/10000000000 : ℝ)^4507 ≤ (16639985771963/50000000000000 : ℝ)^3483 := by
    have hnat : (4273109271 : ℕ)^4507*50000000000000^3483 ≤ 16639985771963^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4273109271 10000000000 16639985771963 50000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (904236609/2000000000 : ℝ)^4507 ≤ (35801102645461/100000000000000 : ℝ)^3483 := by
    have hnat : (904236609 : ℕ)^4507*100000000000000^3483 ≤ 35801102645461^3483*2000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      904236609 2000000000 35801102645461 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (504610767/1250000000 : ℝ)^4507 ≤ (30918925804587/100000000000000 : ℝ)^3483 := by
    have hnat : (504610767 : ℕ)^4507*100000000000000^3483 ≤ 30918925804587^3483*1250000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      504610767 1250000000 30918925804587 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4273109271/10000000000 : ℝ), (904236609/2000000000 : ℝ), (504610767/1250000000 : ℝ)] ![(16639985771963/50000000000000 : ℝ), (35801102645461/100000000000000 : ℝ), (30918925804587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4273109271/10000000000 : ℝ)|^4507 ≤ (16639985771963/50000000000000 : ℝ)^3483
        have hw : |(4273109271/10000000000 : ℝ)|=(4273109271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(904236609/2000000000 : ℝ)|^4507 ≤ (35801102645461/100000000000000 : ℝ)^3483
        have hw : |(904236609/2000000000 : ℝ)|=(904236609/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(504610767/1250000000 : ℝ)|^4507 ≤ (30918925804587/100000000000000 : ℝ)^3483
        have hw : |(504610767/1250000000 : ℝ)|=(504610767/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1505_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162820231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1361/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (10889/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15481/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7741/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1361/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7741/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1361/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7741/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1361/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7741/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1361/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7741/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1361/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7741/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1361/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1361/12500 : ℝ) ^ (4505/1024 : ℝ) ≤ (5796101496578811/100000000000000000000 : ℝ) := by
    have hpowers : (1361/12500 : ℝ)^4505 ≤ (5796101496578811/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1361 : ℕ)^4505*100000000000000000000^1024 ≤ 5796101496578811^1024*12500^4505 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1361 12500 5796101496578811 100000000000000000000 4505 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1361/12500 : ℝ)) (X := (5796101496578811/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4505 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7741/50000 : ℝ) ^ (4505/1024 : ℝ) ≤ (27271799066736899/100000000000000000000 : ℝ) := by
    have hpowers : (7741/50000 : ℝ)^4505 ≤ (27271799066736899/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7741 : ℕ)^4505*100000000000000000000^1024 ≤ 27271799066736899^1024*50000^4505 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7741 50000 27271799066736899 100000000000000000000 4505 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7741/50000 : ℝ)) (X := (27271799066736899/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4505 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005796101496578811/50000000000000000000 : ℝ) ≤ (10000263482447711/10000000000000000 : ℝ) ^ (4505/1024 : ℝ) := by
    have hpowers : (50005796101496578811/50000000000000000000 : ℝ)^1024 ≤ (10000263482447711/10000000000000000 : ℝ)^4505 := by
      have hnat : (50005796101496578811 : ℕ)^1024*10000000000000000^4505 ≤ 10000263482447711^4505*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005796101496578811 50000000000000000000 10000263482447711 10000000000000000 1024 4505 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000263482447711/10000000000000000 : ℝ)) (X := (50005796101496578811/50000000000000000000 : ℝ)) (by norm_num) 4505 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10003306790056331571/10000000000000000000 : ℝ) ≤ (5000375773639989/5000000000000000 : ℝ) ^ (4505/1024 : ℝ) := by
    have hpowers : (10003306790056331571/10000000000000000000 : ℝ)^1024 ≤ (5000375773639989/5000000000000000 : ℝ)^4505 := by
      have hnat : (10003306790056331571 : ℕ)^1024*5000000000000000^4505 ≤ 5000375773639989^4505*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10003306790056331571 10000000000000000000 5000375773639989 5000000000000000 1024 4505 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000375773639989/5000000000000000 : ℝ)) (X := (10003306790056331571/10000000000000000000 : ℝ)) (by norm_num) 4505 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50027271799066736899/50000000000000000000 : ℝ) ≤ (2000247922422449/2000000000000000 : ℝ) ^ (4505/1024 : ℝ) := by
    have hpowers : (50027271799066736899/50000000000000000000 : ℝ)^1024 ≤ (2000247922422449/2000000000000000 : ℝ)^4505 := by
      have hnat : (50027271799066736899 : ℕ)^1024*2000000000000000^4505 ≤ 2000247922422449^4505*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027271799066736899 50000000000000000000 2000247922422449 2000000000000000 1024 4505 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000247922422449/2000000000000000 : ℝ)) (X := (50027271799066736899/50000000000000000000 : ℝ)) (by norm_num) 4505 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5796101496578811/100000000000000000000 : ℝ) ≤ ((22965291169288669071/22970000000000000000 : ℝ)+2*(488064832267/459400000000000 : ℝ)*(1361/12500 : ℝ))^(4505/1024 : ℝ) := by
    rw [show (22965291169288669071/22970000000000000000 : ℝ)+2*(488064832267/459400000000000 : ℝ)*(1361/12500 : ℝ)=(10000263482447711/10000000000000000 : ℝ) by norm_num, show 1+2*(5796101496578811/100000000000000000000 : ℝ)=(50005796101496578811/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27271799066736899/100000000000000000000 : ℝ)+(5796101496578811/100000000000000000000 : ℝ) ≤ ((22965291169288669071/22970000000000000000 : ℝ)+(488064832267/459400000000000 : ℝ)*((7741/50000 : ℝ)+(1361/12500 : ℝ)))^(4505/1024 : ℝ) := by
    rw [show (22965291169288669071/22970000000000000000 : ℝ)+(488064832267/459400000000000 : ℝ)*((7741/50000 : ℝ)+(1361/12500 : ℝ))=(5000375773639989/5000000000000000 : ℝ) by norm_num, show 1+(27271799066736899/100000000000000000000 : ℝ)+(5796101496578811/100000000000000000000 : ℝ)=(10003306790056331571/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27271799066736899/100000000000000000000 : ℝ) ≤ ((22965291169288669071/22970000000000000000 : ℝ)+2*(488064832267/459400000000000 : ℝ)*(7741/50000 : ℝ))^(4505/1024 : ℝ) := by
    rw [show (22965291169288669071/22970000000000000000 : ℝ)+2*(488064832267/459400000000000 : ℝ)*(7741/50000 : ℝ)=(2000247922422449/2000000000000000 : ℝ) by norm_num, show 1+2*(27271799066736899/100000000000000000000 : ℝ)=(50027271799066736899/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (22965291169288669071/22970000000000000000 : ℝ)*(X 1 0+X 2 0)+(488064832267/459400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4505/1024 : ℝ)) (lo := (1361/12500 : ℝ)) (hi := (7741/50000 : ℝ)) (c := (22965291169288669071/22970000000000000000 : ℝ)) (alpha := (488064832267/459400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (22965291169288669071/22970000000000000000 : ℝ)*(X 0 1+X 2 1)+(488064832267/459400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4505/1024 : ℝ)) (lo := (1361/12500 : ℝ)) (hi := (7741/50000 : ℝ)) (c := (22965291169288669071/22970000000000000000 : ℝ)) (alpha := (488064832267/459400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (22965291169288669071/22970000000000000000 : ℝ)*(X 0 2+X 1 2)+(488064832267/459400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4505/1024 : ℝ)) (lo := (1361/12500 : ℝ)) (hi := (7741/50000 : ℝ)) (c := (22965291169288669071/22970000000000000000 : ℝ)) (alpha := (488064832267/459400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-375681499/2000000000 : ℝ)*X 0 0+(5434145533/10000000000 : ℝ)*X 0 1+(1304318893/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351977231/10000000000 : ℝ)*X 1 0+(-994746803/5000000000 : ℝ)*X 1 1+(2608637831/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351977299/10000000000 : ℝ)*X 2 0+(521727561/1000000000 : ℝ)*X 2 1+(-124343349/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4273043279/10000000000 : ℝ)*X 0 0+(806870437/2000000000 : ℝ)*X 0 1+(2261849227/5000000000 : ℝ)*X 0 2+(4273043279/10000000000 : ℝ)*X 1 0+(806870437/2000000000 : ℝ)*X 1 1+(2261849227/5000000000 : ℝ)*X 1 2+(4273043279/10000000000 : ℝ)*X 2 0+(806870437/2000000000 : ℝ)*X 2 1+(2261849227/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1878436739/10000000000 : ℝ)*X 0 0+(5218390387/10000000000 : ℝ)*X 0 1+(2716511259/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1323776813/2500000000 : ℝ)*X 1 0+(-886873343/5000000000 : ℝ)*X 1 1+(5433022529/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1059021453/2000000000 : ℝ)*X 2 0+(5433022519/10000000000 : ℝ)*X 2 1+(-443436671/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4273109271/10000000000 : ℝ)*X 0 0+(904236609/2000000000 : ℝ)*X 0 1+(504610767/1250000000 : ℝ)*X 0 2+(4273109271/10000000000 : ℝ)*X 1 0+(904236609/2000000000 : ℝ)*X 1 1+(504610767/1250000000 : ℝ)*X 1 2+(4273109271/10000000000 : ℝ)*X 2 0+(904236609/2000000000 : ℝ)*X 2 1+(504610767/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3141006171644950657184077671/1148500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (92079587/20000000000000 : ℝ)*(base19) + (96724521/20000000000000 : ℝ)*(base23) + (236569/1250000000000 : ℝ)*(lower2) + (64548207/100000000000000 : ℝ)*(upper3) + (1730711/2500000000000 : ℝ)*(upper5) + (1663656396124811/50000000000000 : ℝ)*(major0) + (1663656396124811/50000000000000 : ℝ)*(major1) + (3327312792249623/100000000000000 : ℝ)*(major2) + (4611066379004151/100000000000000 : ℝ)*(sp0) + (2305537528246431/50000000000000 : ℝ)*(sp1) + (144096094789631/3125000000000 : ℝ)*(sp2) + (204354622010519/10000000000000 : ℝ)*(sp3) + (4568943323/50000000000000 : ℝ)*(sp4) + (3756340687/100000000000000 : ℝ)*(sp7) + (2043549976445877/100000000000000 : ℝ)*(f.failure) + (4611075516890797/100000000000000 : ℝ)*(f.sum) + (12868375477341/9188000000000000000000000000 : ℝ)*base66 + (5955983184350054419/1148500000000000000000000000000000 : ℝ)*base68 + (18748500125198789767/2297000000000000000000000000000000 : ℝ)*base70 + (9234469186061554419/1148500000000000000000000000000000 : ℝ)*base72 + (20792323927601/9188000000000000000000000000 : ℝ)*base74 + (15626717814466789767/2297000000000000000000000000000000 : ℝ)*base76 + (6059294213339229419/1148500000000000000000000000000000 : ℝ)*base78 + (10083510258954229419/1148500000000000000000000000000000 : ℝ)*base80 + (10095650763997/11485000000000000000000000000 : ℝ)*base81 + (52137587/10000000000000000000000 : ℝ)*base89 + (52137587/10000000000000000000000 : ℝ)*base91 + (47862413/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1100013584983502425778367177/114850000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1575964481/100000000000000 : ℝ)*(base19) + (863300093/50000000000000 : ℝ)*(base23) + (104770269/20000000000000 : ℝ)*(lower1) + (100506549/50000000000000 : ℝ)*(upper3) + (12594197/20000000000000 : ℝ)*(lower4) + (20512693/10000000000000 : ℝ)*(upper5) + (336197376133971/10000000000000 : ℝ)*(major0) + (336197376133971/10000000000000 : ℝ)*(major1) + (336197376133971/10000000000000 : ℝ)*(major2) + (1887708553/100000000000000 : ℝ)*(sp2) + (116477733771061/2500000000000 : ℝ)*(sp4) + (4659107774877959/100000000000000 : ℝ)*(sp5) + (4659105736533701/100000000000000 : ℝ)*(sp6) + (2064837852576017/100000000000000 : ℝ)*(sp7) + (2064837852576017/100000000000000 : ℝ)*(f.failure) + (116477733771061/2500000000000 : ℝ)*(f.sum) + (4886552632749/1148500000000000000000000000 : ℝ)*base65 + (7601909638556460941/229700000000000000000000000000000 : ℝ)*base67 + (575981978002560941/229700000000000000000000000000000 : ℝ)*base69 + (19208936332525460941/229700000000000000000000000000000 : ℝ)*base71 + (6876850663/229700000000000000000000000 : ℝ)*base73 + (11525182389610139059/229700000000000000000000000000000 : ℝ)*base76 + (258303464361339059/229700000000000000000000000000000 : ℝ)*base78 + (333493962947160941/229700000000000000000000000000000 : ℝ)*base79 + (1551989832817/459400000000000000000000000 : ℝ)*base81 + (32999927/10000000000000000000000 : ℝ)*base89 + (32999927/10000000000000000000000 : ℝ)*base91 + (32999927/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1505_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162820231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1361/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10889/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15481/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1505_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1505_box_0 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1663519771/10000000000 : ℝ)*x 0 + (5403590607/10000000000 : ℝ)*x 1 + (2701795183/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1663519771/10000000000 : ℝ)^4507 ≤ (2454429968757/25000000000000 : ℝ)^3483 := by
    have hnat : (1663519771 : ℕ)^4507*25000000000000^3483 ≤ 2454429968757^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1663519771 10000000000 2454429968757 25000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5403590607/10000000000 : ℝ)^4507 ≤ (5636392669267/12500000000000 : ℝ)^3483 := by
    have hnat : (5403590607 : ℕ)^4507*12500000000000^3483 ≤ 5636392669267^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403590607 10000000000 5636392669267 12500000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2701795183/5000000000 : ℝ)^4507 ≤ (45091138751821/100000000000000 : ℝ)^3483 := by
    have hnat : (2701795183 : ℕ)^4507*100000000000000^3483 ≤ 45091138751821^3483*5000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701795183 5000000000 45091138751821 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1663519771/10000000000 : ℝ), (5403590607/10000000000 : ℝ), (2701795183/5000000000 : ℝ)] ![(2454429968757/25000000000000 : ℝ), (5636392669267/12500000000000 : ℝ), (45091138751821/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1663519771/10000000000 : ℝ)|^4507 ≤ (2454429968757/25000000000000 : ℝ)^3483
        have hw : |(-1663519771/10000000000 : ℝ)|=(1663519771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5403590607/10000000000 : ℝ)|^4507 ≤ (5636392669267/12500000000000 : ℝ)^3483
        have hw : |(5403590607/10000000000 : ℝ)|=(5403590607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2701795183/5000000000 : ℝ)|^4507 ≤ (45091138751821/100000000000000 : ℝ)^3483
        have hw : |(2701795183/5000000000 : ℝ)|=(2701795183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1505_box_1 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2635340503/5000000000 : ℝ)*x 0 + (-461958191/2500000000 : ℝ)*x 1 + (2701795363/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2635340503/5000000000 : ℝ)^4507 ≤ (43661204393973/100000000000000 : ℝ)^3483 := by
    have hnat : (2635340503 : ℕ)^4507*100000000000000^3483 ≤ 43661204393973^3483*5000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2635340503 5000000000 43661204393973 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (461958191/2500000000 : ℝ)^4507 ≤ (11247652946537/100000000000000 : ℝ)^3483 := by
    have hnat : (461958191 : ℕ)^4507*100000000000000^3483 ≤ 11247652946537^3483*2500000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      461958191 2500000000 11247652946537 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2701795363/5000000000 : ℝ)^4507 ≤ (45091142639097/100000000000000 : ℝ)^3483 := by
    have hnat : (2701795363 : ℕ)^4507*100000000000000^3483 ≤ 45091142639097^3483*5000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701795363 5000000000 45091142639097 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2635340503/5000000000 : ℝ), (-461958191/2500000000 : ℝ), (2701795363/5000000000 : ℝ)] ![(43661204393973/100000000000000 : ℝ), (11247652946537/100000000000000 : ℝ), (45091142639097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2635340503/5000000000 : ℝ)|^4507 ≤ (43661204393973/100000000000000 : ℝ)^3483
        have hw : |(2635340503/5000000000 : ℝ)|=(2635340503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-461958191/2500000000 : ℝ)|^4507 ≤ (11247652946537/100000000000000 : ℝ)^3483
        have hw : |(-461958191/2500000000 : ℝ)|=(461958191/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2701795363/5000000000 : ℝ)|^4507 ≤ (45091142639097/100000000000000 : ℝ)^3483
        have hw : |(2701795363/5000000000 : ℝ)|=(2701795363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1505_box_2 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1317670139/2500000000 : ℝ)*x 0 + (5403590943/10000000000 : ℝ)*x 1 + (-1847833079/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1317670139/2500000000 : ℝ)^4507 ≤ (21830599785163/50000000000000 : ℝ)^3483 := by
    have hnat : (1317670139 : ℕ)^4507*50000000000000^3483 ≤ 21830599785163^3483*2500000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1317670139 2500000000 21830599785163 50000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5403590943/10000000000 : ℝ)^4507 ≤ (45091144982261/100000000000000 : ℝ)^3483 := by
    have hnat : (5403590943 : ℕ)^4507*100000000000000^3483 ≤ 45091144982261^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403590943 10000000000 45091144982261 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1847833079/10000000000 : ℝ)^4507 ≤ (2249531085527/20000000000000 : ℝ)^3483 := by
    have hnat : (1847833079 : ℕ)^4507*20000000000000^3483 ≤ 2249531085527^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1847833079 10000000000 2249531085527 20000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1317670139/2500000000 : ℝ), (5403590943/10000000000 : ℝ), (-1847833079/10000000000 : ℝ)] ![(21830599785163/50000000000000 : ℝ), (45091144982261/100000000000000 : ℝ), (2249531085527/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1317670139/2500000000 : ℝ)|^4507 ≤ (21830599785163/50000000000000 : ℝ)^3483
        have hw : |(1317670139/2500000000 : ℝ)|=(1317670139/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5403590943/10000000000 : ℝ)|^4507 ≤ (45091144982261/100000000000000 : ℝ)^3483
        have hw : |(5403590943/10000000000 : ℝ)|=(5403590943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1847833079/10000000000 : ℝ)|^4507 ≤ (2249531085527/20000000000000 : ℝ)^3483
        have hw : |(-1847833079/10000000000 : ℝ)|=(1847833079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1505_box_3 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1119107167/2500000000 : ℝ)*x 0 + (522297331/1250000000 : ℝ)*x 1 + (4178378009/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1119107167/2500000000 : ℝ)^4507 ≤ (7068638552041/20000000000000 : ℝ)^3483 := by
    have hnat : (1119107167 : ℕ)^4507*20000000000000^3483 ≤ 7068638552041^3483*2500000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119107167 2500000000 7068638552041 20000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (522297331/1250000000 : ℝ)^4507 ≤ (16164203404129/50000000000000 : ℝ)^3483 := by
    have hnat : (522297331 : ℕ)^4507*50000000000000^3483 ≤ 16164203404129^3483*1250000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522297331 1250000000 16164203404129 50000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4178378009/10000000000 : ℝ)^4507 ≤ (32328400410741/100000000000000 : ℝ)^3483 := by
    have hnat : (4178378009 : ℕ)^4507*100000000000000^3483 ≤ 32328400410741^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4178378009 10000000000 32328400410741 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1119107167/2500000000 : ℝ), (522297331/1250000000 : ℝ), (4178378009/10000000000 : ℝ)] ![(7068638552041/20000000000000 : ℝ), (16164203404129/50000000000000 : ℝ), (32328400410741/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1119107167/2500000000 : ℝ)|^4507 ≤ (7068638552041/20000000000000 : ℝ)^3483
        have hw : |(1119107167/2500000000 : ℝ)|=(1119107167/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(522297331/1250000000 : ℝ)|^4507 ≤ (16164203404129/50000000000000 : ℝ)^3483
        have hw : |(522297331/1250000000 : ℝ)|=(522297331/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4178378009/10000000000 : ℝ)|^4507 ≤ (32328400410741/100000000000000 : ℝ)^3483
        have hw : |(4178378009/10000000000 : ℝ)|=(4178378009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1505_box_4 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-524685189/2500000000 : ℝ)*x 0 + (5243391617/10000000000 : ℝ)*x 1 + (2621695923/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (524685189/2500000000 : ℝ)^4507 ≤ (663109234653/5000000000000 : ℝ)^3483 := by
    have hnat : (524685189 : ℕ)^4507*5000000000000^3483 ≤ 663109234653^3483*2500000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524685189 2500000000 663109234653 5000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243391617/10000000000 : ℝ)^4507 ≤ (43368906422087/100000000000000 : ℝ)^3483 := by
    have hnat : (5243391617 : ℕ)^4507*100000000000000^3483 ≤ 43368906422087^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243391617 10000000000 43368906422087 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621695923/5000000000 : ℝ)^4507 ≤ (10842227218261/25000000000000 : ℝ)^3483 := by
    have hnat : (2621695923 : ℕ)^4507*25000000000000^3483 ≤ 10842227218261^3483*5000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621695923 5000000000 10842227218261 25000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-524685189/2500000000 : ℝ), (5243391617/10000000000 : ℝ), (2621695923/5000000000 : ℝ)] ![(663109234653/5000000000000 : ℝ), (43368906422087/100000000000000 : ℝ), (10842227218261/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-524685189/2500000000 : ℝ)|^4507 ≤ (663109234653/5000000000000 : ℝ)^3483
        have hw : |(-524685189/2500000000 : ℝ)|=(524685189/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243391617/10000000000 : ℝ)|^4507 ≤ (43368906422087/100000000000000 : ℝ)^3483
        have hw : |(5243391617/10000000000 : ℝ)|=(5243391617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621695923/5000000000 : ℝ)|^4507 ≤ (10842227218261/25000000000000 : ℝ)^3483
        have hw : |(2621695923/5000000000 : ℝ)|=(2621695923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1505_box_5 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (538227533/1000000000 : ℝ)*x 0 + (-119612741/625000000 : ℝ)*x 1 + (5243391799/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (538227533/1000000000 : ℝ)^4507 ≤ (5607639102207/12500000000000 : ℝ)^3483 := by
    have hnat : (538227533 : ℕ)^4507*12500000000000^3483 ≤ 5607639102207^3483*1000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538227533 1000000000 5607639102207 12500000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (119612741/625000000 : ℝ)^4507 ≤ (147124735021/1250000000000 : ℝ)^3483 := by
    have hnat : (119612741 : ℕ)^4507*1250000000000^3483 ≤ 147124735021^3483*625000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      119612741 625000000 147124735021 1250000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243391799/10000000000 : ℝ)^4507 ≤ (43368908370009/100000000000000 : ℝ)^3483 := by
    have hnat : (5243391799 : ℕ)^4507*100000000000000^3483 ≤ 43368908370009^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243391799 10000000000 43368908370009 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(538227533/1000000000 : ℝ), (-119612741/625000000 : ℝ), (5243391799/10000000000 : ℝ)] ![(5607639102207/12500000000000 : ℝ), (147124735021/1250000000000 : ℝ), (43368908370009/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(538227533/1000000000 : ℝ)|^4507 ≤ (5607639102207/12500000000000 : ℝ)^3483
        have hw : |(538227533/1000000000 : ℝ)|=(538227533/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-119612741/625000000 : ℝ)|^4507 ≤ (147124735021/1250000000000 : ℝ)^3483
        have hw : |(-119612741/625000000 : ℝ)|=(119612741/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243391799/10000000000 : ℝ)|^4507 ≤ (43368908370009/100000000000000 : ℝ)^3483
        have hw : |(5243391799/10000000000 : ℝ)|=(5243391799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1505_box_6 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2691137637/5000000000 : ℝ)*x 0 + (524339191/1000000000 : ℝ)*x 1 + (-1913803781/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2691137637/5000000000 : ℝ)^4507 ≤ (44861112213671/100000000000000 : ℝ)^3483 := by
    have hnat : (2691137637 : ℕ)^4507*100000000000000^3483 ≤ 44861112213671^3483*5000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2691137637 5000000000 44861112213671 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524339191/1000000000 : ℝ)^4507 ≤ (10842227389507/25000000000000 : ℝ)^3483 := by
    have hnat : (524339191 : ℕ)^4507*25000000000000^3483 ≤ 10842227389507^3483*1000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524339191 1000000000 10842227389507 25000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1913803781/10000000000 : ℝ)^4507 ≤ (5884989102409/50000000000000 : ℝ)^3483 := by
    have hnat : (1913803781 : ℕ)^4507*50000000000000^3483 ≤ 5884989102409^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1913803781 10000000000 5884989102409 50000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2691137637/5000000000 : ℝ), (524339191/1000000000 : ℝ), (-1913803781/10000000000 : ℝ)] ![(44861112213671/100000000000000 : ℝ), (10842227389507/25000000000000 : ℝ), (5884989102409/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2691137637/5000000000 : ℝ)|^4507 ≤ (44861112213671/100000000000000 : ℝ)^3483
        have hw : |(2691137637/5000000000 : ℝ)|=(2691137637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524339191/1000000000 : ℝ)|^4507 ≤ (10842227389507/25000000000000 : ℝ)^3483
        have hw : |(524339191/1000000000 : ℝ)|=(524339191/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1913803781/10000000000 : ℝ)|^4507 ≤ (5884989102409/50000000000000 : ℝ)^3483
        have hw : |(-1913803781/10000000000 : ℝ)|=(1913803781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1505_box_7 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2033636421/5000000000 : ℝ)*x 0 + (4382821027/10000000000 : ℝ)*x 1 + (4382821029/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2033636421/5000000000 : ℝ)^4507 ≤ (1951276080159/6250000000000 : ℝ)^3483 := by
    have hnat : (2033636421 : ℕ)^4507*6250000000000^3483 ≤ 1951276080159^3483*5000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2033636421 5000000000 1951276080159 6250000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4382821027/10000000000 : ℝ)^4507 ≤ (17194895672349/50000000000000 : ℝ)^3483 := by
    have hnat : (4382821027 : ℕ)^4507*50000000000000^3483 ≤ 17194895672349^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4382821027 10000000000 17194895672349 50000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4382821029/10000000000 : ℝ)^4507 ≤ (6877958273001/20000000000000 : ℝ)^3483 := by
    have hnat : (4382821029 : ℕ)^4507*20000000000000^3483 ≤ 6877958273001^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4382821029 10000000000 6877958273001 20000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2033636421/5000000000 : ℝ), (4382821027/10000000000 : ℝ), (4382821029/10000000000 : ℝ)] ![(1951276080159/6250000000000 : ℝ), (17194895672349/50000000000000 : ℝ), (6877958273001/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2033636421/5000000000 : ℝ)|^4507 ≤ (1951276080159/6250000000000 : ℝ)^3483
        have hw : |(2033636421/5000000000 : ℝ)|=(2033636421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4382821027/10000000000 : ℝ)|^4507 ≤ (17194895672349/50000000000000 : ℝ)^3483
        have hw : |(4382821027/10000000000 : ℝ)|=(4382821027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4382821029/10000000000 : ℝ)|^4507 ≤ (6877958273001/20000000000000 : ℝ)^3483
        have hw : |(4382821029/10000000000 : ℝ)|=(4382821029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1505_box_8 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2006805383/10000000000 : ℝ)*x 0 + (5131237847/10000000000 : ℝ)*x 1 + (5424064413/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2006805383/10000000000 : ℝ)^4507 ≤ (312883176537/2500000000000 : ℝ)^3483 := by
    have hnat : (2006805383 : ℕ)^4507*2500000000000^3483 ≤ 312883176537^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2006805383 10000000000 312883176537 2500000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5131237847/10000000000 : ℝ)^4507 ≤ (42172332613877/100000000000000 : ℝ)^3483 := by
    have hnat : (5131237847 : ℕ)^4507*100000000000000^3483 ≤ 42172332613877^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5131237847 10000000000 42172332613877 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5424064413/10000000000 : ℝ)^4507 ≤ (22656170152963/50000000000000 : ℝ)^3483 := by
    have hnat : (5424064413 : ℕ)^4507*50000000000000^3483 ≤ 22656170152963^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424064413 10000000000 22656170152963 50000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2006805383/10000000000 : ℝ), (5131237847/10000000000 : ℝ), (5424064413/10000000000 : ℝ)] ![(312883176537/2500000000000 : ℝ), (42172332613877/100000000000000 : ℝ), (22656170152963/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2006805383/10000000000 : ℝ)|^4507 ≤ (312883176537/2500000000000 : ℝ)^3483
        have hw : |(-2006805383/10000000000 : ℝ)|=(2006805383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5131237847/10000000000 : ℝ)|^4507 ≤ (42172332613877/100000000000000 : ℝ)^3483
        have hw : |(5131237847/10000000000 : ℝ)|=(5131237847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5424064413/10000000000 : ℝ)|^4507 ≤ (22656170152963/50000000000000 : ℝ)^3483
        have hw : |(5424064413/10000000000 : ℝ)|=(5424064413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1505_box_9 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (525641249/1000000000 : ℝ)*x 0 + (-1839154083/10000000000 : ℝ)*x 1 + (2712032167/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (525641249/1000000000 : ℝ)^4507 ≤ (43508317978987/100000000000000 : ℝ)^3483 := by
    have hnat : (525641249 : ℕ)^4507*100000000000000^3483 ≤ 43508317978987^3483*1000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525641249 1000000000 43508317978987 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1839154083/10000000000 : ℝ)^4507 ≤ (11179342554827/100000000000000 : ℝ)^3483 := by
    have hnat : (1839154083 : ℕ)^4507*100000000000000^3483 ≤ 11179342554827^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1839154083 10000000000 11179342554827 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2712032167/5000000000 : ℝ)^4507 ≤ (1416010607873/3125000000000 : ℝ)^3483 := by
    have hnat : (2712032167 : ℕ)^4507*3125000000000^3483 ≤ 1416010607873^3483*5000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712032167 5000000000 1416010607873 3125000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(525641249/1000000000 : ℝ), (-1839154083/10000000000 : ℝ), (2712032167/5000000000 : ℝ)] ![(43508317978987/100000000000000 : ℝ), (11179342554827/100000000000000 : ℝ), (1416010607873/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(525641249/1000000000 : ℝ)|^4507 ≤ (43508317978987/100000000000000 : ℝ)^3483
        have hw : |(525641249/1000000000 : ℝ)|=(525641249/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1839154083/10000000000 : ℝ)|^4507 ≤ (11179342554827/100000000000000 : ℝ)^3483
        have hw : |(-1839154083/10000000000 : ℝ)|=(1839154083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2712032167/5000000000 : ℝ)|^4507 ≤ (1416010607873/3125000000000 : ℝ)^3483
        have hw : |(2712032167/5000000000 : ℝ)|=(2712032167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1505_box_10 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1314103139/2500000000 : ℝ)*x 0 + (5424064921/10000000000 : ℝ)*x 1 + (-459788297/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1314103139/2500000000 : ℝ)^4507 ≤ (43508318685891/100000000000000 : ℝ)^3483 := by
    have hnat : (1314103139 : ℕ)^4507*100000000000000^3483 ≤ 43508318685891^3483*2500000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314103139 2500000000 43508318685891 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5424064921/10000000000 : ℝ)^4507 ≤ (22656172898703/50000000000000 : ℝ)^3483 := by
    have hnat : (5424064921 : ℕ)^4507*50000000000000^3483 ≤ 22656172898703^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424064921 10000000000 22656172898703 50000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (459788297/2500000000 : ℝ)^4507 ≤ (1117933551511/10000000000000 : ℝ)^3483 := by
    have hnat : (459788297 : ℕ)^4507*10000000000000^3483 ≤ 1117933551511^3483*2500000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      459788297 2500000000 1117933551511 10000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1314103139/2500000000 : ℝ), (5424064921/10000000000 : ℝ), (-459788297/2500000000 : ℝ)] ![(43508318685891/100000000000000 : ℝ), (22656172898703/50000000000000 : ℝ), (1117933551511/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1314103139/2500000000 : ℝ)|^4507 ≤ (43508318685891/100000000000000 : ℝ)^3483
        have hw : |(1314103139/2500000000 : ℝ)|=(1314103139/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5424064921/10000000000 : ℝ)|^4507 ≤ (22656172898703/50000000000000 : ℝ)^3483
        have hw : |(5424064921/10000000000 : ℝ)|=(5424064921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-459788297/2500000000 : ℝ)|^4507 ≤ (1117933551511/10000000000000 : ℝ)^3483
        have hw : |(-459788297/2500000000 : ℝ)|=(459788297/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1505_box_11 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4527568419/10000000000 : ℝ)*x 0 + (4152217659/10000000000 : ℝ)*x 1 + (4152217101/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4527568419/10000000000 : ℝ)^4507 ≤ (448331804861/1250000000000 : ℝ)^3483 := by
    have hnat : (4527568419 : ℕ)^4507*1250000000000^3483 ≤ 448331804861^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4527568419 10000000000 448331804861 1250000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4152217659/10000000000 : ℝ)^4507 ≤ (8016682646161/25000000000000 : ℝ)^3483 := by
    have hnat : (4152217659 : ℕ)^4507*25000000000000^3483 ≤ 8016682646161^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4152217659 10000000000 8016682646161 25000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4152217101/10000000000 : ℝ)^4507 ≤ (32066725008387/100000000000000 : ℝ)^3483 := by
    have hnat : (4152217101 : ℕ)^4507*100000000000000^3483 ≤ 32066725008387^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4152217101 10000000000 32066725008387 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4527568419/10000000000 : ℝ), (4152217659/10000000000 : ℝ), (4152217101/10000000000 : ℝ)] ![(448331804861/1250000000000 : ℝ), (8016682646161/25000000000000 : ℝ), (32066725008387/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4527568419/10000000000 : ℝ)|^4507 ≤ (448331804861/1250000000000 : ℝ)^3483
        have hw : |(4527568419/10000000000 : ℝ)|=(4527568419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4152217659/10000000000 : ℝ)|^4507 ≤ (8016682646161/25000000000000 : ℝ)^3483
        have hw : |(4152217659/10000000000 : ℝ)|=(4152217659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4152217101/10000000000 : ℝ)|^4507 ≤ (32066725008387/100000000000000 : ℝ)^3483
        have hw : |(4152217101/10000000000 : ℝ)|=(4152217101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1505_box_12 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1755442527/10000000000 : ℝ)*x 0 + (5512115471/10000000000 : ℝ)*x 1 + (1045674207/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1755442527/10000000000 : ℝ)^4507 ≤ (657834629009/6250000000000 : ℝ)^3483 := by
    have hnat : (1755442527 : ℕ)^4507*6250000000000^3483 ≤ 657834629009^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1755442527 10000000000 657834629009 6250000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5512115471/10000000000 : ℝ)^4507 ≤ (578330438577/1250000000000 : ℝ)^3483 := by
    have hnat : (5512115471 : ℕ)^4507*1250000000000^3483 ≤ 578330438577^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5512115471 10000000000 578330438577 1250000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1045674207/2000000000 : ℝ)^4507 ≤ (43208210826289/100000000000000 : ℝ)^3483 := by
    have hnat : (1045674207 : ℕ)^4507*100000000000000^3483 ≤ 43208210826289^3483*2000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045674207 2000000000 43208210826289 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1755442527/10000000000 : ℝ), (5512115471/10000000000 : ℝ), (1045674207/2000000000 : ℝ)] ![(657834629009/6250000000000 : ℝ), (578330438577/1250000000000 : ℝ), (43208210826289/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1755442527/10000000000 : ℝ)|^4507 ≤ (657834629009/6250000000000 : ℝ)^3483
        have hw : |(-1755442527/10000000000 : ℝ)|=(1755442527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5512115471/10000000000 : ℝ)|^4507 ≤ (578330438577/1250000000000 : ℝ)^3483
        have hw : |(5512115471/10000000000 : ℝ)|=(5512115471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1045674207/2000000000 : ℝ)|^4507 ≤ (43208210826289/100000000000000 : ℝ)^3483
        have hw : |(1045674207/2000000000 : ℝ)|=(1045674207/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1505_box_13 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5392738113/10000000000 : ℝ)*x 0 + (-1919809703/10000000000 : ℝ)*x 1 + (2614185611/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5392738113/10000000000 : ℝ)^4507 ≤ (44973990858313/100000000000000 : ℝ)^3483 := by
    have hnat : (5392738113 : ℕ)^4507*100000000000000^3483 ≤ 44973990858313^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392738113 10000000000 44973990858313 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1919809703/10000000000 : ℝ)^4507 ≤ (5908898144643/50000000000000 : ℝ)^3483 := by
    have hnat : (1919809703 : ℕ)^4507*50000000000000^3483 ≤ 5908898144643^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1919809703 10000000000 5908898144643 50000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2614185611/5000000000 : ℝ)^4507 ≤ (21604106413019/50000000000000 : ℝ)^3483 := by
    have hnat : (2614185611 : ℕ)^4507*50000000000000^3483 ≤ 21604106413019^3483*5000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614185611 5000000000 21604106413019 50000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5392738113/10000000000 : ℝ), (-1919809703/10000000000 : ℝ), (2614185611/5000000000 : ℝ)] ![(44973990858313/100000000000000 : ℝ), (5908898144643/50000000000000 : ℝ), (21604106413019/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5392738113/10000000000 : ℝ)|^4507 ≤ (44973990858313/100000000000000 : ℝ)^3483
        have hw : |(5392738113/10000000000 : ℝ)|=(5392738113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1919809703/10000000000 : ℝ)|^4507 ≤ (5908898144643/50000000000000 : ℝ)^3483
        have hw : |(-1919809703/10000000000 : ℝ)|=(1919809703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2614185611/5000000000 : ℝ)|^4507 ≤ (21604106413019/50000000000000 : ℝ)^3483
        have hw : |(2614185611/5000000000 : ℝ)|=(2614185611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1505_box_14 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5392738139/10000000000 : ℝ)*x 0 + (2614185613/5000000000 : ℝ)*x 1 + (-1919809663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5392738139/10000000000 : ℝ)^4507 ≤ (8994798227779/20000000000000 : ℝ)^3483 := by
    have hnat : (5392738139 : ℕ)^4507*20000000000000^3483 ≤ 8994798227779^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392738139 10000000000 8994798227779 20000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2614185613/5000000000 : ℝ)^4507 ≤ (21604106434407/50000000000000 : ℝ)^3483 := by
    have hnat : (2614185613 : ℕ)^4507*50000000000000^3483 ≤ 21604106434407^3483*5000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614185613 5000000000 21604106434407 50000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1919809663/10000000000 : ℝ)^4507 ≤ (11817795970667/100000000000000 : ℝ)^3483 := by
    have hnat : (1919809663 : ℕ)^4507*100000000000000^3483 ≤ 11817795970667^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1919809663 10000000000 11817795970667 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5392738139/10000000000 : ℝ), (2614185613/5000000000 : ℝ), (-1919809663/10000000000 : ℝ)] ![(8994798227779/20000000000000 : ℝ), (21604106434407/50000000000000 : ℝ), (11817795970667/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5392738139/10000000000 : ℝ)|^4507 ≤ (8994798227779/20000000000000 : ℝ)^3483
        have hw : |(5392738139/10000000000 : ℝ)|=(5392738139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2614185613/5000000000 : ℝ)|^4507 ≤ (21604106434407/50000000000000 : ℝ)^3483
        have hw : |(2614185613/5000000000 : ℝ)|=(2614185613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1919809663/10000000000 : ℝ)|^4507 ≤ (11817795970667/100000000000000 : ℝ)^3483
        have hw : |(-1919809663/10000000000 : ℝ)|=(1919809663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1505_box_15 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4028048963/10000000000 : ℝ)*x 0 + (2200983701/5000000000 : ℝ)*x 1 + (4401967187/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4028048963/10000000000 : ℝ)^4507 ≤ (385392123627/1250000000000 : ℝ)^3483 := by
    have hnat : (4028048963 : ℕ)^4507*1250000000000^3483 ≤ 385392123627^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4028048963 10000000000 385392123627 1250000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2200983701/5000000000 : ℝ)^4507 ≤ (6916863227691/20000000000000 : ℝ)^3483 := by
    have hnat : (2200983701 : ℕ)^4507*20000000000000^3483 ≤ 6916863227691^3483*5000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2200983701 5000000000 6916863227691 20000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4401967187/10000000000 : ℝ)^4507 ≤ (34584313952683/100000000000000 : ℝ)^3483 := by
    have hnat : (4401967187 : ℕ)^4507*100000000000000^3483 ≤ 34584313952683^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4401967187 10000000000 34584313952683 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4028048963/10000000000 : ℝ), (2200983701/5000000000 : ℝ), (4401967187/10000000000 : ℝ)] ![(385392123627/1250000000000 : ℝ), (6916863227691/20000000000000 : ℝ), (34584313952683/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4028048963/10000000000 : ℝ)|^4507 ≤ (385392123627/1250000000000 : ℝ)^3483
        have hw : |(4028048963/10000000000 : ℝ)|=(4028048963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2200983701/5000000000 : ℝ)|^4507 ≤ (6916863227691/20000000000000 : ℝ)^3483
        have hw : |(2200983701/5000000000 : ℝ)|=(2200983701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4401967187/10000000000 : ℝ)|^4507 ≤ (34584313952683/100000000000000 : ℝ)^3483
        have hw : |(4401967187/10000000000 : ℝ)|=(4401967187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1505_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162820231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15481/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10889/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(6373/10000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(11719/20000 : ℝ) ∧ (20061/25000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (85957/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15481/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10889/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15481/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10889/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15481/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10889/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15481/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10889/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15481/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10889/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15481/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10889/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10889/100000 : ℝ) ^ (4505/1024 : ℝ) ≤ (5798443839653727/100000000000000000000 : ℝ) := by
    have hpowers : (10889/100000 : ℝ)^4505 ≤ (5798443839653727/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10889 : ℕ)^4505*100000000000000000000^1024 ≤ 5798443839653727^1024*100000^4505 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10889 100000 5798443839653727 100000000000000000000 4505 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10889/100000 : ℝ)) (X := (5798443839653727/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4505 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15481/100000 : ℝ) ^ (4505/1024 : ℝ) ≤ (27264050276859257/100000000000000000000 : ℝ) := by
    have hpowers : (15481/100000 : ℝ)^4505 ≤ (27264050276859257/100000000000000000000 : ℝ)^1024 := by
      have hnat : (15481 : ℕ)^4505*100000000000000000000^1024 ≤ 27264050276859257^1024*100000^4505 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15481 100000 27264050276859257 100000000000000000000 4505 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15481/100000 : ℝ)) (X := (27264050276859257/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4505 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005798443839653727/50000000000000000000 : ℝ) ≤ (2500065897230623/2500000000000000 : ℝ) ^ (4505/1024 : ℝ) := by
    have hpowers : (50005798443839653727/50000000000000000000 : ℝ)^1024 ≤ (2500065897230623/2500000000000000 : ℝ)^4505 := by
      have hnat : (50005798443839653727 : ℕ)^1024*2500000000000000^4505 ≤ 2500065897230623^4505*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005798443839653727 50000000000000000000 2500065897230623 2500000000000000 1024 4505 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500065897230623/2500000000000000 : ℝ)) (X := (50005798443839653727/50000000000000000000 : ℝ)) (by norm_num) 4505 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12504132811764564123/12500000000000000000 : ℝ) ≤ (1000075142442121/1000000000000000 : ℝ) ^ (4505/1024 : ℝ) := by
    have hpowers : (12504132811764564123/12500000000000000000 : ℝ)^1024 ≤ (1000075142442121/1000000000000000 : ℝ)^4505 := by
      have hnat : (12504132811764564123 : ℕ)^1024*1000000000000000^4505 ≤ 1000075142442121^4505*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12504132811764564123 12500000000000000000 1000075142442121 1000000000000000 1024 4505 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000075142442121/1000000000000000 : ℝ)) (X := (12504132811764564123/12500000000000000000 : ℝ)) (by norm_num) 4505 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50027264050276859257/50000000000000000000 : ℝ) ≤ (1250154907489991/1250000000000000 : ℝ) ^ (4505/1024 : ℝ) := by
    have hpowers : (50027264050276859257/50000000000000000000 : ℝ)^1024 ≤ (1250154907489991/1250000000000000 : ℝ)^4505 := by
      have hnat : (50027264050276859257 : ℕ)^1024*1250000000000000^4505 ≤ 1250154907489991^4505*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027264050276859257 50000000000000000000 1250154907489991 1250000000000000 1024 4505 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250154907489991/1250000000000000 : ℝ)) (X := (50027264050276859257/50000000000000000000 : ℝ)) (by norm_num) 4505 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5798443839653727/100000000000000000000 : ℝ) ≤ ((55988519901025613/56000000000000000 : ℝ)+2*(5949213399/5600000000000 : ℝ)*(10889/100000 : ℝ))^(4505/1024 : ℝ) := by
    rw [show (55988519901025613/56000000000000000 : ℝ)+2*(5949213399/5600000000000 : ℝ)*(10889/100000 : ℝ)=(2500065897230623/2500000000000000 : ℝ) by norm_num, show 1+2*(5798443839653727/100000000000000000000 : ℝ)=(50005798443839653727/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27264050276859257/100000000000000000000 : ℝ)+(5798443839653727/100000000000000000000 : ℝ) ≤ ((55988519901025613/56000000000000000 : ℝ)+(5949213399/5600000000000 : ℝ)*((15481/100000 : ℝ)+(10889/100000 : ℝ)))^(4505/1024 : ℝ) := by
    rw [show (55988519901025613/56000000000000000 : ℝ)+(5949213399/5600000000000 : ℝ)*((15481/100000 : ℝ)+(10889/100000 : ℝ))=(1000075142442121/1000000000000000 : ℝ) by norm_num, show 1+(27264050276859257/100000000000000000000 : ℝ)+(5798443839653727/100000000000000000000 : ℝ)=(12504132811764564123/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27264050276859257/100000000000000000000 : ℝ) ≤ ((55988519901025613/56000000000000000 : ℝ)+2*(5949213399/5600000000000 : ℝ)*(15481/100000 : ℝ))^(4505/1024 : ℝ) := by
    rw [show (55988519901025613/56000000000000000 : ℝ)+2*(5949213399/5600000000000 : ℝ)*(15481/100000 : ℝ)=(1250154907489991/1250000000000000 : ℝ) by norm_num, show 1+2*(27264050276859257/100000000000000000000 : ℝ)=(50027264050276859257/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (55988519901025613/56000000000000000 : ℝ)*(X 1 0+X 2 0)+(5949213399/5600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4505/1024 : ℝ)) (lo := (10889/100000 : ℝ)) (hi := (15481/100000 : ℝ)) (c := (55988519901025613/56000000000000000 : ℝ)) (alpha := (5949213399/5600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (55988519901025613/56000000000000000 : ℝ)*(X 0 1+X 2 1)+(5949213399/5600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4505/1024 : ℝ)) (lo := (10889/100000 : ℝ)) (hi := (15481/100000 : ℝ)) (c := (55988519901025613/56000000000000000 : ℝ)) (alpha := (5949213399/5600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (55988519901025613/56000000000000000 : ℝ)*(X 0 2+X 1 2)+(5949213399/5600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4505/1024 : ℝ)) (lo := (10889/100000 : ℝ)) (hi := (15481/100000 : ℝ)) (c := (55988519901025613/56000000000000000 : ℝ)) (alpha := (5949213399/5600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1663519771/10000000000 : ℝ)*X 0 0+(5403590607/10000000000 : ℝ)*X 0 1+(2701795183/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2635340503/5000000000 : ℝ)*X 1 0+(-461958191/2500000000 : ℝ)*X 1 1+(2701795363/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1317670139/2500000000 : ℝ)*X 2 0+(5403590943/10000000000 : ℝ)*X 2 1+(-1847833079/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1119107167/2500000000 : ℝ)*X 0 0+(522297331/1250000000 : ℝ)*X 0 1+(4178378009/10000000000 : ℝ)*X 0 2+(1119107167/2500000000 : ℝ)*X 1 0+(522297331/1250000000 : ℝ)*X 1 1+(4178378009/10000000000 : ℝ)*X 1 2+(1119107167/2500000000 : ℝ)*X 2 0+(522297331/1250000000 : ℝ)*X 2 1+(4178378009/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-524685189/2500000000 : ℝ)*X 0 0+(5243391617/10000000000 : ℝ)*X 0 1+(2621695923/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((538227533/1000000000 : ℝ)*X 1 0+(-119612741/625000000 : ℝ)*X 1 1+(5243391799/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2691137637/5000000000 : ℝ)*X 2 0+(524339191/1000000000 : ℝ)*X 2 1+(-1913803781/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2033636421/5000000000 : ℝ)*X 0 0+(4382821027/10000000000 : ℝ)*X 0 1+(4382821029/10000000000 : ℝ)*X 0 2+(2033636421/5000000000 : ℝ)*X 1 0+(4382821027/10000000000 : ℝ)*X 1 1+(4382821029/10000000000 : ℝ)*X 1 2+(2033636421/5000000000 : ℝ)*X 2 0+(4382821027/10000000000 : ℝ)*X 2 1+(4382821029/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2006805383/10000000000 : ℝ)*X 0 0+(5131237847/10000000000 : ℝ)*X 0 1+(5424064413/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((525641249/1000000000 : ℝ)*X 1 0+(-1839154083/10000000000 : ℝ)*X 1 1+(2712032167/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1314103139/2500000000 : ℝ)*X 2 0+(5424064921/10000000000 : ℝ)*X 2 1+(-459788297/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4527568419/10000000000 : ℝ)*X 0 0+(4152217659/10000000000 : ℝ)*X 0 1+(4152217101/10000000000 : ℝ)*X 0 2+(4527568419/10000000000 : ℝ)*X 1 0+(4152217659/10000000000 : ℝ)*X 1 1+(4152217101/10000000000 : ℝ)*X 1 2+(4527568419/10000000000 : ℝ)*X 2 0+(4152217659/10000000000 : ℝ)*X 2 1+(4152217101/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1755442527/10000000000 : ℝ)*X 0 0+(5512115471/10000000000 : ℝ)*X 0 1+(1045674207/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5392738113/10000000000 : ℝ)*X 1 0+(-1919809703/10000000000 : ℝ)*X 1 1+(2614185611/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5392738139/10000000000 : ℝ)*X 2 0+(2614185613/5000000000 : ℝ)*X 2 1+(-1919809663/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4028048963/10000000000 : ℝ)*X 0 0+(2200983701/5000000000 : ℝ)*X 0 1+(4401967187/10000000000 : ℝ)*X 0 2+(4028048963/10000000000 : ℝ)*X 1 0+(2200983701/5000000000 : ℝ)*X 1 1+(4401967187/10000000000 : ℝ)*X 1 2+(4028048963/10000000000 : ℝ)*X 2 0+(2200983701/5000000000 : ℝ)*X 2 1+(4401967187/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-6373/10000 : ℝ) ≤ (-1784379454937170976015231620773/2800000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10417967/100000000000000 : ℝ)*(upper1) + (1739263/100000000000000 : ℝ)*(lower2) + (1431543/6250000000000 : ℝ)*(upper5) + (2213041566338893/100000000000000 : ℝ)*(major0) + (2213041566338893/100000000000000 : ℝ)*(major1) + (2213041566338893/100000000000000 : ℝ)*(major2) + (54571527/50000000000000 : ℝ)*(sp1) + (267900279/50000000000000 : ℝ)*(sp3) + (193008184147729/6250000000000 : ℝ)*(sp4) + (617626480049739/20000000000000 : ℝ)*(sp5) + (308811548266903/10000000000000 : ℝ)*(sp6) + (1359192700044251/100000000000000 : ℝ)*(sp7) + (312605617/20000000000000 : ℝ)*(sp12) + (17026722719/100000000000000 : ℝ)*(sp14) + (1359193235844809/100000000000000 : ℝ)*(f.failure) + (3088132509391749/100000000000000 : ℝ)*(f.sum) + (225839581347/280000000000000000000000000 : ℝ)*base65 + (51471538366263591/5600000000000000000000000000000 : ℝ)*base68 + (30957763607863591/5600000000000000000000000000000 : ℝ)*base70 + (13630074151863591/5600000000000000000000000000000 : ℝ)*base72 + (298837015507/280000000000000000000000000 : ℝ)*base73 + (15794576768136409/5600000000000000000000000000000 : ℝ)*base75 + (8737347920936409/5600000000000000000000000000000 : ℝ)*base77 + (11278227563863591/5600000000000000000000000000000 : ℝ)*base80 + (1062037218587/280000000000000000000000000 : ℝ)*base81 + (18469121/10000000000000000000000 : ℝ)*base90 + (18469121/10000000000000000000000 : ℝ)*base92 + (18469121/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (11719/20000 : ℝ) ≤ (58597211512168036461532523091/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (38840033/50000000000000 : ℝ)*(lower0) + (55414089/50000000000000 : ℝ)*(upper2) + (4111741/4000000000000 : ℝ)*(upper3) + (26993973/100000000000000 : ℝ)*(lower5) + (1144403811221083/50000000000000 : ℝ)*(major0) + (1144403811221083/50000000000000 : ℝ)*(major1) + (1144403811221083/50000000000000 : ℝ)*(major2) + (315235604138273/10000000000000 : ℝ)*(sp0) + (197022210875419/6250000000000 : ℝ)*(sp1) + (3152352593604723/100000000000000 : ℝ)*(sp2) + (702858721953339/50000000000000 : ℝ)*(sp3) + (667376027/100000000000000 : ℝ)*(sp5) + (3447778007/100000000000000 : ℝ)*(sp6) + (1169469691/12500000000000 : ℝ)*(sp11) + (281145359932841/20000000000000 : ℝ)*(f.failure) + (315235604138273/10000000000000 : ℝ)*(f.sum) + (82753267389/20000000000000000000000000 : ℝ)*base66 + (510234948147303/400000000000000000000000000000 : ℝ)*base68 + (1498912629747303/400000000000000000000000000000 : ℝ)*base70 + (4019521293747303/400000000000000000000000000000 : ℝ)*base72 + (171546932171/20000000000000000000000000 : ℝ)*base73 + (4247092828547303/400000000000000000000000000000 : ℝ)*base76 + (1594716002547303/400000000000000000000000000000 : ℝ)*base78 + (615953032252697/400000000000000000000000000000 : ℝ)*base79 + (57594378189/20000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (3893729/2000000000000000000000 : ℝ)*base90 + (3893729/2000000000000000000000 : ℝ)*base92 + (3893729/2000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (20061/25000 : ℝ) ≤ (561723284370970043376808773909/700000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (28932859/20000000000000 : ℝ)*(lower3) + (63765971/25000000000000 : ℝ)*(upper4) + (16400061/25000000000000 : ℝ)*(lower5) + (1241767690592869/50000000000000 : ℝ)*(major0) + (1241767690592869/50000000000000 : ℝ)*(major1) + (1241767690592869/50000000000000 : ℝ)*(major2) + (250580707/50000000000000 : ℝ)*(sp0) + (7247860719/12500000000000 : ℝ)*(sp1) + (110477245571/50000000000000 : ℝ)*(sp2) + (81733661887/100000000000000 : ℝ)*(sp3) + (3414997950476427/100000000000000 : ℝ)*(sp8) + (426867558594011/12500000000000 : ℝ)*(sp9) + (1707388748573349/50000000000000 : ℝ)*(sp10) + (30504836984891/2000000000000 : ℝ)*(sp11) + (1525323582906437/100000000000000 : ℝ)*(f.failure) + (42687480645473/1250000000000 : ℝ)*(f.sum) + (905931819391/140000000000000000000000000 : ℝ)*base65 + (3385939298936303/2800000000000000000000000000000 : ℝ)*base68 + (8486748899063697/2800000000000000000000000000000 : ℝ)*base69 + (25838555567063697/2800000000000000000000000000000 : ℝ)*base71 + (1058719423429/140000000000000000000000000 : ℝ)*base74 + (20677569585863697/2800000000000000000000000000000 : ℝ)*base75 + (13676561224663697/2800000000000000000000000000000 : ℝ)*base77 + (27098397669463697/2800000000000000000000000000000 : ℝ)*base79 + (268487981009/140000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (76273053/10000000000000000000000 : ℝ)*base90 + (76273053/10000000000000000000000 : ℝ)*base92 + (76273053/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-85957/100000 : ℝ) ≤ (-85954247726251802944243740591/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (38738579/100000000000000 : ℝ)*(lower0) + (366527/4000000000000 : ℝ)*(lower2) + (47002953/100000000000000 : ℝ)*(upper3) + (66530739/100000000000000 : ℝ)*(upper5) + (1261214336221417/50000000000000 : ℝ)*(major0) + (1261214336221417/50000000000000 : ℝ)*(major1) + (1261214336221417/50000000000000 : ℝ)*(major2) + (271842339/100000000000000 : ℝ)*(sp0) + (2224858237/100000000000000 : ℝ)*(sp7) + (722467681/100000000000000 : ℝ)*(sp8) + (1762148461989959/50000000000000 : ℝ)*(sp12) + (1762148959144969/50000000000000 : ℝ)*(sp13) + (1762148959144969/50000000000000 : ℝ)*(sp14) + (1549208617646239/100000000000000 : ℝ)*(sp15) + (387302710626119/25000000000000 : ℝ)*(f.failure) + (1762148959144969/50000000000000 : ℝ)*(f.sum) + (915924963763/140000000000000000000000000 : ℝ)*base65 + (17935239398016379/2800000000000000000000000000000 : ℝ)*base68 + (2385344555583621/2800000000000000000000000000000 : ℝ)*base69 + (31361833754016379/2800000000000000000000000000000 : ℝ)*base72 + (227689677563/140000000000000000000000000 : ℝ)*base73 + (17081506425616379/2800000000000000000000000000000 : ℝ)*base76 + (19813341240416379/2800000000000000000000000000000 : ℝ)*base78 + (8069663482016379/2800000000000000000000000000000 : ℝ)*base80 + (453457512303/140000000000000000000000000 : ℝ)*base81 + (213489/2500000000000000000000 : ℝ)*base89 + (213489/2500000000000000000000 : ℝ)*base91 + (213489/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1505_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162820231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15481/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10889/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(6373/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(11719/20000 : ℝ) else (20061/25000 : ℝ) ≤ X j i ∧ X j i ≤ (85957/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1505_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1505_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162820231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1361/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(6373/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(11719/20000 : ℝ) else (20061/25000 : ℝ) ≤ X j i ∧ X j i ≤ (85957/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1505_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1505_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162820231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1361/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(6373/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(11719/20000 : ℝ) else (20061/25000 : ℝ) ≤ X j i ∧ X j i ≤ (85957/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1505_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
