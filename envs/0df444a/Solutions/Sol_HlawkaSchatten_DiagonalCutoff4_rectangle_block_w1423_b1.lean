-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1423_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:52:11.196576+00:00
-- url     : https://prove2.me/submissions/c1b9ee58-ef74-44fe-8fd5-6374d4c154c8

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
theorem support_rectangle_w1423_s3_0 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-493728659/2500000000 : ℝ)*x 0 + (5417891687/10000000000 : ℝ)*x 1 + (1309532059/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (493728659/2500000000 : ℝ)^4383 ≤ (12044655426967/100000000000000 : ℝ)^3359 := by
    have hnat : (493728659 : ℕ)^4383*100000000000000^3359 ≤ 12044655426967^3359*2500000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      493728659 2500000000 12044655426967 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5417891687/10000000000 : ℝ)^4383 ≤ (44945662859959/100000000000000 : ℝ)^3359 := by
    have hnat : (5417891687 : ℕ)^4383*100000000000000^3359 ≤ 44945662859959^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417891687 10000000000 44945662859959 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1309532059/2500000000 : ℝ)^4383 ≤ (43009681700811/100000000000000 : ℝ)^3359 := by
    have hnat : (1309532059 : ℕ)^4383*100000000000000^3359 ≤ 43009681700811^3359*2500000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1309532059 2500000000 43009681700811 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-493728659/2500000000 : ℝ), (5417891687/10000000000 : ℝ), (1309532059/2500000000 : ℝ)] ![(12044655426967/100000000000000 : ℝ), (44945662859959/100000000000000 : ℝ), (43009681700811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-493728659/2500000000 : ℝ)|^4383 ≤ (12044655426967/100000000000000 : ℝ)^3359
        have hw : |(-493728659/2500000000 : ℝ)|=(493728659/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5417891687/10000000000 : ℝ)|^4383 ≤ (44945662859959/100000000000000 : ℝ)^3359
        have hw : |(5417891687/10000000000 : ℝ)|=(5417891687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1309532059/2500000000 : ℝ)|^4383 ≤ (43009681700811/100000000000000 : ℝ)^3359
        have hw : |(1309532059/2500000000 : ℝ)|=(1309532059/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_s3_1 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349868243/10000000000 : ℝ)*x 0 + (-1033311077/5000000000 : ℝ)*x 1 + (2619064101/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349868243/10000000000 : ℝ)^4383 ≤ (22105368790767/50000000000000 : ℝ)^3359 := by
    have hnat : (5349868243 : ℕ)^4383*50000000000000^3359 ≤ 22105368790767^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349868243 10000000000 22105368790767 50000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1033311077/5000000000 : ℝ)^4383 ≤ (2555916212041/20000000000000 : ℝ)^3359 := by
    have hnat : (1033311077 : ℕ)^4383*20000000000000^3359 ≤ 2555916212041^3359*5000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033311077 5000000000 2555916212041 20000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2619064101/5000000000 : ℝ)^4383 ≤ (8601936267307/20000000000000 : ℝ)^3359 := by
    have hnat : (2619064101 : ℕ)^4383*20000000000000^3359 ≤ 8601936267307^3359*5000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2619064101 5000000000 8601936267307 20000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349868243/10000000000 : ℝ), (-1033311077/5000000000 : ℝ), (2619064101/5000000000 : ℝ)] ![(22105368790767/50000000000000 : ℝ), (2555916212041/20000000000000 : ℝ), (8601936267307/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349868243/10000000000 : ℝ)|^4383 ≤ (22105368790767/50000000000000 : ℝ)^3359
        have hw : |(5349868243/10000000000 : ℝ)|=(5349868243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1033311077/5000000000 : ℝ)|^4383 ≤ (2555916212041/20000000000000 : ℝ)^3359
        have hw : |(-1033311077/5000000000 : ℝ)|=(1033311077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2619064101/5000000000 : ℝ)|^4383 ≤ (8601936267307/20000000000000 : ℝ)^3359
        have hw : |(2619064101/5000000000 : ℝ)|=(2619064101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_s3_2 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (167183383/312500000 : ℝ)*x 0 + (5238128203/10000000000 : ℝ)*x 1 + (-258327767/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167183383/312500000 : ℝ)^4383 ≤ (8842147544343/20000000000000 : ℝ)^3359 := by
    have hnat : (167183383 : ℕ)^4383*20000000000000^3359 ≤ 8842147544343^3359*312500000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167183383 312500000 8842147544343 20000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5238128203/10000000000 : ℝ)^4383 ≤ (43009681347249/100000000000000 : ℝ)^3359 := by
    have hnat : (5238128203 : ℕ)^4383*100000000000000^3359 ≤ 43009681347249^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5238128203 10000000000 43009681347249 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (258327767/1250000000 : ℝ)^4383 ≤ (3194895228741/25000000000000 : ℝ)^3359 := by
    have hnat : (258327767 : ℕ)^4383*25000000000000^3359 ≤ 3194895228741^3359*1250000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258327767 1250000000 3194895228741 25000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167183383/312500000 : ℝ), (5238128203/10000000000 : ℝ), (-258327767/1250000000 : ℝ)] ![(8842147544343/20000000000000 : ℝ), (43009681347249/100000000000000 : ℝ), (3194895228741/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167183383/312500000 : ℝ)|^4383 ≤ (8842147544343/20000000000000 : ℝ)^3359
        have hw : |(167183383/312500000 : ℝ)|=(167183383/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5238128203/10000000000 : ℝ)|^4383 ≤ (43009681347249/100000000000000 : ℝ)^3359
        have hw : |(5238128203/10000000000 : ℝ)|=(5238128203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-258327767/1250000000 : ℝ)|^4383 ≤ (3194895228741/25000000000000 : ℝ)^3359
        have hw : |(-258327767/1250000000 : ℝ)|=(258327767/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_s3_3 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4305207377/10000000000 : ℝ)*x 0 + (411513163/1000000000 : ℝ)*x 1 + (562895653/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4305207377/10000000000 : ℝ)^4383 ≤ (1664892549383/5000000000000 : ℝ)^3359 := by
    have hnat : (4305207377 : ℕ)^4383*5000000000000^3359 ≤ 1664892549383^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4305207377 10000000000 1664892549383 5000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (411513163/1000000000 : ℝ)^4383 ≤ (392407779801/1250000000000 : ℝ)^3359 := by
    have hnat : (411513163 : ℕ)^4383*1250000000000^3359 ≤ 392407779801^3359*1000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      411513163 1000000000 392407779801 1250000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (562895653/1250000000 : ℝ)^4383 ≤ (35309526618607/100000000000000 : ℝ)^3359 := by
    have hnat : (562895653 : ℕ)^4383*100000000000000^3359 ≤ 35309526618607^3359*1250000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562895653 1250000000 35309526618607 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4305207377/10000000000 : ℝ), (411513163/1000000000 : ℝ), (562895653/1250000000 : ℝ)] ![(1664892549383/5000000000000 : ℝ), (392407779801/1250000000000 : ℝ), (35309526618607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4305207377/10000000000 : ℝ)|^4383 ≤ (1664892549383/5000000000000 : ℝ)^3359
        have hw : |(4305207377/10000000000 : ℝ)|=(4305207377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(411513163/1000000000 : ℝ)|^4383 ≤ (392407779801/1250000000000 : ℝ)^3359
        have hw : |(411513163/1000000000 : ℝ)|=(411513163/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(562895653/1250000000 : ℝ)|^4383 ≤ (35309526618607/100000000000000 : ℝ)^3359
        have hw : |(562895653/1250000000 : ℝ)|=(562895653/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_s3_4 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-15799441/80000000 : ℝ)*x 0 + (2619423927/5000000000 : ℝ)*x 1 + (338573001/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (15799441/80000000 : ℝ)^4383 ≤ (6022389344797/50000000000000 : ℝ)^3359 := by
    have hnat : (15799441 : ℕ)^4383*50000000000000^3359 ≤ 6022389344797^3359*80000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15799441 80000000 6022389344797 50000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2619423927/5000000000 : ℝ)^4383 ≤ (10754347962053/25000000000000 : ℝ)^3359 := by
    have hnat : (2619423927 : ℕ)^4383*25000000000000^3359 ≤ 10754347962053^3359*5000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2619423927 5000000000 10754347962053 25000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (338573001/625000000 : ℝ)^4383 ≤ (2246891472131/5000000000000 : ℝ)^3359 := by
    have hnat : (338573001 : ℕ)^4383*5000000000000^3359 ≤ 2246891472131^3359*625000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338573001 625000000 2246891472131 5000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-15799441/80000000 : ℝ), (2619423927/5000000000 : ℝ), (338573001/625000000 : ℝ)] ![(6022389344797/50000000000000 : ℝ), (10754347962053/25000000000000 : ℝ), (2246891472131/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-15799441/80000000 : ℝ)|^4383 ≤ (6022389344797/50000000000000 : ℝ)^3359
        have hw : |(-15799441/80000000 : ℝ)|=(15799441/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2619423927/5000000000 : ℝ)|^4383 ≤ (10754347962053/25000000000000 : ℝ)^3359
        have hw : |(2619423927/5000000000 : ℝ)|=(2619423927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(338573001/625000000 : ℝ)|^4383 ≤ (2246891472131/5000000000000 : ℝ)^3359
        have hw : |(338573001/625000000 : ℝ)|=(338573001/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_s3_5 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2651581469/5000000000 : ℝ)*x 0 + (-1887582263/10000000000 : ℝ)*x 1 + (1354292007/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651581469/5000000000 : ℝ)^4383 ≤ (8741555649101/20000000000000 : ℝ)^3359 := by
    have hnat : (2651581469 : ℕ)^4383*20000000000000^3359 ≤ 8741555649101^3359*5000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651581469 5000000000 8741555649101 20000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1887582263/10000000000 : ℝ)^4383 ≤ (11354392159549/100000000000000 : ℝ)^3359 := by
    have hnat : (1887582263 : ℕ)^4383*100000000000000^3359 ≤ 11354392159549^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1887582263 10000000000 11354392159549 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1354292007/2500000000 : ℝ)^4383 ≤ (1404307174141/3125000000000 : ℝ)^3359 := by
    have hnat : (1354292007 : ℕ)^4383*3125000000000^3359 ≤ 1404307174141^3359*2500000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354292007 2500000000 1404307174141 3125000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651581469/5000000000 : ℝ), (-1887582263/10000000000 : ℝ), (1354292007/2500000000 : ℝ)] ![(8741555649101/20000000000000 : ℝ), (11354392159549/100000000000000 : ℝ), (1404307174141/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651581469/5000000000 : ℝ)|^4383 ≤ (8741555649101/20000000000000 : ℝ)^3359
        have hw : |(2651581469/5000000000 : ℝ)|=(2651581469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1887582263/10000000000 : ℝ)|^4383 ≤ (11354392159549/100000000000000 : ℝ)^3359
        have hw : |(-1887582263/10000000000 : ℝ)|=(1887582263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1354292007/2500000000 : ℝ)|^4383 ≤ (1404307174141/3125000000000 : ℝ)^3359
        have hw : |(1354292007/2500000000 : ℝ)|=(1354292007/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_s3_6 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (662895367/1250000000 : ℝ)*x 0 + (2708584007/5000000000 : ℝ)*x 1 + (-943791143/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (662895367/1250000000 : ℝ)^4383 ≤ (43707778223997/100000000000000 : ℝ)^3359 := by
    have hnat : (662895367 : ℕ)^4383*100000000000000^3359 ≤ 43707778223997^3359*1250000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      662895367 1250000000 43707778223997 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2708584007/5000000000 : ℝ)^4383 ≤ (44937829420971/100000000000000 : ℝ)^3359 := by
    have hnat : (2708584007 : ℕ)^4383*100000000000000^3359 ≤ 44937829420971^3359*5000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708584007 5000000000 44937829420971 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (943791143/5000000000 : ℝ)^4383 ≤ (5677196170039/50000000000000 : ℝ)^3359 := by
    have hnat : (943791143 : ℕ)^4383*50000000000000^3359 ≤ 5677196170039^3359*5000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      943791143 5000000000 5677196170039 50000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(662895367/1250000000 : ℝ), (2708584007/5000000000 : ℝ), (-943791143/5000000000 : ℝ)] ![(43707778223997/100000000000000 : ℝ), (44937829420971/100000000000000 : ℝ), (5677196170039/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(662895367/1250000000 : ℝ)|^4383 ≤ (43707778223997/100000000000000 : ℝ)^3359
        have hw : |(662895367/1250000000 : ℝ)|=(662895367/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2708584007/5000000000 : ℝ)|^4383 ≤ (44937829420971/100000000000000 : ℝ)^3359
        have hw : |(2708584007/5000000000 : ℝ)|=(2708584007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-943791143/5000000000 : ℝ)|^4383 ≤ (5677196170039/50000000000000 : ℝ)^3359
        have hw : |(-943791143/5000000000 : ℝ)|=(943791143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_s3_7 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4305241051/10000000000 : ℝ)*x 0 + (4501612043/10000000000 : ℝ)*x 1 + (514586719/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4305241051/10000000000 : ℝ)^4383 ≤ (6659638166209/20000000000000 : ℝ)^3359 := by
    have hnat : (4305241051 : ℕ)^4383*20000000000000^3359 ≤ 6659638166209^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4305241051 10000000000 6659638166209 20000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4501612043/10000000000 : ℝ)^4383 ≤ (35293636222809/100000000000000 : ℝ)^3359 := by
    have hnat : (4501612043 : ℕ)^4383*100000000000000^3359 ≤ 35293636222809^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4501612043 10000000000 35293636222809 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (514586719/1250000000 : ℝ)^4383 ≤ (7852043230407/25000000000000 : ℝ)^3359 := by
    have hnat : (514586719 : ℕ)^4383*25000000000000^3359 ≤ 7852043230407^3359*1250000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      514586719 1250000000 7852043230407 25000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4305241051/10000000000 : ℝ), (4501612043/10000000000 : ℝ), (514586719/1250000000 : ℝ)] ![(6659638166209/20000000000000 : ℝ), (35293636222809/100000000000000 : ℝ), (7852043230407/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4305241051/10000000000 : ℝ)|^4383 ≤ (6659638166209/20000000000000 : ℝ)^3359
        have hw : |(4305241051/10000000000 : ℝ)|=(4305241051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4501612043/10000000000 : ℝ)|^4383 ≤ (35293636222809/100000000000000 : ℝ)^3359
        have hw : |(4501612043/10000000000 : ℝ)|=(4501612043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(514586719/1250000000 : ℝ)|^4383 ≤ (7852043230407/25000000000000 : ℝ)^3359
        have hw : |(514586719/1250000000 : ℝ)|=(514586719/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1423_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19741123/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7909/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2067/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (11143/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (299/2000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7909/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2067/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7909/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2067/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7909/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2067/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7909/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2067/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7909/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2067/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7909/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2067/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2067/20000 : ℝ) ^ (2191/512 : ℝ) ≤ (605259927467401/10000000000000000000 : ℝ) := by
    have hpowers : (2067/20000 : ℝ)^2191 ≤ (605259927467401/10000000000000000000 : ℝ)^512 := by
      have hnat : (2067 : ℕ)^2191*10000000000000000000^512 ≤ 605259927467401^512*20000^2191 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2067 20000 605259927467401 10000000000000000000 2191 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2067/20000 : ℝ)) (X := (605259927467401/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2191 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7909/50000 : ℝ) ^ (2191/512 : ℝ) ≤ (37405186229423333/100000000000000000000 : ℝ) := by
    have hpowers : (7909/50000 : ℝ)^2191 ≤ (37405186229423333/100000000000000000000 : ℝ)^512 := by
      have hnat : (7909 : ℕ)^2191*100000000000000000000^512 ≤ 37405186229423333^512*50000^2191 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7909 50000 37405186229423333 100000000000000000000 2191 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7909/50000 : ℝ)) (X := (37405186229423333/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2191 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000605259927467401/5000000000000000000 : ℝ) ≤ (10000282865093931/10000000000000000 : ℝ) ^ (2191/512 : ℝ) := by
    have hpowers : (5000605259927467401/5000000000000000000 : ℝ)^512 ≤ (10000282865093931/10000000000000000 : ℝ)^2191 := by
      have hnat : (5000605259927467401 : ℕ)^512*10000000000000000^2191 ≤ 10000282865093931^2191*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000605259927467401 5000000000000000000 10000282865093931 10000000000000000 512 2191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000282865093931/10000000000000000 : ℝ)) (X := (5000605259927467401/5000000000000000000 : ℝ)) (by norm_num) 2191 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100043457785504097343/100000000000000000000 : ℝ) ≤ (10001015366598187/10000000000000000 : ℝ) ^ (2191/512 : ℝ) := by
    have hpowers : (100043457785504097343/100000000000000000000 : ℝ)^512 ≤ (10001015366598187/10000000000000000 : ℝ)^2191 := by
      have hnat : (100043457785504097343 : ℕ)^512*10000000000000000^2191 ≤ 10001015366598187^2191*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100043457785504097343 100000000000000000000 10001015366598187 10000000000000000 512 2191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001015366598187/10000000000000000 : ℝ)) (X := (100043457785504097343/100000000000000000000 : ℝ)) (by norm_num) 2191 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50037405186229423333/50000000000000000000 : ℝ) ≤ (10001747868102443/10000000000000000 : ℝ) ^ (2191/512 : ℝ) := by
    have hpowers : (50037405186229423333/50000000000000000000 : ℝ)^512 ≤ (10001747868102443/10000000000000000 : ℝ)^2191 := by
      have hnat : (50037405186229423333 : ℕ)^512*10000000000000000^2191 ≤ 10001747868102443^2191*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50037405186229423333 50000000000000000000 10001747868102443 10000000000000000 512 2191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001747868102443/10000000000000000 : ℝ)) (X := (50037405186229423333/50000000000000000000 : ℝ)) (by norm_num) 2191 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(605259927467401/10000000000000000000 : ℝ) ≤ ((54816410143217052153/54830000000000000000 : ℝ)+2*(2861334001/2141796875000 : ℝ)*(2067/20000 : ℝ))^(2191/512 : ℝ) := by
    rw [show (54816410143217052153/54830000000000000000 : ℝ)+2*(2861334001/2141796875000 : ℝ)*(2067/20000 : ℝ)=(10000282865093931/10000000000000000 : ℝ) by norm_num, show 1+2*(605259927467401/10000000000000000000 : ℝ)=(5000605259927467401/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(37405186229423333/100000000000000000000 : ℝ)+(605259927467401/10000000000000000000 : ℝ) ≤ ((54816410143217052153/54830000000000000000 : ℝ)+(2861334001/2141796875000 : ℝ)*((7909/50000 : ℝ)+(2067/20000 : ℝ)))^(2191/512 : ℝ) := by
    rw [show (54816410143217052153/54830000000000000000 : ℝ)+(2861334001/2141796875000 : ℝ)*((7909/50000 : ℝ)+(2067/20000 : ℝ))=(10001015366598187/10000000000000000 : ℝ) by norm_num, show 1+(37405186229423333/100000000000000000000 : ℝ)+(605259927467401/10000000000000000000 : ℝ)=(100043457785504097343/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(37405186229423333/100000000000000000000 : ℝ) ≤ ((54816410143217052153/54830000000000000000 : ℝ)+2*(2861334001/2141796875000 : ℝ)*(7909/50000 : ℝ))^(2191/512 : ℝ) := by
    rw [show (54816410143217052153/54830000000000000000 : ℝ)+2*(2861334001/2141796875000 : ℝ)*(7909/50000 : ℝ)=(10001747868102443/10000000000000000 : ℝ) by norm_num, show 1+2*(37405186229423333/100000000000000000000 : ℝ)=(50037405186229423333/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (54816410143217052153/54830000000000000000 : ℝ)*(X 1 0+X 2 0)+(2861334001/2141796875000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2191/512 : ℝ)) (lo := (2067/20000 : ℝ)) (hi := (7909/50000 : ℝ)) (c := (54816410143217052153/54830000000000000000 : ℝ)) (alpha := (2861334001/2141796875000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (54816410143217052153/54830000000000000000 : ℝ)*(X 0 1+X 2 1)+(2861334001/2141796875000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2191/512 : ℝ)) (lo := (2067/20000 : ℝ)) (hi := (7909/50000 : ℝ)) (c := (54816410143217052153/54830000000000000000 : ℝ)) (alpha := (2861334001/2141796875000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (54816410143217052153/54830000000000000000 : ℝ)*(X 0 2+X 1 2)+(2861334001/2141796875000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2191/512 : ℝ)) (lo := (2067/20000 : ℝ)) (hi := (7909/50000 : ℝ)) (c := (54816410143217052153/54830000000000000000 : ℝ)) (alpha := (2861334001/2141796875000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-493728659/2500000000 : ℝ)*X 0 0+(5417891687/10000000000 : ℝ)*X 0 1+(1309532059/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349868243/10000000000 : ℝ)*X 1 0+(-1033311077/5000000000 : ℝ)*X 1 1+(2619064101/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((167183383/312500000 : ℝ)*X 2 0+(5238128203/10000000000 : ℝ)*X 2 1+(-258327767/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4305207377/10000000000 : ℝ)*X 0 0+(411513163/1000000000 : ℝ)*X 0 1+(562895653/1250000000 : ℝ)*X 0 2+(4305207377/10000000000 : ℝ)*X 1 0+(411513163/1000000000 : ℝ)*X 1 1+(562895653/1250000000 : ℝ)*X 1 2+(4305207377/10000000000 : ℝ)*X 2 0+(411513163/1000000000 : ℝ)*X 2 1+(562895653/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-15799441/80000000 : ℝ)*X 0 0+(2619423927/5000000000 : ℝ)*X 0 1+(338573001/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2651581469/5000000000 : ℝ)*X 1 0+(-1887582263/10000000000 : ℝ)*X 1 1+(1354292007/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((662895367/1250000000 : ℝ)*X 2 0+(2708584007/5000000000 : ℝ)*X 2 1+(-943791143/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4305241051/10000000000 : ℝ)*X 0 0+(4501612043/10000000000 : ℝ)*X 0 1+(514586719/1250000000 : ℝ)*X 0 2+(4305241051/10000000000 : ℝ)*X 1 0+(4501612043/10000000000 : ℝ)*X 1 1+(514586719/1250000000 : ℝ)*X 1 2+(4305241051/10000000000 : ℝ)*X 2 0+(4501612043/10000000000 : ℝ)*X 2 1+(514586719/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1321988728017497737778163987/171343750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1457048883/100000000000000 : ℝ)*(base19) + (286306747/20000000000000 : ℝ)*(base23) + (8167167/4000000000000 : ℝ)*(upper3) + (20882061/100000000000000 : ℝ)*(upper4) + (4999043/2500000000000 : ℝ)*(upper5) + (254376187687931/6250000000000 : ℝ)*(major0) + (254376187687931/6250000000000 : ℝ)*(major1) + (254376187687931/6250000000000 : ℝ)*(major2) + (5562891728565469/100000000000000 : ℝ)*(sp0) + (21730142827003/390625000000 : ℝ)*(sp1) + (1112583317845583/20000000000000 : ℝ)*(sp2) + (1288553964684873/50000000000000 : ℝ)*(sp3) + (13146098091/50000000000000 : ℝ)*(sp4) + (2949675441/25000000000000 : ℝ)*(sp7) + (2577119728071509/100000000000000 : ℝ)*(f.failure) + (5562918020761651/100000000000000 : ℝ)*(f.sum) + (46623762802751/6853750000000000000000000000 : ℝ)*base66 + (8520303463277547057/342687500000000000000000000000000 : ℝ)*base68 + (7296919288370984557/342687500000000000000000000000000 : ℝ)*base70 + (8782492767231359557/342687500000000000000000000000000 : ℝ)*base72 + (21294495126003/3426875000000000000000000000 : ℝ)*base74 + (7782536789359734557/342687500000000000000000000000000 : ℝ)*base76 + (2035229349389359557/342687500000000000000000000000000 : ℝ)*base78 + (7700710488031422057/342687500000000000000000000000000 : ℝ)*base80 + (28939913673663/3426875000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (11964607/1250000000000000000000 : ℝ)*base89 + (11964607/1250000000000000000000 : ℝ)*base91 + (11964607/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1247351807949003095846953389/137075000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (793594599/50000000000000 : ℝ)*(base19) + (1689849967/100000000000000 : ℝ)*(base23) + (99210291/50000000000000 : ℝ)*(upper3) + (3121353/6250000000000 : ℝ)*(lower4) + (195341893/100000000000000 : ℝ)*(upper5) + (410292180832729/10000000000000 : ℝ)*(major0) + (410292180832729/10000000000000 : ℝ)*(major1) + (410292180832729/10000000000000 : ℝ)*(major2) + (935006749/3125000000000 : ℝ)*(sp1) + (31124053787/100000000000000 : ℝ)*(sp2) + (5607889660738061/100000000000000 : ℝ)*(sp4) + (2803929076666447/50000000000000 : ℝ)*(sp5) + (2803928423417153/50000000000000 : ℝ)*(sp6) + (1298976826295321/50000000000000 : ℝ)*(sp7) + (1298976826295321/50000000000000 : ℝ)*(f.failure) + (5607889660738061/100000000000000 : ℝ)*(f.sum) + (5146796616737/5483000000000000000000000000 : ℝ)*base65 + (1094928225785284463/548300000000000000000000000000000 : ℝ)*base68 + (3344079481416715537/548300000000000000000000000000000 : ℝ)*base69 + (1381217143339315537/548300000000000000000000000000000 : ℝ)*base71 + (8528186522687/1370750000000000000000000000 : ℝ)*base74 + (7771061581323115537/548300000000000000000000000000000 : ℝ)*base75 + (2434731130595715537/548300000000000000000000000000000 : ℝ)*base77 + (2157164113481415537/548300000000000000000000000000000 : ℝ)*base79 + (1675329699637/274150000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (3685483/625000000000000000000 : ℝ)*base89 + (3685483/625000000000000000000 : ℝ)*base91 + (3685483/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1423_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19741123/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7909/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2067/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11143/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (299/2000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1423_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1423_s4_0 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-395169059/2000000000 : ℝ)*x 0 + (5409965857/10000000000 : ℝ)*x 1 + (1049088271/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (395169059/2000000000 : ℝ)^4383 ≤ (2410412440867/20000000000000 : ℝ)^3359 := by
    have hnat : (395169059 : ℕ)^4383*20000000000000^3359 ≤ 2410412440867^3359*2000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      395169059 2000000000 2410412440867 20000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5409965857/10000000000 : ℝ)^4383 ≤ (11214971664789/25000000000000 : ℝ)^3359 := by
    have hnat : (5409965857 : ℕ)^4383*25000000000000^3359 ≤ 11214971664789^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409965857 10000000000 11214971664789 25000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1049088271/2000000000 : ℝ)^4383 ≤ (43088051113247/100000000000000 : ℝ)^3359 := by
    have hnat : (1049088271 : ℕ)^4383*100000000000000^3359 ≤ 43088051113247^3359*2000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049088271 2000000000 43088051113247 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-395169059/2000000000 : ℝ), (5409965857/10000000000 : ℝ), (1049088271/2000000000 : ℝ)] ![(2410412440867/20000000000000 : ℝ), (11214971664789/25000000000000 : ℝ), (43088051113247/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-395169059/2000000000 : ℝ)|^4383 ≤ (2410412440867/20000000000000 : ℝ)^3359
        have hw : |(-395169059/2000000000 : ℝ)|=(395169059/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5409965857/10000000000 : ℝ)|^4383 ≤ (11214971664789/25000000000000 : ℝ)^3359
        have hw : |(5409965857/10000000000 : ℝ)|=(5409965857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1049088271/2000000000 : ℝ)|^4383 ≤ (43088051113247/100000000000000 : ℝ)^3359
        have hw : |(1049088271/2000000000 : ℝ)|=(1049088271/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_s4_1 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347824301/10000000000 : ℝ)*x 0 + (-1029818571/5000000000 : ℝ)*x 1 + (5245441519/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347824301/10000000000 : ℝ)^4383 ≤ (44188698706893/100000000000000 : ℝ)^3359 := by
    have hnat : (5347824301 : ℕ)^4383*100000000000000^3359 ≤ 44188698706893^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347824301 10000000000 44188698706893 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1029818571/5000000000 : ℝ)^4383 ≤ (2544649682009/20000000000000 : ℝ)^3359 := by
    have hnat : (1029818571 : ℕ)^4383*20000000000000^3359 ≤ 2544649682009^3359*5000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1029818571 5000000000 2544649682009 20000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245441519/10000000000 : ℝ)^4383 ≤ (4308805287109/10000000000000 : ℝ)^3359 := by
    have hnat : (5245441519 : ℕ)^4383*10000000000000^3359 ≤ 4308805287109^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245441519 10000000000 4308805287109 10000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347824301/10000000000 : ℝ), (-1029818571/5000000000 : ℝ), (5245441519/10000000000 : ℝ)] ![(44188698706893/100000000000000 : ℝ), (2544649682009/20000000000000 : ℝ), (4308805287109/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347824301/10000000000 : ℝ)|^4383 ≤ (44188698706893/100000000000000 : ℝ)^3359
        have hw : |(5347824301/10000000000 : ℝ)|=(5347824301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1029818571/5000000000 : ℝ)|^4383 ≤ (2544649682009/20000000000000 : ℝ)^3359
        have hw : |(-1029818571/5000000000 : ℝ)|=(1029818571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245441519/10000000000 : ℝ)|^4383 ≤ (4308805287109/10000000000000 : ℝ)^3359
        have hw : |(5245441519/10000000000 : ℝ)|=(5245441519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_s4_2 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347824299/10000000000 : ℝ)*x 0 + (5245441549/10000000000 : ℝ)*x 1 + (-411927421/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347824299/10000000000 : ℝ)^4383 ≤ (44188698685329/100000000000000 : ℝ)^3359 := by
    have hnat : (5347824299 : ℕ)^4383*100000000000000^3359 ≤ 44188698685329^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347824299 10000000000 44188698685329 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245441549/10000000000 : ℝ)^4383 ≤ (43088053192647/100000000000000 : ℝ)^3359 := by
    have hnat : (5245441549 : ℕ)^4383*100000000000000^3359 ≤ 43088053192647^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245441549 10000000000 43088053192647 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (411927421/2000000000 : ℝ)^4383 ≤ (12723248111801/100000000000000 : ℝ)^3359 := by
    have hnat : (411927421 : ℕ)^4383*100000000000000^3359 ≤ 12723248111801^3359*2000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      411927421 2000000000 12723248111801 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347824299/10000000000 : ℝ), (5245441549/10000000000 : ℝ), (-411927421/2000000000 : ℝ)] ![(44188698685329/100000000000000 : ℝ), (43088053192647/100000000000000 : ℝ), (12723248111801/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347824299/10000000000 : ℝ)|^4383 ≤ (44188698685329/100000000000000 : ℝ)^3359
        have hw : |(5347824299/10000000000 : ℝ)|=(5347824299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245441549/10000000000 : ℝ)|^4383 ≤ (43088053192647/100000000000000 : ℝ)^3359
        have hw : |(5245441549/10000000000 : ℝ)|=(5245441549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-411927421/2000000000 : ℝ)|^4383 ≤ (12723248111801/100000000000000 : ℝ)^3359
        have hw : |(-411927421/2000000000 : ℝ)|=(411927421/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_s4_3 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4305777659/10000000000 : ℝ)*x 0 + (258219379/625000000 : ℝ)*x 1 + (2243324577/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4305777659/10000000000 : ℝ)^4383 ≤ (33303606474019/100000000000000 : ℝ)^3359 := by
    have hnat : (4305777659 : ℕ)^4383*100000000000000^3359 ≤ 33303606474019^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4305777659 10000000000 33303606474019 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (258219379/625000000 : ℝ)^4383 ≤ (123264668049/390625000000 : ℝ)^3359 := by
    have hnat : (258219379 : ℕ)^4383*390625000000^3359 ≤ 123264668049^3359*625000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258219379 625000000 123264668049 390625000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2243324577/5000000000 : ℝ)^4383 ≤ (8785159621949/25000000000000 : ℝ)^3359 := by
    have hnat : (2243324577 : ℕ)^4383*25000000000000^3359 ≤ 8785159621949^3359*5000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2243324577 5000000000 8785159621949 25000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4305777659/10000000000 : ℝ), (258219379/625000000 : ℝ), (2243324577/5000000000 : ℝ)] ![(33303606474019/100000000000000 : ℝ), (123264668049/390625000000 : ℝ), (8785159621949/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4305777659/10000000000 : ℝ)|^4383 ≤ (33303606474019/100000000000000 : ℝ)^3359
        have hw : |(4305777659/10000000000 : ℝ)|=(4305777659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(258219379/625000000 : ℝ)|^4383 ≤ (123264668049/390625000000 : ℝ)^3359
        have hw : |(258219379/625000000 : ℝ)|=(258219379/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2243324577/5000000000 : ℝ)|^4383 ≤ (8785159621949/25000000000000 : ℝ)^3359
        have hw : |(2243324577/5000000000 : ℝ)|=(2243324577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_s4_4 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-987928647/5000000000 : ℝ)*x 0 + (524604457/1000000000 : ℝ)*x 1 + (676169931/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (987928647/5000000000 : ℝ)^4383 ≤ (12052157706969/100000000000000 : ℝ)^3359 := by
    have hnat : (987928647 : ℕ)^4383*100000000000000^3359 ≤ 12052157706969^3359*5000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      987928647 5000000000 12052157706969 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524604457/1000000000 : ℝ)^4383 ≤ (10773629205087/25000000000000 : ℝ)^3359 := by
    have hnat : (524604457 : ℕ)^4383*25000000000000^3359 ≤ 10773629205087^3359*1000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524604457 1000000000 10773629205087 25000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676169931/1250000000 : ℝ)^4383 ≤ (11213331364577/25000000000000 : ℝ)^3359 := by
    have hnat : (676169931 : ℕ)^4383*25000000000000^3359 ≤ 11213331364577^3359*1250000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676169931 1250000000 11213331364577 25000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-987928647/5000000000 : ℝ), (524604457/1000000000 : ℝ), (676169931/1250000000 : ℝ)] ![(12052157706969/100000000000000 : ℝ), (10773629205087/25000000000000 : ℝ), (11213331364577/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-987928647/5000000000 : ℝ)|^4383 ≤ (12052157706969/100000000000000 : ℝ)^3359
        have hw : |(-987928647/5000000000 : ℝ)|=(987928647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524604457/1000000000 : ℝ)|^4383 ≤ (10773629205087/25000000000000 : ℝ)^3359
        have hw : |(524604457/1000000000 : ℝ)|=(524604457/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(676169931/1250000000 : ℝ)|^4383 ≤ (11213331364577/25000000000000 : ℝ)^3359
        have hw : |(676169931/1250000000 : ℝ)|=(676169931/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_s4_5 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305077871/10000000000 : ℝ)*x 0 + (-1895719109/10000000000 : ℝ)*x 1 + (1352339869/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305077871/10000000000 : ℝ)^4383 ≤ (21864186644447/50000000000000 : ℝ)^3359 := by
    have hnat : (5305077871 : ℕ)^4383*50000000000000^3359 ≤ 21864186644447^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305077871 10000000000 21864186644447 50000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1895719109/10000000000 : ℝ)^4383 ≤ (11418300942671/100000000000000 : ℝ)^3359 := by
    have hnat : (1895719109 : ℕ)^4383*100000000000000^3359 ≤ 11418300942671^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1895719109 10000000000 11418300942671 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1352339869/2500000000 : ℝ)^4383 ≤ (5606665720157/12500000000000 : ℝ)^3359 := by
    have hnat : (1352339869 : ℕ)^4383*12500000000000^3359 ≤ 5606665720157^3359*2500000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352339869 2500000000 5606665720157 12500000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305077871/10000000000 : ℝ), (-1895719109/10000000000 : ℝ), (1352339869/2500000000 : ℝ)] ![(21864186644447/50000000000000 : ℝ), (11418300942671/100000000000000 : ℝ), (5606665720157/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305077871/10000000000 : ℝ)|^4383 ≤ (21864186644447/50000000000000 : ℝ)^3359
        have hw : |(5305077871/10000000000 : ℝ)|=(5305077871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1895719109/10000000000 : ℝ)|^4383 ≤ (11418300942671/100000000000000 : ℝ)^3359
        have hw : |(-1895719109/10000000000 : ℝ)|=(1895719109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1352339869/2500000000 : ℝ)|^4383 ≤ (5606665720157/12500000000000 : ℝ)^3359
        have hw : |(1352339869/2500000000 : ℝ)|=(1352339869/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_s4_6 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326269471/2500000000 : ℝ)*x 0 + (5409359477/10000000000 : ℝ)*x 1 + (-1895719089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326269471/2500000000 : ℝ)^4383 ≤ (10932093357179/25000000000000 : ℝ)^3359 := by
    have hnat : (1326269471 : ℕ)^4383*25000000000000^3359 ≤ 10932093357179^3359*2500000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326269471 2500000000 10932093357179 25000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5409359477/10000000000 : ℝ)^4383 ≤ (1794133030883/4000000000000 : ℝ)^3359 := by
    have hnat : (5409359477 : ℕ)^4383*4000000000000^3359 ≤ 1794133030883^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409359477 10000000000 1794133030883 4000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1895719089/10000000000 : ℝ)^4383 ≤ (11418300785483/100000000000000 : ℝ)^3359 := by
    have hnat : (1895719089 : ℕ)^4383*100000000000000^3359 ≤ 11418300785483^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1895719089 10000000000 11418300785483 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326269471/2500000000 : ℝ), (5409359477/10000000000 : ℝ), (-1895719089/10000000000 : ℝ)] ![(10932093357179/25000000000000 : ℝ), (1794133030883/4000000000000 : ℝ), (11418300785483/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326269471/2500000000 : ℝ)|^4383 ≤ (10932093357179/25000000000000 : ℝ)^3359
        have hw : |(1326269471/2500000000 : ℝ)|=(1326269471/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5409359477/10000000000 : ℝ)|^4383 ≤ (1794133030883/4000000000000 : ℝ)^3359
        have hw : |(5409359477/10000000000 : ℝ)|=(5409359477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1895719089/10000000000 : ℝ)|^4383 ≤ (11418300785483/100000000000000 : ℝ)^3359
        have hw : |(-1895719089/10000000000 : ℝ)|=(1895719089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_s4_7 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4305803569/10000000000 : ℝ)*x 0 + (56066839/125000000 : ℝ)*x 1 + (1033204721/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4305803569/10000000000 : ℝ)^4383 ≤ (8325966993091/25000000000000 : ℝ)^3359 := by
    have hnat : (4305803569 : ℕ)^4383*25000000000000^3359 ≤ 8325966993091^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4305803569 10000000000 8325966993091 25000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (56066839/125000000 : ℝ)^4383 ≤ (17563666173453/50000000000000 : ℝ)^3359 := by
    have hnat : (56066839 : ℕ)^4383*50000000000000^3359 ≤ 17563666173453^3359*125000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56066839 125000000 17563666173453 50000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1033204721/2500000000 : ℝ)^4383 ≤ (3946099957647/12500000000000 : ℝ)^3359 := by
    have hnat : (1033204721 : ℕ)^4383*12500000000000^3359 ≤ 3946099957647^3359*2500000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033204721 2500000000 3946099957647 12500000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4305803569/10000000000 : ℝ), (56066839/125000000 : ℝ), (1033204721/2500000000 : ℝ)] ![(8325966993091/25000000000000 : ℝ), (17563666173453/50000000000000 : ℝ), (3946099957647/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4305803569/10000000000 : ℝ)|^4383 ≤ (8325966993091/25000000000000 : ℝ)^3359
        have hw : |(4305803569/10000000000 : ℝ)|=(4305803569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(56066839/125000000 : ℝ)|^4383 ≤ (17563666173453/50000000000000 : ℝ)^3359
        have hw : |(56066839/125000000 : ℝ)|=(56066839/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1033204721/2500000000 : ℝ)|^4383 ≤ (3946099957647/12500000000000 : ℝ)^3359
        have hw : |(1033204721/2500000000 : ℝ)|=(1033204721/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1423_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19741123/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (299/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11143/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11299/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (462/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (299/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11143/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (299/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11143/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (299/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11143/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (299/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11143/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (299/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11143/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (299/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11143/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11143/100000 : ℝ) ^ (2191/512 : ℝ) ≤ (2088234198977271/25000000000000000000 : ℝ) := by
    have hpowers : (11143/100000 : ℝ)^2191 ≤ (2088234198977271/25000000000000000000 : ℝ)^512 := by
      have hnat : (11143 : ℕ)^2191*25000000000000000000^512 ≤ 2088234198977271^512*100000^2191 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11143 100000 2088234198977271 25000000000000000000 2191 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11143/100000 : ℝ)) (X := (2088234198977271/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2191 512 (by norm_num) hpowers
    exact h
  have hpowhi : (299/2000 : ℝ) ^ (2191/512 : ℝ) ≤ (117518063480363/400000000000000000 : ℝ) := by
    have hpowers : (299/2000 : ℝ)^2191 ≤ (117518063480363/400000000000000000 : ℝ)^512 := by
      have hnat : (299 : ℕ)^2191*400000000000000000^512 ≤ 117518063480363^512*2000^2191 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        299 2000 117518063480363 400000000000000000 2191 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (299/2000 : ℝ)) (X := (117518063480363/400000000000000000 : ℝ)) (by norm_num) (by norm_num) 2191 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502088234198977271/12500000000000000000 : ℝ) ≤ (10000390363296653/10000000000000000 : ℝ) ^ (2191/512 : ℝ) := by
    have hpowers : (12502088234198977271/12500000000000000000 : ℝ)^512 ≤ (10000390363296653/10000000000000000 : ℝ)^2191 := by
      have hnat : (12502088234198977271 : ℕ)^512*10000000000000000^2191 ≤ 10000390363296653^2191*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502088234198977271 12500000000000000000 10000390363296653 10000000000000000 512 2191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000390363296653/10000000000000000 : ℝ)) (X := (12502088234198977271/12500000000000000000 : ℝ)) (by norm_num) 2191 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50018866226332999917/50000000000000000000 : ℝ) ≤ (1250110202095719/1250000000000000 : ℝ) ^ (2191/512 : ℝ) := by
    have hpowers : (50018866226332999917/50000000000000000000 : ℝ)^512 ≤ (1250110202095719/1250000000000000 : ℝ)^2191 := by
      have hnat : (50018866226332999917 : ℕ)^512*1250000000000000^2191 ≤ 1250110202095719^2191*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018866226332999917 50000000000000000000 1250110202095719 1250000000000000 512 2191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250110202095719/1250000000000000 : ℝ)) (X := (50018866226332999917/50000000000000000000 : ℝ)) (by norm_num) 2191 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (200117518063480363/200000000000000000 : ℝ) ≤ (10001372870234851/10000000000000000 : ℝ) ^ (2191/512 : ℝ) := by
    have hpowers : (200117518063480363/200000000000000000 : ℝ)^512 ≤ (10001372870234851/10000000000000000 : ℝ)^2191 := by
      have hnat : (200117518063480363 : ℕ)^512*10000000000000000^2191 ≤ 10001372870234851^2191*200000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        200117518063480363 200000000000000000 10001372870234851 10000000000000000 512 2191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001372870234851/10000000000000000 : ℝ)) (X := (200117518063480363/200000000000000000 : ℝ)) (by norm_num) 2191 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2088234198977271/25000000000000000000 : ℝ) ≤ ((38060538038258017657/38070000000000000000 : ℝ)+2*(491253469099/380700000000000 : ℝ)*(11143/100000 : ℝ))^(2191/512 : ℝ) := by
    rw [show (38060538038258017657/38070000000000000000 : ℝ)+2*(491253469099/380700000000000 : ℝ)*(11143/100000 : ℝ)=(10000390363296653/10000000000000000 : ℝ) by norm_num, show 1+2*(2088234198977271/25000000000000000000 : ℝ)=(12502088234198977271/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(117518063480363/400000000000000000 : ℝ)+(2088234198977271/25000000000000000000 : ℝ) ≤ ((38060538038258017657/38070000000000000000 : ℝ)+(491253469099/380700000000000 : ℝ)*((299/2000 : ℝ)+(11143/100000 : ℝ)))^(2191/512 : ℝ) := by
    rw [show (38060538038258017657/38070000000000000000 : ℝ)+(491253469099/380700000000000 : ℝ)*((299/2000 : ℝ)+(11143/100000 : ℝ))=(1250110202095719/1250000000000000 : ℝ) by norm_num, show 1+(117518063480363/400000000000000000 : ℝ)+(2088234198977271/25000000000000000000 : ℝ)=(50018866226332999917/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(117518063480363/400000000000000000 : ℝ) ≤ ((38060538038258017657/38070000000000000000 : ℝ)+2*(491253469099/380700000000000 : ℝ)*(299/2000 : ℝ))^(2191/512 : ℝ) := by
    rw [show (38060538038258017657/38070000000000000000 : ℝ)+2*(491253469099/380700000000000 : ℝ)*(299/2000 : ℝ)=(10001372870234851/10000000000000000 : ℝ) by norm_num, show 1+2*(117518063480363/400000000000000000 : ℝ)=(200117518063480363/200000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (38060538038258017657/38070000000000000000 : ℝ)*(X 1 0+X 2 0)+(491253469099/380700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2191/512 : ℝ)) (lo := (11143/100000 : ℝ)) (hi := (299/2000 : ℝ)) (c := (38060538038258017657/38070000000000000000 : ℝ)) (alpha := (491253469099/380700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (38060538038258017657/38070000000000000000 : ℝ)*(X 0 1+X 2 1)+(491253469099/380700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2191/512 : ℝ)) (lo := (11143/100000 : ℝ)) (hi := (299/2000 : ℝ)) (c := (38060538038258017657/38070000000000000000 : ℝ)) (alpha := (491253469099/380700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (38060538038258017657/38070000000000000000 : ℝ)*(X 0 2+X 1 2)+(491253469099/380700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2191/512 : ℝ)) (lo := (11143/100000 : ℝ)) (hi := (299/2000 : ℝ)) (c := (38060538038258017657/38070000000000000000 : ℝ)) (alpha := (491253469099/380700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-395169059/2000000000 : ℝ)*X 0 0+(5409965857/10000000000 : ℝ)*X 0 1+(1049088271/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347824301/10000000000 : ℝ)*X 1 0+(-1029818571/5000000000 : ℝ)*X 1 1+(5245441519/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347824299/10000000000 : ℝ)*X 2 0+(5245441549/10000000000 : ℝ)*X 2 1+(-411927421/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4305777659/10000000000 : ℝ)*X 0 0+(258219379/625000000 : ℝ)*X 0 1+(2243324577/5000000000 : ℝ)*X 0 2+(4305777659/10000000000 : ℝ)*X 1 0+(258219379/625000000 : ℝ)*X 1 1+(2243324577/5000000000 : ℝ)*X 1 2+(4305777659/10000000000 : ℝ)*X 2 0+(258219379/625000000 : ℝ)*X 2 1+(2243324577/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-987928647/5000000000 : ℝ)*X 0 0+(524604457/1000000000 : ℝ)*X 0 1+(676169931/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305077871/10000000000 : ℝ)*X 1 0+(-1895719109/10000000000 : ℝ)*X 1 1+(1352339869/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326269471/2500000000 : ℝ)*X 2 0+(5409359477/10000000000 : ℝ)*X 2 1+(-1895719089/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4305803569/10000000000 : ℝ)*X 0 0+(56066839/125000000 : ℝ)*X 0 1+(1033204721/2500000000 : ℝ)*X 0 2+(4305803569/10000000000 : ℝ)*X 1 0+(56066839/125000000 : ℝ)*X 1 1+(1033204721/2500000000 : ℝ)*X 1 2+(4305803569/10000000000 : ℝ)*X 2 0+(56066839/125000000 : ℝ)*X 2 1+(1033204721/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (59300162654511031002149927/5875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1532053549/100000000000000 : ℝ)*(base19) + (281889847/20000000000000 : ℝ)*(base23) + (64350993/100000000000000 : ℝ)*(lower2) + (26029573/12500000000000 : ℝ)*(upper3) + (33263911/20000000000000 : ℝ)*(upper5) + (2223507469142997/50000000000000 : ℝ)*(major0) + (2223507469142997/50000000000000 : ℝ)*(major1) + (2223507469142997/50000000000000 : ℝ)*(major2) + (6078159680267429/100000000000000 : ℝ)*(sp0) + (151954899100793/2500000000000 : ℝ)*(sp1) + (3039098043318017/50000000000000 : ℝ)*(sp2) + (2815814491641067/100000000000000 : ℝ)*(sp3) + (472697723/1250000000000 : ℝ)*(sp4) + (8776195411/50000000000000 : ℝ)*(sp7) + (2815832044031889/100000000000000 : ℝ)*(f.failure) + (6078197496085269/100000000000000 : ℝ)*(f.sum) + (83934843497/1057500000000000000000000000 : ℝ)*base65 + (4597198794097700219/211500000000000000000000000000000 : ℝ)*base68 + (993373561897700219/211500000000000000000000000000000 : ℝ)*base70 + (13868748487299781/211500000000000000000000000000000 : ℝ)*base71 + (5695241672593/1057500000000000000000000000 : ℝ)*base74 + (683294271645200219/211500000000000000000000000000000 : ℝ)*base76 + (1602702408841700219/211500000000000000000000000000000 : ℝ)*base78 + (2318048613147200219/211500000000000000000000000000000 : ℝ)*base80 + (1283770071197/1057500000000000000000000000 : ℝ)*base81 + (11671347/1250000000000000000000 : ℝ)*base89 + (11671347/1250000000000000000000 : ℝ)*base91 + (11671347/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (23584592659996799404858039/3375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1119592421/100000000000000 : ℝ)*(base19) + (1247262589/100000000000000 : ℝ)*(base23) + (29644429/20000000000000 : ℝ)*(upper3) + (23245891/50000000000000 : ℝ)*(lower4) + (134882781/100000000000000 : ℝ)*(upper5) + (2239947982733569/50000000000000 : ℝ)*(major0) + (2239947982733569/50000000000000 : ℝ)*(major1) + (2239947982733569/50000000000000 : ℝ)*(major2) + (23358470709/100000000000000 : ℝ)*(sp1) + (5292948227/20000000000000 : ℝ)*(sp2) + (612313951927953/10000000000000 : ℝ)*(sp4) + (15307787603041/250000000000 : ℝ)*(sp5) + (3061555903637903/50000000000000 : ℝ)*(sp6) + (2836652178720493/100000000000000 : ℝ)*(sp7) + (2836652178720493/100000000000000 : ℝ)*(f.failure) + (612313951927953/10000000000000 : ℝ)*(f.sum) + (90629766056267/19035000000000000000000000000 : ℝ)*base65 + (4951609369548272167/1903500000000000000000000000000000 : ℝ)*base68 + (14122876028820272167/1903500000000000000000000000000000 : ℝ)*base70 + (9313522161320727833/1903500000000000000000000000000000 : ℝ)*base71 + (2969217112487/1189687500000000000000000000 : ℝ)*base73 + (9330003756478772167/1903500000000000000000000000000000 : ℝ)*base76 + (7527751307889272167/1903500000000000000000000000000000 : ℝ)*base78 + (10907050754017772167/1903500000000000000000000000000000 : ℝ)*base80 + (6821188790057/19035000000000000000000000000 : ℝ)*base81 + (9933639/1250000000000000000000 : ℝ)*base89 + (9933639/1250000000000000000000 : ℝ)*base91 + (9933639/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1423_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19741123/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (299/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11143/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11299/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (462/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1423_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1423_s5_0 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1975987173/10000000000 : ℝ)*x 0 + (2704359933/5000000000 : ℝ)*x 1 + (163956053/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1975987173/10000000000 : ℝ)^4383 ≤ (1205319145331/10000000000000 : ℝ)^3359 := by
    have hnat : (1975987173 : ℕ)^4383*10000000000000^3359 ≤ 1205319145331^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1975987173 10000000000 1205319145331 10000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2704359933/5000000000 : ℝ)^4383 ≤ (44846405576467/100000000000000 : ℝ)^3359 := by
    have hnat : (2704359933 : ℕ)^4383*100000000000000^3359 ≤ 44846405576467^3359*5000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704359933 5000000000 44846405576467 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (163956053/312500000 : ℝ)^4383 ≤ (21550201479193/50000000000000 : ℝ)^3359 := by
    have hnat : (163956053 : ℕ)^4383*50000000000000^3359 ≤ 21550201479193^3359*312500000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163956053 312500000 21550201479193 50000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1975987173/10000000000 : ℝ), (2704359933/5000000000 : ℝ), (163956053/312500000 : ℝ)] ![(1205319145331/10000000000000 : ℝ), (44846405576467/100000000000000 : ℝ), (21550201479193/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1975987173/10000000000 : ℝ)|^4383 ≤ (1205319145331/10000000000000 : ℝ)^3359
        have hw : |(-1975987173/10000000000 : ℝ)|=(1975987173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2704359933/5000000000 : ℝ)|^4383 ≤ (44846405576467/100000000000000 : ℝ)^3359
        have hw : |(2704359933/5000000000 : ℝ)|=(2704359933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(163956053/312500000 : ℝ)|^4383 ≤ (21550201479193/50000000000000 : ℝ)^3359
        have hw : |(163956053/312500000 : ℝ)|=(163956053/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_s5_1 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334218897/625000000 : ℝ)*x 0 + (-1029268091/5000000000 : ℝ)*x 1 + (5246593211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334218897/625000000 : ℝ)^4383 ≤ (44185227514831/100000000000000 : ℝ)^3359 := by
    have hnat : (334218897 : ℕ)^4383*100000000000000^3359 ≤ 44185227514831^3359*625000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334218897 625000000 44185227514831 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1029268091/5000000000 : ℝ)^4383 ≤ (2542874941333/20000000000000 : ℝ)^3359 := by
    have hnat : (1029268091 : ℕ)^4383*20000000000000^3359 ≤ 2542874941333^3359*5000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1029268091 5000000000 2542874941333 20000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246593211/10000000000 : ℝ)^4383 ≤ (21550198879769/50000000000000 : ℝ)^3359 := by
    have hnat : (5246593211 : ℕ)^4383*50000000000000^3359 ≤ 21550198879769^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246593211 10000000000 21550198879769 50000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334218897/625000000 : ℝ), (-1029268091/5000000000 : ℝ), (5246593211/10000000000 : ℝ)] ![(44185227514831/100000000000000 : ℝ), (2542874941333/20000000000000 : ℝ), (21550198879769/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334218897/625000000 : ℝ)|^4383 ≤ (44185227514831/100000000000000 : ℝ)^3359
        have hw : |(334218897/625000000 : ℝ)|=(334218897/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1029268091/5000000000 : ℝ)|^4383 ≤ (2542874941333/20000000000000 : ℝ)^3359
        have hw : |(-1029268091/5000000000 : ℝ)|=(1029268091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246593211/10000000000 : ℝ)|^4383 ≤ (21550198879769/50000000000000 : ℝ)^3359
        have hw : |(5246593211/10000000000 : ℝ)|=(5246593211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_s5_2 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336875501/2500000000 : ℝ)*x 0 + (1311648373/2500000000 : ℝ)*x 1 + (-1029268137/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336875501/2500000000 : ℝ)^4383 ≤ (11046305940699/25000000000000 : ℝ)^3359 := by
    have hnat : (1336875501 : ℕ)^4383*25000000000000^3359 ≤ 11046305940699^3359*2500000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336875501 2500000000 11046305940699 25000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311648373/2500000000 : ℝ)^4383 ≤ (21550200385827/50000000000000 : ℝ)^3359 := by
    have hnat : (1311648373 : ℕ)^4383*50000000000000^3359 ≤ 21550200385827^3359*2500000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311648373 2500000000 21550200385827 50000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1029268137/5000000000 : ℝ)^4383 ≤ (6357187724061/50000000000000 : ℝ)^3359 := by
    have hnat : (1029268137 : ℕ)^4383*50000000000000^3359 ≤ 6357187724061^3359*5000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1029268137 5000000000 6357187724061 50000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336875501/2500000000 : ℝ), (1311648373/2500000000 : ℝ), (-1029268137/5000000000 : ℝ)] ![(11046305940699/25000000000000 : ℝ), (21550200385827/50000000000000 : ℝ), (6357187724061/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336875501/2500000000 : ℝ)|^4383 ≤ (11046305940699/25000000000000 : ℝ)^3359
        have hw : |(1336875501/2500000000 : ℝ)|=(1336875501/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311648373/2500000000 : ℝ)|^4383 ≤ (21550200385827/50000000000000 : ℝ)^3359
        have hw : |(1311648373/2500000000 : ℝ)|=(1311648373/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1029268137/5000000000 : ℝ)|^4383 ≤ (6357187724061/50000000000000 : ℝ)^3359
        have hw : |(-1029268137/5000000000 : ℝ)|=(1029268137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_s5_3 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2152931229/5000000000 : ℝ)*x 0 + (2067043753/5000000000 : ℝ)*x 1 + (140126609/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2152931229/5000000000 : ℝ)^4383 ≤ (1332178492607/4000000000000 : ℝ)^3359 := by
    have hnat : (2152931229 : ℕ)^4383*4000000000000^3359 ≤ 1332178492607^3359*5000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2152931229 5000000000 1332178492607 4000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2067043753/5000000000 : ℝ)^4383 ≤ (31581444861667/100000000000000 : ℝ)^3359 := by
    have hnat : (2067043753 : ℕ)^4383*100000000000000^3359 ≤ 31581444861667^3359*5000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2067043753 5000000000 31581444861667 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (140126609/312500000 : ℝ)^4383 ≤ (17557046400037/50000000000000 : ℝ)^3359 := by
    have hnat : (140126609 : ℕ)^4383*50000000000000^3359 ≤ 17557046400037^3359*312500000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140126609 312500000 17557046400037 50000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2152931229/5000000000 : ℝ), (2067043753/5000000000 : ℝ), (140126609/312500000 : ℝ)] ![(1332178492607/4000000000000 : ℝ), (31581444861667/100000000000000 : ℝ), (17557046400037/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2152931229/5000000000 : ℝ)|^4383 ≤ (1332178492607/4000000000000 : ℝ)^3359
        have hw : |(2152931229/5000000000 : ℝ)|=(2152931229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2067043753/5000000000 : ℝ)|^4383 ≤ (31581444861667/100000000000000 : ℝ)^3359
        have hw : |(2067043753/5000000000 : ℝ)|=(2067043753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(140126609/312500000 : ℝ)|^4383 ≤ (17557046400037/50000000000000 : ℝ)^3359
        have hw : |(140126609/312500000 : ℝ)|=(140126609/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_s5_4 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-987999331/5000000000 : ℝ)*x 0 + (5247179031/10000000000 : ℝ)*x 1 + (1081626293/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (987999331/5000000000 : ℝ)^4383 ≤ (6026641449371/50000000000000 : ℝ)^3359 := by
    have hnat : (987999331 : ℕ)^4383*50000000000000^3359 ≤ 6026641449371^3359*5000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      987999331 5000000000 6026641449371 50000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247179031/10000000000 : ℝ)^4383 ≤ (43106677431213/100000000000000 : ℝ)^3359 := by
    have hnat : (5247179031 : ℕ)^4383*100000000000000^3359 ≤ 43106677431213^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247179031 10000000000 43106677431213 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081626293/2000000000 : ℝ)^4383 ≤ (4484003966171/10000000000000 : ℝ)^3359 := by
    have hnat : (1081626293 : ℕ)^4383*10000000000000^3359 ≤ 4484003966171^3359*2000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081626293 2000000000 4484003966171 10000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-987999331/5000000000 : ℝ), (5247179031/10000000000 : ℝ), (1081626293/2000000000 : ℝ)] ![(6026641449371/50000000000000 : ℝ), (43106677431213/100000000000000 : ℝ), (4484003966171/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-987999331/5000000000 : ℝ)|^4383 ≤ (6026641449371/50000000000000 : ℝ)^3359
        have hw : |(-987999331/5000000000 : ℝ)|=(987999331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247179031/10000000000 : ℝ)|^4383 ≤ (43106677431213/100000000000000 : ℝ)^3359
        have hw : |(5247179031/10000000000 : ℝ)|=(5247179031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081626293/2000000000 : ℝ)|^4383 ≤ (4484003966171/10000000000000 : ℝ)^3359
        have hw : |(1081626293/2000000000 : ℝ)|=(1081626293/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_s5_5 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305378593/10000000000 : ℝ)*x 0 + (-1896997911/10000000000 : ℝ)*x 1 + (676016433/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305378593/10000000000 : ℝ)^4383 ≤ (2186580387517/5000000000000 : ℝ)^3359 := by
    have hnat : (5305378593 : ℕ)^4383*5000000000000^3359 ≤ 2186580387517^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305378593 10000000000 2186580387517 5000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1896997911/10000000000 : ℝ)^4383 ≤ (5714176291233/50000000000000 : ℝ)^3359 := by
    have hnat : (1896997911 : ℕ)^4383*50000000000000^3359 ≤ 5714176291233^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1896997911 10000000000 5714176291233 50000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676016433/1250000000 : ℝ)^4383 ≤ (11210009912723/25000000000000 : ℝ)^3359 := by
    have hnat : (676016433 : ℕ)^4383*25000000000000^3359 ≤ 11210009912723^3359*1250000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676016433 1250000000 11210009912723 25000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305378593/10000000000 : ℝ), (-1896997911/10000000000 : ℝ), (676016433/1250000000 : ℝ)] ![(2186580387517/5000000000000 : ℝ), (5714176291233/50000000000000 : ℝ), (11210009912723/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305378593/10000000000 : ℝ)|^4383 ≤ (2186580387517/5000000000000 : ℝ)^3359
        have hw : |(5305378593/10000000000 : ℝ)|=(5305378593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1896997911/10000000000 : ℝ)|^4383 ≤ (5714176291233/50000000000000 : ℝ)^3359
        have hw : |(-1896997911/10000000000 : ℝ)|=(1896997911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(676016433/1250000000 : ℝ)|^4383 ≤ (11210009912723/25000000000000 : ℝ)^3359
        have hw : |(676016433/1250000000 : ℝ)|=(676016433/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_s5_6 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4144827/7812500 : ℝ)*x 0 + (1352032861/2500000000 : ℝ)*x 1 + (-59281187/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4144827/7812500 : ℝ)^4383 ≤ (43731607395401/100000000000000 : ℝ)^3359 := by
    have hnat : (4144827 : ℕ)^4383*100000000000000^3359 ≤ 43731607395401^3359*7812500^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4144827 7812500 43731607395401 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352032861/2500000000 : ℝ)^4383 ≤ (8968007886903/20000000000000 : ℝ)^3359 := by
    have hnat : (1352032861 : ℕ)^4383*20000000000000^3359 ≤ 8968007886903^3359*2500000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352032861 2500000000 8968007886903 20000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (59281187/312500000 : ℝ)^4383 ≤ (11428353156319/100000000000000 : ℝ)^3359 := by
    have hnat : (59281187 : ℕ)^4383*100000000000000^3359 ≤ 11428353156319^3359*312500000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      59281187 312500000 11428353156319 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4144827/7812500 : ℝ), (1352032861/2500000000 : ℝ), (-59281187/312500000 : ℝ)] ![(43731607395401/100000000000000 : ℝ), (8968007886903/20000000000000 : ℝ), (11428353156319/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4144827/7812500 : ℝ)|^4383 ≤ (43731607395401/100000000000000 : ℝ)^3359
        have hw : |(4144827/7812500 : ℝ)|=(4144827/7812500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352032861/2500000000 : ℝ)|^4383 ≤ (8968007886903/20000000000000 : ℝ)^3359
        have hw : |(1352032861/2500000000 : ℝ)|=(1352032861/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-59281187/312500000 : ℝ)|^4383 ≤ (11428353156319/100000000000000 : ℝ)^3359
        have hw : |(-59281187/312500000 : ℝ)|=(59281187/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1423_s5_7 (p : ℝ) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1076471899/2500000000 : ℝ)*x 0 + (89655737/200000000 : ℝ)*x 1 + (4135358297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1076471899/2500000000 : ℝ)^4383 ≤ (33304716023577/100000000000000 : ℝ)^3359 := by
    have hnat : (1076471899 : ℕ)^4383*100000000000000^3359 ≤ 33304716023577^3359*2500000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076471899 2500000000 33304716023577 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (89655737/200000000 : ℝ)^4383 ≤ (3510117109321/10000000000000 : ℝ)^3359 := by
    have hnat : (89655737 : ℕ)^4383*10000000000000^3359 ≤ 3510117109321^3359*200000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89655737 200000000 3510117109321 10000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4135358297/10000000000 : ℝ)^4383 ≤ (31594112868071/100000000000000 : ℝ)^3359 := by
    have hnat : (4135358297 : ℕ)^4383*100000000000000^3359 ≤ 31594112868071^3359*10000000000^4383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4135358297 10000000000 31594112868071 100000000000000 4383 3359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4383/1024 : ℝ)) 4383 3359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1076471899/2500000000 : ℝ), (89655737/200000000 : ℝ), (4135358297/10000000000 : ℝ)] ![(33304716023577/100000000000000 : ℝ), (3510117109321/10000000000000 : ℝ), (31594112868071/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1076471899/2500000000 : ℝ)|^4383 ≤ (33304716023577/100000000000000 : ℝ)^3359
        have hw : |(1076471899/2500000000 : ℝ)|=(1076471899/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(89655737/200000000 : ℝ)|^4383 ≤ (3510117109321/10000000000000 : ℝ)^3359
        have hw : |(89655737/200000000 : ℝ)|=(89655737/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4135358297/10000000000 : ℝ)|^4383 ≤ (31594112868071/100000000000000 : ℝ)^3359
        have hw : |(4135358297/10000000000 : ℝ)|=(4135358297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1423_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19741123/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (462/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11299/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2831/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7379/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (462/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11299/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (462/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11299/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (462/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11299/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (462/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11299/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (462/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11299/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (462/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11299/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11299/100000 : ℝ) ^ (2191/512 : ℝ) ≤ (2216241469146603/25000000000000000000 : ℝ) := by
    have hpowers : (11299/100000 : ℝ)^2191 ≤ (2216241469146603/25000000000000000000 : ℝ)^512 := by
      have hnat : (11299 : ℕ)^2191*25000000000000000000^512 ≤ 2216241469146603^512*100000^2191 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11299 100000 2216241469146603 25000000000000000000 2191 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11299/100000 : ℝ)) (X := (2216241469146603/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2191 512 (by norm_num) hpowers
    exact h
  have hpowhi : (462/3125 : ℝ) ^ (2191/512 : ℝ) ≤ (28008722620057941/100000000000000000000 : ℝ) := by
    have hpowers : (462/3125 : ℝ)^2191 ≤ (28008722620057941/100000000000000000000 : ℝ)^512 := by
      have hnat : (462 : ℕ)^2191*100000000000000000000^512 ≤ 28008722620057941^512*3125^2191 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        462 3125 28008722620057941 100000000000000000000 2191 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (462/3125 : ℝ)) (X := (28008722620057941/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2191 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502216241469146603/12500000000000000000 : ℝ) ≤ (200008285813271/200000000000000 : ℝ) ^ (2191/512 : ℝ) := by
    have hpowers : (12502216241469146603/12500000000000000000 : ℝ)^512 ≤ (200008285813271/200000000000000 : ℝ)^2191 := by
      have hnat : (12502216241469146603 : ℕ)^512*200000000000000^2191 ≤ 200008285813271^2191*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502216241469146603 12500000000000000000 200008285813271 200000000000000 512 2191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200008285813271/200000000000000 : ℝ)) (X := (12502216241469146603/12500000000000000000 : ℝ)) (by norm_num) 2191 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100036873688496644353/100000000000000000000 : ℝ) ≤ (5000430777310141/5000000000000000 : ℝ) ^ (2191/512 : ℝ) := by
    have hpowers : (100036873688496644353/100000000000000000000 : ℝ)^512 ≤ (5000430777310141/5000000000000000 : ℝ)^2191 := by
      have hnat : (100036873688496644353 : ℕ)^512*5000000000000000^2191 ≤ 5000430777310141^2191*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100036873688496644353 100000000000000000000 5000430777310141 5000000000000000 512 2191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000430777310141/5000000000000000 : ℝ)) (X := (100036873688496644353/100000000000000000000 : ℝ)) (by norm_num) 2191 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50028008722620057941/50000000000000000000 : ℝ) ≤ (5000654409288507/5000000000000000 : ℝ) ^ (2191/512 : ℝ) := by
    have hpowers : (50028008722620057941/50000000000000000000 : ℝ)^512 ≤ (5000654409288507/5000000000000000 : ℝ)^2191 := by
      have hnat : (50028008722620057941 : ℕ)^512*5000000000000000^2191 ≤ 5000654409288507^2191*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50028008722620057941 50000000000000000000 5000654409288507 5000000000000000 512 2191 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000654409288507/5000000000000000 : ℝ)) (X := (50028008722620057941/50000000000000000000 : ℝ)) (by norm_num) 2191 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2216241469146603/25000000000000000000 : ℝ) ≤ ((17420668266034121007/17425000000000000000 : ℝ)+2*(111815989183/87125000000000 : ℝ)*(11299/100000 : ℝ))^(2191/512 : ℝ) := by
    rw [show (17420668266034121007/17425000000000000000 : ℝ)+2*(111815989183/87125000000000 : ℝ)*(11299/100000 : ℝ)=(200008285813271/200000000000000 : ℝ) by norm_num, show 1+2*(2216241469146603/25000000000000000000 : ℝ)=(12502216241469146603/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(28008722620057941/100000000000000000000 : ℝ)+(2216241469146603/25000000000000000000 : ℝ) ≤ ((17420668266034121007/17425000000000000000 : ℝ)+(111815989183/87125000000000 : ℝ)*((462/3125 : ℝ)+(11299/100000 : ℝ)))^(2191/512 : ℝ) := by
    rw [show (17420668266034121007/17425000000000000000 : ℝ)+(111815989183/87125000000000 : ℝ)*((462/3125 : ℝ)+(11299/100000 : ℝ))=(5000430777310141/5000000000000000 : ℝ) by norm_num, show 1+(28008722620057941/100000000000000000000 : ℝ)+(2216241469146603/25000000000000000000 : ℝ)=(100036873688496644353/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(28008722620057941/100000000000000000000 : ℝ) ≤ ((17420668266034121007/17425000000000000000 : ℝ)+2*(111815989183/87125000000000 : ℝ)*(462/3125 : ℝ))^(2191/512 : ℝ) := by
    rw [show (17420668266034121007/17425000000000000000 : ℝ)+2*(111815989183/87125000000000 : ℝ)*(462/3125 : ℝ)=(5000654409288507/5000000000000000 : ℝ) by norm_num, show 1+2*(28008722620057941/100000000000000000000 : ℝ)=(50028008722620057941/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17420668266034121007/17425000000000000000 : ℝ)*(X 1 0+X 2 0)+(111815989183/87125000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2191/512 : ℝ)) (lo := (11299/100000 : ℝ)) (hi := (462/3125 : ℝ)) (c := (17420668266034121007/17425000000000000000 : ℝ)) (alpha := (111815989183/87125000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17420668266034121007/17425000000000000000 : ℝ)*(X 0 1+X 2 1)+(111815989183/87125000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2191/512 : ℝ)) (lo := (11299/100000 : ℝ)) (hi := (462/3125 : ℝ)) (c := (17420668266034121007/17425000000000000000 : ℝ)) (alpha := (111815989183/87125000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17420668266034121007/17425000000000000000 : ℝ)*(X 0 2+X 1 2)+(111815989183/87125000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2191/512 : ℝ)) (lo := (11299/100000 : ℝ)) (hi := (462/3125 : ℝ)) (c := (17420668266034121007/17425000000000000000 : ℝ)) (alpha := (111815989183/87125000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1975987173/10000000000 : ℝ)*X 0 0+(2704359933/5000000000 : ℝ)*X 0 1+(163956053/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334218897/625000000 : ℝ)*X 1 0+(-1029268091/5000000000 : ℝ)*X 1 1+(5246593211/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336875501/2500000000 : ℝ)*X 2 0+(1311648373/2500000000 : ℝ)*X 2 1+(-1029268137/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2152931229/5000000000 : ℝ)*X 0 0+(2067043753/5000000000 : ℝ)*X 0 1+(140126609/312500000 : ℝ)*X 0 2+(2152931229/5000000000 : ℝ)*X 1 0+(2067043753/5000000000 : ℝ)*X 1 1+(140126609/312500000 : ℝ)*X 1 2+(2152931229/5000000000 : ℝ)*X 2 0+(2067043753/5000000000 : ℝ)*X 2 1+(140126609/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-987999331/5000000000 : ℝ)*X 0 0+(5247179031/10000000000 : ℝ)*X 0 1+(1081626293/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305378593/10000000000 : ℝ)*X 1 0+(-1896997911/10000000000 : ℝ)*X 1 1+(676016433/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((4144827/7812500 : ℝ)*X 2 0+(1352032861/2500000000 : ℝ)*X 2 1+(-59281187/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1076471899/2500000000 : ℝ)*X 0 0+(89655737/200000000 : ℝ)*X 0 1+(4135358297/10000000000 : ℝ)*X 0 2+(1076471899/2500000000 : ℝ)*X 1 0+(89655737/200000000 : ℝ)*X 1 1+(4135358297/10000000000 : ℝ)*X 1 2+(1076471899/2500000000 : ℝ)*X 2 0+(89655737/200000000 : ℝ)*X 2 1+(4135358297/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1423_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3004107007781893815684335859/435625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (338245651/50000000000000 : ℝ)*(base19) + (92280859/25000000000000 : ℝ)*(base23) + (1919443/2500000000000 : ℝ)*(upper2) + (22414067/100000000000000 : ℝ)*(upper3) + (138658211/100000000000000 : ℝ)*(upper5) + (4512744073731721/100000000000000 : ℝ)*(major0) + (4512744073731721/100000000000000 : ℝ)*(major1) + (4512744073731721/100000000000000 : ℝ)*(major2) + (616803644831093/10000000000000 : ℝ)*(sp0) + (1542008942954907/25000000000000 : ℝ)*(sp1) + (3084014894658313/50000000000000 : ℝ)*(sp2) + (2857446094994931/100000000000000 : ℝ)*(sp3) + (1572467717/25000000000000 : ℝ)*(sp6) + (5374288073/100000000000000 : ℝ)*(sp7) + (714362867320751/25000000000000 : ℝ)*(f.failure) + (616803644831093/10000000000000 : ℝ)*(f.sum) + (12648861183257/4356250000000000000000000000 : ℝ)*base66 + (13336226192726963047/1742500000000000000000000000000000 : ℝ)*base67 + (26538471255774463047/1742500000000000000000000000000000 : ℝ)*base69 + (3695669915571963047/1742500000000000000000000000000000 : ℝ)*base71 + (12783144895943/4356250000000000000000000000 : ℝ)*base73 + (26197902718484463047/1742500000000000000000000000000000 : ℝ)*base75 + (9428044681968036953/1742500000000000000000000000000000 : ℝ)*base78 + (10211163955756963047/1742500000000000000000000000000000 : ℝ)*base79 + (61200996671247/17425000000000000000000000000 : ℝ)*base81 + (2181627/312500000000000000000 : ℝ)*base90 + (2181627/312500000000000000000 : ℝ)*base92 + (2181627/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1318060930079507249836385613/174250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6642909/500000000000 : ℝ)*(base19) + (164101123/12500000000000 : ℝ)*(base23) + (38062803/25000000000000 : ℝ)*(upper3) + (3003383/12500000000000 : ℝ)*(lower4) + (35255321/20000000000000 : ℝ)*(upper5) + (909130469314447/20000000000000 : ℝ)*(major0) + (909130469314447/20000000000000 : ℝ)*(major1) + (909130469314447/20000000000000 : ℝ)*(major2) + (28302570823/100000000000000 : ℝ)*(sp1) + (12739802777/50000000000000 : ℝ)*(sp2) + (6213015585190661/100000000000000 : ℝ)*(sp4) + (3106492977019019/50000000000000 : ℝ)*(sp5) + (3106494396388061/50000000000000 : ℝ)*(sp6) + (1439144427906987/50000000000000 : ℝ)*(sp7) + (1439144427906987/50000000000000 : ℝ)*(f.failure) + (6213015585190661/100000000000000 : ℝ)*(f.sum) + (6549649922017/1742500000000000000000000000 : ℝ)*base65 + (657809860872011871/348500000000000000000000000000000 : ℝ)*base68 + (2477125970194011871/348500000000000000000000000000000 : ℝ)*base70 + (13682956092488129/348500000000000000000000000000000 : ℝ)*base71 + (1822610111589/871250000000000000000000000 : ℝ)*base74 + (3384343650685988129/348500000000000000000000000000000 : ℝ)*base75 + (3731732466451488129/348500000000000000000000000000000 : ℝ)*base77 + (5180330011245488129/348500000000000000000000000000000 : ℝ)*base79 + (5250677717643/1742500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (5823599/625000000000000000000 : ℝ)*base90 + (5823599/625000000000000000000 : ℝ)*base92 + (5823599/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1423_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19741123/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (462/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11299/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2831/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7379/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1423_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1423_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19741123/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7909/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2067/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2831/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7379/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1423_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1423_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1423_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2191/512 : ℝ) ≤ p) (hpb : p ≤ (4383/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19741123/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7909/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2067/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2831/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7379/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1423_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
