-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1420_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:51:25.651132+00:00
-- url     : https://prove2.me/submissions/b10504d6-07aa-4e46-9a7f-fb288f0e06ba

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
theorem support_rectangle_w1420_s0_0 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-176392047/1000000000 : ℝ)*x 0 + (5963903849/10000000000 : ℝ)*x 1 + (1207293779/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (176392047/1000000000 : ℝ)^1095 ≤ (10388690138337/100000000000000 : ℝ)^839 := by
    have hnat : (176392047 : ℕ)^1095*100000000000000^839 ≤ 10388690138337^839*1000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      176392047 1000000000 10388690138337 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5963903849/10000000000 : ℝ)^1095 ≤ (12734426547051/25000000000000 : ℝ)^839 := by
    have hnat : (5963903849 : ℕ)^1095*25000000000000^839 ≤ 12734426547051^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5963903849 10000000000 12734426547051 25000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1207293779/2500000000 : ℝ)^1095 ≤ (38673603661559/100000000000000 : ℝ)^839 := by
    have hnat : (1207293779 : ℕ)^1095*100000000000000^839 ≤ 38673603661559^839*2500000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1207293779 2500000000 38673603661559 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-176392047/1000000000 : ℝ), (5963903849/10000000000 : ℝ), (1207293779/2500000000 : ℝ)] ![(10388690138337/100000000000000 : ℝ), (12734426547051/25000000000000 : ℝ), (38673603661559/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-176392047/1000000000 : ℝ)|^1095 ≤ (10388690138337/100000000000000 : ℝ)^839
        have hw : |(-176392047/1000000000 : ℝ)|=(176392047/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5963903849/10000000000 : ℝ)|^1095 ≤ (12734426547051/25000000000000 : ℝ)^839
        have hw : |(5963903849/10000000000 : ℝ)|=(5963903849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1207293779/2500000000 : ℝ)|^1095 ≤ (38673603661559/100000000000000 : ℝ)^839
        have hw : |(1207293779/2500000000 : ℝ)|=(1207293779/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_s0_1 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5493100707/10000000000 : ℝ)*x 0 + (-481065147/2000000000 : ℝ)*x 1 + (603646937/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5493100707/10000000000 : ℝ)^1095 ≤ (45754030332671/100000000000000 : ℝ)^839 := by
    have hnat : (5493100707 : ℕ)^1095*100000000000000^839 ≤ 45754030332671^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5493100707 10000000000 45754030332671 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (481065147/2000000000 : ℝ)^1095 ≤ (15572362013851/100000000000000 : ℝ)^839 := by
    have hnat : (481065147 : ℕ)^1095*100000000000000^839 ≤ 15572362013851^839*2000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      481065147 2000000000 15572362013851 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (603646937/1250000000 : ℝ)^1095 ≤ (38673607633269/100000000000000 : ℝ)^839 := by
    have hnat : (603646937 : ℕ)^1095*100000000000000^839 ≤ 38673607633269^839*1250000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      603646937 1250000000 38673607633269 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5493100707/10000000000 : ℝ), (-481065147/2000000000 : ℝ), (603646937/1250000000 : ℝ)] ![(45754030332671/100000000000000 : ℝ), (15572362013851/100000000000000 : ℝ), (38673607633269/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5493100707/10000000000 : ℝ)|^1095 ≤ (45754030332671/100000000000000 : ℝ)^839
        have hw : |(5493100707/10000000000 : ℝ)|=(5493100707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-481065147/2000000000 : ℝ)|^1095 ≤ (15572362013851/100000000000000 : ℝ)^839
        have hw : |(-481065147/2000000000 : ℝ)|=(481065147/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(603646937/1250000000 : ℝ)|^1095 ≤ (38673607633269/100000000000000 : ℝ)^839
        have hw : |(603646937/1250000000 : ℝ)|=(603646937/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_s0_2 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (68663763/125000000 : ℝ)*x 0 + (4829175337/10000000000 : ℝ)*x 1 + (-37583211/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (68663763/125000000 : ℝ)^1095 ≤ (11438508488167/25000000000000 : ℝ)^839 := by
    have hnat : (68663763 : ℕ)^1095*25000000000000^839 ≤ 11438508488167^839*125000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68663763 125000000 11438508488167 25000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4829175337/10000000000 : ℝ)^1095 ≤ (19336802985711/50000000000000 : ℝ)^839 := by
    have hnat : (4829175337 : ℕ)^1095*50000000000000^839 ≤ 19336802985711^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4829175337 10000000000 19336802985711 50000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (37583211/156250000 : ℝ)^1095 ≤ (15572360062009/100000000000000 : ℝ)^839 := by
    have hnat : (37583211 : ℕ)^1095*100000000000000^839 ≤ 15572360062009^839*156250000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37583211 156250000 15572360062009 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(68663763/125000000 : ℝ), (4829175337/10000000000 : ℝ), (-37583211/156250000 : ℝ)] ![(11438508488167/25000000000000 : ℝ), (19336802985711/50000000000000 : ℝ), (15572360062009/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(68663763/125000000 : ℝ)|^1095 ≤ (11438508488167/25000000000000 : ℝ)^839
        have hw : |(68663763/125000000 : ℝ)|=(68663763/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4829175337/10000000000 : ℝ)|^1095 ≤ (19336802985711/50000000000000 : ℝ)^839
        have hw : |(4829175337/10000000000 : ℝ)|=(4829175337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-37583211/156250000 : ℝ)|^1095 ≤ (15572360062009/100000000000000 : ℝ)^839
        have hw : |(-37583211/156250000 : ℝ)|=(37583211/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_s0_3 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2083647201/5000000000 : ℝ)*x 0 + (620717977/2000000000 : ℝ)*x 1 + (693786969/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2083647201/5000000000 : ℝ)^1095 ≤ (31905248641303/100000000000000 : ℝ)^839 := by
    have hnat : (2083647201 : ℕ)^1095*100000000000000^839 ≤ 31905248641303^839*5000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2083647201 5000000000 31905248641303 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (620717977/2000000000 : ℝ)^1095 ≤ (10858988155523/50000000000000 : ℝ)^839 := by
    have hnat : (620717977 : ℕ)^1095*50000000000000^839 ≤ 10858988155523^839*2000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      620717977 2000000000 10858988155523 50000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (693786969/1250000000 : ℝ)^1095 ≤ (46376775028431/100000000000000 : ℝ)^839 := by
    have hnat : (693786969 : ℕ)^1095*100000000000000^839 ≤ 46376775028431^839*1250000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      693786969 1250000000 46376775028431 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2083647201/5000000000 : ℝ), (620717977/2000000000 : ℝ), (693786969/1250000000 : ℝ)] ![(31905248641303/100000000000000 : ℝ), (10858988155523/50000000000000 : ℝ), (46376775028431/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2083647201/5000000000 : ℝ)|^1095 ≤ (31905248641303/100000000000000 : ℝ)^839
        have hw : |(2083647201/5000000000 : ℝ)|=(2083647201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(620717977/2000000000 : ℝ)|^1095 ≤ (10858988155523/50000000000000 : ℝ)^839
        have hw : |(620717977/2000000000 : ℝ)|=(620717977/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(693786969/1250000000 : ℝ)|^1095 ≤ (46376775028431/100000000000000 : ℝ)^839
        have hw : |(693786969/1250000000 : ℝ)|=(693786969/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_s0_4 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-55249417/312500000 : ℝ)*x 0 + (4858228043/10000000000 : ℝ)*x 1 + (11867627/20000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (55249417/312500000 : ℝ)^1095 ≤ (325622355817/3125000000000 : ℝ)^839 := by
    have hnat : (55249417 : ℕ)^1095*3125000000000^839 ≤ 325622355817^839*312500000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55249417 312500000 325622355817 3125000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4858228043/10000000000 : ℝ)^1095 ≤ (19488769645427/50000000000000 : ℝ)^839 := by
    have hnat : (4858228043 : ℕ)^1095*50000000000000^839 ≤ 19488769645427^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4858228043 10000000000 19488769645427 50000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (11867627/20000000 : ℝ)^1095 ≤ (2530127265511/5000000000000 : ℝ)^839 := by
    have hnat : (11867627 : ℕ)^1095*5000000000000^839 ≤ 2530127265511^839*20000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11867627 20000000 2530127265511 5000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-55249417/312500000 : ℝ), (4858228043/10000000000 : ℝ), (11867627/20000000 : ℝ)] ![(325622355817/3125000000000 : ℝ), (19488769645427/50000000000000 : ℝ), (2530127265511/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-55249417/312500000 : ℝ)|^1095 ≤ (325622355817/3125000000000 : ℝ)^839
        have hw : |(-55249417/312500000 : ℝ)|=(55249417/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4858228043/10000000000 : ℝ)|^1095 ≤ (19488769645427/50000000000000 : ℝ)^839
        have hw : |(4858228043/10000000000 : ℝ)|=(4858228043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(11867627/20000000 : ℝ)|^1095 ≤ (2530127265511/5000000000000 : ℝ)^839
        have hw : |(11867627/20000000 : ℝ)|=(11867627/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_s0_5 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1036685989/2000000000 : ℝ)*x 0 + (-20323237/156250000 : ℝ)*x 1 + (1186762717/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1036685989/2000000000 : ℝ)^1095 ≤ (42416982902929/100000000000000 : ℝ)^839 := by
    have hnat : (1036685989 : ℕ)^1095*100000000000000^839 ≤ 42416982902929^839*2000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036685989 2000000000 42416982902929 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (20323237/156250000 : ℝ)^1095 ≤ (436279426603/6250000000000 : ℝ)^839 := by
    have hnat : (20323237 : ℕ)^1095*6250000000000^839 ≤ 436279426603^839*156250000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20323237 156250000 436279426603 6250000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1186762717/2000000000 : ℝ)^1095 ≤ (2530127312813/5000000000000 : ℝ)^839 := by
    have hnat : (1186762717 : ℕ)^1095*5000000000000^839 ≤ 2530127312813^839*2000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1186762717 2000000000 2530127312813 5000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1036685989/2000000000 : ℝ), (-20323237/156250000 : ℝ), (1186762717/2000000000 : ℝ)] ![(42416982902929/100000000000000 : ℝ), (436279426603/6250000000000 : ℝ), (2530127312813/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1036685989/2000000000 : ℝ)|^1095 ≤ (42416982902929/100000000000000 : ℝ)^839
        have hw : |(1036685989/2000000000 : ℝ)|=(1036685989/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-20323237/156250000 : ℝ)|^1095 ≤ (436279426603/6250000000000 : ℝ)^839
        have hw : |(-20323237/156250000 : ℝ)|=(20323237/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1186762717/2000000000 : ℝ)|^1095 ≤ (2530127312813/5000000000000 : ℝ)^839
        have hw : |(1186762717/2000000000 : ℝ)|=(1186762717/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_s0_6 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5183429963/10000000000 : ℝ)*x 0 + (593381341/1000000000 : ℝ)*x 1 + (-65034371/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5183429963/10000000000 : ℝ)^1095 ≤ (42416983095171/100000000000000 : ℝ)^839 := by
    have hnat : (5183429963 : ℕ)^1095*100000000000000^839 ≤ 42416983095171^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183429963 10000000000 42416983095171 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (593381341/1000000000 : ℝ)^1095 ≤ (50602544308531/100000000000000 : ℝ)^839 := by
    have hnat : (593381341 : ℕ)^1095*100000000000000^839 ≤ 50602544308531^839*1000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      593381341 1000000000 50602544308531 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (65034371/500000000 : ℝ)^1095 ≤ (6980472590729/100000000000000 : ℝ)^839 := by
    have hnat : (65034371 : ℕ)^1095*100000000000000^839 ≤ 6980472590729^839*500000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65034371 500000000 6980472590729 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5183429963/10000000000 : ℝ), (593381341/1000000000 : ℝ), (-65034371/500000000 : ℝ)] ![(42416983095171/100000000000000 : ℝ), (50602544308531/100000000000000 : ℝ), (6980472590729/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5183429963/10000000000 : ℝ)|^1095 ≤ (42416983095171/100000000000000 : ℝ)^839
        have hw : |(5183429963/10000000000 : ℝ)|=(5183429963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(593381341/1000000000 : ℝ)|^1095 ≤ (50602544308531/100000000000000 : ℝ)^839
        have hw : |(593381341/1000000000 : ℝ)|=(593381341/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-65034371/500000000 : ℝ)|^1095 ≤ (6980472590729/100000000000000 : ℝ)^839
        have hw : |(-65034371/500000000 : ℝ)|=(65034371/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_s0_7 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4176052393/10000000000 : ℝ)*x 0 + (5487651623/10000000000 : ℝ)*x 1 + (1584235559/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4176052393/10000000000 : ℝ)^1095 ≤ (15996394040213/50000000000000 : ℝ)^839 := by
    have hnat : (4176052393 : ℕ)^1095*50000000000000^839 ≤ 15996394040213^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4176052393 10000000000 15996394040213 50000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5487651623/10000000000 : ℝ)^1095 ≤ (2855925191463/6250000000000 : ℝ)^839 := by
    have hnat : (5487651623 : ℕ)^1095*6250000000000^839 ≤ 2855925191463^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5487651623 10000000000 2855925191463 6250000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1584235559/5000000000 : ℝ)^1095 ≤ (11156204420547/50000000000000 : ℝ)^839 := by
    have hnat : (1584235559 : ℕ)^1095*50000000000000^839 ≤ 11156204420547^839*5000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1584235559 5000000000 11156204420547 50000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4176052393/10000000000 : ℝ), (5487651623/10000000000 : ℝ), (1584235559/5000000000 : ℝ)] ![(15996394040213/50000000000000 : ℝ), (2855925191463/6250000000000 : ℝ), (11156204420547/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4176052393/10000000000 : ℝ)|^1095 ≤ (15996394040213/50000000000000 : ℝ)^839
        have hw : |(4176052393/10000000000 : ℝ)|=(4176052393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5487651623/10000000000 : ℝ)|^1095 ≤ (2855925191463/6250000000000 : ℝ)^839
        have hw : |(5487651623/10000000000 : ℝ)|=(5487651623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1584235559/5000000000 : ℝ)|^1095 ≤ (11156204420547/50000000000000 : ℝ)^839
        have hw : |(1584235559/5000000000 : ℝ)|=(1584235559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1420_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157810149/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (62/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (329/1250 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4379/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4379 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4379*1^1024 ≤ 0^1024*1^4379 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4379 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4379 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4379/1024 : ℝ) ≤ (397459058990315913/20000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4379 ≤ (397459058990315913/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4379*20000000000000000000^1024 ≤ 397459058990315913^1024*5^4379 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 397459058990315913 20000000000000000000 4379 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (397459058990315913/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4379 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4379/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4379 := by
      have hnat : (1 : ℕ)^1024*1^4379 ≤ 1^4379*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4379 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4379 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20397459058990315913/20000000000000000000 : ℝ) ≤ (10046121877286651/10000000000000000 : ℝ) ^ (4379/1024 : ℝ) := by
    have hpowers : (20397459058990315913/20000000000000000000 : ℝ)^1024 ≤ (10046121877286651/10000000000000000 : ℝ)^4379 := by
      have hnat : (20397459058990315913 : ℕ)^1024*10000000000000000^4379 ≤ 10046121877286651^4379*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20397459058990315913 20000000000000000000 10046121877286651 10000000000000000 1024 4379 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10046121877286651/10000000000000000 : ℝ)) (X := (20397459058990315913/20000000000000000000 : ℝ)) (by norm_num) 4379 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10397459058990315913/10000000000000000000 : ℝ) ≤ (5046121877286651/5000000000000000 : ℝ) ^ (4379/1024 : ℝ) := by
    have hpowers : (10397459058990315913/10000000000000000000 : ℝ)^1024 ≤ (5046121877286651/5000000000000000 : ℝ)^4379 := by
      have hnat : (10397459058990315913 : ℕ)^1024*5000000000000000^4379 ≤ 5046121877286651^4379*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10397459058990315913 10000000000000000000 5046121877286651 5000000000000000 1024 4379 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5046121877286651/5000000000000000 : ℝ)) (X := (10397459058990315913/10000000000000000000 : ℝ)) (by norm_num) 4379 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(46121877286651/4000000000000000 : ℝ)*(0 : ℝ))^(4379/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(46121877286651/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(397459058990315913/20000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(46121877286651/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4379/1024 : ℝ) := by
    rw [show (1 : ℝ)+(46121877286651/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10046121877286651/10000000000000000 : ℝ) by norm_num, show 1+(397459058990315913/20000000000000000000 : ℝ)+(0 : ℝ)=(20397459058990315913/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(397459058990315913/20000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(46121877286651/4000000000000000 : ℝ)*(2/5 : ℝ))^(4379/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(46121877286651/4000000000000000 : ℝ)*(2/5 : ℝ)=(5046121877286651/5000000000000000 : ℝ) by norm_num, show 1+2*(397459058990315913/20000000000000000000 : ℝ)=(10397459058990315913/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(46121877286651/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4379/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (46121877286651/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(46121877286651/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4379/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (46121877286651/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(46121877286651/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4379/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (46121877286651/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-176392047/1000000000 : ℝ)*X 0 0+(5963903849/10000000000 : ℝ)*X 0 1+(1207293779/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5493100707/10000000000 : ℝ)*X 1 0+(-481065147/2000000000 : ℝ)*X 1 1+(603646937/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((68663763/125000000 : ℝ)*X 2 0+(4829175337/10000000000 : ℝ)*X 2 1+(-37583211/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2083647201/5000000000 : ℝ)*X 0 0+(620717977/2000000000 : ℝ)*X 0 1+(693786969/1250000000 : ℝ)*X 0 2+(2083647201/5000000000 : ℝ)*X 1 0+(620717977/2000000000 : ℝ)*X 1 1+(693786969/1250000000 : ℝ)*X 1 2+(2083647201/5000000000 : ℝ)*X 2 0+(620717977/2000000000 : ℝ)*X 2 1+(693786969/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-55249417/312500000 : ℝ)*X 0 0+(4858228043/10000000000 : ℝ)*X 0 1+(11867627/20000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1036685989/2000000000 : ℝ)*X 1 0+(-20323237/156250000 : ℝ)*X 1 1+(1186762717/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5183429963/10000000000 : ℝ)*X 2 0+(593381341/1000000000 : ℝ)*X 2 1+(-65034371/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4176052393/10000000000 : ℝ)*X 0 0+(5487651623/10000000000 : ℝ)*X 0 1+(1584235559/5000000000 : ℝ)*X 0 2+(4176052393/10000000000 : ℝ)*X 1 0+(5487651623/10000000000 : ℝ)*X 1 1+(1584235559/5000000000 : ℝ)*X 1 2+(4176052393/10000000000 : ℝ)*X 2 0+(5487651623/10000000000 : ℝ)*X 2 1+(1584235559/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (205402464421820266154901/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1018010683/100000000000000 : ℝ)*(base19) + (1026890653/100000000000000 : ℝ)*(base23) + (58722663/50000000000000 : ℝ)*(upper3) + (978743/4000000000000 : ℝ)*(upper4) + (31109133/20000000000000 : ℝ)*(upper5) + (322497940975639/50000000000000 : ℝ)*(major0) + (322497940975639/50000000000000 : ℝ)*(major1) + (322497940975639/50000000000000 : ℝ)*(major2) + (440635635517831/50000000000000 : ℝ)*(sp0) + (440637129152447/50000000000000 : ℝ)*(sp1) + (881274249424923/100000000000000 : ℝ)*(sp2) + (408714559377807/100000000000000 : ℝ)*(sp3) + (2002639957/50000000000000 : ℝ)*(sp4) + (179127419/10000000000000 : ℝ)*(sp7) + (102179087662999/25000000000000 : ℝ)*(f.failure) + (110159409539447/12500000000000 : ℝ)*(f.sum) + (123871741905011/100000000000000000000000000000 : ℝ)*base66 + (114303770105011/200000000000000000000000000000 : ℝ)*base68 + (928776204305011/200000000000000000000000000000 : ℝ)*base70 + (607913617505011/200000000000000000000000000000 : ℝ)*base72 + (28321536605011/100000000000000000000000000000 : ℝ)*base74 + (1558906530705011/200000000000000000000000000000 : ℝ)*base76 + (623965589905011/200000000000000000000000000000 : ℝ)*base78 + (15750312305011/200000000000000000000000000000 : ℝ)*base80 + (437155398305011/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (16023149/2500000000000000000000 : ℝ)*base90 + (16023149/2500000000000000000000 : ℝ)*base92 + (16023149/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (69383925119345535182787/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (194972417/25000000000000 : ℝ)*(base19) + (392709801/50000000000000 : ℝ)*(base23) + (31189887/25000000000000 : ℝ)*(base32) + (125573971/100000000000000 : ℝ)*(upper3) + (25085851/50000000000000 : ℝ)*(upper5) + (68045619509421/10000000000000 : ℝ)*(major0) + (68045619509421/10000000000000 : ℝ)*(major1) + (68045619509421/10000000000000 : ℝ)*(major2) + (1805535919/100000000000000 : ℝ)*(sp1) + (11525347/625000000000 : ℝ)*(sp2) + (464862843875183/50000000000000 : ℝ)*(sp4) + (46486155116239/5000000000000 : ℝ)*(sp5) + (185944611655049/20000000000000 : ℝ)*(sp6) + (13474576938707/3125000000000 : ℝ)*(sp7) + (107796646699543/25000000000000 : ℝ)*(f.failure) + (464862843875183/50000000000000 : ℝ)*(f.sum) + (652105479071/20000000000000000000000000000 : ℝ)*base65 + (117901192439071/40000000000000000000000000000 : ℝ)*base67 + (17226893240929/40000000000000000000000000000 : ℝ)*base70 + (193577150560929/40000000000000000000000000000 : ℝ)*base72 + (77975447099071/20000000000000000000000000000 : ℝ)*base73 + (234348338200929/40000000000000000000000000000 : ℝ)*base76 + (106520146640929/40000000000000000000000000000 : ℝ)*base78 + (194500085640929/40000000000000000000000000000 : ℝ)*base80 + (12029978999071/20000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (10938093/2500000000000000000000 : ℝ)*base90 + (10938093/2500000000000000000000 : ℝ)*base92 + (10938093/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1420_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157810149/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (62/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (329/1250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1420_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1420_s1_0 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-484389209/2500000000 : ℝ)*x 0 + (350552729/625000000 : ℝ)*x 1 + (5072935651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (484389209/2500000000 : ℝ)^1095 ≤ (2935741875741/25000000000000 : ℝ)^839 := by
    have hnat : (484389209 : ℕ)^1095*25000000000000^839 ≤ 2935741875741^839*2500000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      484389209 2500000000 2935741875741 25000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (350552729/625000000 : ℝ)^1095 ≤ (235081405341/500000000000 : ℝ)^839 := by
    have hnat : (350552729 : ℕ)^1095*500000000000^839 ≤ 235081405341^839*625000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      350552729 625000000 235081405341 500000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5072935651/10000000000 : ℝ)^1095 ≤ (41240751425673/100000000000000 : ℝ)^839 := by
    have hnat : (5072935651 : ℕ)^1095*100000000000000^839 ≤ 41240751425673^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5072935651 10000000000 41240751425673 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-484389209/2500000000 : ℝ), (350552729/625000000 : ℝ), (5072935651/10000000000 : ℝ)] ![(2935741875741/25000000000000 : ℝ), (235081405341/500000000000 : ℝ), (41240751425673/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-484389209/2500000000 : ℝ)|^1095 ≤ (2935741875741/25000000000000 : ℝ)^839
        have hw : |(-484389209/2500000000 : ℝ)|=(484389209/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(350552729/625000000 : ℝ)|^1095 ≤ (235081405341/500000000000 : ℝ)^839
        have hw : |(350552729/625000000 : ℝ)|=(350552729/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5072935651/10000000000 : ℝ)|^1095 ≤ (41240751425673/100000000000000 : ℝ)^839
        have hw : |(5072935651/10000000000 : ℝ)|=(5072935651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_s1_1 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5397713703/10000000000 : ℝ)*x 0 + (-2221726329/10000000000 : ℝ)*x 1 + (5072932883/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5397713703/10000000000 : ℝ)^1095 ≤ (44719849667291/100000000000000 : ℝ)^839 := by
    have hnat : (5397713703 : ℕ)^1095*100000000000000^839 ≤ 44719849667291^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397713703 10000000000 44719849667291 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2221726329/10000000000 : ℝ)^1095 ≤ (14039428262303/100000000000000 : ℝ)^839 := by
    have hnat : (2221726329 : ℕ)^1095*100000000000000^839 ≤ 14039428262303^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2221726329 10000000000 14039428262303 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5072932883/10000000000 : ℝ)^1095 ≤ (1649628882277/4000000000000 : ℝ)^839 := by
    have hnat : (5072932883 : ℕ)^1095*4000000000000^839 ≤ 1649628882277^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5072932883 10000000000 1649628882277 4000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5397713703/10000000000 : ℝ), (-2221726329/10000000000 : ℝ), (5072932883/10000000000 : ℝ)] ![(44719849667291/100000000000000 : ℝ), (14039428262303/100000000000000 : ℝ), (1649628882277/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5397713703/10000000000 : ℝ)|^1095 ≤ (44719849667291/100000000000000 : ℝ)^839
        have hw : |(5397713703/10000000000 : ℝ)|=(5397713703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2221726329/10000000000 : ℝ)|^1095 ≤ (14039428262303/100000000000000 : ℝ)^839
        have hw : |(-2221726329/10000000000 : ℝ)|=(2221726329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5072932883/10000000000 : ℝ)|^1095 ≤ (1649628882277/4000000000000 : ℝ)^839
        have hw : |(5072932883/10000000000 : ℝ)|=(5072932883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_s1_2 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1079542401/2000000000 : ℝ)*x 0 + (5072935383/10000000000 : ℝ)*x 1 + (-2221725339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079542401/2000000000 : ℝ)^1095 ≤ (5589978913371/12500000000000 : ℝ)^839 := by
    have hnat : (1079542401 : ℕ)^1095*12500000000000^839 ≤ 5589978913371^839*2000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079542401 2000000000 5589978913371 12500000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5072935383/10000000000 : ℝ)^1095 ≤ (20620374291083/50000000000000 : ℝ)^839 := by
    have hnat : (5072935383 : ℕ)^1095*50000000000000^839 ≤ 20620374291083^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5072935383 10000000000 20620374291083 50000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2221725339/10000000000 : ℝ)^1095 ≤ (14039420097491/100000000000000 : ℝ)^839 := by
    have hnat : (2221725339 : ℕ)^1095*100000000000000^839 ≤ 14039420097491^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2221725339 10000000000 14039420097491 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1079542401/2000000000 : ℝ), (5072935383/10000000000 : ℝ), (-2221725339/10000000000 : ℝ)] ![(5589978913371/12500000000000 : ℝ), (20620374291083/50000000000000 : ℝ), (14039420097491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1079542401/2000000000 : ℝ)|^1095 ≤ (5589978913371/12500000000000 : ℝ)^839
        have hw : |(1079542401/2000000000 : ℝ)|=(1079542401/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5072935383/10000000000 : ℝ)|^1095 ≤ (20620374291083/50000000000000 : ℝ)^839
        have hw : |(5072935383/10000000000 : ℝ)|=(5072935383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2221725339/10000000000 : ℝ)|^1095 ≤ (14039420097491/100000000000000 : ℝ)^839
        have hw : |(-2221725339/10000000000 : ℝ)|=(2221725339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_s1_3 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4278276883/10000000000 : ℝ)*x 0 + (3735465613/10000000000 : ℝ)*x 1 + (2445500097/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4278276883/10000000000 : ℝ)^1095 ≤ (16509341716229/50000000000000 : ℝ)^839 := by
    have hnat : (4278276883 : ℕ)^1095*50000000000000^839 ≤ 16509341716229^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4278276883 10000000000 16509341716229 50000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3735465613/10000000000 : ℝ)^1095 ≤ (54023959087/195312500000 : ℝ)^839 := by
    have hnat : (3735465613 : ℕ)^1095*195312500000^839 ≤ 54023959087^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3735465613 10000000000 54023959087 195312500000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2445500097/5000000000 : ℝ)^1095 ≤ (9830262375627/25000000000000 : ℝ)^839 := by
    have hnat : (2445500097 : ℕ)^1095*25000000000000^839 ≤ 9830262375627^839*5000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2445500097 5000000000 9830262375627 25000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4278276883/10000000000 : ℝ), (3735465613/10000000000 : ℝ), (2445500097/5000000000 : ℝ)] ![(16509341716229/50000000000000 : ℝ), (54023959087/195312500000 : ℝ), (9830262375627/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4278276883/10000000000 : ℝ)|^1095 ≤ (16509341716229/50000000000000 : ℝ)^839
        have hw : |(4278276883/10000000000 : ℝ)|=(4278276883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3735465613/10000000000 : ℝ)|^1095 ≤ (54023959087/195312500000 : ℝ)^839
        have hw : |(3735465613/10000000000 : ℝ)|=(3735465613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2445500097/5000000000 : ℝ)|^1095 ≤ (9830262375627/25000000000000 : ℝ)^839
        have hw : |(2445500097/5000000000 : ℝ)|=(2445500097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_s1_4 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1937966609/10000000000 : ℝ)*x 0 + (1269815561/2500000000 : ℝ)*x 1 + (2801204707/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1937966609/10000000000 : ℝ)^1095 ≤ (5873104452563/50000000000000 : ℝ)^839 := by
    have hnat : (1937966609 : ℕ)^1095*50000000000000^839 ≤ 5873104452563^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1937966609 10000000000 5873104452563 50000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1269815561/2500000000 : ℝ)^1095 ≤ (1290871561319/3125000000000 : ℝ)^839 := by
    have hnat : (1269815561 : ℕ)^1095*3125000000000^839 ≤ 1290871561319^839*2500000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1269815561 2500000000 1290871561319 3125000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2801204707/5000000000 : ℝ)^1095 ≤ (23472950555851/50000000000000 : ℝ)^839 := by
    have hnat : (2801204707 : ℕ)^1095*50000000000000^839 ≤ 23472950555851^839*5000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2801204707 5000000000 23472950555851 50000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1937966609/10000000000 : ℝ), (1269815561/2500000000 : ℝ), (2801204707/5000000000 : ℝ)] ![(5873104452563/50000000000000 : ℝ), (1290871561319/3125000000000 : ℝ), (23472950555851/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1937966609/10000000000 : ℝ)|^1095 ≤ (5873104452563/50000000000000 : ℝ)^839
        have hw : |(-1937966609/10000000000 : ℝ)|=(1937966609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1269815561/2500000000 : ℝ)|^1095 ≤ (1290871561319/3125000000000 : ℝ)^839
        have hw : |(1269815561/2500000000 : ℝ)|=(1269815561/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2801204707/5000000000 : ℝ)|^1095 ≤ (23472950555851/50000000000000 : ℝ)^839
        have hw : |(2801204707/5000000000 : ℝ)|=(2801204707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_s1_5 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1314447003/2500000000 : ℝ)*x 0 + (-1692249621/10000000000 : ℝ)*x 1 + (5602409423/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1314447003/2500000000 : ℝ)^1095 ≤ (21606432833989/50000000000000 : ℝ)^839 := by
    have hnat : (1314447003 : ℕ)^1095*50000000000000^839 ≤ 21606432833989^839*2500000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314447003 2500000000 21606432833989 50000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1692249621/10000000000 : ℝ)^1095 ≤ (2460308273497/25000000000000 : ℝ)^839 := by
    have hnat : (1692249621 : ℕ)^1095*25000000000000^839 ≤ 2460308273497^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1692249621 10000000000 2460308273497 25000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5602409423/10000000000 : ℝ)^1095 ≤ (4694590121013/10000000000000 : ℝ)^839 := by
    have hnat : (5602409423 : ℕ)^1095*10000000000000^839 ≤ 4694590121013^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5602409423 10000000000 4694590121013 10000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1314447003/2500000000 : ℝ), (-1692249621/10000000000 : ℝ), (5602409423/10000000000 : ℝ)] ![(21606432833989/50000000000000 : ℝ), (2460308273497/25000000000000 : ℝ), (4694590121013/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1314447003/2500000000 : ℝ)|^1095 ≤ (21606432833989/50000000000000 : ℝ)^839
        have hw : |(1314447003/2500000000 : ℝ)|=(1314447003/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1692249621/10000000000 : ℝ)|^1095 ≤ (2460308273497/25000000000000 : ℝ)^839
        have hw : |(-1692249621/10000000000 : ℝ)|=(1692249621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5602409423/10000000000 : ℝ)|^1095 ≤ (4694590121013/10000000000000 : ℝ)^839
        have hw : |(5602409423/10000000000 : ℝ)|=(5602409423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_s1_6 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (328611749/625000000 : ℝ)*x 0 + (1400602347/2500000000 : ℝ)*x 1 + (-105765607/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (328611749/625000000 : ℝ)^1095 ≤ (21606432683817/50000000000000 : ℝ)^839 := by
    have hnat : (328611749 : ℕ)^1095*50000000000000^839 ≤ 21606432683817^839*625000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328611749 625000000 21606432683817 50000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1400602347/2500000000 : ℝ)^1095 ≤ (9389180165471/20000000000000 : ℝ)^839 := by
    have hnat : (1400602347 : ℕ)^1095*20000000000000^839 ≤ 9389180165471^839*2500000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1400602347 2500000000 9389180165471 20000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105765607/625000000 : ℝ)^1095 ≤ (9841233784671/100000000000000 : ℝ)^839 := by
    have hnat : (105765607 : ℕ)^1095*100000000000000^839 ≤ 9841233784671^839*625000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105765607 625000000 9841233784671 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(328611749/625000000 : ℝ), (1400602347/2500000000 : ℝ), (-105765607/625000000 : ℝ)] ![(21606432683817/50000000000000 : ℝ), (9389180165471/20000000000000 : ℝ), (9841233784671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(328611749/625000000 : ℝ)|^1095 ≤ (21606432683817/50000000000000 : ℝ)^839
        have hw : |(328611749/625000000 : ℝ)|=(328611749/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1400602347/2500000000 : ℝ)|^1095 ≤ (9389180165471/20000000000000 : ℝ)^839
        have hw : |(1400602347/2500000000 : ℝ)|=(1400602347/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-105765607/625000000 : ℝ)|^1095 ≤ (9841233784671/100000000000000 : ℝ)^839
        have hw : |(-105765607/625000000 : ℝ)|=(105765607/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_s1_7 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4279159947/10000000000 : ℝ)*x 0 + (1219339049/2500000000 : ℝ)*x 1 + (3749344517/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4279159947/10000000000 : ℝ)^1095 ≤ (33027578492379/100000000000000 : ℝ)^839 := by
    have hnat : (4279159947 : ℕ)^1095*100000000000000^839 ≤ 33027578492379^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4279159947 10000000000 33027578492379 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1219339049/2500000000 : ℝ)^1095 ≤ (39177950622171/100000000000000 : ℝ)^839 := by
    have hnat : (1219339049 : ℕ)^1095*100000000000000^839 ≤ 39177950622171^839*2500000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1219339049 2500000000 39177950622171 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3749344517/10000000000 : ℝ)^1095 ≤ (13897235431853/50000000000000 : ℝ)^839 := by
    have hnat : (3749344517 : ℕ)^1095*50000000000000^839 ≤ 13897235431853^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3749344517 10000000000 13897235431853 50000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4279159947/10000000000 : ℝ), (1219339049/2500000000 : ℝ), (3749344517/10000000000 : ℝ)] ![(33027578492379/100000000000000 : ℝ), (39177950622171/100000000000000 : ℝ), (13897235431853/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4279159947/10000000000 : ℝ)|^1095 ≤ (33027578492379/100000000000000 : ℝ)^839
        have hw : |(4279159947/10000000000 : ℝ)|=(4279159947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1219339049/2500000000 : ℝ)|^1095 ≤ (39177950622171/100000000000000 : ℝ)^839
        have hw : |(1219339049/2500000000 : ℝ)|=(1219339049/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3749344517/10000000000 : ℝ)|^1095 ≤ (13897235431853/50000000000000 : ℝ)^839
        have hw : |(3749344517/10000000000 : ℝ)|=(3749344517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1420_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157810149/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (329/1250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (62/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (7577/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9453/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (329/1250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (62/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (329/1250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (62/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (329/1250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (62/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (329/1250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (62/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (329/1250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (62/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (329/1250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (62/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (62/3125 : ℝ) ^ (4379/1024 : ℝ) ≤ (1311001108323/25000000000000000000 : ℝ) := by
    have hpowers : (62/3125 : ℝ)^4379 ≤ (1311001108323/25000000000000000000 : ℝ)^1024 := by
      have hnat : (62 : ℕ)^4379*25000000000000000000^1024 ≤ 1311001108323^1024*3125^4379 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        62 3125 1311001108323 25000000000000000000 4379 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (62/3125 : ℝ)) (X := (1311001108323/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4379 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (329/1250 : ℝ) ^ (4379/1024 : ℝ) ≤ (82960161514626729/25000000000000000000 : ℝ) := by
    have hpowers : (329/1250 : ℝ)^4379 ≤ (82960161514626729/25000000000000000000 : ℝ)^1024 := by
      have hnat : (329 : ℕ)^4379*25000000000000000000^1024 ≤ 82960161514626729^1024*1250^4379 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        329 1250 82960161514626729 25000000000000000000 4379 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (329/1250 : ℝ)) (X := (82960161514626729/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4379 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500001311001108323/12500000000000000000 : ℝ) ≤ (1250000030656887/1250000000000000 : ℝ) ^ (4379/1024 : ℝ) := by
    have hpowers : (12500001311001108323/12500000000000000000 : ℝ)^1024 ≤ (1250000030656887/1250000000000000 : ℝ)^4379 := by
      have hnat : (12500001311001108323 : ℕ)^1024*1250000000000000^4379 ≤ 1250000030656887^4379*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500001311001108323 12500000000000000000 1250000030656887 1250000000000000 1024 4379 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250000030656887/1250000000000000 : ℝ)) (X := (12500001311001108323/12500000000000000000 : ℝ)) (by norm_num) 4379 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6270740368128933763/6250000000000000000 : ℝ) ≤ (312742192179019/312500000000000 : ℝ) ^ (4379/1024 : ℝ) := by
    have hpowers : (6270740368128933763/6250000000000000000 : ℝ)^1024 ≤ (312742192179019/312500000000000 : ℝ)^4379 := by
      have hnat : (6270740368128933763 : ℕ)^1024*312500000000000^4379 ≤ 312742192179019^4379*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6270740368128933763 6250000000000000000 312742192179019 312500000000000 1024 4379 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312742192179019/312500000000000 : ℝ)) (X := (6270740368128933763/6250000000000000000 : ℝ)) (by norm_num) 4379 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12582960161514626729/12500000000000000000 : ℝ) ≤ (250387501355053/250000000000000 : ℝ) ^ (4379/1024 : ℝ) := by
    have hpowers : (12582960161514626729/12500000000000000000 : ℝ)^1024 ≤ (250387501355053/250000000000000 : ℝ)^4379 := by
      have hnat : (12582960161514626729 : ℕ)^1024*250000000000000^4379 ≤ 250387501355053^4379*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12582960161514626729 12500000000000000000 250387501355053 250000000000000 1024 4379 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250387501355053/250000000000000 : ℝ)) (X := (12582960161514626729/12500000000000000000 : ℝ)) (by norm_num) 4379 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1311001108323/25000000000000000000 : ℝ) ≤ ((380201959918089251/380250000000000000 : ℝ)+2*(968738059189/304200000000000 : ℝ)*(62/3125 : ℝ))^(4379/1024 : ℝ) := by
    rw [show (380201959918089251/380250000000000000 : ℝ)+2*(968738059189/304200000000000 : ℝ)*(62/3125 : ℝ)=(1250000030656887/1250000000000000 : ℝ) by norm_num, show 1+2*(1311001108323/25000000000000000000 : ℝ)=(12500001311001108323/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(82960161514626729/25000000000000000000 : ℝ)+(1311001108323/25000000000000000000 : ℝ) ≤ ((380201959918089251/380250000000000000 : ℝ)+(968738059189/304200000000000 : ℝ)*((329/1250 : ℝ)+(62/3125 : ℝ)))^(4379/1024 : ℝ) := by
    rw [show (380201959918089251/380250000000000000 : ℝ)+(968738059189/304200000000000 : ℝ)*((329/1250 : ℝ)+(62/3125 : ℝ))=(312742192179019/312500000000000 : ℝ) by norm_num, show 1+(82960161514626729/25000000000000000000 : ℝ)+(1311001108323/25000000000000000000 : ℝ)=(6270740368128933763/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(82960161514626729/25000000000000000000 : ℝ) ≤ ((380201959918089251/380250000000000000 : ℝ)+2*(968738059189/304200000000000 : ℝ)*(329/1250 : ℝ))^(4379/1024 : ℝ) := by
    rw [show (380201959918089251/380250000000000000 : ℝ)+2*(968738059189/304200000000000 : ℝ)*(329/1250 : ℝ)=(250387501355053/250000000000000 : ℝ) by norm_num, show 1+2*(82960161514626729/25000000000000000000 : ℝ)=(12582960161514626729/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (380201959918089251/380250000000000000 : ℝ)*(X 1 0+X 2 0)+(968738059189/304200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4379/1024 : ℝ)) (lo := (62/3125 : ℝ)) (hi := (329/1250 : ℝ)) (c := (380201959918089251/380250000000000000 : ℝ)) (alpha := (968738059189/304200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (380201959918089251/380250000000000000 : ℝ)*(X 0 1+X 2 1)+(968738059189/304200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4379/1024 : ℝ)) (lo := (62/3125 : ℝ)) (hi := (329/1250 : ℝ)) (c := (380201959918089251/380250000000000000 : ℝ)) (alpha := (968738059189/304200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (380201959918089251/380250000000000000 : ℝ)*(X 0 2+X 1 2)+(968738059189/304200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4379/1024 : ℝ)) (lo := (62/3125 : ℝ)) (hi := (329/1250 : ℝ)) (c := (380201959918089251/380250000000000000 : ℝ)) (alpha := (968738059189/304200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-484389209/2500000000 : ℝ)*X 0 0+(350552729/625000000 : ℝ)*X 0 1+(5072935651/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5397713703/10000000000 : ℝ)*X 1 0+(-2221726329/10000000000 : ℝ)*X 1 1+(5072932883/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1079542401/2000000000 : ℝ)*X 2 0+(5072935383/10000000000 : ℝ)*X 2 1+(-2221725339/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4278276883/10000000000 : ℝ)*X 0 0+(3735465613/10000000000 : ℝ)*X 0 1+(2445500097/5000000000 : ℝ)*X 0 2+(4278276883/10000000000 : ℝ)*X 1 0+(3735465613/10000000000 : ℝ)*X 1 1+(2445500097/5000000000 : ℝ)*X 1 2+(4278276883/10000000000 : ℝ)*X 2 0+(3735465613/10000000000 : ℝ)*X 2 1+(2445500097/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1937966609/10000000000 : ℝ)*X 0 0+(1269815561/2500000000 : ℝ)*X 0 1+(2801204707/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1314447003/2500000000 : ℝ)*X 1 0+(-1692249621/10000000000 : ℝ)*X 1 1+(5602409423/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((328611749/625000000 : ℝ)*X 2 0+(1400602347/2500000000 : ℝ)*X 2 1+(-105765607/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4279159947/10000000000 : ℝ)*X 0 0+(1219339049/2500000000 : ℝ)*X 0 1+(3749344517/10000000000 : ℝ)*X 0 2+(4279159947/10000000000 : ℝ)*X 1 0+(1219339049/2500000000 : ℝ)*X 1 1+(3749344517/10000000000 : ℝ)*X 1 2+(4279159947/10000000000 : ℝ)*X 2 0+(1219339049/2500000000 : ℝ)*X 2 1+(3749344517/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10397209420775134219449/1625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (123759103/100000000000000 : ℝ)*(base1) + (1714710743/100000000000000 : ℝ)*(base19) + (1127711187/100000000000000 : ℝ)*(base23) + (35604389/25000000000000 : ℝ)*(upper3) + (456746523/100000000000000 : ℝ)*(upper5) + (3414251754303/250000000000 : ℝ)*(major0) + (3414251754303/250000000000 : ℝ)*(major1) + (3414251754303/250000000000 : ℝ)*(major2) + (1865991591766419/100000000000000 : ℝ)*(sp0) + (932996039526089/50000000000000 : ℝ)*(sp1) + (932996333025867/50000000000000 : ℝ)*(sp2) + (432702447364387/50000000000000 : ℝ)*(sp3) + (581438901/25000000000000 : ℝ)*(sp4) + (2377915507/100000000000000 : ℝ)*(sp7) + (108175924550423/12500000000000 : ℝ)*(f.failure) + (1865993793762921/100000000000000 : ℝ)*(f.sum) + (132963531469/39000000000000000000000000 : ℝ)*base66 + (591172916549/1218750000000000000000000000 : ℝ)*base68 + (5656017975973/2437500000000000000000000000 : ℝ)*base70 + (8624241776321/4875000000000000000000000000 : ℝ)*base72 + (378283873/152343750000000000000000 : ℝ)*base74 + (29478281528321/4875000000000000000000000000 : ℝ)*base76 + (9210565514321/4875000000000000000000000000 : ℝ)*base78 + (6964996562473/2437500000000000000000000000 : ℝ)*base80 + (101373804391/39000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (11643027/1250000000000000000000 : ℝ)*base89 + (11643027/1250000000000000000000 : ℝ)*base91 + (11643027/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (171208486283764491489991/66015625000000000000000000000 : ℝ) := by norm_num
    linear_combination (3116929/20000000000000 : ℝ)*(base1) + (586138149/100000000000000 : ℝ)*(base19) + (11405117/2000000000000 : ℝ)*(base23) + (67242033/100000000000000 : ℝ)*(upper3) + (26109801/50000000000000 : ℝ)*(upper5) + (349752942786553/25000000000000 : ℝ)*(major0) + (349752942786553/25000000000000 : ℝ)*(major1) + (349752942786553/25000000000000 : ℝ)*(major2) + (866453533/25000000000000 : ℝ)*(sp1) + (3251570923/100000000000000 : ℝ)*(sp2) + (29867308690273/1562500000000 : ℝ)*(sp4) + (1911503688640547/100000000000000 : ℝ)*(sp5) + (955751959383027/50000000000000 : ℝ)*(sp6) + (443257849833239/50000000000000 : ℝ)*(sp7) + (886515715251123/100000000000000 : ℝ)*(f.failure) + (477876935148207/25000000000000 : ℝ)*(f.sum) + (1073344986643/950625000000000000000000000 : ℝ)*base65 + (23992376258811947/9506250000000000000000000000000 : ℝ)*base68 + (17316685185299447/9506250000000000000000000000000 : ℝ)*base70 + (50738830156124447/9506250000000000000000000000000 : ℝ)*base72 + (40877518748369/7605000000000000000000000000 : ℝ)*base73 + (106428800557855697/9506250000000000000000000000000 : ℝ)*base76 + (13409235073068197/9506250000000000000000000000000 : ℝ)*base78 + (68034987394143197/9506250000000000000000000000000 : ℝ)*base80 + (2089941001529/7605000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (93047327/10000000000000000000000 : ℝ)*base89 + (93047327/10000000000000000000000 : ℝ)*base91 + (93047327/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1420_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157810149/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (329/1250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (62/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (7577/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9453/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1420_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1420_s2_0 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1971363799/10000000000 : ℝ)*x 0 + (2730102101/5000000000 : ℝ)*x 1 + (5199824897/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1971363799/10000000000 : ℝ)^1095 ≤ (12011088998313/100000000000000 : ℝ)^839 := by
    have hnat : (1971363799 : ℕ)^1095*100000000000000^839 ≤ 12011088998313^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1971363799 10000000000 12011088998313 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2730102101/5000000000 : ℝ)^1095 ≤ (9079348835811/20000000000000 : ℝ)^839 := by
    have hnat : (2730102101 : ℕ)^1095*20000000000000^839 ≤ 9079348835811^839*5000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2730102101 5000000000 9079348835811 20000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5199824897/10000000000 : ℝ)^1095 ≤ (8518433362399/20000000000000 : ℝ)^839 := by
    have hnat : (5199824897 : ℕ)^1095*20000000000000^839 ≤ 8518433362399^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5199824897 10000000000 8518433362399 20000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1971363799/10000000000 : ℝ), (2730102101/5000000000 : ℝ), (5199824897/10000000000 : ℝ)] ![(12011088998313/100000000000000 : ℝ), (9079348835811/20000000000000 : ℝ), (8518433362399/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1971363799/10000000000 : ℝ)|^1095 ≤ (12011088998313/100000000000000 : ℝ)^839
        have hw : |(-1971363799/10000000000 : ℝ)|=(1971363799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2730102101/5000000000 : ℝ)|^1095 ≤ (9079348835811/20000000000000 : ℝ)^839
        have hw : |(2730102101/5000000000 : ℝ)|=(2730102101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5199824897/10000000000 : ℝ)|^1095 ≤ (8518433362399/20000000000000 : ℝ)^839
        have hw : |(5199824897/10000000000 : ℝ)|=(5199824897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_s2_1 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1340178047/2500000000 : ℝ)*x 0 + (-16843051/80000000 : ℝ)*x 1 + (5199824829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1340178047/2500000000 : ℝ)^1095 ≤ (44320174654439/100000000000000 : ℝ)^839 := by
    have hnat : (1340178047 : ℕ)^1095*100000000000000^839 ≤ 44320174654439^839*2500000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1340178047 2500000000 44320174654439 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16843051/80000000 : ℝ)^1095 ≤ (3271914811823/25000000000000 : ℝ)^839 := by
    have hnat : (16843051 : ℕ)^1095*25000000000000^839 ≤ 3271914811823^839*80000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16843051 80000000 3271914811823 25000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5199824829/10000000000 : ℝ)^1095 ≤ (42592166085049/100000000000000 : ℝ)^839 := by
    have hnat : (5199824829 : ℕ)^1095*100000000000000^839 ≤ 42592166085049^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5199824829 10000000000 42592166085049 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1340178047/2500000000 : ℝ), (-16843051/80000000 : ℝ), (5199824829/10000000000 : ℝ)] ![(44320174654439/100000000000000 : ℝ), (3271914811823/25000000000000 : ℝ), (42592166085049/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1340178047/2500000000 : ℝ)|^1095 ≤ (44320174654439/100000000000000 : ℝ)^839
        have hw : |(1340178047/2500000000 : ℝ)|=(1340178047/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-16843051/80000000 : ℝ)|^1095 ≤ (3271914811823/25000000000000 : ℝ)^839
        have hw : |(-16843051/80000000 : ℝ)|=(16843051/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5199824829/10000000000 : ℝ)|^1095 ≤ (42592166085049/100000000000000 : ℝ)^839
        have hw : |(5199824829/10000000000 : ℝ)|=(5199824829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_s2_2 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5360711857/10000000000 : ℝ)*x 0 + (2599912601/5000000000 : ℝ)*x 1 + (-2105381323/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5360711857/10000000000 : ℝ)^1095 ≤ (44320171082869/100000000000000 : ℝ)^839 := by
    have hnat : (5360711857 : ℕ)^1095*100000000000000^839 ≤ 44320171082869^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5360711857 10000000000 44320171082869 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2599912601/5000000000 : ℝ)^1095 ≤ (42592170072561/100000000000000 : ℝ)^839 := by
    have hnat : (2599912601 : ℕ)^1095*100000000000000^839 ≤ 42592170072561^839*5000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2599912601 5000000000 42592170072561 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2105381323/10000000000 : ℝ)^1095 ≤ (2617531765083/20000000000000 : ℝ)^839 := by
    have hnat : (2105381323 : ℕ)^1095*20000000000000^839 ≤ 2617531765083^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2105381323 10000000000 2617531765083 20000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5360711857/10000000000 : ℝ), (2599912601/5000000000 : ℝ), (-2105381323/10000000000 : ℝ)] ![(44320171082869/100000000000000 : ℝ), (42592170072561/100000000000000 : ℝ), (2617531765083/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5360711857/10000000000 : ℝ)|^1095 ≤ (44320171082869/100000000000000 : ℝ)^839
        have hw : |(5360711857/10000000000 : ℝ)|=(5360711857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2599912601/5000000000 : ℝ)|^1095 ≤ (42592170072561/100000000000000 : ℝ)^839
        have hw : |(2599912601/5000000000 : ℝ)|=(2599912601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2105381323/10000000000 : ℝ)|^1095 ≤ (2617531765083/20000000000000 : ℝ)^839
        have hw : |(-2105381323/10000000000 : ℝ)|=(2105381323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_s2_3 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4302117369/10000000000 : ℝ)*x 0 + (402965509/1000000000 : ℝ)*x 1 + (7345737/16000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4302117369/10000000000 : ℝ)^1095 ≤ (16629511896893/50000000000000 : ℝ)^839 := by
    have hnat : (4302117369 : ℕ)^1095*50000000000000^839 ≤ 16629511896893^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4302117369 10000000000 16629511896893 50000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (402965509/1000000000 : ℝ)^1095 ≤ (3053691616589/10000000000000 : ℝ)^839 := by
    have hnat : (402965509 : ℕ)^1095*10000000000000^839 ≤ 3053691616589^839*1000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      402965509 1000000000 3053691616589 10000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7345737/16000000 : ℝ)^1095 ≤ (18102030015293/50000000000000 : ℝ)^839 := by
    have hnat : (7345737 : ℕ)^1095*50000000000000^839 ≤ 18102030015293^839*16000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7345737 16000000 18102030015293 50000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4302117369/10000000000 : ℝ), (402965509/1000000000 : ℝ), (7345737/16000000 : ℝ)] ![(16629511896893/50000000000000 : ℝ), (3053691616589/10000000000000 : ℝ), (18102030015293/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4302117369/10000000000 : ℝ)|^1095 ≤ (16629511896893/50000000000000 : ℝ)^839
        have hw : |(4302117369/10000000000 : ℝ)|=(4302117369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(402965509/1000000000 : ℝ)|^1095 ≤ (3053691616589/10000000000000 : ℝ)^839
        have hw : |(402965509/1000000000 : ℝ)|=(402965509/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7345737/16000000 : ℝ)|^1095 ≤ (18102030015293/50000000000000 : ℝ)^839
        have hw : |(7345737/16000000 : ℝ)|=(7345737/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_s2_4 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1971411139/10000000000 : ℝ)*x 0 + (5201327907/10000000000 : ℝ)*x 1 + (5458688613/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1971411139/10000000000 : ℝ)^1095 ≤ (12011465439913/100000000000000 : ℝ)^839 := by
    have hnat : (1971411139 : ℕ)^1095*100000000000000^839 ≤ 12011465439913^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1971411139 10000000000 12011465439913 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5201327907/10000000000 : ℝ)^1095 ≤ (42608235269699/100000000000000 : ℝ)^839 := by
    have hnat : (5201327907 : ℕ)^1095*100000000000000^839 ≤ 42608235269699^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5201327907 10000000000 42608235269699 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5458688613/10000000000 : ℝ)^1095 ≤ (5672537410851/12500000000000 : ℝ)^839 := by
    have hnat : (5458688613 : ℕ)^1095*12500000000000^839 ≤ 5672537410851^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5458688613 10000000000 5672537410851 12500000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1971411139/10000000000 : ℝ), (5201327907/10000000000 : ℝ), (5458688613/10000000000 : ℝ)] ![(12011465439913/100000000000000 : ℝ), (42608235269699/100000000000000 : ℝ), (5672537410851/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1971411139/10000000000 : ℝ)|^1095 ≤ (12011465439913/100000000000000 : ℝ)^839
        have hw : |(-1971411139/10000000000 : ℝ)|=(1971411139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5201327907/10000000000 : ℝ)|^1095 ≤ (42608235269699/100000000000000 : ℝ)^839
        have hw : |(5201327907/10000000000 : ℝ)|=(5201327907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5458688613/10000000000 : ℝ)|^1095 ≤ (5672537410851/12500000000000 : ℝ)^839
        have hw : |(5458688613/10000000000 : ℝ)|=(5458688613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_s2_5 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5293062773/10000000000 : ℝ)*x 0 + (-36930349/200000000 : ℝ)*x 1 + (5458688899/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293062773/10000000000 : ℝ)^1095 ≤ (43591630667663/100000000000000 : ℝ)^839 := by
    have hnat : (5293062773 : ℕ)^1095*100000000000000^839 ≤ 43591630667663^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293062773 10000000000 43591630667663 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (36930349/200000000 : ℝ)^1095 ≤ (5514033462393/50000000000000 : ℝ)^839 := by
    have hnat : (36930349 : ℕ)^1095*50000000000000^839 ≤ 5514033462393^839*200000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36930349 200000000 5514033462393 50000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5458688899/10000000000 : ℝ)^1095 ≤ (22690151194959/50000000000000 : ℝ)^839 := by
    have hnat : (5458688899 : ℕ)^1095*50000000000000^839 ≤ 22690151194959^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5458688899 10000000000 22690151194959 50000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293062773/10000000000 : ℝ), (-36930349/200000000 : ℝ), (5458688899/10000000000 : ℝ)] ![(43591630667663/100000000000000 : ℝ), (5514033462393/50000000000000 : ℝ), (22690151194959/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293062773/10000000000 : ℝ)|^1095 ≤ (43591630667663/100000000000000 : ℝ)^839
        have hw : |(5293062773/10000000000 : ℝ)|=(5293062773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-36930349/200000000 : ℝ)|^1095 ≤ (5514033462393/50000000000000 : ℝ)^839
        have hw : |(-36930349/200000000 : ℝ)|=(36930349/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5458688899/10000000000 : ℝ)|^1095 ≤ (22690151194959/50000000000000 : ℝ)^839
        have hw : |(5458688899/10000000000 : ℝ)|=(5458688899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_s2_6 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2646531367/5000000000 : ℝ)*x 0 + (1364672221/2500000000 : ℝ)*x 1 + (-923258763/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2646531367/5000000000 : ℝ)^1095 ≤ (43591630248471/100000000000000 : ℝ)^839 := by
    have hnat : (2646531367 : ℕ)^1095*100000000000000^839 ≤ 43591630248471^839*5000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646531367 5000000000 43591630248471 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1364672221/2500000000 : ℝ)^1095 ≤ (1418134444599/3125000000000 : ℝ)^839 := by
    have hnat : (1364672221 : ℕ)^1095*3125000000000^839 ≤ 1418134444599^839*2500000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1364672221 2500000000 1418134444599 3125000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (923258763/5000000000 : ℝ)^1095 ≤ (11028067517181/100000000000000 : ℝ)^839 := by
    have hnat : (923258763 : ℕ)^1095*100000000000000^839 ≤ 11028067517181^839*5000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      923258763 5000000000 11028067517181 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2646531367/5000000000 : ℝ), (1364672221/2500000000 : ℝ), (-923258763/5000000000 : ℝ)] ![(43591630248471/100000000000000 : ℝ), (1418134444599/3125000000000 : ℝ), (11028067517181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2646531367/5000000000 : ℝ)|^1095 ≤ (43591630248471/100000000000000 : ℝ)^839
        have hw : |(2646531367/5000000000 : ℝ)|=(2646531367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1364672221/2500000000 : ℝ)|^1095 ≤ (1418134444599/3125000000000 : ℝ)^839
        have hw : |(1364672221/2500000000 : ℝ)|=(1364672221/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-923258763/5000000000 : ℝ)|^1095 ≤ (11028067517181/100000000000000 : ℝ)^839
        have hw : |(-923258763/5000000000 : ℝ)|=(923258763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1420_s2_7 (p : ℝ) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4302219183/10000000000 : ℝ)*x 0 + (183513799/400000000 : ℝ)*x 1 + (2016461341/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4302219183/10000000000 : ℝ)^1095 ≤ (16630025536463/50000000000000 : ℝ)^839 := by
    have hnat : (4302219183 : ℕ)^1095*50000000000000^839 ≤ 16630025536463^839*10000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4302219183 10000000000 16630025536463 50000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (183513799/400000000 : ℝ)^1095 ≤ (1808535564673/5000000000000 : ℝ)^839 := by
    have hnat : (183513799 : ℕ)^1095*5000000000000^839 ≤ 1808535564673^839*400000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      183513799 400000000 1808535564673 5000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2016461341/5000000000 : ℝ)^1095 ≤ (30569237627933/100000000000000 : ℝ)^839 := by
    have hnat : (2016461341 : ℕ)^1095*100000000000000^839 ≤ 30569237627933^839*5000000000^1095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2016461341 5000000000 30569237627933 100000000000000 1095 839 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1095/256 : ℝ)) 1095 839 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4302219183/10000000000 : ℝ), (183513799/400000000 : ℝ), (2016461341/5000000000 : ℝ)] ![(16630025536463/50000000000000 : ℝ), (1808535564673/5000000000000 : ℝ), (30569237627933/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4302219183/10000000000 : ℝ)|^1095 ≤ (16630025536463/50000000000000 : ℝ)^839
        have hw : |(4302219183/10000000000 : ℝ)|=(4302219183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(183513799/400000000 : ℝ)|^1095 ≤ (1808535564673/5000000000000 : ℝ)^839
        have hw : |(183513799/400000000 : ℝ)|=(183513799/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2016461341/5000000000 : ℝ)|^1095 ≤ (30569237627933/100000000000000 : ℝ)^839
        have hw : |(2016461341/5000000000 : ℝ)|=(2016461341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1420_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157810149/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9453/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7577/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10319/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15827/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9453/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (7577/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9453/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (7577/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9453/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (7577/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9453/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (7577/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9453/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (7577/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9453/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (7577/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (7577/100000 : ℝ) ^ (4379/1024 : ℝ) ≤ (403886162734371/25000000000000000000 : ℝ) := by
    have hpowers : (7577/100000 : ℝ)^4379 ≤ (403886162734371/25000000000000000000 : ℝ)^1024 := by
      have hnat : (7577 : ℕ)^4379*25000000000000000000^1024 ≤ 403886162734371^1024*100000^4379 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7577 100000 403886162734371 25000000000000000000 4379 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7577/100000 : ℝ)) (X := (403886162734371/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4379 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (9453/50000 : ℝ) ^ (4379/1024 : ℝ) ≤ (16125177010811527/20000000000000000000 : ℝ) := by
    have hpowers : (9453/50000 : ℝ)^4379 ≤ (16125177010811527/20000000000000000000 : ℝ)^1024 := by
      have hnat : (9453 : ℕ)^4379*20000000000000000000^1024 ≤ 16125177010811527^1024*50000^4379 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9453 50000 16125177010811527 20000000000000000000 4379 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9453/50000 : ℝ)) (X := (16125177010811527/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4379 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500403886162734371/12500000000000000000 : ℝ) ≤ (2500018888984317/2500000000000000 : ℝ) ^ (4379/1024 : ℝ) := by
    have hpowers : (12500403886162734371/12500000000000000000 : ℝ)^1024 ≤ (2500018888984317/2500000000000000 : ℝ)^4379 := by
      have hnat : (12500403886162734371 : ℕ)^1024*2500000000000000^4379 ≤ 2500018888984317^4379*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500403886162734371 12500000000000000000 2500018888984317 2500000000000000 1024 4379 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500018888984317/2500000000000000 : ℝ)) (X := (12500403886162734371/12500000000000000000 : ℝ)) (by norm_num) 4379 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100082241429704995119/100000000000000000000 : ℝ) ≤ (2000384511098089/2000000000000000 : ℝ) ^ (4379/1024 : ℝ) := by
    have hpowers : (100082241429704995119/100000000000000000000 : ℝ)^1024 ≤ (2000384511098089/2000000000000000 : ℝ)^4379 := by
      have hnat : (100082241429704995119 : ℕ)^1024*2000000000000000^4379 ≤ 2000384511098089^4379*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100082241429704995119 100000000000000000000 2000384511098089 2000000000000000 1024 4379 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000384511098089/2000000000000000 : ℝ)) (X := (100082241429704995119/100000000000000000000 : ℝ)) (by norm_num) 4379 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10016125177010811527/10000000000000000000 : ℝ) ≤ (5001884777521811/5000000000000000 : ℝ) ^ (4379/1024 : ℝ) := by
    have hpowers : (10016125177010811527/10000000000000000000 : ℝ)^1024 ≤ (5001884777521811/5000000000000000 : ℝ)^4379 := by
      have hnat : (10016125177010811527 : ℕ)^1024*5000000000000000^4379 ≤ 5001884777521811^4379*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10016125177010811527 10000000000000000000 5001884777521811 5000000000000000 1024 4379 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001884777521811/5000000000000000 : ℝ)) (X := (10016125177010811527/10000000000000000000 : ℝ)) (by norm_num) 4379 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(403886162734371/25000000000000000000 : ℝ) ≤ ((56631433270992232457/56645000000000000000 : ℝ)+2*(1846999553177/1132900000000000 : ℝ)*(7577/100000 : ℝ))^(4379/1024 : ℝ) := by
    rw [show (56631433270992232457/56645000000000000000 : ℝ)+2*(1846999553177/1132900000000000 : ℝ)*(7577/100000 : ℝ)=(2500018888984317/2500000000000000 : ℝ) by norm_num, show 1+2*(403886162734371/25000000000000000000 : ℝ)=(12500403886162734371/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16125177010811527/20000000000000000000 : ℝ)+(403886162734371/25000000000000000000 : ℝ) ≤ ((56631433270992232457/56645000000000000000 : ℝ)+(1846999553177/1132900000000000 : ℝ)*((9453/50000 : ℝ)+(7577/100000 : ℝ)))^(4379/1024 : ℝ) := by
    rw [show (56631433270992232457/56645000000000000000 : ℝ)+(1846999553177/1132900000000000 : ℝ)*((9453/50000 : ℝ)+(7577/100000 : ℝ))=(2000384511098089/2000000000000000 : ℝ) by norm_num, show 1+(16125177010811527/20000000000000000000 : ℝ)+(403886162734371/25000000000000000000 : ℝ)=(100082241429704995119/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16125177010811527/20000000000000000000 : ℝ) ≤ ((56631433270992232457/56645000000000000000 : ℝ)+2*(1846999553177/1132900000000000 : ℝ)*(9453/50000 : ℝ))^(4379/1024 : ℝ) := by
    rw [show (56631433270992232457/56645000000000000000 : ℝ)+2*(1846999553177/1132900000000000 : ℝ)*(9453/50000 : ℝ)=(5001884777521811/5000000000000000 : ℝ) by norm_num, show 1+2*(16125177010811527/20000000000000000000 : ℝ)=(10016125177010811527/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (56631433270992232457/56645000000000000000 : ℝ)*(X 1 0+X 2 0)+(1846999553177/1132900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4379/1024 : ℝ)) (lo := (7577/100000 : ℝ)) (hi := (9453/50000 : ℝ)) (c := (56631433270992232457/56645000000000000000 : ℝ)) (alpha := (1846999553177/1132900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (56631433270992232457/56645000000000000000 : ℝ)*(X 0 1+X 2 1)+(1846999553177/1132900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4379/1024 : ℝ)) (lo := (7577/100000 : ℝ)) (hi := (9453/50000 : ℝ)) (c := (56631433270992232457/56645000000000000000 : ℝ)) (alpha := (1846999553177/1132900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (56631433270992232457/56645000000000000000 : ℝ)*(X 0 2+X 1 2)+(1846999553177/1132900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4379/1024 : ℝ)) (lo := (7577/100000 : ℝ)) (hi := (9453/50000 : ℝ)) (c := (56631433270992232457/56645000000000000000 : ℝ)) (alpha := (1846999553177/1132900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1971363799/10000000000 : ℝ)*X 0 0+(2730102101/5000000000 : ℝ)*X 0 1+(5199824897/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1340178047/2500000000 : ℝ)*X 1 0+(-16843051/80000000 : ℝ)*X 1 1+(5199824829/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5360711857/10000000000 : ℝ)*X 2 0+(2599912601/5000000000 : ℝ)*X 2 1+(-2105381323/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4302117369/10000000000 : ℝ)*X 0 0+(402965509/1000000000 : ℝ)*X 0 1+(7345737/16000000 : ℝ)*X 0 2+(4302117369/10000000000 : ℝ)*X 1 0+(402965509/1000000000 : ℝ)*X 1 1+(7345737/16000000 : ℝ)*X 1 2+(4302117369/10000000000 : ℝ)*X 2 0+(402965509/1000000000 : ℝ)*X 2 1+(7345737/16000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1971411139/10000000000 : ℝ)*X 0 0+(5201327907/10000000000 : ℝ)*X 0 1+(5458688613/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5293062773/10000000000 : ℝ)*X 1 0+(-36930349/200000000 : ℝ)*X 1 1+(5458688899/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2646531367/5000000000 : ℝ)*X 2 0+(1364672221/2500000000 : ℝ)*X 2 1+(-923258763/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4302219183/10000000000 : ℝ)*X 0 0+(183513799/400000000 : ℝ)*X 0 1+(2016461341/5000000000 : ℝ)*X 0 2+(4302219183/10000000000 : ℝ)*X 1 0+(183513799/400000000 : ℝ)*X 1 1+(2016461341/5000000000 : ℝ)*X 1 2+(4302219183/10000000000 : ℝ)*X 2 0+(183513799/400000000 : ℝ)*X 2 1+(2016461341/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1420_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5173123737436626344634098241/708062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (500850739/50000000000000 : ℝ)*(base19) + (547645881/100000000000000 : ℝ)*(base23) + (116283199/100000000000000 : ℝ)*(lower2) + (110855131/50000000000000 : ℝ)*(upper3) + (47202203/100000000000000 : ℝ)*(upper5) + (702718388393029/25000000000000 : ℝ)*(major0) + (702718388393029/25000000000000 : ℝ)*(major1) + (702718388393029/25000000000000 : ℝ)*(major2) + (1920281864604679/50000000000000 : ℝ)*(sp0) + (3840571728696007/100000000000000 : ℝ)*(sp1) + (960143045687901/25000000000000 : ℝ)*(sp2) + (1781168278998997/100000000000000 : ℝ)*(sp3) + (4500594063/50000000000000 : ℝ)*(sp4) + (585421351/10000000000000 : ℝ)*(sp7) + (1781174133212507/100000000000000 : ℝ)*(f.failure) + (768114546079497/20000000000000 : ℝ)*(f.sum) + (468469889099683/56645000000000000000000000000 : ℝ)*base66 + (1289936965292257747/1416125000000000000000000000000000 : ℝ)*base68 + (15642477447645367253/1416125000000000000000000000000000 : ℝ)*base69 + (11411071500938382747/1416125000000000000000000000000000 : ℝ)*base72 + (53772562811443/56645000000000000000000000000 : ℝ)*base74 + (20923260763716492253/1416125000000000000000000000000000 : ℝ)*base75 + (2216674205355617253/1416125000000000000000000000000000 : ℝ)*base77 + (2144209478971492253/1416125000000000000000000000000000 : ℝ)*base79 + (68910736039347/56645000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (21666457/10000000000000000000000 : ℝ)*base90 + (21666457/10000000000000000000000 : ℝ)*base92 + (21666457/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2586667888385527249741654173/708062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (140735629/100000000000000 : ℝ)*(base19) + (26507981/12500000000000 : ℝ)*(base23) + (3299711/3125000000000 : ℝ)*(upper3) + (9218563/20000000000000 : ℝ)*(lower4) + (12386687/25000000000000 : ℝ)*(upper5) + (710956166563863/25000000000000 : ℝ)*(major0) + (710956166563863/25000000000000 : ℝ)*(major1) + (710956166563863/25000000000000 : ℝ)*(major2) + (335357897/12500000000000 : ℝ)*(sp1) + (92258741/2500000000000 : ℝ)*(sp2) + (971398713369309/25000000000000 : ℝ)*(sp4) + (121424750933701/3125000000000 : ℝ)*(sp5) + (971397737765937/25000000000000 : ℝ)*(sp6) + (360410871452311/20000000000000 : ℝ)*(sp7) + (360410871452311/20000000000000 : ℝ)*(f.failure) + (971398713369309/25000000000000 : ℝ)*(f.sum) + (253561615399159/56645000000000000000000000000 : ℝ)*base65 + (1849464365890326391/1416125000000000000000000000000000 : ℝ)*base67 + (4662505728900798609/1416125000000000000000000000000000 : ℝ)*base70 + (4693681454821826391/1416125000000000000000000000000000 : ℝ)*base71 + (251240701853379/56645000000000000000000000000 : ℝ)*base73 + (14355328504365298609/1416125000000000000000000000000000 : ℝ)*base76 + (2905878994122173609/1416125000000000000000000000000000 : ℝ)*base78 + (9267937471902173609/1416125000000000000000000000000000 : ℝ)*base80 + (160513143646707/28322500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (5304339/2000000000000000000000 : ℝ)*base89 + (5304339/2000000000000000000000 : ℝ)*base91 + (5304339/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1420_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157810149/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9453/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7577/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10319/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15827/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1420_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1420_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157810149/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10319/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15827/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1420_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1420_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1420_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4379/1024 : ℝ) ≤ p) (hpb : p ≤ (1095/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157810149/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10319/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15827/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1420_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
