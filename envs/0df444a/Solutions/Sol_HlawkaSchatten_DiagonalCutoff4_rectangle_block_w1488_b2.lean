-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1488_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:14:58.49898+00:00
-- url     : https://prove2.me/submissions/68804b25-c781-49a4-9494-03de02b38911

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
theorem support_rectangle_w1488_s6_0 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-119003993/625000000 : ℝ)*x 0 + (135909373/250000000 : ℝ)*x 1 + (5216327781/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (119003993/625000000 : ℝ)^4473 ≤ (5818226909381/50000000000000 : ℝ)^3449 := by
    have hnat : (119003993 : ℕ)^4473*50000000000000^3449 ≤ 5818226909381^3449*625000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      119003993 625000000 5818226909381 50000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (135909373/250000000 : ℝ)^4473 ≤ (11341314439343/25000000000000 : ℝ)^3449 := by
    have hnat : (135909373 : ℕ)^4473*25000000000000^3449 ≤ 11341314439343^3449*250000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135909373 250000000 11341314439343 25000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5216327781/10000000000 : ℝ)^4473 ≤ (1719931535987/4000000000000 : ℝ)^3449 := by
    have hnat : (5216327781 : ℕ)^4473*4000000000000^3449 ≤ 1719931535987^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216327781 10000000000 1719931535987 4000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-119003993/625000000 : ℝ), (135909373/250000000 : ℝ), (5216327781/10000000000 : ℝ)] ![(5818226909381/50000000000000 : ℝ), (11341314439343/25000000000000 : ℝ), (1719931535987/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-119003993/625000000 : ℝ)|^4473 ≤ (5818226909381/50000000000000 : ℝ)^3449
        have hw : |(-119003993/625000000 : ℝ)|=(119003993/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(135909373/250000000 : ℝ)|^4473 ≤ (11341314439343/25000000000000 : ℝ)^3449
        have hw : |(135909373/250000000 : ℝ)|=(135909373/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5216327781/10000000000 : ℝ)|^4473 ≤ (1719931535987/4000000000000 : ℝ)^3449
        have hw : |(5216327781/10000000000 : ℝ)|=(5216327781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1488_s6_1 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338222781/2500000000 : ℝ)*x 0 + (-2016817887/10000000000 : ℝ)*x 1 + (521632787/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338222781/2500000000 : ℝ)^4473 ≤ (22231918964601/50000000000000 : ℝ)^3449 := by
    have hnat : (1338222781 : ℕ)^4473*50000000000000^3449 ≤ 22231918964601^3449*2500000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338222781 2500000000 22231918964601 50000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2016817887/10000000000 : ℝ)^4473 ≤ (12537872699281/100000000000000 : ℝ)^3449 := by
    have hnat : (2016817887 : ℕ)^4473*100000000000000^3449 ≤ 12537872699281^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2016817887 10000000000 12537872699281 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (521632787/1000000000 : ℝ)^4473 ≤ (10749572337779/25000000000000 : ℝ)^3449 := by
    have hnat : (521632787 : ℕ)^4473*25000000000000^3449 ≤ 10749572337779^3449*1000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521632787 1000000000 10749572337779 25000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338222781/2500000000 : ℝ), (-2016817887/10000000000 : ℝ), (521632787/1000000000 : ℝ)] ![(22231918964601/50000000000000 : ℝ), (12537872699281/100000000000000 : ℝ), (10749572337779/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338222781/2500000000 : ℝ)|^4473 ≤ (22231918964601/50000000000000 : ℝ)^3449
        have hw : |(1338222781/2500000000 : ℝ)|=(1338222781/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2016817887/10000000000 : ℝ)|^4473 ≤ (12537872699281/100000000000000 : ℝ)^3449
        have hw : |(-2016817887/10000000000 : ℝ)|=(2016817887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(521632787/1000000000 : ℝ)|^4473 ≤ (10749572337779/25000000000000 : ℝ)^3449
        have hw : |(521632787/1000000000 : ℝ)|=(521632787/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1488_s6_2 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676445633/5000000000 : ℝ)*x 0 + (5216327497/10000000000 : ℝ)*x 1 + (-2016818193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676445633/5000000000 : ℝ)^4473 ≤ (1778553578357/4000000000000 : ℝ)^3449 := by
    have hnat : (2676445633 : ℕ)^4473*4000000000000^3449 ≤ 1778553578357^3449*5000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676445633 5000000000 1778553578357 4000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216327497/10000000000 : ℝ)^4473 ≤ (8599657072723/20000000000000 : ℝ)^3449 := by
    have hnat : (5216327497 : ℕ)^4473*20000000000000^3449 ≤ 8599657072723^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216327497 10000000000 8599657072723 20000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2016818193/10000000000 : ℝ)^4473 ≤ (391808598949/3125000000000 : ℝ)^3449 := by
    have hnat : (2016818193 : ℕ)^4473*3125000000000^3449 ≤ 391808598949^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2016818193 10000000000 391808598949 3125000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676445633/5000000000 : ℝ), (5216327497/10000000000 : ℝ), (-2016818193/10000000000 : ℝ)] ![(1778553578357/4000000000000 : ℝ), (8599657072723/20000000000000 : ℝ), (391808598949/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676445633/5000000000 : ℝ)|^4473 ≤ (1778553578357/4000000000000 : ℝ)^3449
        have hw : |(2676445633/5000000000 : ℝ)|=(2676445633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216327497/10000000000 : ℝ)|^4473 ≤ (8599657072723/20000000000000 : ℝ)^3449
        have hw : |(5216327497/10000000000 : ℝ)|=(5216327497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2016818193/10000000000 : ℝ)|^4473 ≤ (391808598949/3125000000000 : ℝ)^3449
        have hw : |(-2016818193/10000000000 : ℝ)|=(2016818193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1488_s6_3 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2140540603/5000000000 : ℝ)*x 0 + (2020946037/5000000000 : ℝ)*x 1 + (453244289/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2140540603/5000000000 : ℝ)^4473 ≤ (4159801126381/12500000000000 : ℝ)^3449 := by
    have hnat : (2140540603 : ℕ)^4473*12500000000000^3449 ≤ 4159801126381^3449*5000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2140540603 5000000000 4159801126381 12500000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2020946037/5000000000 : ℝ)^4473 ≤ (6177469839697/20000000000000 : ℝ)^3449 := by
    have hnat : (2020946037 : ℕ)^4473*20000000000000^3449 ≤ 6177469839697^3449*5000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2020946037 5000000000 6177469839697 20000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (453244289/1000000000 : ℝ)^4473 ≤ (8958560444403/25000000000000 : ℝ)^3449 := by
    have hnat : (453244289 : ℕ)^4473*25000000000000^3449 ≤ 8958560444403^3449*1000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      453244289 1000000000 8958560444403 25000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2140540603/5000000000 : ℝ), (2020946037/5000000000 : ℝ), (453244289/1000000000 : ℝ)] ![(4159801126381/12500000000000 : ℝ), (6177469839697/20000000000000 : ℝ), (8958560444403/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2140540603/5000000000 : ℝ)|^4473 ≤ (4159801126381/12500000000000 : ℝ)^3449
        have hw : |(2140540603/5000000000 : ℝ)|=(2140540603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2020946037/5000000000 : ℝ)|^4473 ≤ (6177469839697/20000000000000 : ℝ)^3449
        have hw : |(2020946037/5000000000 : ℝ)|=(2020946037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(453244289/1000000000 : ℝ)|^4473 ≤ (8958560444403/25000000000000 : ℝ)^3449
        have hw : |(453244289/1000000000 : ℝ)|=(453244289/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1488_s6_4 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-476023589/2500000000 : ℝ)*x 0 + (104349097/200000000 : ℝ)*x 1 + (5435239209/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (476023589/2500000000 : ℝ)^4473 ≤ (11636695303571/100000000000000 : ℝ)^3449 := by
    have hnat : (476023589 : ℕ)^4473*100000000000000^3449 ≤ 11636695303571^3449*2500000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      476023589 2500000000 11636695303571 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (104349097/200000000 : ℝ)^4473 ≤ (43010337550263/100000000000000 : ℝ)^3449 := by
    have hnat : (104349097 : ℕ)^4473*100000000000000^3449 ≤ 43010337550263^3449*200000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104349097 200000000 43010337550263 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5435239209/10000000000 : ℝ)^4473 ≤ (22676483565039/50000000000000 : ℝ)^3449 := by
    have hnat : (5435239209 : ℕ)^4473*50000000000000^3449 ≤ 22676483565039^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435239209 10000000000 22676483565039 50000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-476023589/2500000000 : ℝ), (104349097/200000000 : ℝ), (5435239209/10000000000 : ℝ)] ![(11636695303571/100000000000000 : ℝ), (43010337550263/100000000000000 : ℝ), (22676483565039/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-476023589/2500000000 : ℝ)|^4473 ≤ (11636695303571/100000000000000 : ℝ)^3449
        have hw : |(-476023589/2500000000 : ℝ)|=(476023589/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(104349097/200000000 : ℝ)|^4473 ≤ (43010337550263/100000000000000 : ℝ)^3449
        have hw : |(104349097/200000000 : ℝ)|=(104349097/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5435239209/10000000000 : ℝ)|^4473 ≤ (22676483565039/50000000000000 : ℝ)^3449
        have hw : |(5435239209/10000000000 : ℝ)|=(5435239209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1488_s6_5 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295345387/10000000000 : ℝ)*x 0 + (-898953271/5000000000 : ℝ)*x 1 + (2717619609/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295345387/10000000000 : ℝ)^4473 ≤ (21922453630931/50000000000000 : ℝ)^3449 := by
    have hnat : (5295345387 : ℕ)^4473*50000000000000^3449 ≤ 21922453630931^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295345387 10000000000 21922453630931 50000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (898953271/5000000000 : ℝ)^4473 ≤ (2700531374813/25000000000000 : ℝ)^3449 := by
    have hnat : (898953271 : ℕ)^4473*25000000000000^3449 ≤ 2700531374813^3449*5000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898953271 5000000000 2700531374813 25000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2717619609/5000000000 : ℝ)^4473 ≤ (2834560451717/6250000000000 : ℝ)^3449 := by
    have hnat : (2717619609 : ℕ)^4473*6250000000000^3449 ≤ 2834560451717^3449*5000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717619609 5000000000 2834560451717 6250000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295345387/10000000000 : ℝ), (-898953271/5000000000 : ℝ), (2717619609/5000000000 : ℝ)] ![(21922453630931/50000000000000 : ℝ), (2700531374813/25000000000000 : ℝ), (2834560451717/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295345387/10000000000 : ℝ)|^4473 ≤ (21922453630931/50000000000000 : ℝ)^3449
        have hw : |(5295345387/10000000000 : ℝ)|=(5295345387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-898953271/5000000000 : ℝ)|^4473 ≤ (2700531374813/25000000000000 : ℝ)^3449
        have hw : |(-898953271/5000000000 : ℝ)|=(898953271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2717619609/5000000000 : ℝ)|^4473 ≤ (2834560451717/6250000000000 : ℝ)^3449
        have hw : |(2717619609/5000000000 : ℝ)|=(2717619609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1488_s6_6 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (661918177/1250000000 : ℝ)*x 0 + (5435239201/10000000000 : ℝ)*x 1 + (-449476631/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661918177/1250000000 : ℝ)^4473 ≤ (43844907573269/100000000000000 : ℝ)^3449 := by
    have hnat : (661918177 : ℕ)^4473*100000000000000^3449 ≤ 43844907573269^3449*1250000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661918177 1250000000 43844907573269 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5435239201/10000000000 : ℝ)^4473 ≤ (2834560440219/6250000000000 : ℝ)^3449 := by
    have hnat : (5435239201 : ℕ)^4473*6250000000000^3449 ≤ 2834560440219^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435239201 10000000000 2834560440219 6250000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (449476631/2500000000 : ℝ)^4473 ≤ (10802125358997/100000000000000 : ℝ)^3449 := by
    have hnat : (449476631 : ℕ)^4473*100000000000000^3449 ≤ 10802125358997^3449*2500000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449476631 2500000000 10802125358997 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661918177/1250000000 : ℝ), (5435239201/10000000000 : ℝ), (-449476631/2500000000 : ℝ)] ![(43844907573269/100000000000000 : ℝ), (2834560440219/6250000000000 : ℝ), (10802125358997/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661918177/1250000000 : ℝ)|^4473 ≤ (43844907573269/100000000000000 : ℝ)^3449
        have hw : |(661918177/1250000000 : ℝ)|=(661918177/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5435239201/10000000000 : ℝ)|^4473 ≤ (2834560440219/6250000000000 : ℝ)^3449
        have hw : |(5435239201/10000000000 : ℝ)|=(5435239201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-449476631/2500000000 : ℝ)|^4473 ≤ (10802125358997/100000000000000 : ℝ)^3449
        have hw : |(-449476631/2500000000 : ℝ)|=(449476631/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1488_s6_7 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2140574001/5000000000 : ℝ)*x 0 + (452992901/1000000000 : ℝ)*x 1 + (4044424523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2140574001/5000000000 : ℝ)^4473 ≤ (1039971325013/3125000000000 : ℝ)^3449 := by
    have hnat : (2140574001 : ℕ)^4473*3125000000000^3449 ≤ 1039971325013^3449*5000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2140574001 5000000000 1039971325013 3125000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (452992901/1000000000 : ℝ)^4473 ≤ (35808467864417/100000000000000 : ℝ)^3449 := by
    have hnat : (452992901 : ℕ)^4473*100000000000000^3449 ≤ 35808467864417^3449*1000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      452992901 1000000000 35808467864417 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4044424523/10000000000 : ℝ)^4473 ≤ (15456224859373/50000000000000 : ℝ)^3449 := by
    have hnat : (4044424523 : ℕ)^4473*50000000000000^3449 ≤ 15456224859373^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4044424523 10000000000 15456224859373 50000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2140574001/5000000000 : ℝ), (452992901/1000000000 : ℝ), (4044424523/10000000000 : ℝ)] ![(1039971325013/3125000000000 : ℝ), (35808467864417/100000000000000 : ℝ), (15456224859373/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2140574001/5000000000 : ℝ)|^4473 ≤ (1039971325013/3125000000000 : ℝ)^3449
        have hw : |(2140574001/5000000000 : ℝ)|=(2140574001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(452992901/1000000000 : ℝ)|^4473 ≤ (35808467864417/100000000000000 : ℝ)^3449
        have hw : |(452992901/1000000000 : ℝ)|=(452992901/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4044424523/10000000000 : ℝ)|^4473 ≤ (15456224859373/50000000000000 : ℝ)^3449
        have hw : |(4044424523/10000000000 : ℝ)|=(4044424523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1488_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80732249/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15479/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5409/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (541/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15477/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15479/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5409/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15479/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5409/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15479/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5409/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15479/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5409/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15479/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5409/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15479/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5409/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5409/50000 : ℝ) ^ (4471/1024 : ℝ) ≤ (6065714531631713/100000000000000000000 : ℝ) := by
    have hpowers : (5409/50000 : ℝ)^4471 ≤ (6065714531631713/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5409 : ℕ)^4471*100000000000000000000^1024 ≤ 6065714531631713^1024*50000^4471 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5409 50000 6065714531631713 100000000000000000000 4471 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5409/50000 : ℝ)) (X := (6065714531631713/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4471 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15479/100000 : ℝ) ^ (4471/1024 : ℝ) ≤ (28989891427683657/100000000000000000000 : ℝ) := by
    have hpowers : (15479/100000 : ℝ)^4471 ≤ (28989891427683657/100000000000000000000 : ℝ)^1024 := by
      have hnat : (15479 : ℕ)^4471*100000000000000000000^1024 ≤ 28989891427683657^1024*100000^4471 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15479 100000 28989891427683657 100000000000000000000 4471 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15479/100000 : ℝ)) (X := (28989891427683657/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4471 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006065714531631713/50000000000000000000 : ℝ) ≤ (5000138917495677/5000000000000000 : ℝ) ^ (4471/1024 : ℝ) := by
    have hpowers : (50006065714531631713/50000000000000000000 : ℝ)^1024 ≤ (5000138917495677/5000000000000000 : ℝ)^4471 := by
      have hnat : (50006065714531631713 : ℕ)^1024*5000000000000000^4471 ≤ 5000138917495677^4471*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006065714531631713 50000000000000000000 5000138917495677 5000000000000000 1024 4471 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000138917495677/5000000000000000 : ℝ)) (X := (50006065714531631713/50000000000000000000 : ℝ)) (by norm_num) 4471 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10003505560595931537/10000000000000000000 : ℝ) ≤ (5000401387727743/5000000000000000 : ℝ) ^ (4471/1024 : ℝ) := by
    have hpowers : (10003505560595931537/10000000000000000000 : ℝ)^1024 ≤ (5000401387727743/5000000000000000 : ℝ)^4471 := by
      have hnat : (10003505560595931537 : ℕ)^1024*5000000000000000^4471 ≤ 5000401387727743^4471*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10003505560595931537 10000000000000000000 5000401387727743 5000000000000000 1024 4471 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000401387727743/5000000000000000 : ℝ)) (X := (10003505560595931537/10000000000000000000 : ℝ)) (by norm_num) 4471 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50028989891427683657/50000000000000000000 : ℝ) ≤ (5000663857959809/5000000000000000 : ℝ) ^ (4471/1024 : ℝ) := by
    have hpowers : (50028989891427683657/50000000000000000000 : ℝ)^1024 ≤ (5000663857959809/5000000000000000 : ℝ)^4471 := by
      have hnat : (50028989891427683657 : ℕ)^1024*5000000000000000^4471 ≤ 5000663857959809^4471*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50028989891427683657 50000000000000000000 5000663857959809 5000000000000000 1024 4471 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000663857959809/5000000000000000 : ℝ)) (X := (50028989891427683657/50000000000000000000 : ℝ)) (by norm_num) 4471 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6065714531631713/100000000000000000000 : ℝ) ≤ ((23299968688506370521/23305000000000000000 : ℝ)+2*(131235116033/116525000000000 : ℝ)*(5409/50000 : ℝ))^(4471/1024 : ℝ) := by
    rw [show (23299968688506370521/23305000000000000000 : ℝ)+2*(131235116033/116525000000000 : ℝ)*(5409/50000 : ℝ)=(5000138917495677/5000000000000000 : ℝ) by norm_num, show 1+2*(6065714531631713/100000000000000000000 : ℝ)=(50006065714531631713/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(28989891427683657/100000000000000000000 : ℝ)+(6065714531631713/100000000000000000000 : ℝ) ≤ ((23299968688506370521/23305000000000000000 : ℝ)+(131235116033/116525000000000 : ℝ)*((15479/100000 : ℝ)+(5409/50000 : ℝ)))^(4471/1024 : ℝ) := by
    rw [show (23299968688506370521/23305000000000000000 : ℝ)+(131235116033/116525000000000 : ℝ)*((15479/100000 : ℝ)+(5409/50000 : ℝ))=(5000401387727743/5000000000000000 : ℝ) by norm_num, show 1+(28989891427683657/100000000000000000000 : ℝ)+(6065714531631713/100000000000000000000 : ℝ)=(10003505560595931537/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(28989891427683657/100000000000000000000 : ℝ) ≤ ((23299968688506370521/23305000000000000000 : ℝ)+2*(131235116033/116525000000000 : ℝ)*(15479/100000 : ℝ))^(4471/1024 : ℝ) := by
    rw [show (23299968688506370521/23305000000000000000 : ℝ)+2*(131235116033/116525000000000 : ℝ)*(15479/100000 : ℝ)=(5000663857959809/5000000000000000 : ℝ) by norm_num, show 1+2*(28989891427683657/100000000000000000000 : ℝ)=(50028989891427683657/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (23299968688506370521/23305000000000000000 : ℝ)*(X 1 0+X 2 0)+(131235116033/116525000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4471/1024 : ℝ)) (lo := (5409/50000 : ℝ)) (hi := (15479/100000 : ℝ)) (c := (23299968688506370521/23305000000000000000 : ℝ)) (alpha := (131235116033/116525000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (23299968688506370521/23305000000000000000 : ℝ)*(X 0 1+X 2 1)+(131235116033/116525000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4471/1024 : ℝ)) (lo := (5409/50000 : ℝ)) (hi := (15479/100000 : ℝ)) (c := (23299968688506370521/23305000000000000000 : ℝ)) (alpha := (131235116033/116525000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (23299968688506370521/23305000000000000000 : ℝ)*(X 0 2+X 1 2)+(131235116033/116525000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4471/1024 : ℝ)) (lo := (5409/50000 : ℝ)) (hi := (15479/100000 : ℝ)) (c := (23299968688506370521/23305000000000000000 : ℝ)) (alpha := (131235116033/116525000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-119003993/625000000 : ℝ)*X 0 0+(135909373/250000000 : ℝ)*X 0 1+(5216327781/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338222781/2500000000 : ℝ)*X 1 0+(-2016817887/10000000000 : ℝ)*X 1 1+(521632787/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676445633/5000000000 : ℝ)*X 2 0+(5216327497/10000000000 : ℝ)*X 2 1+(-2016818193/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2140540603/5000000000 : ℝ)*X 0 0+(2020946037/5000000000 : ℝ)*X 0 1+(453244289/1000000000 : ℝ)*X 0 2+(2140540603/5000000000 : ℝ)*X 1 0+(2020946037/5000000000 : ℝ)*X 1 1+(453244289/1000000000 : ℝ)*X 1 2+(2140540603/5000000000 : ℝ)*X 2 0+(2020946037/5000000000 : ℝ)*X 2 1+(453244289/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-476023589/2500000000 : ℝ)*X 0 0+(104349097/200000000 : ℝ)*X 0 1+(5435239209/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5295345387/10000000000 : ℝ)*X 1 0+(-898953271/5000000000 : ℝ)*X 1 1+(2717619609/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((661918177/1250000000 : ℝ)*X 2 0+(5435239201/10000000000 : ℝ)*X 2 1+(-449476631/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2140574001/5000000000 : ℝ)*X 0 0+(452992901/1000000000 : ℝ)*X 0 1+(4044424523/10000000000 : ℝ)*X 0 2+(2140574001/5000000000 : ℝ)*X 1 0+(452992901/1000000000 : ℝ)*X 1 1+(4044424523/10000000000 : ℝ)*X 1 2+(2140574001/5000000000 : ℝ)*X 2 0+(452992901/1000000000 : ℝ)*X 2 1+(4044424523/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1248197984236678736708176497/291312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4728723/6250000000000 : ℝ)*(base19) + (266144269/50000000000000 : ℝ)*(base23) + (8013463/20000000000000 : ℝ)*(lower2) + (54991017/25000000000000 : ℝ)*(lower4) + (9812547/50000000000000 : ℝ)*(lower5) + (1645757116123881/50000000000000 : ℝ)*(major0) + (1645757116123881/50000000000000 : ℝ)*(major1) + (1645757116123881/50000000000000 : ℝ)*(major2) + (1136121847014551/25000000000000 : ℝ)*(sp0) + (568061351664177/12500000000000 : ℝ)*(sp1) + (2272245178342223/50000000000000 : ℝ)*(sp2) + (2038531359649739/100000000000000 : ℝ)*(sp3) + (175045739/5000000000000 : ℝ)*(sp4) + (6073048167/100000000000000 : ℝ)*(sp7) + (1019268716348953/50000000000000 : ℝ)*(f.failure) + (568061361121623/12500000000000 : ℝ)*(f.sum) + (2534699033737/2913125000000000000000000000 : ℝ)*base66 + (7583826994988112001/1165250000000000000000000000000000 : ℝ)*base67 + (8865765876913362001/1165250000000000000000000000000000 : ℝ)*base69 + (14141134900569112001/1165250000000000000000000000000000 : ℝ)*base71 + (9211993653859/5826250000000000000000000000 : ℝ)*base74 + (6381534938479362001/1165250000000000000000000000000000 : ℝ)*base75 + (13937298822726112001/1165250000000000000000000000000000 : ℝ)*base77 + (978995130287387999/1165250000000000000000000000000000 : ℝ)*base80 + (22118226693181/23305000000000000000000000000 : ℝ)*base82 + (5514703/2500000000000000000000 : ℝ)*base90 + (5514703/2500000000000000000000 : ℝ)*base92 + (5514703/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1438543688693540211440819829/582625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (94368927/25000000000000 : ℝ)*(base19) + (449448413/100000000000000 : ℝ)*(base23) + (31358687/25000000000000 : ℝ)*(lower1) + (6375801/12500000000000 : ℝ)*(upper3) + (9485603/50000000000000 : ℝ)*(lower4) + (50868267/100000000000000 : ℝ)*(upper5) + (1662850689067217/50000000000000 : ℝ)*(major0) + (1662850689067217/50000000000000 : ℝ)*(major1) + (1662850689067217/50000000000000 : ℝ)*(major2) + (506111139/50000000000000 : ℝ)*(sp2) + (573961509432249/12500000000000 : ℝ)*(sp4) + (1147922924495571/25000000000000 : ℝ)*(sp5) + (4591690613787301/100000000000000 : ℝ)*(sp6) + (2059710598508431/100000000000000 : ℝ)*(sp7) + (2059710598508431/100000000000000 : ℝ)*(f.failure) + (573961509432249/12500000000000 : ℝ)*(f.sum) + (64478469640131/11652500000000000000000000000 : ℝ)*base66 + (11774110840568989943/1165250000000000000000000000000000 : ℝ)*base68 + (1316287581008260057/1165250000000000000000000000000000 : ℝ)*base69 + (19959274599533989943/1165250000000000000000000000000000 : ℝ)*base72 + (18961940506889/11652500000000000000000000000 : ℝ)*base73 + (28448894274252260057/1165250000000000000000000000000000 : ℝ)*base75 + (6702738106662010057/1165250000000000000000000000000000 : ℝ)*base77 + (5766509894509260057/1165250000000000000000000000000000 : ℝ)*base79 + (181127193584387/23305000000000000000000000000 : ℝ)*base82 + (19908681/5000000000000000000000 : ℝ)*base90 + (19908681/5000000000000000000000 : ℝ)*base92 + (19908681/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1488_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80732249/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15479/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5409/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (541/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15477/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1488_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1488_box_0 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-105377941/625000000 : ℝ)*x 0 + (5405431157/10000000000 : ℝ)*x 1 + (1351357649/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105377941/625000000 : ℝ)^4473 ≤ (4969344697943/50000000000000 : ℝ)^3449 := by
    have hnat : (105377941 : ℕ)^4473*50000000000000^3449 ≤ 4969344697943^3449*625000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105377941 625000000 4969344697943 50000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5405431157/10000000000 : ℝ)^4473 ≤ (45030658324059/100000000000000 : ℝ)^3449 := by
    have hnat : (5405431157 : ℕ)^4473*100000000000000^3449 ≤ 45030658324059^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405431157 10000000000 45030658324059 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1351357649/2500000000 : ℝ)^4473 ≤ (11257663065757/25000000000000 : ℝ)^3449 := by
    have hnat : (1351357649 : ℕ)^4473*25000000000000^3449 ≤ 11257663065757^3449*2500000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351357649 2500000000 11257663065757 25000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-105377941/625000000 : ℝ), (5405431157/10000000000 : ℝ), (1351357649/2500000000 : ℝ)] ![(4969344697943/50000000000000 : ℝ), (45030658324059/100000000000000 : ℝ), (11257663065757/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-105377941/625000000 : ℝ)|^4473 ≤ (4969344697943/50000000000000 : ℝ)^3449
        have hw : |(-105377941/625000000 : ℝ)|=(105377941/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5405431157/10000000000 : ℝ)|^4473 ≤ (45030658324059/100000000000000 : ℝ)^3449
        have hw : |(5405431157/10000000000 : ℝ)|=(5405431157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1351357649/2500000000 : ℝ)|^4473 ≤ (11257663065757/25000000000000 : ℝ)^3449
        have hw : |(1351357649/2500000000 : ℝ)|=(1351357649/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1488_box_1 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2635197507/5000000000 : ℝ)*x 0 + (-37463367/200000000 : ℝ)*x 1 + (1351357679/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2635197507/5000000000 : ℝ)^4473 ≤ (21788586670469/50000000000000 : ℝ)^3449 := by
    have hnat : (2635197507 : ℕ)^4473*50000000000000^3449 ≤ 21788586670469^3449*5000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2635197507 5000000000 21788586670469 50000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (37463367/200000000 : ℝ)^4473 ≤ (11392173084211/100000000000000 : ℝ)^3449 := by
    have hnat : (37463367 : ℕ)^4473*100000000000000^3449 ≤ 11392173084211^3449*200000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37463367 200000000 11392173084211 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1351357679/2500000000 : ℝ)^4473 ≤ (9006130711901/20000000000000 : ℝ)^3449 := by
    have hnat : (1351357679 : ℕ)^4473*20000000000000^3449 ≤ 9006130711901^3449*2500000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351357679 2500000000 9006130711901 20000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2635197507/5000000000 : ℝ), (-37463367/200000000 : ℝ), (1351357679/2500000000 : ℝ)] ![(21788586670469/50000000000000 : ℝ), (11392173084211/100000000000000 : ℝ), (9006130711901/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2635197507/5000000000 : ℝ)|^4473 ≤ (21788586670469/50000000000000 : ℝ)^3449
        have hw : |(2635197507/5000000000 : ℝ)|=(2635197507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-37463367/200000000 : ℝ)|^4473 ≤ (11392173084211/100000000000000 : ℝ)^3449
        have hw : |(-37463367/200000000 : ℝ)|=(37463367/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1351357679/2500000000 : ℝ)|^4473 ≤ (9006130711901/20000000000000 : ℝ)^3449
        have hw : |(1351357679/2500000000 : ℝ)|=(1351357679/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1488_box_2 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5270394877/10000000000 : ℝ)*x 0 + (1081086211/2000000000 : ℝ)*x 1 + (-1873168071/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5270394877/10000000000 : ℝ)^4473 ≤ (43577171871869/100000000000000 : ℝ)^3449 := by
    have hnat : (5270394877 : ℕ)^4473*100000000000000^3449 ≤ 43577171871869^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5270394877 10000000000 43577171871869 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081086211/2000000000 : ℝ)^4473 ≤ (45030657222053/100000000000000 : ℝ)^3449 := by
    have hnat : (1081086211 : ℕ)^4473*100000000000000^3449 ≤ 45030657222053^3449*2000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081086211 2000000000 45030657222053 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1873168071/10000000000 : ℝ)^4473 ≤ (5696085441809/50000000000000 : ℝ)^3449 := by
    have hnat : (1873168071 : ℕ)^4473*50000000000000^3449 ≤ 5696085441809^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1873168071 10000000000 5696085441809 50000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5270394877/10000000000 : ℝ), (1081086211/2000000000 : ℝ), (-1873168071/10000000000 : ℝ)] ![(43577171871869/100000000000000 : ℝ), (45030657222053/100000000000000 : ℝ), (5696085441809/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5270394877/10000000000 : ℝ)|^4473 ≤ (43577171871869/100000000000000 : ℝ)^3449
        have hw : |(5270394877/10000000000 : ℝ)|=(5270394877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1081086211/2000000000 : ℝ)|^4473 ≤ (45030657222053/100000000000000 : ℝ)^3449
        have hw : |(1081086211/2000000000 : ℝ)|=(1081086211/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1873168071/10000000000 : ℝ)|^4473 ≤ (5696085441809/50000000000000 : ℝ)^3449
        have hw : |(-1873168071/10000000000 : ℝ)|=(1873168071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1488_box_3 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (897055881/2000000000 : ℝ)*x 0 + (4186125077/10000000000 : ℝ)*x 1 + (4186124999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (897055881/2000000000 : ℝ)^4473 ≤ (35351400442119/100000000000000 : ℝ)^3449 := by
    have hnat : (897055881 : ℕ)^4473*100000000000000^3449 ≤ 35351400442119^3449*2000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      897055881 2000000000 35351400442119 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4186125077/10000000000 : ℝ)^4473 ≤ (6464860032373/20000000000000 : ℝ)^3449 := by
    have hnat : (4186125077 : ℕ)^4473*20000000000000^3449 ≤ 6464860032373^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4186125077 10000000000 6464860032373 20000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4186124999/10000000000 : ℝ)^4473 ≤ (16162149690373/50000000000000 : ℝ)^3449 := by
    have hnat : (4186124999 : ℕ)^4473*50000000000000^3449 ≤ 16162149690373^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4186124999 10000000000 16162149690373 50000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(897055881/2000000000 : ℝ), (4186125077/10000000000 : ℝ), (4186124999/10000000000 : ℝ)] ![(35351400442119/100000000000000 : ℝ), (6464860032373/20000000000000 : ℝ), (16162149690373/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(897055881/2000000000 : ℝ)|^4473 ≤ (35351400442119/100000000000000 : ℝ)^3449
        have hw : |(897055881/2000000000 : ℝ)|=(897055881/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4186125077/10000000000 : ℝ)|^4473 ≤ (6464860032373/20000000000000 : ℝ)^3449
        have hw : |(4186125077/10000000000 : ℝ)|=(4186125077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4186124999/10000000000 : ℝ)|^4473 ≤ (16162149690373/50000000000000 : ℝ)^3449
        have hw : |(4186124999/10000000000 : ℝ)|=(4186124999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1488_box_4 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2127542381/10000000000 : ℝ)*x 0 + (5242764729/10000000000 : ℝ)*x 1 + (2621382321/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2127542381/10000000000 : ℝ)^4473 ≤ (6718879409151/50000000000000 : ℝ)^3449 := by
    have hnat : (2127542381 : ℕ)^4473*50000000000000^3449 ≤ 6718879409151^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2127542381 10000000000 6718879409151 50000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242764729/10000000000 : ℝ)^4473 ≤ (67626751647/156250000000 : ℝ)^3449 := by
    have hnat : (5242764729 : ℕ)^4473*156250000000^3449 ≤ 67626751647^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242764729 10000000000 67626751647 156250000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621382321/5000000000 : ℝ)^4473 ≤ (43281120122623/100000000000000 : ℝ)^3449 := by
    have hnat : (2621382321 : ℕ)^4473*100000000000000^3449 ≤ 43281120122623^3449*5000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621382321 5000000000 43281120122623 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2127542381/10000000000 : ℝ), (5242764729/10000000000 : ℝ), (2621382321/5000000000 : ℝ)] ![(6718879409151/50000000000000 : ℝ), (67626751647/156250000000 : ℝ), (43281120122623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2127542381/10000000000 : ℝ)|^4473 ≤ (6718879409151/50000000000000 : ℝ)^3449
        have hw : |(-2127542381/10000000000 : ℝ)|=(2127542381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242764729/10000000000 : ℝ)|^4473 ≤ (67626751647/156250000000 : ℝ)^3449
        have hw : |(5242764729/10000000000 : ℝ)|=(5242764729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621382321/5000000000 : ℝ)|^4473 ≤ (43281120122623/100000000000000 : ℝ)^3449
        have hw : |(2621382321/5000000000 : ℝ)|=(2621382321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1488_box_5 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5383858839/10000000000 : ℝ)*x 0 + (-969942133/5000000000 : ℝ)*x 1 + (163836397/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5383858839/10000000000 : ℝ)^4473 ≤ (44797729699161/100000000000000 : ℝ)^3449 := by
    have hnat : (5383858839 : ℕ)^4473*100000000000000^3449 ≤ 44797729699161^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5383858839 10000000000 44797729699161 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (969942133/5000000000 : ℝ)^4473 ≤ (2980287374941/25000000000000 : ℝ)^3449 := by
    have hnat : (969942133 : ℕ)^4473*25000000000000^3449 ≤ 2980287374941^3449*5000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      969942133 5000000000 2980287374941 25000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (163836397/312500000 : ℝ)^4473 ≤ (2164056039321/5000000000000 : ℝ)^3449 := by
    have hnat : (163836397 : ℕ)^4473*5000000000000^3449 ≤ 2164056039321^3449*312500000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163836397 312500000 2164056039321 5000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5383858839/10000000000 : ℝ), (-969942133/5000000000 : ℝ), (163836397/312500000 : ℝ)] ![(44797729699161/100000000000000 : ℝ), (2980287374941/25000000000000 : ℝ), (2164056039321/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5383858839/10000000000 : ℝ)|^4473 ≤ (44797729699161/100000000000000 : ℝ)^3449
        have hw : |(5383858839/10000000000 : ℝ)|=(5383858839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-969942133/5000000000 : ℝ)|^4473 ≤ (2980287374941/25000000000000 : ℝ)^3449
        have hw : |(-969942133/5000000000 : ℝ)|=(969942133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(163836397/312500000 : ℝ)|^4473 ≤ (2164056039321/5000000000000 : ℝ)^3449
        have hw : |(163836397/312500000 : ℝ)|=(163836397/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1488_box_6 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (672982363/1250000000 : ℝ)*x 0 + (2621382341/5000000000 : ℝ)*x 1 + (-1939884207/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (672982363/1250000000 : ℝ)^4473 ≤ (22398865200293/50000000000000 : ℝ)^3449 := by
    have hnat : (672982363 : ℕ)^4473*50000000000000^3449 ≤ 22398865200293^3449*1250000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672982363 1250000000 22398865200293 50000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621382341/5000000000 : ℝ)^4473 ≤ (43281120550879/100000000000000 : ℝ)^3449 := by
    have hnat : (2621382341 : ℕ)^4473*100000000000000^3449 ≤ 43281120550879^3449*5000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621382341 5000000000 43281120550879 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1939884207/10000000000 : ℝ)^4473 ≤ (2384229805909/20000000000000 : ℝ)^3449 := by
    have hnat : (1939884207 : ℕ)^4473*20000000000000^3449 ≤ 2384229805909^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1939884207 10000000000 2384229805909 20000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(672982363/1250000000 : ℝ), (2621382341/5000000000 : ℝ), (-1939884207/10000000000 : ℝ)] ![(22398865200293/50000000000000 : ℝ), (43281120550879/100000000000000 : ℝ), (2384229805909/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(672982363/1250000000 : ℝ)|^4473 ≤ (22398865200293/50000000000000 : ℝ)^3449
        have hw : |(672982363/1250000000 : ℝ)|=(672982363/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621382341/5000000000 : ℝ)|^4473 ≤ (43281120550879/100000000000000 : ℝ)^3449
        have hw : |(2621382341/5000000000 : ℝ)|=(2621382341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1939884207/10000000000 : ℝ)|^4473 ≤ (2384229805909/20000000000000 : ℝ)^3449
        have hw : |(-1939884207/10000000000 : ℝ)|=(1939884207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1488_box_7 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (127330749/312500000 : ℝ)*x 0 + (2195667593/5000000000 : ℝ)*x 1 + (2195667639/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (127330749/312500000 : ℝ)^4473 ≤ (7802933756009/25000000000000 : ℝ)^3449 := by
    have hnat : (127330749 : ℕ)^4473*25000000000000^3449 ≤ 7802933756009^3449*312500000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127330749 312500000 7802933756009 25000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2195667593/5000000000 : ℝ)^4473 ≤ (6878826402273/20000000000000 : ℝ)^3449 := by
    have hnat : (2195667593 : ℕ)^4473*20000000000000^3449 ≤ 6878826402273^3449*5000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2195667593 5000000000 6878826402273 20000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2195667639/5000000000 : ℝ)^4473 ≤ (34394132945869/100000000000000 : ℝ)^3449 := by
    have hnat : (2195667639 : ℕ)^4473*100000000000000^3449 ≤ 34394132945869^3449*5000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2195667639 5000000000 34394132945869 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(127330749/312500000 : ℝ), (2195667593/5000000000 : ℝ), (2195667639/5000000000 : ℝ)] ![(7802933756009/25000000000000 : ℝ), (6878826402273/20000000000000 : ℝ), (34394132945869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(127330749/312500000 : ℝ)|^4473 ≤ (7802933756009/25000000000000 : ℝ)^3449
        have hw : |(127330749/312500000 : ℝ)|=(127330749/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2195667593/5000000000 : ℝ)|^4473 ≤ (6878826402273/20000000000000 : ℝ)^3449
        have hw : |(2195667593/5000000000 : ℝ)|=(2195667593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2195667639/5000000000 : ℝ)|^4473 ≤ (34394132945869/100000000000000 : ℝ)^3449
        have hw : |(2195667639/5000000000 : ℝ)|=(2195667639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1488_box_8 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-508594773/2500000000 : ℝ)*x 0 + (1282268739/2500000000 : ℝ)*x 1 + (1356488451/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (508594773/2500000000 : ℝ)^4473 ≤ (2535928064283/20000000000000 : ℝ)^3449 := by
    have hnat : (508594773 : ℕ)^4473*20000000000000^3449 ≤ 2535928064283^3449*2500000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      508594773 2500000000 2535928064283 20000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1282268739/2500000000 : ℝ)^4473 ≤ (42067850276971/100000000000000 : ℝ)^3449 := by
    have hnat : (1282268739 : ℕ)^4473*100000000000000^3449 ≤ 42067850276971^3449*2500000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1282268739 2500000000 42067850276971 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1356488451/2500000000 : ℝ)^4473 ≤ (2828281836933/6250000000000 : ℝ)^3449 := by
    have hnat : (1356488451 : ℕ)^4473*6250000000000^3449 ≤ 2828281836933^3449*2500000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356488451 2500000000 2828281836933 6250000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-508594773/2500000000 : ℝ), (1282268739/2500000000 : ℝ), (1356488451/2500000000 : ℝ)] ![(2535928064283/20000000000000 : ℝ), (42067850276971/100000000000000 : ℝ), (2828281836933/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-508594773/2500000000 : ℝ)|^4473 ≤ (2535928064283/20000000000000 : ℝ)^3449
        have hw : |(-508594773/2500000000 : ℝ)|=(508594773/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1282268739/2500000000 : ℝ)|^4473 ≤ (42067850276971/100000000000000 : ℝ)^3449
        have hw : |(1282268739/2500000000 : ℝ)|=(1282268739/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1356488451/2500000000 : ℝ)|^4473 ≤ (2828281836933/6250000000000 : ℝ)^3449
        have hw : |(1356488451/2500000000 : ℝ)|=(1356488451/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1488_box_9 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1051214631/2000000000 : ℝ)*x 0 + (-932249527/5000000000 : ℝ)*x 1 + (1085190553/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051214631/2000000000 : ℝ)^4473 ≤ (43423660168527/100000000000000 : ℝ)^3449 := by
    have hnat : (1051214631 : ℕ)^4473*100000000000000^3449 ≤ 43423660168527^3449*2000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051214631 2000000000 43423660168527 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (932249527/5000000000 : ℝ)^4473 ≤ (11323841656809/100000000000000 : ℝ)^3449 := by
    have hnat : (932249527 : ℕ)^4473*100000000000000^3449 ≤ 11323841656809^3449*5000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      932249527 5000000000 11323841656809 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1085190553/2000000000 : ℝ)^4473 ≤ (17676757091/39062500000 : ℝ)^3449 := by
    have hnat : (1085190553 : ℕ)^4473*39062500000^3449 ≤ 17676757091^3449*2000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085190553 2000000000 17676757091 39062500000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1051214631/2000000000 : ℝ), (-932249527/5000000000 : ℝ), (1085190553/2000000000 : ℝ)] ![(43423660168527/100000000000000 : ℝ), (11323841656809/100000000000000 : ℝ), (17676757091/39062500000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1051214631/2000000000 : ℝ)|^4473 ≤ (43423660168527/100000000000000 : ℝ)^3449
        have hw : |(1051214631/2000000000 : ℝ)|=(1051214631/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-932249527/5000000000 : ℝ)|^4473 ≤ (11323841656809/100000000000000 : ℝ)^3449
        have hw : |(-932249527/5000000000 : ℝ)|=(932249527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1085190553/2000000000 : ℝ)|^4473 ≤ (17676757091/39062500000 : ℝ)^3449
        have hw : |(1085190553/2000000000 : ℝ)|=(1085190553/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1488_box_10 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (82126123/156250000 : ℝ)*x 0 + (542595463/1000000000 : ℝ)*x 1 + (-1864498239/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (82126123/156250000 : ℝ)^4473 ≤ (43423646421861/100000000000000 : ℝ)^3449 := by
    have hnat : (82126123 : ℕ)^4473*100000000000000^3449 ≤ 43423646421861^3449*156250000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82126123 156250000 43423646421861 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (542595463/1000000000 : ℝ)^4473 ≤ (2262625916253/5000000000000 : ℝ)^3449 := by
    have hnat : (542595463 : ℕ)^4473*5000000000000^3449 ≤ 2262625916253^3449*1000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542595463 1000000000 2262625916253 5000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1864498239/10000000000 : ℝ)^4473 ≤ (5661917618701/50000000000000 : ℝ)^3449 := by
    have hnat : (1864498239 : ℕ)^4473*50000000000000^3449 ≤ 5661917618701^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1864498239 10000000000 5661917618701 50000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(82126123/156250000 : ℝ), (542595463/1000000000 : ℝ), (-1864498239/10000000000 : ℝ)] ![(43423646421861/100000000000000 : ℝ), (2262625916253/5000000000000 : ℝ), (5661917618701/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(82126123/156250000 : ℝ)|^4473 ≤ (43423646421861/100000000000000 : ℝ)^3449
        have hw : |(82126123/156250000 : ℝ)|=(82126123/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(542595463/1000000000 : ℝ)|^4473 ≤ (2262625916253/5000000000000 : ℝ)^3449
        have hw : |(542595463/1000000000 : ℝ)|=(542595463/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1864498239/10000000000 : ℝ)|^4473 ≤ (5661917618701/50000000000000 : ℝ)^3449
        have hw : |(-1864498239/10000000000 : ℝ)|=(1864498239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1488_box_11 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (907187823/2000000000 : ℝ)*x 0 + (4160204013/10000000000 : ℝ)*x 1 + (832040651/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (907187823/2000000000 : ℝ)^4473 ≤ (17935047189641/50000000000000 : ℝ)^3449 := by
    have hnat : (907187823 : ℕ)^4473*50000000000000^3449 ≤ 17935047189641^3449*2000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      907187823 2000000000 17935047189641 50000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4160204013/10000000000 : ℝ)^4473 ≤ (32064956592741/100000000000000 : ℝ)^3449 := by
    have hnat : (4160204013 : ℕ)^4473*100000000000000^3449 ≤ 32064956592741^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4160204013 10000000000 32064956592741 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (832040651/2000000000 : ℝ)^4473 ≤ (8016237253963/25000000000000 : ℝ)^3449 := by
    have hnat : (832040651 : ℕ)^4473*25000000000000^3449 ≤ 8016237253963^3449*2000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      832040651 2000000000 8016237253963 25000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(907187823/2000000000 : ℝ), (4160204013/10000000000 : ℝ), (832040651/2000000000 : ℝ)] ![(17935047189641/50000000000000 : ℝ), (32064956592741/100000000000000 : ℝ), (8016237253963/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(907187823/2000000000 : ℝ)|^4473 ≤ (17935047189641/50000000000000 : ℝ)^3449
        have hw : |(907187823/2000000000 : ℝ)|=(907187823/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4160204013/10000000000 : ℝ)|^4473 ≤ (32064956592741/100000000000000 : ℝ)^3449
        have hw : |(4160204013/10000000000 : ℝ)|=(4160204013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(832040651/2000000000 : ℝ)|^4473 ≤ (8016237253963/25000000000000 : ℝ)^3449
        have hw : |(832040651/2000000000 : ℝ)|=(832040651/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1488_box_12 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1779294667/10000000000 : ℝ)*x 0 + (1103075941/2000000000 : ℝ)*x 1 + (2613881031/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1779294667/10000000000 : ℝ)^4473 ≤ (5328662776969/50000000000000 : ℝ)^3449 := by
    have hnat : (1779294667 : ℕ)^4473*50000000000000^3449 ≤ 5328662776969^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1779294667 10000000000 5328662776969 50000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1103075941/2000000000 : ℝ)^4473 ≤ (46222109794371/100000000000000 : ℝ)^3449 := by
    have hnat : (1103075941 : ℕ)^4473*100000000000000^3449 ≤ 46222109794371^3449*2000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103075941 2000000000 46222109794371 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2613881031/5000000000 : ℝ)^4473 ≤ (2695035290133/6250000000000 : ℝ)^3449 := by
    have hnat : (2613881031 : ℕ)^4473*6250000000000^3449 ≤ 2695035290133^3449*5000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2613881031 5000000000 2695035290133 6250000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1779294667/10000000000 : ℝ), (1103075941/2000000000 : ℝ), (2613881031/5000000000 : ℝ)] ![(5328662776969/50000000000000 : ℝ), (46222109794371/100000000000000 : ℝ), (2695035290133/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1779294667/10000000000 : ℝ)|^4473 ≤ (5328662776969/50000000000000 : ℝ)^3449
        have hw : |(-1779294667/10000000000 : ℝ)|=(1779294667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1103075941/2000000000 : ℝ)|^4473 ≤ (46222109794371/100000000000000 : ℝ)^3449
        have hw : |(1103075941/2000000000 : ℝ)|=(1103075941/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2613881031/5000000000 : ℝ)|^4473 ≤ (2695035290133/6250000000000 : ℝ)^3449
        have hw : |(2613881031/5000000000 : ℝ)|=(2613881031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1488_box_13 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5394322449/10000000000 : ℝ)*x 0 + (-1945855333/10000000000 : ℝ)*x 1 + (5227761979/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5394322449/10000000000 : ℝ)^4473 ≤ (44910676728499/100000000000000 : ℝ)^3449 := by
    have hnat : (5394322449 : ℕ)^4473*100000000000000^3449 ≤ 44910676728499^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394322449 10000000000 44910676728499 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1945855333/10000000000 : ℝ)^4473 ≤ (11968759503697/100000000000000 : ℝ)^3449 := by
    have hnat : (1945855333 : ℕ)^4473*100000000000000^3449 ≤ 11968759503697^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1945855333 10000000000 11968759503697 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5227761979/10000000000 : ℝ)^4473 ≤ (10780140938563/25000000000000 : ℝ)^3449 := by
    have hnat : (5227761979 : ℕ)^4473*25000000000000^3449 ≤ 10780140938563^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5227761979 10000000000 10780140938563 25000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5394322449/10000000000 : ℝ), (-1945855333/10000000000 : ℝ), (5227761979/10000000000 : ℝ)] ![(44910676728499/100000000000000 : ℝ), (11968759503697/100000000000000 : ℝ), (10780140938563/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5394322449/10000000000 : ℝ)|^4473 ≤ (44910676728499/100000000000000 : ℝ)^3449
        have hw : |(5394322449/10000000000 : ℝ)|=(5394322449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1945855333/10000000000 : ℝ)|^4473 ≤ (11968759503697/100000000000000 : ℝ)^3449
        have hw : |(-1945855333/10000000000 : ℝ)|=(1945855333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5227761979/10000000000 : ℝ)|^4473 ≤ (10780140938563/25000000000000 : ℝ)^3449
        have hw : |(5227761979/10000000000 : ℝ)|=(5227761979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1488_box_14 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5394322467/10000000000 : ℝ)*x 0 + (5227762159/10000000000 : ℝ)*x 1 + (-1945855067/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5394322467/10000000000 : ℝ)^4473 ≤ (11227669230713/25000000000000 : ℝ)^3449 := by
    have hnat : (5394322467 : ℕ)^4473*25000000000000^3449 ≤ 11227669230713^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394322467 10000000000 11227669230713 25000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5227762159/10000000000 : ℝ)^4473 ≤ (43120565679767/100000000000000 : ℝ)^3449 := by
    have hnat : (5227762159 : ℕ)^4473*100000000000000^3449 ≤ 43120565679767^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5227762159 10000000000 43120565679767 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1945855067/10000000000 : ℝ)^4473 ≤ (374023668181/3125000000000 : ℝ)^3449 := by
    have hnat : (1945855067 : ℕ)^4473*3125000000000^3449 ≤ 374023668181^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1945855067 10000000000 374023668181 3125000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5394322467/10000000000 : ℝ), (5227762159/10000000000 : ℝ), (-1945855067/10000000000 : ℝ)] ![(11227669230713/25000000000000 : ℝ), (43120565679767/100000000000000 : ℝ), (374023668181/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5394322467/10000000000 : ℝ)|^4473 ≤ (11227669230713/25000000000000 : ℝ)^3449
        have hw : |(5394322467/10000000000 : ℝ)|=(5394322467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5227762159/10000000000 : ℝ)|^4473 ≤ (43120565679767/100000000000000 : ℝ)^3449
        have hw : |(5227762159/10000000000 : ℝ)|=(5227762159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1945855067/10000000000 : ℝ)|^4473 ≤ (374023668181/3125000000000 : ℝ)^3449
        have hw : |(-1945855067/10000000000 : ℝ)|=(1945855067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1488_box_15 (p : ℝ) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (80716933/200000000 : ℝ)*x 0 + (68909997/156250000 : ℝ)*x 1 + (4410238727/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (80716933/200000000 : ℝ)^4473 ≤ (30827448495081/100000000000000 : ℝ)^3449 := by
    have hnat : (80716933 : ℕ)^4473*100000000000000^3449 ≤ 30827448495081^3449*200000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80716933 200000000 30827448495081 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (68909997/156250000 : ℝ)^4473 ≤ (17293140619803/50000000000000 : ℝ)^3449 := by
    have hnat : (68909997 : ℕ)^4473*50000000000000^3449 ≤ 17293140619803^3449*156250000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68909997 156250000 17293140619803 50000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4410238727/10000000000 : ℝ)^4473 ≤ (34586270245167/100000000000000 : ℝ)^3449 := by
    have hnat : (4410238727 : ℕ)^4473*100000000000000^3449 ≤ 34586270245167^3449*10000000000^4473 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4410238727 10000000000 34586270245167 100000000000000 4473 3449 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4473/1024 : ℝ)) 4473 3449 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(80716933/200000000 : ℝ), (68909997/156250000 : ℝ), (4410238727/10000000000 : ℝ)] ![(30827448495081/100000000000000 : ℝ), (17293140619803/50000000000000 : ℝ), (34586270245167/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(80716933/200000000 : ℝ)|^4473 ≤ (30827448495081/100000000000000 : ℝ)^3449
        have hw : |(80716933/200000000 : ℝ)|=(80716933/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(68909997/156250000 : ℝ)|^4473 ≤ (17293140619803/50000000000000 : ℝ)^3449
        have hw : |(68909997/156250000 : ℝ)|=(68909997/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4410238727/10000000000 : ℝ)|^4473 ≤ (34586270245167/100000000000000 : ℝ)^3449
        have hw : |(4410238727/10000000000 : ℝ)|=(4410238727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1488_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80732249/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15477/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (541/5000 : ℝ)*pair X i i ≤ pair X i h) :
    -(6371/10000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(11703/20000 : ℝ) ∧ (80057/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (42923/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15477/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (541/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15477/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (541/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15477/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (541/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15477/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (541/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15477/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (541/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15477/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (541/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (541/5000 : ℝ) ^ (4471/1024 : ℝ) ≤ (6070612374366917/100000000000000000000 : ℝ) := by
    have hpowers : (541/5000 : ℝ)^4471 ≤ (6070612374366917/100000000000000000000 : ℝ)^1024 := by
      have hnat : (541 : ℕ)^4471*100000000000000000000^1024 ≤ 6070612374366917^1024*5000^4471 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        541 5000 6070612374366917 100000000000000000000 4471 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (541/5000 : ℝ)) (X := (6070612374366917/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4471 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15477/100000 : ℝ) ^ (4471/1024 : ℝ) ≤ (1158941617660799/4000000000000000000 : ℝ) := by
    have hpowers : (15477/100000 : ℝ)^4471 ≤ (1158941617660799/4000000000000000000 : ℝ)^1024 := by
      have hnat : (15477 : ℕ)^4471*4000000000000000000^1024 ≤ 1158941617660799^1024*100000^4471 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15477 100000 1158941617660799 4000000000000000000 4471 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15477/100000 : ℝ)) (X := (1158941617660799/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4471 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006070612374366917/50000000000000000000 : ℝ) ≤ (5000139029661227/5000000000000000 : ℝ) ^ (4471/1024 : ℝ) := by
    have hpowers : (50006070612374366917/50000000000000000000 : ℝ)^1024 ≤ (5000139029661227/5000000000000000 : ℝ)^4471 := by
      have hnat : (50006070612374366917 : ℕ)^1024*5000000000000000^4471 ≤ 5000139029661227^4471*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006070612374366917 50000000000000000000 5000139029661227 5000000000000000 1024 4471 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000139029661227/5000000000000000 : ℝ)) (X := (50006070612374366917/50000000000000000000 : ℝ)) (by norm_num) 4471 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25008761038203971723/25000000000000000000 : ℝ) ≤ (2500200628303311/2500000000000000 : ℝ) ^ (4471/1024 : ℝ) := by
    have hpowers : (25008761038203971723/25000000000000000000 : ℝ)^1024 ≤ (2500200628303311/2500000000000000 : ℝ)^4471 := by
      have hnat : (25008761038203971723 : ℕ)^1024*2500000000000000^4471 ≤ 2500200628303311^4471*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25008761038203971723 25000000000000000000 2500200628303311 2500000000000000 1024 4471 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500200628303311/2500000000000000 : ℝ)) (X := (25008761038203971723/25000000000000000000 : ℝ)) (by norm_num) 4471 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2001158941617660799/2000000000000000000 : ℝ) ≤ (5000663483552017/5000000000000000 : ℝ) ^ (4471/1024 : ℝ) := by
    have hpowers : (2001158941617660799/2000000000000000000 : ℝ)^1024 ≤ (5000663483552017/5000000000000000 : ℝ)^4471 := by
      have hnat : (2001158941617660799 : ℕ)^1024*5000000000000000^4471 ≤ 5000663483552017^4471*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2001158941617660799 2000000000000000000 5000663483552017 5000000000000000 1024 4471 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000663483552017/5000000000000000 : ℝ)) (X := (2001158941617660799/2000000000000000000 : ℝ)) (by norm_num) 4471 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6070612374366917/100000000000000000000 : ℝ) ≤ ((23279972870033986339/23285000000000000000 : ℝ)+2*(52445389079/46570000000000 : ℝ)*(541/5000 : ℝ))^(4471/1024 : ℝ) := by
    rw [show (23279972870033986339/23285000000000000000 : ℝ)+2*(52445389079/46570000000000 : ℝ)*(541/5000 : ℝ)=(5000139029661227/5000000000000000 : ℝ) by norm_num, show 1+2*(6070612374366917/100000000000000000000 : ℝ)=(50006070612374366917/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1158941617660799/4000000000000000000 : ℝ)+(6070612374366917/100000000000000000000 : ℝ) ≤ ((23279972870033986339/23285000000000000000 : ℝ)+(52445389079/46570000000000 : ℝ)*((15477/100000 : ℝ)+(541/5000 : ℝ)))^(4471/1024 : ℝ) := by
    rw [show (23279972870033986339/23285000000000000000 : ℝ)+(52445389079/46570000000000 : ℝ)*((15477/100000 : ℝ)+(541/5000 : ℝ))=(2500200628303311/2500000000000000 : ℝ) by norm_num, show 1+(1158941617660799/4000000000000000000 : ℝ)+(6070612374366917/100000000000000000000 : ℝ)=(25008761038203971723/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1158941617660799/4000000000000000000 : ℝ) ≤ ((23279972870033986339/23285000000000000000 : ℝ)+2*(52445389079/46570000000000 : ℝ)*(15477/100000 : ℝ))^(4471/1024 : ℝ) := by
    rw [show (23279972870033986339/23285000000000000000 : ℝ)+2*(52445389079/46570000000000 : ℝ)*(15477/100000 : ℝ)=(5000663483552017/5000000000000000 : ℝ) by norm_num, show 1+2*(1158941617660799/4000000000000000000 : ℝ)=(2001158941617660799/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (23279972870033986339/23285000000000000000 : ℝ)*(X 1 0+X 2 0)+(52445389079/46570000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4471/1024 : ℝ)) (lo := (541/5000 : ℝ)) (hi := (15477/100000 : ℝ)) (c := (23279972870033986339/23285000000000000000 : ℝ)) (alpha := (52445389079/46570000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (23279972870033986339/23285000000000000000 : ℝ)*(X 0 1+X 2 1)+(52445389079/46570000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4471/1024 : ℝ)) (lo := (541/5000 : ℝ)) (hi := (15477/100000 : ℝ)) (c := (23279972870033986339/23285000000000000000 : ℝ)) (alpha := (52445389079/46570000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (23279972870033986339/23285000000000000000 : ℝ)*(X 0 2+X 1 2)+(52445389079/46570000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4471/1024 : ℝ)) (lo := (541/5000 : ℝ)) (hi := (15477/100000 : ℝ)) (c := (23279972870033986339/23285000000000000000 : ℝ)) (alpha := (52445389079/46570000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-105377941/625000000 : ℝ)*X 0 0+(5405431157/10000000000 : ℝ)*X 0 1+(1351357649/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2635197507/5000000000 : ℝ)*X 1 0+(-37463367/200000000 : ℝ)*X 1 1+(1351357679/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5270394877/10000000000 : ℝ)*X 2 0+(1081086211/2000000000 : ℝ)*X 2 1+(-1873168071/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((897055881/2000000000 : ℝ)*X 0 0+(4186125077/10000000000 : ℝ)*X 0 1+(4186124999/10000000000 : ℝ)*X 0 2+(897055881/2000000000 : ℝ)*X 1 0+(4186125077/10000000000 : ℝ)*X 1 1+(4186124999/10000000000 : ℝ)*X 1 2+(897055881/2000000000 : ℝ)*X 2 0+(4186125077/10000000000 : ℝ)*X 2 1+(4186124999/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2127542381/10000000000 : ℝ)*X 0 0+(5242764729/10000000000 : ℝ)*X 0 1+(2621382321/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5383858839/10000000000 : ℝ)*X 1 0+(-969942133/5000000000 : ℝ)*X 1 1+(163836397/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((672982363/1250000000 : ℝ)*X 2 0+(2621382341/5000000000 : ℝ)*X 2 1+(-1939884207/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((127330749/312500000 : ℝ)*X 0 0+(2195667593/5000000000 : ℝ)*X 0 1+(2195667639/5000000000 : ℝ)*X 0 2+(127330749/312500000 : ℝ)*X 1 0+(2195667593/5000000000 : ℝ)*X 1 1+(2195667639/5000000000 : ℝ)*X 1 2+(127330749/312500000 : ℝ)*X 2 0+(2195667593/5000000000 : ℝ)*X 2 1+(2195667639/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-508594773/2500000000 : ℝ)*X 0 0+(1282268739/2500000000 : ℝ)*X 0 1+(1356488451/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1051214631/2000000000 : ℝ)*X 1 0+(-932249527/5000000000 : ℝ)*X 1 1+(1085190553/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((82126123/156250000 : ℝ)*X 2 0+(542595463/1000000000 : ℝ)*X 2 1+(-1864498239/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((907187823/2000000000 : ℝ)*X 0 0+(4160204013/10000000000 : ℝ)*X 0 1+(832040651/2000000000 : ℝ)*X 0 2+(907187823/2000000000 : ℝ)*X 1 0+(4160204013/10000000000 : ℝ)*X 1 1+(832040651/2000000000 : ℝ)*X 1 2+(907187823/2000000000 : ℝ)*X 2 0+(4160204013/10000000000 : ℝ)*X 2 1+(832040651/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1779294667/10000000000 : ℝ)*X 0 0+(1103075941/2000000000 : ℝ)*X 0 1+(2613881031/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5394322449/10000000000 : ℝ)*X 1 0+(-1945855333/10000000000 : ℝ)*X 1 1+(5227761979/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5394322467/10000000000 : ℝ)*X 2 0+(5227762159/10000000000 : ℝ)*X 2 1+(-1945855067/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((80716933/200000000 : ℝ)*X 0 0+(68909997/156250000 : ℝ)*X 0 1+(4410238727/10000000000 : ℝ)*X 0 2+(80716933/200000000 : ℝ)*X 1 0+(68909997/156250000 : ℝ)*X 1 1+(4410238727/10000000000 : ℝ)*X 1 2+(80716933/200000000 : ℝ)*X 2 0+(68909997/156250000 : ℝ)*X 2 1+(4410238727/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1488_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-6371/10000 : ℝ) ≤ (-1483439220239131527034775403/2328500000000000000000000000 : ℝ) := by norm_num
    linear_combination (15457773/100000000000000 : ℝ)*(upper0) + (1154139/12500000000000 : ℝ)*(lower1) + (25748499/100000000000000 : ℝ)*(lower2) + (1155351/50000000000000 : ℝ)*(lower3) + (2187756653323899/100000000000000 : ℝ)*(major0) + (2187756653323899/100000000000000 : ℝ)*(major1) + (2187756653323899/100000000000000 : ℝ)*(major2) + (10625733/3125000000000 : ℝ)*(sp3) + (1520901348482033/50000000000000 : ℝ)*(sp4) + (760450837143277/25000000000000 : ℝ)*(sp5) + (1520898818291513/50000000000000 : ℝ)*(sp6) + (1354945595722679/100000000000000 : ℝ)*(sp7) + (651609043/100000000000000 : ℝ)*(sp8) + (2855995041/50000000000000 : ℝ)*(sp14) + (270989187149227/20000000000000 : ℝ)*(f.failure) + (760450837143277/25000000000000 : ℝ)*(f.sum) + (1249886226787/291062500000000000000000000 : ℝ)*base65 + (20829097815279284239/2328500000000000000000000000000000 : ℝ)*base68 + (21292482406106284239/2328500000000000000000000000000000 : ℝ)*base70 + (2513561409755284239/2328500000000000000000000000000000 : ℝ)*base72 + (801204887649/1164250000000000000000000000 : ℝ)*base73 + (7045418272985715761/2328500000000000000000000000000000 : ℝ)*base75 + (7416014388143715761/2328500000000000000000000000000000 : ℝ)*base77 + (4838564147202715761/2328500000000000000000000000000000 : ℝ)*base79 + (2399853628617/1164250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (4321523/1000000000000000000000 : ℝ)*base89 + (4321523/1000000000000000000000 : ℝ)*base91 + (4321523/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (11703/20000 : ℝ) ≤ (340645703370675810964964457058017/582125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (277607/1000000000000 : ℝ)*(upper0) + (7109031/50000000000000 : ℝ)*(upper3) + (12628477/20000000000000 : ℝ)*(upper4) + (2262375143447001/100000000000000 : ℝ)*(major0) + (2262375143447001/100000000000000 : ℝ)*(major1) + (2262375143447001/100000000000000 : ℝ)*(major2) + (3104078909012969/100000000000000 : ℝ)*(sp0) + (48501316583543/1562500000000 : ℝ)*(sp1) + (155203747420479/5000000000000 : ℝ)*(sp2) + (56046274695141/4000000000000 : ℝ)*(sp3) + (657585169/100000000000000 : ℝ)*(sp5) + (9970522341/100000000000000 : ℝ)*(sp6) + (525359047/20000000000000 : ℝ)*(sp7) + (751239869/12500000000000 : ℝ)*(sp8) + (4378623419293/312500000000 : ℝ)*(f.failure) + (38801061486649/1250000000000 : ℝ)*(f.sum) + (20688337714309/4657000000000000000000000000 : ℝ)*base65 + (13952716653885980661/2328500000000000000000000000000000 : ℝ)*base68 + (10202407443160480661/2328500000000000000000000000000000 : ℝ)*base70 + (7116082141660019339/2328500000000000000000000000000000 : ℝ)*base71 + (44727194127359/4657000000000000000000000000 : ℝ)*base74 + (2204514007526480661/2328500000000000000000000000000000 : ℝ)*base76 + (1433337664082480661/2328500000000000000000000000000000 : ℝ)*base78 + (18692672300170480661/2328500000000000000000000000000000 : ℝ)*base80 + (233194272351/582125000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (26293/15625000000000000000 : ℝ)*base90 + (26293/15625000000000000000 : ℝ)*base92 + (26293/15625000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (80057/100000 : ℝ) ≤ (116511942010547918568178553063757/145531250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (22502629/100000000000000 : ℝ)*(upper0) + (33010623/25000000000000 : ℝ)*(upper1) + (11618709/100000000000000 : ℝ)*(upper4) + (614753833380529/25000000000000 : ℝ)*(major0) + (614753833380529/25000000000000 : ℝ)*(major1) + (614753833380529/25000000000000 : ℝ)*(major2) + (154920117841/50000000000000 : ℝ)*(sp2) + (3250800217/20000000000000 : ℝ)*(sp3) + (4637617187/100000000000000 : ℝ)*(sp4) + (1684193921005623/50000000000000 : ℝ)*(sp8) + (1684199594597367/50000000000000 : ℝ)*(sp9) + (842022337239763/25000000000000 : ℝ)*(sp10) + (761464321736181/50000000000000 : ℝ)*(sp11) + (6709566301/100000000000000 : ℝ)*(sp12) + (1522944897473447/100000000000000 : ℝ)*(f.failure) + (1684199594597367/50000000000000 : ℝ)*(f.sum) + (3315804980877/931400000000000000000000000 : ℝ)*base66 + (4036201429390718331/582125000000000000000000000000000 : ℝ)*base67 + (3620828598029468331/582125000000000000000000000000000 : ℝ)*base69 + (686979704058031669/582125000000000000000000000000000 : ℝ)*base72 + (4985466276727/4657000000000000000000000000 : ℝ)*base74 + (2544080711583218331/582125000000000000000000000000000 : ℝ)*base75 + (2143532852939968331/582125000000000000000000000000000 : ℝ)*base77 + (3536946832782968331/582125000000000000000000000000000 : ℝ)*base79 + (2313408955047/4657000000000000000000000000 : ℝ)*base82 + (5907697/5000000000000000000000 : ℝ)*base90 + (5907697/5000000000000000000000 : ℝ)*base92 + (5907697/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-42923/50000 : ℝ) ≤ (-999434227399610145163846897186953/1164250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9841469/100000000000000 : ℝ)*(lower0) + (38797949/25000000000000 : ℝ)*(lower2) + (179805813/100000000000000 : ℝ)*(upper3) + (29939947/100000000000000 : ℝ)*(upper5) + (2497502304084197/100000000000000 : ℝ)*(major0) + (2497502304084197/100000000000000 : ℝ)*(major1) + (2497502304084197/100000000000000 : ℝ)*(major2) + (137257813/50000000000000 : ℝ)*(sp0) + (142334707563/100000000000000 : ℝ)*(sp5) + (20524915067/50000000000000 : ℝ)*(sp7) + (869209447859043/25000000000000 : ℝ)*(sp12) + (1738347865622117/50000000000000 : ℝ)*(sp13) + (1738419032975899/50000000000000 : ℝ)*(sp14) + (154674002899513/10000000000000 : ℝ)*(sp15) + (96673817426579/6250000000000 : ℝ)*(f.failure) + (1738419032975899/50000000000000 : ℝ)*(f.sum) + (14730779729651/2328500000000000000000000000 : ℝ)*base65 + (47289845332335715217/2328500000000000000000000000000000 : ℝ)*base68 + (27260060427591715217/2328500000000000000000000000000000 : ℝ)*base70 + (21749544358712215217/2328500000000000000000000000000000 : ℝ)*base72 + (16012824232269/2328500000000000000000000000 : ℝ)*base73 + (8608392803814715217/2328500000000000000000000000000000 : ℝ)*base76 + (21714005029037715217/2328500000000000000000000000000000 : ℝ)*base78 + (29097189469525715217/2328500000000000000000000000000000 : ℝ)*base80 + (7737614624327/2328500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (578829/312500000000000000000 : ℝ)*base90 + (578829/312500000000000000000 : ℝ)*base92 + (578829/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1488_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80732249/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15477/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (541/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(6371/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(11703/20000 : ℝ) else (80057/100000 : ℝ) ≤ X j i ∧ X j i ≤ (42923/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1488_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1488_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80732249/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15479/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5409/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(6371/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(11703/20000 : ℝ) else (80057/100000 : ℝ) ≤ X j i ∧ X j i ≤ (42923/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1488_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1488_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4471/1024 : ℝ) ≤ p) (hpb : p ≤ (4473/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80732249/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15479/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5409/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(6371/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(11703/20000 : ℝ) else (80057/100000 : ℝ) ≤ X j i ∧ X j i ≤ (42923/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1488_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
