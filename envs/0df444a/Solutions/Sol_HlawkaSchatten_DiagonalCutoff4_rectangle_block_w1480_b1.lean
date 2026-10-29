-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1480_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:12:39.848025+00:00
-- url     : https://prove2.me/submissions/ea1a950f-da24-4566-be45-f6f2814aa462

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
theorem support_rectangle_w1480_s3_0 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-191562079/1000000000 : ℝ)*x 0 + (2721069803/5000000000 : ℝ)*x 1 + (2605808689/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (191562079/1000000000 : ℝ)^4457 ≤ (5850673208089/50000000000000 : ℝ)^3433 := by
    have hnat : (191562079 : ℕ)^4457*50000000000000^3433 ≤ 5850673208089^3433*1000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      191562079 1000000000 5850673208089 50000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2721069803/5000000000 : ℝ)^4457 ≤ (45389426117943/100000000000000 : ℝ)^3433 := by
    have hnat : (2721069803 : ℕ)^4457*100000000000000^3433 ≤ 45389426117943^3433*5000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2721069803 5000000000 45389426117943 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2605808689/5000000000 : ℝ)^4457 ≤ (8581845490223/20000000000000 : ℝ)^3433 := by
    have hnat : (2605808689 : ℕ)^4457*20000000000000^3433 ≤ 8581845490223^3433*5000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2605808689 5000000000 8581845490223 20000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-191562079/1000000000 : ℝ), (2721069803/5000000000 : ℝ), (2605808689/5000000000 : ℝ)] ![(5850673208089/50000000000000 : ℝ), (45389426117943/100000000000000 : ℝ), (8581845490223/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-191562079/1000000000 : ℝ)|^4457 ≤ (5850673208089/50000000000000 : ℝ)^3433
        have hw : |(-191562079/1000000000 : ℝ)|=(191562079/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2721069803/5000000000 : ℝ)|^4457 ≤ (45389426117943/100000000000000 : ℝ)^3433
        have hw : |(2721069803/5000000000 : ℝ)|=(2721069803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2605808689/5000000000 : ℝ)|^4457 ≤ (8581845490223/20000000000000 : ℝ)^3433
        have hw : |(2605808689/5000000000 : ℝ)|=(2605808689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1480_s3_1 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354531973/10000000000 : ℝ)*x 0 + (-2033878041/10000000000 : ℝ)*x 1 + (1042323497/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354531973/10000000000 : ℝ)^4457 ≤ (22221542304173/50000000000000 : ℝ)^3433 := by
    have hnat : (5354531973 : ℕ)^4457*50000000000000^3433 ≤ 22221542304173^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354531973 10000000000 22221542304173 50000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2033878041/10000000000 : ℝ)^4457 ≤ (12647686780897/100000000000000 : ℝ)^3433 := by
    have hnat : (2033878041 : ℕ)^4457*100000000000000^3433 ≤ 12647686780897^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2033878041 10000000000 12647686780897 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1042323497/2000000000 : ℝ)^4457 ≤ (2681826787179/6250000000000 : ℝ)^3433 := by
    have hnat : (1042323497 : ℕ)^4457*6250000000000^3433 ≤ 2681826787179^3433*2000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042323497 2000000000 2681826787179 6250000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354531973/10000000000 : ℝ), (-2033878041/10000000000 : ℝ), (1042323497/2000000000 : ℝ)] ![(22221542304173/50000000000000 : ℝ), (12647686780897/100000000000000 : ℝ), (2681826787179/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354531973/10000000000 : ℝ)|^4457 ≤ (22221542304173/50000000000000 : ℝ)^3433
        have hw : |(5354531973/10000000000 : ℝ)|=(5354531973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2033878041/10000000000 : ℝ)|^4457 ≤ (12647686780897/100000000000000 : ℝ)^3433
        have hw : |(-2033878041/10000000000 : ℝ)|=(2033878041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1042323497/2000000000 : ℝ)|^4457 ≤ (2681826787179/6250000000000 : ℝ)^3433
        have hw : |(1042323497/2000000000 : ℝ)|=(1042323497/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1480_s3_2 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354531979/10000000000 : ℝ)*x 0 + (1302904327/2500000000 : ℝ)*x 1 + (-508469567/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354531979/10000000000 : ℝ)^4457 ≤ (44443084673001/100000000000000 : ℝ)^3433 := by
    have hnat : (5354531979 : ℕ)^4457*100000000000000^3433 ≤ 44443084673001^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354531979 10000000000 44443084673001 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1302904327/2500000000 : ℝ)^4457 ≤ (10727306675717/25000000000000 : ℝ)^3433 := by
    have hnat : (1302904327 : ℕ)^4457*25000000000000^3433 ≤ 10727306675717^3433*2500000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1302904327 2500000000 10727306675717 25000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (508469567/2500000000 : ℝ)^4457 ≤ (790480538347/6250000000000 : ℝ)^3433 := by
    have hnat : (508469567 : ℕ)^4457*6250000000000^3433 ≤ 790480538347^3433*2500000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      508469567 2500000000 790480538347 6250000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354531979/10000000000 : ℝ), (1302904327/2500000000 : ℝ), (-508469567/2500000000 : ℝ)] ![(44443084673001/100000000000000 : ℝ), (10727306675717/25000000000000 : ℝ), (790480538347/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354531979/10000000000 : ℝ)|^4457 ≤ (44443084673001/100000000000000 : ℝ)^3433
        have hw : |(5354531979/10000000000 : ℝ)|=(5354531979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1302904327/2500000000 : ℝ)|^4457 ≤ (10727306675717/25000000000000 : ℝ)^3433
        have hw : |(1302904327/2500000000 : ℝ)|=(1302904327/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-508469567/2500000000 : ℝ)|^4457 ≤ (790480538347/6250000000000 : ℝ)^3433
        have hw : |(-508469567/2500000000 : ℝ)|=(508469567/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1480_s3_3 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (428445903/1000000000 : ℝ)*x 0 + (4035619189/10000000000 : ℝ)*x 1 + (4546582341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (428445903/1000000000 : ℝ)^4457 ≤ (33273418393007/100000000000000 : ℝ)^3433 := by
    have hnat : (428445903 : ℕ)^4457*100000000000000^3433 ≤ 33273418393007^3433*1000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      428445903 1000000000 33273418393007 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4035619189/10000000000 : ℝ)^4457 ≤ (30786514288649/100000000000000 : ℝ)^3433 := by
    have hnat : (4035619189 : ℕ)^4457*100000000000000^3433 ≤ 30786514288649^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4035619189 10000000000 30786514288649 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4546582341/10000000000 : ℝ)^4457 ≤ (3594006730657/10000000000000 : ℝ)^3433 := by
    have hnat : (4546582341 : ℕ)^4457*10000000000000^3433 ≤ 3594006730657^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4546582341 10000000000 3594006730657 10000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(428445903/1000000000 : ℝ), (4035619189/10000000000 : ℝ), (4546582341/10000000000 : ℝ)] ![(33273418393007/100000000000000 : ℝ), (30786514288649/100000000000000 : ℝ), (3594006730657/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(428445903/1000000000 : ℝ)|^4457 ≤ (33273418393007/100000000000000 : ℝ)^3433
        have hw : |(428445903/1000000000 : ℝ)|=(428445903/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4035619189/10000000000 : ℝ)|^4457 ≤ (30786514288649/100000000000000 : ℝ)^3433
        have hw : |(4035619189/10000000000 : ℝ)|=(4035619189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4546582341/10000000000 : ℝ)|^4457 ≤ (3594006730657/10000000000000 : ℝ)^3433
        have hw : |(4546582341/10000000000 : ℝ)|=(4546582341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1480_s3_4 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1915654803/10000000000 : ℝ)*x 0 + (2606421957/5000000000 : ℝ)*x 1 + (42507061/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1915654803/10000000000 : ℝ)^4457 ≤ (11701616153607/100000000000000 : ℝ)^3433 := by
    have hnat : (1915654803 : ℕ)^4457*100000000000000^3433 ≤ 11701616153607^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1915654803 10000000000 11701616153607 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2606421957/5000000000 : ℝ)^4457 ≤ (4292233865421/10000000000000 : ℝ)^3433 := by
    have hnat : (2606421957 : ℕ)^4457*10000000000000^3433 ≤ 4292233865421^3433*5000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2606421957 5000000000 4292233865421 10000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42507061/78125000 : ℝ)^4457 ≤ (45376045177959/100000000000000 : ℝ)^3433 := by
    have hnat : (42507061 : ℕ)^4457*100000000000000^3433 ≤ 45376045177959^3433*78125000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42507061 78125000 45376045177959 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1915654803/10000000000 : ℝ), (2606421957/5000000000 : ℝ), (42507061/78125000 : ℝ)] ![(11701616153607/100000000000000 : ℝ), (4292233865421/10000000000000 : ℝ), (45376045177959/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1915654803/10000000000 : ℝ)|^4457 ≤ (11701616153607/100000000000000 : ℝ)^3433
        have hw : |(-1915654803/10000000000 : ℝ)|=(1915654803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2606421957/5000000000 : ℝ)|^4457 ≤ (4292233865421/10000000000000 : ℝ)^3433
        have hw : |(2606421957/5000000000 : ℝ)|=(2606421957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(42507061/78125000 : ℝ)|^4457 ≤ (45376045177959/100000000000000 : ℝ)^3433
        have hw : |(42507061/78125000 : ℝ)|=(42507061/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1480_s3_5 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (661790599/1250000000 : ℝ)*x 0 + (-451148021/2500000000 : ℝ)*x 1 + (5440903951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661790599/1250000000 : ℝ)^4457 ≤ (350363135681/800000000000 : ℝ)^3433 := by
    have hnat : (661790599 : ℕ)^4457*800000000000^3433 ≤ 350363135681^3433*1250000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661790599 1250000000 350363135681 800000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (451148021/2500000000 : ℝ)^4457 ≤ (10828561298327/100000000000000 : ℝ)^3433 := by
    have hnat : (451148021 : ℕ)^4457*100000000000000^3433 ≤ 10828561298327^3433*2500000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451148021 2500000000 10828561298327 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5440903951/10000000000 : ℝ)^4457 ≤ (22688023363139/50000000000000 : ℝ)^3433 := by
    have hnat : (5440903951 : ℕ)^4457*50000000000000^3433 ≤ 22688023363139^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5440903951 10000000000 22688023363139 50000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661790599/1250000000 : ℝ), (-451148021/2500000000 : ℝ), (5440903951/10000000000 : ℝ)] ![(350363135681/800000000000 : ℝ), (10828561298327/100000000000000 : ℝ), (22688023363139/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661790599/1250000000 : ℝ)|^4457 ≤ (350363135681/800000000000 : ℝ)^3433
        have hw : |(661790599/1250000000 : ℝ)|=(661790599/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-451148021/2500000000 : ℝ)|^4457 ≤ (10828561298327/100000000000000 : ℝ)^3433
        have hw : |(-451148021/2500000000 : ℝ)|=(451148021/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5440903951/10000000000 : ℝ)|^4457 ≤ (22688023363139/50000000000000 : ℝ)^3433
        have hw : |(5440903951/10000000000 : ℝ)|=(5440903951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1480_s3_6 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294325207/10000000000 : ℝ)*x 0 + (5440903463/10000000000 : ℝ)*x 1 + (-180459219/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294325207/10000000000 : ℝ)^4457 ≤ (10948849104261/25000000000000 : ℝ)^3433 := by
    have hnat : (5294325207 : ℕ)^4457*25000000000000^3433 ≤ 10948849104261^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294325207 10000000000 10948849104261 25000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5440903463/10000000000 : ℝ)^4457 ≤ (5672005180313/12500000000000 : ℝ)^3433 := by
    have hnat : (5440903463 : ℕ)^4457*12500000000000^3433 ≤ 5672005180313^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5440903463 10000000000 5672005180313 12500000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (180459219/1000000000 : ℝ)^4457 ≤ (10828562124111/100000000000000 : ℝ)^3433 := by
    have hnat : (180459219 : ℕ)^4457*100000000000000^3433 ≤ 10828562124111^3433*1000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      180459219 1000000000 10828562124111 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294325207/10000000000 : ℝ), (5440903463/10000000000 : ℝ), (-180459219/1000000000 : ℝ)] ![(10948849104261/25000000000000 : ℝ), (5672005180313/12500000000000 : ℝ), (10828562124111/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294325207/10000000000 : ℝ)|^4457 ≤ (10948849104261/25000000000000 : ℝ)^3433
        have hw : |(5294325207/10000000000 : ℝ)|=(5294325207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5440903463/10000000000 : ℝ)|^4457 ≤ (5672005180313/12500000000000 : ℝ)^3433
        have hw : |(5440903463/10000000000 : ℝ)|=(5440903463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-180459219/1000000000 : ℝ)|^4457 ≤ (10828562124111/100000000000000 : ℝ)^3433
        have hw : |(-180459219/1000000000 : ℝ)|=(180459219/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1480_s3_7 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1071133659/2500000000 : ℝ)*x 0 + (141995739/312500000 : ℝ)*x 1 + (2019179401/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071133659/2500000000 : ℝ)^4457 ≤ (16637090348033/50000000000000 : ℝ)^3433 := by
    have hnat : (1071133659 : ℕ)^4457*50000000000000^3433 ≤ 16637090348033^3433*2500000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071133659 2500000000 16637090348033 50000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (141995739/312500000 : ℝ)^4457 ≤ (17956084299423/50000000000000 : ℝ)^3433 := by
    have hnat : (141995739 : ℕ)^4457*50000000000000^3433 ≤ 17956084299423^3433*312500000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      141995739 312500000 17956084299423 50000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2019179401/5000000000 : ℝ)^4457 ≤ (1925853168507/6250000000000 : ℝ)^3433 := by
    have hnat : (2019179401 : ℕ)^4457*6250000000000^3433 ≤ 1925853168507^3433*5000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2019179401 5000000000 1925853168507 6250000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071133659/2500000000 : ℝ), (141995739/312500000 : ℝ), (2019179401/5000000000 : ℝ)] ![(16637090348033/50000000000000 : ℝ), (17956084299423/50000000000000 : ℝ), (1925853168507/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071133659/2500000000 : ℝ)|^4457 ≤ (16637090348033/50000000000000 : ℝ)^3433
        have hw : |(1071133659/2500000000 : ℝ)|=(1071133659/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(141995739/312500000 : ℝ)|^4457 ≤ (17956084299423/50000000000000 : ℝ)^3433
        have hw : |(141995739/312500000 : ℝ)|=(141995739/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2019179401/5000000000 : ℝ)|^4457 ≤ (1925853168507/6250000000000 : ℝ)^3433
        have hw : |(2019179401/5000000000 : ℝ)|=(2019179401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1480_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40206863/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16131/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1273/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (2139/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7787/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16131/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1273/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16131/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1273/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16131/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1273/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16131/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1273/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16131/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1273/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16131/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1273/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1273/12500 : ℝ) ^ (4455/1024 : ℝ) ≤ (482907223175671/10000000000000000000 : ℝ) := by
    have hpowers : (1273/12500 : ℝ)^4455 ≤ (482907223175671/10000000000000000000 : ℝ)^1024 := by
      have hnat : (1273 : ℕ)^4455*10000000000000000000^1024 ≤ 482907223175671^1024*12500^4455 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1273 12500 482907223175671 10000000000000000000 4455 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1273/12500 : ℝ)) (X := (482907223175671/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4455 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16131/100000 : ℝ) ^ (4455/1024 : ℝ) ≤ (35715962289365073/100000000000000000000 : ℝ) := by
    have hpowers : (16131/100000 : ℝ)^4455 ≤ (35715962289365073/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16131 : ℕ)^4455*100000000000000000000^1024 ≤ 35715962289365073^1024*100000^4455 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16131 100000 35715962289365073 100000000000000000000 4455 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16131/100000 : ℝ)) (X := (35715962289365073/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4455 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000482907223175671/5000000000000000000 : ℝ) ≤ (10000221988151197/10000000000000000 : ℝ) ^ (4455/1024 : ℝ) := by
    have hpowers : (5000482907223175671/5000000000000000000 : ℝ)^1024 ≤ (10000221988151197/10000000000000000 : ℝ)^4455 := by
      have hnat : (5000482907223175671 : ℕ)^1024*10000000000000000^4455 ≤ 10000221988151197^4455*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000482907223175671 5000000000000000000 10000221988151197 10000000000000000 1024 4455 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000221988151197/10000000000000000 : ℝ)) (X := (5000482907223175671/5000000000000000000 : ℝ)) (by norm_num) 4455 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100040545034521121783/100000000000000000000 : ℝ) ≤ (10000931798760073/10000000000000000 : ℝ) ^ (4455/1024 : ℝ) := by
    have hpowers : (100040545034521121783/100000000000000000000 : ℝ)^1024 ≤ (10000931798760073/10000000000000000 : ℝ)^4455 := by
      have hnat : (100040545034521121783 : ℕ)^1024*10000000000000000^4455 ≤ 10000931798760073^4455*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100040545034521121783 100000000000000000000 10000931798760073 10000000000000000 1024 4455 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000931798760073/10000000000000000 : ℝ)) (X := (100040545034521121783/100000000000000000000 : ℝ)) (by norm_num) 4455 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035715962289365073/50000000000000000000 : ℝ) ≤ (10001641609368949/10000000000000000 : ℝ) ^ (4455/1024 : ℝ) := by
    have hpowers : (50035715962289365073/50000000000000000000 : ℝ)^1024 ≤ (10001641609368949/10000000000000000 : ℝ)^4455 := by
      have hnat : (50035715962289365073 : ℕ)^1024*10000000000000000^4455 ≤ 10001641609368949^4455*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035715962289365073 50000000000000000000 10001641609368949 10000000000000000 1024 4455 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001641609368949/10000000000000000 : ℝ)) (X := (50035715962289365073/50000000000000000000 : ℝ)) (by norm_num) 4455 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(482907223175671/10000000000000000000 : ℝ) ≤ ((3129308565318609589/3130000000000000000 : ℝ)+2*(177452652219/148675000000000 : ℝ)*(1273/12500 : ℝ))^(4455/1024 : ℝ) := by
    rw [show (3129308565318609589/3130000000000000000 : ℝ)+2*(177452652219/148675000000000 : ℝ)*(1273/12500 : ℝ)=(10000221988151197/10000000000000000 : ℝ) by norm_num, show 1+2*(482907223175671/10000000000000000000 : ℝ)=(5000482907223175671/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35715962289365073/100000000000000000000 : ℝ)+(482907223175671/10000000000000000000 : ℝ) ≤ ((3129308565318609589/3130000000000000000 : ℝ)+(177452652219/148675000000000 : ℝ)*((16131/100000 : ℝ)+(1273/12500 : ℝ)))^(4455/1024 : ℝ) := by
    rw [show (3129308565318609589/3130000000000000000 : ℝ)+(177452652219/148675000000000 : ℝ)*((16131/100000 : ℝ)+(1273/12500 : ℝ))=(10000931798760073/10000000000000000 : ℝ) by norm_num, show 1+(35715962289365073/100000000000000000000 : ℝ)+(482907223175671/10000000000000000000 : ℝ)=(100040545034521121783/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35715962289365073/100000000000000000000 : ℝ) ≤ ((3129308565318609589/3130000000000000000 : ℝ)+2*(177452652219/148675000000000 : ℝ)*(16131/100000 : ℝ))^(4455/1024 : ℝ) := by
    rw [show (3129308565318609589/3130000000000000000 : ℝ)+2*(177452652219/148675000000000 : ℝ)*(16131/100000 : ℝ)=(10001641609368949/10000000000000000 : ℝ) by norm_num, show 1+2*(35715962289365073/100000000000000000000 : ℝ)=(50035715962289365073/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3129308565318609589/3130000000000000000 : ℝ)*(X 1 0+X 2 0)+(177452652219/148675000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4455/1024 : ℝ)) (lo := (1273/12500 : ℝ)) (hi := (16131/100000 : ℝ)) (c := (3129308565318609589/3130000000000000000 : ℝ)) (alpha := (177452652219/148675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3129308565318609589/3130000000000000000 : ℝ)*(X 0 1+X 2 1)+(177452652219/148675000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4455/1024 : ℝ)) (lo := (1273/12500 : ℝ)) (hi := (16131/100000 : ℝ)) (c := (3129308565318609589/3130000000000000000 : ℝ)) (alpha := (177452652219/148675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3129308565318609589/3130000000000000000 : ℝ)*(X 0 2+X 1 2)+(177452652219/148675000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4455/1024 : ℝ)) (lo := (1273/12500 : ℝ)) (hi := (16131/100000 : ℝ)) (c := (3129308565318609589/3130000000000000000 : ℝ)) (alpha := (177452652219/148675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-191562079/1000000000 : ℝ)*X 0 0+(2721069803/5000000000 : ℝ)*X 0 1+(2605808689/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5354531973/10000000000 : ℝ)*X 1 0+(-2033878041/10000000000 : ℝ)*X 1 1+(1042323497/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5354531979/10000000000 : ℝ)*X 2 0+(1302904327/2500000000 : ℝ)*X 2 1+(-508469567/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((428445903/1000000000 : ℝ)*X 0 0+(4035619189/10000000000 : ℝ)*X 0 1+(4546582341/10000000000 : ℝ)*X 0 2+(428445903/1000000000 : ℝ)*X 1 0+(4035619189/10000000000 : ℝ)*X 1 1+(4546582341/10000000000 : ℝ)*X 1 2+(428445903/1000000000 : ℝ)*X 2 0+(4035619189/10000000000 : ℝ)*X 2 1+(4546582341/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1915654803/10000000000 : ℝ)*X 0 0+(2606421957/5000000000 : ℝ)*X 0 1+(42507061/78125000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((661790599/1250000000 : ℝ)*X 1 0+(-451148021/2500000000 : ℝ)*X 1 1+(5440903951/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5294325207/10000000000 : ℝ)*X 2 0+(5440903463/10000000000 : ℝ)*X 2 1+(-180459219/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1071133659/2500000000 : ℝ)*X 0 0+(141995739/312500000 : ℝ)*X 0 1+(2019179401/5000000000 : ℝ)*X 0 2+(1071133659/2500000000 : ℝ)*X 1 0+(141995739/312500000 : ℝ)*X 1 1+(2019179401/5000000000 : ℝ)*X 1 2+(1071133659/2500000000 : ℝ)*X 2 0+(141995739/312500000 : ℝ)*X 2 1+(2019179401/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7525236438305861013330895407/743375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2173580669/100000000000000 : ℝ)*(base19) + (100354861/5000000000000 : ℝ)*(base23) + (91746923/100000000000000 : ℝ)*(lower2) + (186792973/50000000000000 : ℝ)*(upper3) + (40336687/100000000000000 : ℝ)*(upper5) + (1573790911703741/50000000000000 : ℝ)*(major0) + (1573790911703741/50000000000000 : ℝ)*(major1) + (1573790911703741/50000000000000 : ℝ)*(major2) + (4338014924726167/100000000000000 : ℝ)*(sp0) + (2169021937433839/50000000000000 : ℝ)*(sp1) + (2169022020675563/50000000000000 : ℝ)*(sp2) + (78284028788137/4000000000000 : ℝ)*(sp3) + (31123722179/100000000000000 : ℝ)*(sp4) + (516913361/3125000000000 : ℝ)*(sp7) + (1957117260930977/100000000000000 : ℝ)*(f.failure) + (2169023024224173/50000000000000 : ℝ)*(f.sum) + (22368861866307/29735000000000000000000000000 : ℝ)*base65 + (12246758575465776531/2973500000000000000000000000000000 : ℝ)*base67 + (11504491031752776531/2973500000000000000000000000000000 : ℝ)*base69 + (16475011448328723469/2973500000000000000000000000000000 : ℝ)*base72 + (9894670524327/29735000000000000000000000000 : ℝ)*base73 + (23272230060660776531/2973500000000000000000000000000000 : ℝ)*base75 + (44364613397661276531/2973500000000000000000000000000000 : ℝ)*base77 + (6285931800465776531/2973500000000000000000000000000000 : ℝ)*base79 + (220688587591603/29735000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (5304849/2500000000000000000000 : ℝ)*base90 + (5304849/2500000000000000000000 : ℝ)*base92 + (5304849/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (331098093211831922021313/29735000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1292891169/100000000000000 : ℝ)*(base19) + (944445291/50000000000000 : ℝ)*(base23) + (41856999/50000000000000 : ℝ)*(upper3) + (140918629/100000000000000 : ℝ)*(lower4) + (68746703/25000000000000 : ℝ)*(upper5) + (3181518216304889/100000000000000 : ℝ)*(major0) + (3181518216304889/100000000000000 : ℝ)*(major1) + (3181518216304889/100000000000000 : ℝ)*(major2) + (6197818891/25000000000000 : ℝ)*(sp1) + (23571142883/100000000000000 : ℝ)*(sp2) + (2192408840487397/50000000000000 : ℝ)*(sp4) + (219239579840403/5000000000000 : ℝ)*(sp5) + (274049513808833/6250000000000 : ℝ)*(sp6) + (1978218380469579/100000000000000 : ℝ)*(sp7) + (1978218380469579/100000000000000 : ℝ)*(f.failure) + (2192408840487397/50000000000000 : ℝ)*(f.sum) + (79585928279903/14867500000000000000000000000 : ℝ)*base66 + (44433100687477031799/5947000000000000000000000000000000 : ℝ)*base67 + (8533450428416968201/5947000000000000000000000000000000 : ℝ)*base70 + (42871247794238968201/5947000000000000000000000000000000 : ℝ)*base72 + (10265473760449/1858437500000000000000000000 : ℝ)*base73 + (18118028415872968201/5947000000000000000000000000000000 : ℝ)*base76 + (42258992329994031799/5947000000000000000000000000000000 : ℝ)*base77 + (29395908323413031799/5947000000000000000000000000000000 : ℝ)*base79 + (49575675232087/14867500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (13520677/2500000000000000000000 : ℝ)*base89 + (13520677/2500000000000000000000 : ℝ)*base91 + (13520677/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1480_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40206863/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16131/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1273/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2139/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7787/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1480_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1480_s4_0 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-958125377/5000000000 : ℝ)*x 0 + (2719032531/5000000000 : ℝ)*x 1 + (2607638313/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (958125377/5000000000 : ℝ)^4457 ≤ (2341268505613/20000000000000 : ℝ)^3433 := by
    have hnat : (958125377 : ℕ)^4457*20000000000000^3433 ≤ 2341268505613^3433*5000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      958125377 5000000000 2341268505613 20000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2719032531/5000000000 : ℝ)^4457 ≤ (11336327828573/25000000000000 : ℝ)^3433 := by
    have hnat : (2719032531 : ℕ)^4457*25000000000000^3433 ≤ 11336327828573^3433*5000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719032531 5000000000 11336327828573 25000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2607638313/5000000000 : ℝ)^4457 ≤ (42948346142187/100000000000000 : ℝ)^3433 := by
    have hnat : (2607638313 : ℕ)^4457*100000000000000^3433 ≤ 42948346142187^3433*5000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607638313 5000000000 42948346142187 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-958125377/5000000000 : ℝ), (2719032531/5000000000 : ℝ), (2607638313/5000000000 : ℝ)] ![(2341268505613/20000000000000 : ℝ), (11336327828573/25000000000000 : ℝ), (42948346142187/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-958125377/5000000000 : ℝ)|^4457 ≤ (2341268505613/20000000000000 : ℝ)^3433
        have hw : |(-958125377/5000000000 : ℝ)|=(958125377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2719032531/5000000000 : ℝ)|^4457 ≤ (11336327828573/25000000000000 : ℝ)^3433
        have hw : |(2719032531/5000000000 : ℝ)|=(2719032531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2607638313/5000000000 : ℝ)|^4457 ≤ (42948346142187/100000000000000 : ℝ)^3433
        have hw : |(2607638313/5000000000 : ℝ)|=(2607638313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1480_s4_1 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (535347357/1000000000 : ℝ)*x 0 + (-2030443353/10000000000 : ℝ)*x 1 + (2607638773/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535347357/1000000000 : ℝ)^4457 ≤ (2221583987669/5000000000000 : ℝ)^3433 := by
    have hnat : (535347357 : ℕ)^4457*5000000000000^3433 ≤ 2221583987669^3433*1000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535347357 1000000000 2221583987669 5000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2030443353/10000000000 : ℝ)^4457 ≤ (6309982124893/50000000000000 : ℝ)^3433 := by
    have hnat : (2030443353 : ℕ)^4457*50000000000000^3433 ≤ 6309982124893^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2030443353 10000000000 6309982124893 50000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2607638773/5000000000 : ℝ)^4457 ≤ (42948355978351/100000000000000 : ℝ)^3433 := by
    have hnat : (2607638773 : ℕ)^4457*100000000000000^3433 ≤ 42948355978351^3433*5000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607638773 5000000000 42948355978351 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535347357/1000000000 : ℝ), (-2030443353/10000000000 : ℝ), (2607638773/5000000000 : ℝ)] ![(2221583987669/5000000000000 : ℝ), (6309982124893/50000000000000 : ℝ), (42948355978351/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535347357/1000000000 : ℝ)|^4457 ≤ (2221583987669/5000000000000 : ℝ)^3433
        have hw : |(535347357/1000000000 : ℝ)|=(535347357/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2030443353/10000000000 : ℝ)|^4457 ≤ (6309982124893/50000000000000 : ℝ)^3433
        have hw : |(-2030443353/10000000000 : ℝ)|=(2030443353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2607638773/5000000000 : ℝ)|^4457 ≤ (42948355978351/100000000000000 : ℝ)^3433
        have hw : |(2607638773/5000000000 : ℝ)|=(2607638773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1480_s4_2 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676737043/5000000000 : ℝ)*x 0 + (5215276731/10000000000 : ℝ)*x 1 + (-406088749/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676737043/5000000000 : ℝ)^4457 ≤ (4443168531339/10000000000000 : ℝ)^3433 := by
    have hnat : (2676737043 : ℕ)^4457*10000000000000^3433 ≤ 4443168531339^3433*5000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676737043 5000000000 4443168531339 10000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5215276731/10000000000 : ℝ)^4457 ≤ (42948347264793/100000000000000 : ℝ)^3433 := by
    have hnat : (5215276731 : ℕ)^4457*100000000000000^3433 ≤ 42948347264793^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215276731 10000000000 42948347264793 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (406088749/2000000000 : ℝ)^4457 ≤ (6309983706477/50000000000000 : ℝ)^3433 := by
    have hnat : (406088749 : ℕ)^4457*50000000000000^3433 ≤ 6309983706477^3433*2000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      406088749 2000000000 6309983706477 50000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676737043/5000000000 : ℝ), (5215276731/10000000000 : ℝ), (-406088749/2000000000 : ℝ)] ![(4443168531339/10000000000000 : ℝ), (42948347264793/100000000000000 : ℝ), (6309983706477/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676737043/5000000000 : ℝ)|^4457 ≤ (4443168531339/10000000000000 : ℝ)^3433
        have hw : |(2676737043/5000000000 : ℝ)|=(2676737043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5215276731/10000000000 : ℝ)|^4457 ≤ (42948347264793/100000000000000 : ℝ)^3433
        have hw : |(5215276731/10000000000 : ℝ)|=(5215276731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-406088749/2000000000 : ℝ)|^4457 ≤ (6309983706477/50000000000000 : ℝ)^3433
        have hw : |(-406088749/2000000000 : ℝ)|=(406088749/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1480_s4_3 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4284851267/10000000000 : ℝ)*x 0 + (2022072279/5000000000 : ℝ)*x 1 + (2268982211/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4284851267/10000000000 : ℝ)^4457 ≤ (33277373195011/100000000000000 : ℝ)^3433 := by
    have hnat : (4284851267 : ℕ)^4457*100000000000000^3433 ≤ 33277373195011^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4284851267 10000000000 33277373195011 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2022072279/5000000000 : ℝ)^4457 ≤ (1929436112101/6250000000000 : ℝ)^3433 := by
    have hnat : (2022072279 : ℕ)^4457*6250000000000^3433 ≤ 1929436112101^3433*5000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2022072279 5000000000 1929436112101 6250000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2268982211/5000000000 : ℝ)^4457 ≤ (35851648994393/100000000000000 : ℝ)^3433 := by
    have hnat : (2268982211 : ℕ)^4457*100000000000000^3433 ≤ 35851648994393^3433*5000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2268982211 5000000000 35851648994393 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4284851267/10000000000 : ℝ), (2022072279/5000000000 : ℝ), (2268982211/5000000000 : ℝ)] ![(33277373195011/100000000000000 : ℝ), (1929436112101/6250000000000 : ℝ), (35851648994393/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4284851267/10000000000 : ℝ)|^4457 ≤ (33277373195011/100000000000000 : ℝ)^3433
        have hw : |(4284851267/10000000000 : ℝ)|=(4284851267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2022072279/5000000000 : ℝ)|^4457 ≤ (1929436112101/6250000000000 : ℝ)^3433
        have hw : |(2022072279/5000000000 : ℝ)|=(2022072279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2268982211/5000000000 : ℝ)|^4457 ≤ (35851648994393/100000000000000 : ℝ)^3433
        have hw : |(2268982211/5000000000 : ℝ)|=(2268982211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1480_s4_4 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1916281359/10000000000 : ℝ)*x 0 + (5216422851/10000000000 : ℝ)*x 1 + (1087382111/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1916281359/10000000000 : ℝ)^4457 ≤ (5853292631179/50000000000000 : ℝ)^3433 := by
    have hnat : (1916281359 : ℕ)^4457*50000000000000^3433 ≤ 5853292631179^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1916281359 10000000000 5853292631179 50000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216422851/10000000000 : ℝ)^4457 ≤ (21480300694151/50000000000000 : ℝ)^3433 := by
    have hnat : (5216422851 : ℕ)^4457*50000000000000^3433 ≤ 21480300694151^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216422851 10000000000 21480300694151 50000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1087382111/2000000000 : ℝ)^4457 ≤ (45332813339687/100000000000000 : ℝ)^3433 := by
    have hnat : (1087382111 : ℕ)^4457*100000000000000^3433 ≤ 45332813339687^3433*2000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087382111 2000000000 45332813339687 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1916281359/10000000000 : ℝ), (5216422851/10000000000 : ℝ), (1087382111/2000000000 : ℝ)] ![(5853292631179/50000000000000 : ℝ), (21480300694151/50000000000000 : ℝ), (45332813339687/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1916281359/10000000000 : ℝ)|^4457 ≤ (5853292631179/50000000000000 : ℝ)^3433
        have hw : |(-1916281359/10000000000 : ℝ)|=(1916281359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216422851/10000000000 : ℝ)|^4457 ≤ (21480300694151/50000000000000 : ℝ)^3433
        have hw : |(5216422851/10000000000 : ℝ)|=(5216422851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1087382111/2000000000 : ℝ)|^4457 ≤ (45332813339687/100000000000000 : ℝ)^3433
        have hw : |(1087382111/2000000000 : ℝ)|=(1087382111/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1480_s4_5 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295289791/10000000000 : ℝ)*x 0 + (-904404931/5000000000 : ℝ)*x 1 + (1359227633/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295289791/10000000000 : ℝ)^4457 ≤ (4380575591077/10000000000000 : ℝ)^3433 := by
    have hnat : (5295289791 : ℕ)^4457*10000000000000^3433 ≤ 4380575591077^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295289791 10000000000 4380575591077 10000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (904404931/5000000000 : ℝ)^4457 ≤ (10861430982863/100000000000000 : ℝ)^3433 := by
    have hnat : (904404931 : ℕ)^4457*100000000000000^3433 ≤ 10861430982863^3433*5000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      904404931 5000000000 10861430982863 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1359227633/2500000000 : ℝ)^4457 ≤ (45332813090711/100000000000000 : ℝ)^3433 := by
    have hnat : (1359227633 : ℕ)^4457*100000000000000^3433 ≤ 45332813090711^3433*2500000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359227633 2500000000 45332813090711 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295289791/10000000000 : ℝ), (-904404931/5000000000 : ℝ), (1359227633/2500000000 : ℝ)] ![(4380575591077/10000000000000 : ℝ), (10861430982863/100000000000000 : ℝ), (45332813090711/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295289791/10000000000 : ℝ)|^4457 ≤ (4380575591077/10000000000000 : ℝ)^3433
        have hw : |(5295289791/10000000000 : ℝ)|=(5295289791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-904404931/5000000000 : ℝ)|^4457 ≤ (10861430982863/100000000000000 : ℝ)^3433
        have hw : |(-904404931/5000000000 : ℝ)|=(904404931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1359227633/2500000000 : ℝ)|^4457 ≤ (45332813090711/100000000000000 : ℝ)^3433
        have hw : |(1359227633/2500000000 : ℝ)|=(1359227633/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1480_s4_6 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295289761/10000000000 : ℝ)*x 0 + (2718455273/5000000000 : ℝ)*x 1 + (-1808809883/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295289761/10000000000 : ℝ)^4457 ≤ (21902877794283/50000000000000 : ℝ)^3433 := by
    have hnat : (5295289761 : ℕ)^4457*50000000000000^3433 ≤ 21902877794283^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295289761 10000000000 21902877794283 50000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2718455273/5000000000 : ℝ)^4457 ≤ (45332813242261/100000000000000 : ℝ)^3433 := by
    have hnat : (2718455273 : ℕ)^4457*100000000000000^3433 ≤ 45332813242261^3433*5000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718455273 5000000000 45332813242261 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1808809883/10000000000 : ℝ)^4457 ≤ (678839446661/6250000000000 : ℝ)^3433 := by
    have hnat : (1808809883 : ℕ)^4457*6250000000000^3433 ≤ 678839446661^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1808809883 10000000000 678839446661 6250000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295289761/10000000000 : ℝ), (2718455273/5000000000 : ℝ), (-1808809883/10000000000 : ℝ)] ![(21902877794283/50000000000000 : ℝ), (45332813242261/100000000000000 : ℝ), (678839446661/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295289761/10000000000 : ℝ)|^4457 ≤ (21902877794283/50000000000000 : ℝ)^3433
        have hw : |(5295289761/10000000000 : ℝ)|=(5295289761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2718455273/5000000000 : ℝ)|^4457 ≤ (45332813242261/100000000000000 : ℝ)^3433
        have hw : |(2718455273/5000000000 : ℝ)|=(2718455273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1808809883/10000000000 : ℝ)|^4457 ≤ (678839446661/6250000000000 : ℝ)^3433
        have hw : |(-1808809883/10000000000 : ℝ)|=(1808809883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1480_s4_7 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2142459547/5000000000 : ℝ)*x 0 + (4535425021/10000000000 : ℝ)*x 1 + (2023351637/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2142459547/5000000000 : ℝ)^4457 ≤ (33278057084219/100000000000000 : ℝ)^3433 := by
    have hnat : (2142459547 : ℕ)^4457*100000000000000^3433 ≤ 33278057084219^3433*5000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2142459547 5000000000 33278057084219 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4535425021/10000000000 : ℝ)^4457 ≤ (35825604740849/100000000000000 : ℝ)^3433 := by
    have hnat : (4535425021 : ℕ)^4457*100000000000000^3433 ≤ 35825604740849^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4535425021 10000000000 35825604740849 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2023351637/5000000000 : ℝ)^4457 ≤ (30896338164591/100000000000000 : ℝ)^3433 := by
    have hnat : (2023351637 : ℕ)^4457*100000000000000^3433 ≤ 30896338164591^3433*5000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2023351637 5000000000 30896338164591 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2142459547/5000000000 : ℝ), (4535425021/10000000000 : ℝ), (2023351637/5000000000 : ℝ)] ![(33278057084219/100000000000000 : ℝ), (35825604740849/100000000000000 : ℝ), (30896338164591/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2142459547/5000000000 : ℝ)|^4457 ≤ (33278057084219/100000000000000 : ℝ)^3433
        have hw : |(2142459547/5000000000 : ℝ)|=(2142459547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4535425021/10000000000 : ℝ)|^4457 ≤ (35825604740849/100000000000000 : ℝ)^3433
        have hw : |(4535425021/10000000000 : ℝ)|=(4535425021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2023351637/5000000000 : ℝ)|^4457 ≤ (30896338164591/100000000000000 : ℝ)^3433
        have hw : |(2023351637/5000000000 : ℝ)|=(2023351637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1480_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40206863/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7787/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2139/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (5387/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15489/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7787/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2139/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7787/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2139/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7787/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2139/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7787/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2139/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7787/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2139/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7787/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2139/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2139/20000 : ℝ) ^ (4455/1024 : ℝ) ≤ (5975408387572541/100000000000000000000 : ℝ) := by
    have hpowers : (2139/20000 : ℝ)^4455 ≤ (5975408387572541/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2139 : ℕ)^4455*100000000000000000000^1024 ≤ 5975408387572541^1024*20000^4455 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2139 20000 5975408387572541 100000000000000000000 4455 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2139/20000 : ℝ)) (X := (5975408387572541/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4455 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7787/50000 : ℝ) ^ (4455/1024 : ℝ) ≤ (30652615535291011/100000000000000000000 : ℝ) := by
    have hpowers : (7787/50000 : ℝ)^4455 ≤ (30652615535291011/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7787 : ℕ)^4455*100000000000000000000^1024 ≤ 30652615535291011^1024*50000^4455 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7787 50000 30652615535291011 100000000000000000000 4455 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7787/50000 : ℝ)) (X := (30652615535291011/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4455 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005975408387572541/50000000000000000000 : ℝ) ≤ (10000274681778883/10000000000000000 : ℝ) ^ (4455/1024 : ℝ) := by
    have hpowers : (50005975408387572541/50000000000000000000 : ℝ)^1024 ≤ (10000274681778883/10000000000000000 : ℝ)^4455 := by
      have hnat : (50005975408387572541 : ℕ)^1024*10000000000000000^4455 ≤ 10000274681778883^4455*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005975408387572541 50000000000000000000 10000274681778883 10000000000000000 1024 4455 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000274681778883/10000000000000000 : ℝ)) (X := (50005975408387572541/50000000000000000000 : ℝ)) (by norm_num) 4455 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (1563072312873794743/1562500000000000000 : ℝ) ≤ (5000420895706691/5000000000000000 : ℝ) ^ (4455/1024 : ℝ) := by
    have hpowers : (1563072312873794743/1562500000000000000 : ℝ)^1024 ≤ (5000420895706691/5000000000000000 : ℝ)^4455 := by
      have hnat : (1563072312873794743 : ℕ)^1024*5000000000000000^4455 ≤ 5000420895706691^4455*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1563072312873794743 1562500000000000000 5000420895706691 5000000000000000 1024 4455 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000420895706691/5000000000000000 : ℝ)) (X := (1563072312873794743/1562500000000000000 : ℝ)) (by norm_num) 4455 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50030652615535291011/50000000000000000000 : ℝ) ≤ (10001408901047881/10000000000000000 : ℝ) ^ (4455/1024 : ℝ) := by
    have hpowers : (50030652615535291011/50000000000000000000 : ℝ)^1024 ≤ (10001408901047881/10000000000000000 : ℝ)^4455 := by
      have hnat : (50030652615535291011 : ℕ)^1024*10000000000000000^4455 ≤ 10001408901047881^4455*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030652615535291011 50000000000000000000 10001408901047881 10000000000000000 1024 4455 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001408901047881/10000000000000000 : ℝ)) (X := (50030652615535291011/50000000000000000000 : ℝ)) (by norm_num) 4455 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5975408387572541/100000000000000000000 : ℝ) ≤ ((48779209697317236547/48790000000000000000 : ℝ)+2*(567109634499/487900000000000 : ℝ)*(2139/20000 : ℝ))^(4455/1024 : ℝ) := by
    rw [show (48779209697317236547/48790000000000000000 : ℝ)+2*(567109634499/487900000000000 : ℝ)*(2139/20000 : ℝ)=(10000274681778883/10000000000000000 : ℝ) by norm_num, show 1+2*(5975408387572541/100000000000000000000 : ℝ)=(50005975408387572541/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30652615535291011/100000000000000000000 : ℝ)+(5975408387572541/100000000000000000000 : ℝ) ≤ ((48779209697317236547/48790000000000000000 : ℝ)+(567109634499/487900000000000 : ℝ)*((7787/50000 : ℝ)+(2139/20000 : ℝ)))^(4455/1024 : ℝ) := by
    rw [show (48779209697317236547/48790000000000000000 : ℝ)+(567109634499/487900000000000 : ℝ)*((7787/50000 : ℝ)+(2139/20000 : ℝ))=(5000420895706691/5000000000000000 : ℝ) by norm_num, show 1+(30652615535291011/100000000000000000000 : ℝ)+(5975408387572541/100000000000000000000 : ℝ)=(1563072312873794743/1562500000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30652615535291011/100000000000000000000 : ℝ) ≤ ((48779209697317236547/48790000000000000000 : ℝ)+2*(567109634499/487900000000000 : ℝ)*(7787/50000 : ℝ))^(4455/1024 : ℝ) := by
    rw [show (48779209697317236547/48790000000000000000 : ℝ)+2*(567109634499/487900000000000 : ℝ)*(7787/50000 : ℝ)=(10001408901047881/10000000000000000 : ℝ) by norm_num, show 1+2*(30652615535291011/100000000000000000000 : ℝ)=(50030652615535291011/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (48779209697317236547/48790000000000000000 : ℝ)*(X 1 0+X 2 0)+(567109634499/487900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4455/1024 : ℝ)) (lo := (2139/20000 : ℝ)) (hi := (7787/50000 : ℝ)) (c := (48779209697317236547/48790000000000000000 : ℝ)) (alpha := (567109634499/487900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (48779209697317236547/48790000000000000000 : ℝ)*(X 0 1+X 2 1)+(567109634499/487900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4455/1024 : ℝ)) (lo := (2139/20000 : ℝ)) (hi := (7787/50000 : ℝ)) (c := (48779209697317236547/48790000000000000000 : ℝ)) (alpha := (567109634499/487900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (48779209697317236547/48790000000000000000 : ℝ)*(X 0 2+X 1 2)+(567109634499/487900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4455/1024 : ℝ)) (lo := (2139/20000 : ℝ)) (hi := (7787/50000 : ℝ)) (c := (48779209697317236547/48790000000000000000 : ℝ)) (alpha := (567109634499/487900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-958125377/5000000000 : ℝ)*X 0 0+(2719032531/5000000000 : ℝ)*X 0 1+(2607638313/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((535347357/1000000000 : ℝ)*X 1 0+(-2030443353/10000000000 : ℝ)*X 1 1+(2607638773/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676737043/5000000000 : ℝ)*X 2 0+(5215276731/10000000000 : ℝ)*X 2 1+(-406088749/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4284851267/10000000000 : ℝ)*X 0 0+(2022072279/5000000000 : ℝ)*X 0 1+(2268982211/5000000000 : ℝ)*X 0 2+(4284851267/10000000000 : ℝ)*X 1 0+(2022072279/5000000000 : ℝ)*X 1 1+(2268982211/5000000000 : ℝ)*X 1 2+(4284851267/10000000000 : ℝ)*X 2 0+(2022072279/5000000000 : ℝ)*X 2 1+(2268982211/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1916281359/10000000000 : ℝ)*X 0 0+(5216422851/10000000000 : ℝ)*X 0 1+(1087382111/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5295289791/10000000000 : ℝ)*X 1 0+(-904404931/5000000000 : ℝ)*X 1 1+(1359227633/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5295289761/10000000000 : ℝ)*X 2 0+(2718455273/5000000000 : ℝ)*X 2 1+(-1808809883/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2142459547/5000000000 : ℝ)*X 0 0+(4535425021/10000000000 : ℝ)*X 0 1+(2023351637/5000000000 : ℝ)*X 0 2+(2142459547/5000000000 : ℝ)*X 1 0+(4535425021/10000000000 : ℝ)*X 1 1+(2023351637/5000000000 : ℝ)*X 1 2+(2142459547/5000000000 : ℝ)*X 2 0+(4535425021/10000000000 : ℝ)*X 2 1+(2023351637/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (309773834738082898390099587/71750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (296868647/50000000000000 : ℝ)*(base19) + (15223841/1562500000000 : ℝ)*(base23) + (27864607/100000000000000 : ℝ)*(lower2) + (723609/195312500000 : ℝ)*(upper3) + (197639/500000000000 : ℝ)*(upper5) + (1628409722110727/50000000000000 : ℝ)*(major0) + (1628409722110727/50000000000000 : ℝ)*(major1) + (1628409722110727/50000000000000 : ℝ)*(major2) + (561073062728533/12500000000000 : ℝ)*(sp0) + (140268707557879/3125000000000 : ℝ)*(sp1) + (2244299130631799/50000000000000 : ℝ)*(sp2) + (506258081450391/25000000000000 : ℝ)*(sp3) + (14733761157/100000000000000 : ℝ)*(sp4) + (3591569199/50000000000000 : ℝ)*(sp7) + (1012519754469981/50000000000000 : ℝ)*(f.failure) + (2244299617794711/50000000000000 : ℝ)*(f.sum) + (637539086949/24395000000000000000000000000 : ℝ)*base66 + (4412742785840705667/348500000000000000000000000000000 : ℝ)*base67 + (6085896717561705667/348500000000000000000000000000000 : ℝ)*base69 + (1954892896463205667/348500000000000000000000000000000 : ℝ)*base71 + (622536479839/1524687500000000000000000000 : ℝ)*base74 + (2544074319145205667/348500000000000000000000000000000 : ℝ)*base75 + (3205358129365205667/348500000000000000000000000000000 : ℝ)*base77 + (3306873119535205667/348500000000000000000000000000000 : ℝ)*base79 + (5575352300537/3049375000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (11320397/1250000000000000000000 : ℝ)*base90 + (11320397/1250000000000000000000 : ℝ)*base92 + (11320397/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (233460848842845664742229/24395000000000000000000000000 : ℝ) := by norm_num
    linear_combination (806587367/50000000000000 : ℝ)*(base19) + (1710226261/100000000000000 : ℝ)*(base23) + (1511763/781250000000 : ℝ)*(upper3) + (59270997/100000000000000 : ℝ)*(lower4) + (101908193/50000000000000 : ℝ)*(upper5) + (822694172313343/25000000000000 : ℝ)*(major0) + (822694172313343/25000000000000 : ℝ)*(major1) + (822694172313343/25000000000000 : ℝ)*(major2) + (12005635791/50000000000000 : ℝ)*(sp1) + (24995296221/100000000000000 : ℝ)*(sp2) + (4535399465495369/100000000000000 : ℝ)*(sp4) + (1133843460262263/25000000000000 : ℝ)*(sp5) + (2267686379986443/50000000000000 : ℝ)*(sp6) + (1023076797005207/50000000000000 : ℝ)*(sp7) + (1023076797005207/50000000000000 : ℝ)*(f.failure) + (4535399465495369/100000000000000 : ℝ)*(f.sum) + (23187252814853/24395000000000000000000000000 : ℝ)*base65 + (457989885354386197/174250000000000000000000000000000 : ℝ)*base68 + (288519851134113803/174250000000000000000000000000000 : ℝ)*base69 + (446753387173136197/174250000000000000000000000000000 : ℝ)*base72 + (14263225661963/6098750000000000000000000000 : ℝ)*base74 + (2511916109189863803/174250000000000000000000000000000 : ℝ)*base75 + (115075071361863803/174250000000000000000000000000000 : ℝ)*base77 + (24928501538386197/174250000000000000000000000000000 : ℝ)*base80 + (27933860395307/24395000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (18135641/1250000000000000000000 : ℝ)*base89 + (18135641/1250000000000000000000 : ℝ)*base91 + (18135641/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1480_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40206863/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7787/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2139/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5387/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1480_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1480_s5_0 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1916335237/10000000000 : ℝ)*x 0 + (2718752229/5000000000 : ℝ)*x 1 + (5215781581/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1916335237/10000000000 : ℝ)^4457 ≤ (1463376572777/12500000000000 : ℝ)^3433 := by
    have hnat : (1916335237 : ℕ)^4457*12500000000000^3433 ≤ 1463376572777^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1916335237 10000000000 1463376572777 12500000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2718752229/5000000000 : ℝ)^4457 ≤ (45339242465261/100000000000000 : ℝ)^3433 := by
    have hnat : (2718752229 : ℕ)^4457*100000000000000^3433 ≤ 45339242465261^3433*5000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718752229 5000000000 45339242465261 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215781581/10000000000 : ℝ)^4457 ≤ (42953744937651/100000000000000 : ℝ)^3433 := by
    have hnat : (5215781581 : ℕ)^4457*100000000000000^3433 ≤ 42953744937651^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215781581 10000000000 42953744937651 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1916335237/10000000000 : ℝ), (2718752229/5000000000 : ℝ), (5215781581/10000000000 : ℝ)] ![(1463376572777/12500000000000 : ℝ), (45339242465261/100000000000000 : ℝ), (42953744937651/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1916335237/10000000000 : ℝ)|^4457 ≤ (1463376572777/12500000000000 : ℝ)^3433
        have hw : |(-1916335237/10000000000 : ℝ)|=(1916335237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2718752229/5000000000 : ℝ)|^4457 ≤ (45339242465261/100000000000000 : ℝ)^3433
        have hw : |(2718752229/5000000000 : ℝ)|=(2718752229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215781581/10000000000 : ℝ)|^4457 ≤ (42953744937651/100000000000000 : ℝ)^3433
        have hw : |(5215781581/10000000000 : ℝ)|=(5215781581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1480_s5_1 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070665701/2000000000 : ℝ)*x 0 + (-2029969353/10000000000 : ℝ)*x 1 + (2607890737/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070665701/2000000000 : ℝ)^4457 ≤ (44430116653293/100000000000000 : ℝ)^3433 := by
    have hnat : (1070665701 : ℕ)^4457*100000000000000^3433 ≤ 44430116653293^3433*2000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070665701 2000000000 44430116653293 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2029969353/10000000000 : ℝ)^4457 ≤ (6308069766431/50000000000000 : ℝ)^3433 := by
    have hnat : (2029969353 : ℕ)^4457*50000000000000^3433 ≤ 6308069766431^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2029969353 10000000000 6308069766431 50000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2607890737/5000000000 : ℝ)^4457 ≤ (42953743793629/100000000000000 : ℝ)^3433 := by
    have hnat : (2607890737 : ℕ)^4457*100000000000000^3433 ≤ 42953743793629^3433*5000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607890737 5000000000 42953743793629 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070665701/2000000000 : ℝ), (-2029969353/10000000000 : ℝ), (2607890737/5000000000 : ℝ)] ![(44430116653293/100000000000000 : ℝ), (6308069766431/50000000000000 : ℝ), (42953743793629/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070665701/2000000000 : ℝ)|^4457 ≤ (44430116653293/100000000000000 : ℝ)^3433
        have hw : |(1070665701/2000000000 : ℝ)|=(1070665701/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2029969353/10000000000 : ℝ)|^4457 ≤ (6308069766431/50000000000000 : ℝ)^3433
        have hw : |(-2029969353/10000000000 : ℝ)|=(2029969353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2607890737/5000000000 : ℝ)|^4457 ≤ (42953743793629/100000000000000 : ℝ)^3433
        have hw : |(2607890737/5000000000 : ℝ)|=(2607890737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1480_s5_2 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (133833219/250000000 : ℝ)*x 0 + (651972661/1250000000 : ℝ)*x 1 + (-101498463/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133833219/250000000 : ℝ)^4457 ≤ (888602388019/2000000000000 : ℝ)^3433 := by
    have hnat : (133833219 : ℕ)^4457*2000000000000^3433 ≤ 888602388019^3433*250000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133833219 250000000 888602388019 2000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (651972661/1250000000 : ℝ)^4457 ≤ (10738435451239/25000000000000 : ℝ)^3433 := by
    have hnat : (651972661 : ℕ)^4457*25000000000000^3433 ≤ 10738435451239^3433*1250000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      651972661 1250000000 10738435451239 25000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (101498463/500000000 : ℝ)^4457 ≤ (12616138782469/100000000000000 : ℝ)^3433 := by
    have hnat : (101498463 : ℕ)^4457*100000000000000^3433 ≤ 12616138782469^3433*500000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      101498463 500000000 12616138782469 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(133833219/250000000 : ℝ), (651972661/1250000000 : ℝ), (-101498463/500000000 : ℝ)] ![(888602388019/2000000000000 : ℝ), (10738435451239/25000000000000 : ℝ), (12616138782469/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(133833219/250000000 : ℝ)|^4457 ≤ (888602388019/2000000000000 : ℝ)^3433
        have hw : |(133833219/250000000 : ℝ)|=(133833219/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(651972661/1250000000 : ℝ)|^4457 ≤ (10738435451239/25000000000000 : ℝ)^3433
        have hw : |(651972661/1250000000 : ℝ)|=(651972661/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-101498463/500000000 : ℝ)|^4457 ≤ (12616138782469/100000000000000 : ℝ)^3433
        have hw : |(-101498463/500000000 : ℝ)|=(101498463/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1480_s5_3 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (171396157/400000000 : ℝ)*x 0 + (161812713/400000000 : ℝ)*x 1 + (4536778929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (171396157/400000000 : ℝ)^4457 ≤ (6655580827449/20000000000000 : ℝ)^3433 := by
    have hnat : (171396157 : ℕ)^4457*20000000000000^3433 ≤ 6655580827449^3433*400000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171396157 400000000 6655580827449 20000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (161812713/400000000 : ℝ)^4457 ≤ (30882605878407/100000000000000 : ℝ)^3433 := by
    have hnat : (161812713 : ℕ)^4457*100000000000000^3433 ≤ 30882605878407^3433*400000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161812713 400000000 30882605878407 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4536778929/10000000000 : ℝ)^4457 ≤ (17919744981893/50000000000000 : ℝ)^3433 := by
    have hnat : (4536778929 : ℕ)^4457*50000000000000^3433 ≤ 17919744981893^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4536778929 10000000000 17919744981893 50000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(171396157/400000000 : ℝ), (161812713/400000000 : ℝ), (4536778929/10000000000 : ℝ)] ![(6655580827449/20000000000000 : ℝ), (30882605878407/100000000000000 : ℝ), (17919744981893/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(171396157/400000000 : ℝ)|^4457 ≤ (6655580827449/20000000000000 : ℝ)^3433
        have hw : |(171396157/400000000 : ℝ)|=(171396157/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(161812713/400000000 : ℝ)|^4457 ≤ (30882605878407/100000000000000 : ℝ)^3433
        have hw : |(161812713/400000000 : ℝ)|=(161812713/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4536778929/10000000000 : ℝ)|^4457 ≤ (17919744981893/50000000000000 : ℝ)^3433
        have hw : |(4536778929/10000000000 : ℝ)|=(4536778929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1480_s5_4 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-191636573/1000000000 : ℝ)*x 0 + (5216916223/10000000000 : ℝ)*x 1 + (2718180703/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (191636573/1000000000 : ℝ)^4457 ≤ (5853627215697/50000000000000 : ℝ)^3433 := by
    have hnat : (191636573 : ℕ)^4457*50000000000000^3433 ≤ 5853627215697^3433*1000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      191636573 1000000000 5853627215697 50000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216916223/10000000000 : ℝ)^4457 ≤ (10741469171639/25000000000000 : ℝ)^3433 := by
    have hnat : (5216916223 : ℕ)^4457*25000000000000^3433 ≤ 10741469171639^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216916223 10000000000 10741469171639 25000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2718180703/5000000000 : ℝ)^4457 ≤ (45326868872019/100000000000000 : ℝ)^3433 := by
    have hnat : (2718180703 : ℕ)^4457*100000000000000^3433 ≤ 45326868872019^3433*5000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718180703 5000000000 45326868872019 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-191636573/1000000000 : ℝ), (5216916223/10000000000 : ℝ), (2718180703/5000000000 : ℝ)] ![(5853627215697/50000000000000 : ℝ), (10741469171639/25000000000000 : ℝ), (45326868872019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-191636573/1000000000 : ℝ)|^4457 ≤ (5853627215697/50000000000000 : ℝ)^3433
        have hw : |(-191636573/1000000000 : ℝ)|=(191636573/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216916223/10000000000 : ℝ)|^4457 ≤ (10741469171639/25000000000000 : ℝ)^3433
        have hw : |(5216916223/10000000000 : ℝ)|=(5216916223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2718180703/5000000000 : ℝ)|^4457 ≤ (45326868872019/100000000000000 : ℝ)^3433
        have hw : |(2718180703/5000000000 : ℝ)|=(2718180703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1480_s5_5 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (165481959/312500000 : ℝ)*x 0 + (-361877861/2000000000 : ℝ)*x 1 + (679545169/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165481959/312500000 : ℝ)^4457 ≤ (21903591624799/50000000000000 : ℝ)^3433 := by
    have hnat : (165481959 : ℕ)^4457*50000000000000^3433 ≤ 21903591624799^3433*312500000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165481959 312500000 21903591624799 50000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (361877861/2000000000 : ℝ)^4457 ≤ (10865948444031/100000000000000 : ℝ)^3433 := by
    have hnat : (361877861 : ℕ)^4457*100000000000000^3433 ≤ 10865948444031^3433*2000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      361877861 2000000000 10865948444031 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (679545169/1250000000 : ℝ)^4457 ≤ (9065373657497/20000000000000 : ℝ)^3433 := by
    have hnat : (679545169 : ℕ)^4457*20000000000000^3433 ≤ 9065373657497^3433*1250000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      679545169 1250000000 9065373657497 20000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165481959/312500000 : ℝ), (-361877861/2000000000 : ℝ), (679545169/1250000000 : ℝ)] ![(21903591624799/50000000000000 : ℝ), (10865948444031/100000000000000 : ℝ), (9065373657497/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165481959/312500000 : ℝ)|^4457 ≤ (21903591624799/50000000000000 : ℝ)^3433
        have hw : |(165481959/312500000 : ℝ)|=(165481959/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-361877861/2000000000 : ℝ)|^4457 ≤ (10865948444031/100000000000000 : ℝ)^3433
        have hw : |(-361877861/2000000000 : ℝ)|=(361877861/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(679545169/1250000000 : ℝ)|^4457 ≤ (9065373657497/20000000000000 : ℝ)^3433
        have hw : |(679545169/1250000000 : ℝ)|=(679545169/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1480_s5_6 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295422621/10000000000 : ℝ)*x 0 + (5436361381/10000000000 : ℝ)*x 1 + (-904694679/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295422621/10000000000 : ℝ)^4457 ≤ (43807182530003/100000000000000 : ℝ)^3433 := by
    have hnat : (5295422621 : ℕ)^4457*100000000000000^3433 ≤ 43807182530003^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295422621 10000000000 43807182530003 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5436361381/10000000000 : ℝ)^4457 ≤ (22663434300701/50000000000000 : ℝ)^3433 := by
    have hnat : (5436361381 : ℕ)^4457*50000000000000^3433 ≤ 22663434300701^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436361381 10000000000 22663434300701 50000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (904694679/5000000000 : ℝ)^4457 ≤ (43463795429/400000000000 : ℝ)^3433 := by
    have hnat : (904694679 : ℕ)^4457*400000000000^3433 ≤ 43463795429^3433*5000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      904694679 5000000000 43463795429 400000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295422621/10000000000 : ℝ), (5436361381/10000000000 : ℝ), (-904694679/5000000000 : ℝ)] ![(43807182530003/100000000000000 : ℝ), (22663434300701/50000000000000 : ℝ), (43463795429/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295422621/10000000000 : ℝ)|^4457 ≤ (43807182530003/100000000000000 : ℝ)^3433
        have hw : |(5295422621/10000000000 : ℝ)|=(5295422621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5436361381/10000000000 : ℝ)|^4457 ≤ (22663434300701/50000000000000 : ℝ)^3433
        have hw : |(5436361381/10000000000 : ℝ)|=(5436361381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-904694679/5000000000 : ℝ)|^4457 ≤ (43463795429/400000000000 : ℝ)^3433
        have hw : |(-904694679/5000000000 : ℝ)|=(904694679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1480_s5_7 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1071242771/2500000000 : ℝ)*x 0 + (4534263193/10000000000 : ℝ)*x 1 + (809570463/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071242771/2500000000 : ℝ)^4457 ≤ (33278581293577/100000000000000 : ℝ)^3433 := by
    have hnat : (1071242771 : ℕ)^4457*100000000000000^3433 ≤ 33278581293577^3433*2500000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071242771 2500000000 33278581293577 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4534263193/10000000000 : ℝ)^4457 ≤ (35813690411139/100000000000000 : ℝ)^3433 := by
    have hnat : (4534263193 : ℕ)^4457*100000000000000^3433 ≤ 35813690411139^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4534263193 10000000000 35813690411139 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (809570463/2000000000 : ℝ)^4457 ≤ (30907728287093/100000000000000 : ℝ)^3433 := by
    have hnat : (809570463 : ℕ)^4457*100000000000000^3433 ≤ 30907728287093^3433*2000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      809570463 2000000000 30907728287093 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071242771/2500000000 : ℝ), (4534263193/10000000000 : ℝ), (809570463/2000000000 : ℝ)] ![(33278581293577/100000000000000 : ℝ), (35813690411139/100000000000000 : ℝ), (30907728287093/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071242771/2500000000 : ℝ)|^4457 ≤ (33278581293577/100000000000000 : ℝ)^3433
        have hw : |(1071242771/2500000000 : ℝ)|=(1071242771/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4534263193/10000000000 : ℝ)|^4457 ≤ (35813690411139/100000000000000 : ℝ)^3433
        have hw : |(4534263193/10000000000 : ℝ)|=(4534263193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(809570463/2000000000 : ℝ)|^4457 ≤ (30907728287093/100000000000000 : ℝ)^3433
        have hw : |(809570463/2000000000 : ℝ)|=(809570463/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1480_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40206863/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5387/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2157/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15477/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15489/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5387/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15489/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5387/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15489/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5387/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15489/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5387/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15489/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5387/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15489/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5387/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5387/50000 : ℝ) ^ (4455/1024 : ℝ) ≤ (1542456293333669/25000000000000000000 : ℝ) := by
    have hpowers : (5387/50000 : ℝ)^4455 ≤ (1542456293333669/25000000000000000000 : ℝ)^1024 := by
      have hnat : (5387 : ℕ)^4455*25000000000000000000^1024 ≤ 1542456293333669^1024*50000^4455 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5387 50000 1542456293333669 25000000000000000000 4455 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5387/50000 : ℝ)) (X := (1542456293333669/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4455 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15489/100000 : ℝ) ^ (4455/1024 : ℝ) ≤ (14965702600635417/50000000000000000000 : ℝ) := by
    have hpowers : (15489/100000 : ℝ)^4455 ≤ (14965702600635417/50000000000000000000 : ℝ)^1024 := by
      have hnat : (15489 : ℕ)^4455*50000000000000000000^1024 ≤ 14965702600635417^1024*100000^4455 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15489 100000 14965702600635417 50000000000000000000 4455 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15489/100000 : ℝ)) (X := (14965702600635417/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4455 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501542456293333669/12500000000000000000 : ℝ) ≤ (10000283618441923/10000000000000000 : ℝ) ^ (4455/1024 : ℝ) := by
    have hpowers : (12501542456293333669/12500000000000000000 : ℝ)^1024 ≤ (10000283618441923/10000000000000000 : ℝ)^4455 := by
      have hnat : (12501542456293333669 : ℕ)^1024*10000000000000000^4455 ≤ 10000283618441923^4455*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501542456293333669 12500000000000000000 10000283618441923 10000000000000000 1024 4455 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000283618441923/10000000000000000 : ℝ)) (X := (12501542456293333669/12500000000000000000 : ℝ)) (by norm_num) 4455 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10003610123037460551/10000000000000000000 : ℝ) ≤ (2000165937247583/2000000000000000 : ℝ) ^ (4455/1024 : ℝ) := by
    have hpowers : (10003610123037460551/10000000000000000000 : ℝ)^1024 ≤ (2000165937247583/2000000000000000 : ℝ)^4455 := by
      have hnat : (10003610123037460551 : ℕ)^1024*2000000000000000^4455 ≤ 2000165937247583^4455*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10003610123037460551 10000000000000000000 2000165937247583 2000000000000000 1024 4455 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000165937247583/2000000000000000 : ℝ)) (X := (10003610123037460551/10000000000000000000 : ℝ)) (by norm_num) 4455 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25014965702600635417/25000000000000000000 : ℝ) ≤ (10001375754033907/10000000000000000 : ℝ) ^ (4455/1024 : ℝ) := by
    have hpowers : (25014965702600635417/25000000000000000000 : ℝ)^1024 ≤ (10001375754033907/10000000000000000 : ℝ)^4455 := by
      have hnat : (25014965702600635417 : ℕ)^1024*10000000000000000^4455 ≤ 10001375754033907^4455*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014965702600635417 25000000000000000000 10001375754033907 10000000000000000 1024 4455 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001375754033907/10000000000000000 : ℝ)) (X := (25014965702600635417/25000000000000000000 : ℝ)) (by norm_num) 4455 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1542456293333669/25000000000000000000 : ℝ) ≤ ((47139570592085631329/47150000000000000000 : ℝ)+2*(68258474499/58937500000000 : ℝ)*(5387/50000 : ℝ))^(4455/1024 : ℝ) := by
    rw [show (47139570592085631329/47150000000000000000 : ℝ)+2*(68258474499/58937500000000 : ℝ)*(5387/50000 : ℝ)=(10000283618441923/10000000000000000 : ℝ) by norm_num, show 1+2*(1542456293333669/25000000000000000000 : ℝ)=(12501542456293333669/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14965702600635417/50000000000000000000 : ℝ)+(1542456293333669/25000000000000000000 : ℝ) ≤ ((47139570592085631329/47150000000000000000 : ℝ)+(68258474499/58937500000000 : ℝ)*((15489/100000 : ℝ)+(5387/50000 : ℝ)))^(4455/1024 : ℝ) := by
    rw [show (47139570592085631329/47150000000000000000 : ℝ)+(68258474499/58937500000000 : ℝ)*((15489/100000 : ℝ)+(5387/50000 : ℝ))=(2000165937247583/2000000000000000 : ℝ) by norm_num, show 1+(14965702600635417/50000000000000000000 : ℝ)+(1542456293333669/25000000000000000000 : ℝ)=(10003610123037460551/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14965702600635417/50000000000000000000 : ℝ) ≤ ((47139570592085631329/47150000000000000000 : ℝ)+2*(68258474499/58937500000000 : ℝ)*(15489/100000 : ℝ))^(4455/1024 : ℝ) := by
    rw [show (47139570592085631329/47150000000000000000 : ℝ)+2*(68258474499/58937500000000 : ℝ)*(15489/100000 : ℝ)=(10001375754033907/10000000000000000 : ℝ) by norm_num, show 1+2*(14965702600635417/50000000000000000000 : ℝ)=(25014965702600635417/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (47139570592085631329/47150000000000000000 : ℝ)*(X 1 0+X 2 0)+(68258474499/58937500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4455/1024 : ℝ)) (lo := (5387/50000 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (47139570592085631329/47150000000000000000 : ℝ)) (alpha := (68258474499/58937500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (47139570592085631329/47150000000000000000 : ℝ)*(X 0 1+X 2 1)+(68258474499/58937500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4455/1024 : ℝ)) (lo := (5387/50000 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (47139570592085631329/47150000000000000000 : ℝ)) (alpha := (68258474499/58937500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (47139570592085631329/47150000000000000000 : ℝ)*(X 0 2+X 1 2)+(68258474499/58937500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4455/1024 : ℝ)) (lo := (5387/50000 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (47139570592085631329/47150000000000000000 : ℝ)) (alpha := (68258474499/58937500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1916335237/10000000000 : ℝ)*X 0 0+(2718752229/5000000000 : ℝ)*X 0 1+(5215781581/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1070665701/2000000000 : ℝ)*X 1 0+(-2029969353/10000000000 : ℝ)*X 1 1+(2607890737/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((133833219/250000000 : ℝ)*X 2 0+(651972661/1250000000 : ℝ)*X 2 1+(-101498463/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((171396157/400000000 : ℝ)*X 0 0+(161812713/400000000 : ℝ)*X 0 1+(4536778929/10000000000 : ℝ)*X 0 2+(171396157/400000000 : ℝ)*X 1 0+(161812713/400000000 : ℝ)*X 1 1+(4536778929/10000000000 : ℝ)*X 1 2+(171396157/400000000 : ℝ)*X 2 0+(161812713/400000000 : ℝ)*X 2 1+(4536778929/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-191636573/1000000000 : ℝ)*X 0 0+(5216916223/10000000000 : ℝ)*X 0 1+(2718180703/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((165481959/312500000 : ℝ)*X 1 0+(-361877861/2000000000 : ℝ)*X 1 1+(679545169/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5295422621/10000000000 : ℝ)*X 2 0+(5436361381/10000000000 : ℝ)*X 2 1+(-904694679/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1071242771/2500000000 : ℝ)*X 0 0+(4534263193/10000000000 : ℝ)*X 0 1+(809570463/2000000000 : ℝ)*X 0 2+(1071242771/2500000000 : ℝ)*X 1 0+(4534263193/10000000000 : ℝ)*X 1 1+(809570463/2000000000 : ℝ)*X 1 2+(1071242771/2500000000 : ℝ)*X 2 0+(4534263193/10000000000 : ℝ)*X 2 1+(809570463/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (294116008126229419369553457/117875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (367744147/100000000000000 : ℝ)*(base19) + (24390917/6250000000000 : ℝ)*(base23) + (102957823/100000000000000 : ℝ)*(lower2) + (88967367/100000000000000 : ℝ)*(upper3) + (14122357/20000000000000 : ℝ)*(upper5) + (163622280996937/5000000000000 : ℝ)*(major0) + (163622280996937/5000000000000 : ℝ)*(major1) + (163622280996937/5000000000000 : ℝ)*(major2) + (4510133780579101/100000000000000 : ℝ)*(sp0) + (563766895975173/12500000000000 : ℝ)*(sp1) + (4510135145290859/100000000000000 : ℝ)*(sp2) + (1017375820217497/50000000000000 : ℝ)*(sp3) + (175496643/10000000000000 : ℝ)*(sp4) + (1990362609/50000000000000 : ℝ)*(sp7) + (508688905290053/25000000000000 : ℝ)*(f.failure) + (4510135535545531/100000000000000 : ℝ)*(f.sum) + (20981473129641/4715000000000000000000000000 : ℝ)*base65 + (3510579139563360727/235750000000000000000000000000000 : ℝ)*base68 + (6263517958352110727/235750000000000000000000000000000 : ℝ)*base70 + (2559682318470860727/235750000000000000000000000000000 : ℝ)*base72 + (3144526187259/1178750000000000000000000000 : ℝ)*base73 + (6403039701343360727/235750000000000000000000000000000 : ℝ)*base76 + (1829836605110860727/235750000000000000000000000000000 : ℝ)*base78 + (3202482237086360727/235750000000000000000000000000000 : ℝ)*base80 + (7710985912131/1178750000000000000000000000 : ℝ)*base82 + (11233739/625000000000000000000 : ℝ)*base89 + (11233739/625000000000000000000 : ℝ)*base91 + (11233739/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (761532062719619310232675113/117875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15993037/1562500000000 : ℝ)*(base19) + (518067017/50000000000000 : ℝ)*(base23) + (142123489/100000000000000 : ℝ)*(upper3) + (10180003/25000000000000 : ℝ)*(lower4) + (33055373/20000000000000 : ℝ)*(upper5) + (165320522695701/5000000000000 : ℝ)*(major0) + (165320522695701/5000000000000 : ℝ)*(major1) + (165320522695701/5000000000000 : ℝ)*(major2) + (3404460907/25000000000000 : ℝ)*(sp1) + (101630283/781250000000 : ℝ)*(sp2) + (911389253512127/20000000000000 : ℝ)*(sp4) + (2278465813081319/50000000000000 : ℝ)*(sp5) + (4556932222750377/100000000000000 : ℝ)*(sp6) + (2055874424917221/100000000000000 : ℝ)*(sp7) + (2055874424917221/100000000000000 : ℝ)*(f.failure) + (911389253512127/20000000000000 : ℝ)*(f.sum) + (1700737814721/2357500000000000000000000000 : ℝ)*base66 + (1255746194245083371/235750000000000000000000000000000 : ℝ)*base68 + (503619099365333371/235750000000000000000000000000000 : ℝ)*base70 + (1427311261812416629/235750000000000000000000000000000 : ℝ)*base71 + (20424645370417/4715000000000000000000000000 : ℝ)*base74 + (1344174916626166629/235750000000000000000000000000000 : ℝ)*base75 + (1752331942702666629/235750000000000000000000000000000 : ℝ)*base77 + (2387061498756916629/235750000000000000000000000000000 : ℝ)*base79 + (10914617816867/4715000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (8912277/2500000000000000000000 : ℝ)*base90 + (8912277/2500000000000000000000 : ℝ)*base92 + (8912277/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1480_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40206863/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5387/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2157/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15477/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1480_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1480_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40206863/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16131/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1273/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2157/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15477/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1480_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1480_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1480_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40206863/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16131/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1273/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2157/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15477/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1480_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
