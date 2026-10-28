-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1209_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:06:25.567426+00:00
-- url     : https://prove2.me/submissions/4fe39864-1a86-41af-b308-aef9d8cb2bf9

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
theorem support_rectangle_w1209_box_0 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2010527741/10000000000 : ℝ)*x 0 + (1075066979/2000000000 : ℝ)*x 1 + (2687667333/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2010527741/10000000000 : ℝ)^4201 ≤ (1198823657757/10000000000000 : ℝ)^3177 := by
    have hnat : (2010527741 : ℕ)^4201*10000000000000^3177 ≤ 1198823657757^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2010527741 10000000000 1198823657757 10000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1075066979/2000000000 : ℝ)^4201 ≤ (22002941474313/50000000000000 : ℝ)^3177 := by
    have hnat : (1075066979 : ℕ)^4201*50000000000000^3177 ≤ 22002941474313^3177*2000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075066979 2000000000 22002941474313 50000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2687667333/5000000000 : ℝ)^4201 ≤ (44005880469629/100000000000000 : ℝ)^3177 := by
    have hnat : (2687667333 : ℕ)^4201*100000000000000^3177 ≤ 44005880469629^3177*5000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687667333 5000000000 44005880469629 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2010527741/10000000000 : ℝ), (1075066979/2000000000 : ℝ), (2687667333/5000000000 : ℝ)] ![(1198823657757/10000000000000 : ℝ), (22002941474313/50000000000000 : ℝ), (44005880469629/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2010527741/10000000000 : ℝ)|^4201 ≤ (1198823657757/10000000000000 : ℝ)^3177
        have hw : |(-2010527741/10000000000 : ℝ)|=(2010527741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1075066979/2000000000 : ℝ)|^4201 ≤ (22002941474313/50000000000000 : ℝ)^3177
        have hw : |(1075066979/2000000000 : ℝ)|=(1075066979/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2687667333/5000000000 : ℝ)|^4201 ≤ (44005880469629/100000000000000 : ℝ)^3177
        have hw : |(2687667333/5000000000 : ℝ)|=(2687667333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_box_1 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1059310787/2000000000 : ℝ)*x 0 + (-2117528471/10000000000 : ℝ)*x 1 + (5375334397/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059310787/2000000000 : ℝ)^4201 ≤ (10788768752961/25000000000000 : ℝ)^3177 := by
    have hnat : (1059310787 : ℕ)^4201*25000000000000^3177 ≤ 10788768752961^3177*2000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059310787 2000000000 10788768752961 25000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2117528471/10000000000 : ℝ)^4201 ≤ (64195237069/500000000000 : ℝ)^3177 := by
    have hnat : (2117528471 : ℕ)^4201*500000000000^3177 ≤ 64195237069^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117528471 10000000000 64195237069 500000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5375334397/10000000000 : ℝ)^4201 ≤ (22002938778809/50000000000000 : ℝ)^3177 := by
    have hnat : (5375334397 : ℕ)^4201*50000000000000^3177 ≤ 22002938778809^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375334397 10000000000 22002938778809 50000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1059310787/2000000000 : ℝ), (-2117528471/10000000000 : ℝ), (5375334397/10000000000 : ℝ)] ![(10788768752961/25000000000000 : ℝ), (64195237069/500000000000 : ℝ), (22002938778809/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1059310787/2000000000 : ℝ)|^4201 ≤ (10788768752961/25000000000000 : ℝ)^3177
        have hw : |(1059310787/2000000000 : ℝ)|=(1059310787/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2117528471/10000000000 : ℝ)|^4201 ≤ (64195237069/500000000000 : ℝ)^3177
        have hw : |(-2117528471/10000000000 : ℝ)|=(2117528471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5375334397/10000000000 : ℝ)|^4201 ≤ (22002938778809/50000000000000 : ℝ)^3177
        have hw : |(5375334397/10000000000 : ℝ)|=(5375334397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_box_2 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5296554641/10000000000 : ℝ)*x 0 + (5375334367/10000000000 : ℝ)*x 1 + (-2117527563/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5296554641/10000000000 : ℝ)^4201 ≤ (8631016523647/20000000000000 : ℝ)^3177 := by
    have hnat : (5296554641 : ℕ)^4201*20000000000000^3177 ≤ 8631016523647^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296554641 10000000000 8631016523647 20000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5375334367/10000000000 : ℝ)^4201 ≤ (22002938616429/50000000000000 : ℝ)^3177 := by
    have hnat : (5375334367 : ℕ)^4201*50000000000000^3177 ≤ 22002938616429^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375334367 10000000000 22002938616429 50000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2117527563/10000000000 : ℝ)^4201 ≤ (1283904013391/10000000000000 : ℝ)^3177 := by
    have hnat : (2117527563 : ℕ)^4201*10000000000000^3177 ≤ 1283904013391^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117527563 10000000000 1283904013391 10000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5296554641/10000000000 : ℝ), (5375334367/10000000000 : ℝ), (-2117527563/10000000000 : ℝ)] ![(8631016523647/20000000000000 : ℝ), (22002938616429/50000000000000 : ℝ), (1283904013391/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5296554641/10000000000 : ℝ)|^4201 ≤ (8631016523647/20000000000000 : ℝ)^3177
        have hw : |(5296554641/10000000000 : ℝ)|=(5296554641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5375334367/10000000000 : ℝ)|^4201 ≤ (22002938616429/50000000000000 : ℝ)^3177
        have hw : |(5375334367/10000000000 : ℝ)|=(5375334367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2117527563/10000000000 : ℝ)|^4201 ≤ (1283904013391/10000000000000 : ℝ)^3177
        have hw : |(-2117527563/10000000000 : ℝ)|=(2117527563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_box_3 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (278885687/625000000 : ℝ)*x 0 + (860791667/2000000000 : ℝ)*x 1 + (2151980071/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (278885687/625000000 : ℝ)^4201 ≤ (34402429713739/100000000000000 : ℝ)^3177 := by
    have hnat : (278885687 : ℕ)^4201*100000000000000^3177 ≤ 34402429713739^3177*625000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      278885687 625000000 34402429713739 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (860791667/2000000000 : ℝ)^4201 ≤ (6559755206413/20000000000000 : ℝ)^3177 := by
    have hnat : (860791667 : ℕ)^4201*20000000000000^3177 ≤ 6559755206413^3177*2000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      860791667 2000000000 6559755206413 20000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2151980071/5000000000 : ℝ)^4201 ≤ (2049924640059/6250000000000 : ℝ)^3177 := by
    have hnat : (2151980071 : ℕ)^4201*6250000000000^3177 ≤ 2049924640059^3177*5000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151980071 5000000000 2049924640059 6250000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(278885687/625000000 : ℝ), (860791667/2000000000 : ℝ), (2151980071/5000000000 : ℝ)] ![(34402429713739/100000000000000 : ℝ), (6559755206413/20000000000000 : ℝ), (2049924640059/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(278885687/625000000 : ℝ)|^4201 ≤ (34402429713739/100000000000000 : ℝ)^3177
        have hw : |(278885687/625000000 : ℝ)|=(278885687/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(860791667/2000000000 : ℝ)|^4201 ≤ (6559755206413/20000000000000 : ℝ)^3177
        have hw : |(860791667/2000000000 : ℝ)|=(860791667/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2151980071/5000000000 : ℝ)|^4201 ≤ (2049924640059/6250000000000 : ℝ)^3177
        have hw : |(2151980071/5000000000 : ℝ)|=(2151980071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_box_4 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2261362459/10000000000 : ℝ)*x 0 + (1320484261/2500000000 : ℝ)*x 1 + (2640968547/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2261362459/10000000000 : ℝ)^4201 ≤ (7002335910579/50000000000000 : ℝ)^3177 := by
    have hnat : (2261362459 : ℕ)^4201*50000000000000^3177 ≤ 7002335910579^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2261362459 10000000000 7002335910579 50000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1320484261/2500000000 : ℝ)^4201 ≤ (42997663809373/100000000000000 : ℝ)^3177 := by
    have hnat : (1320484261 : ℕ)^4201*100000000000000^3177 ≤ 42997663809373^3177*2500000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320484261 2500000000 42997663809373 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2640968547/5000000000 : ℝ)^4201 ≤ (4299766434759/10000000000000 : ℝ)^3177 := by
    have hnat : (2640968547 : ℕ)^4201*10000000000000^3177 ≤ 4299766434759^3177*5000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640968547 5000000000 4299766434759 10000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2261362459/10000000000 : ℝ), (1320484261/2500000000 : ℝ), (2640968547/5000000000 : ℝ)] ![(7002335910579/50000000000000 : ℝ), (42997663809373/100000000000000 : ℝ), (4299766434759/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2261362459/10000000000 : ℝ)|^4201 ≤ (7002335910579/50000000000000 : ℝ)^3177
        have hw : |(-2261362459/10000000000 : ℝ)|=(2261362459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1320484261/2500000000 : ℝ)|^4201 ≤ (42997663809373/100000000000000 : ℝ)^3177
        have hw : |(1320484261/2500000000 : ℝ)|=(1320484261/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2640968547/5000000000 : ℝ)|^4201 ≤ (4299766434759/10000000000000 : ℝ)^3177
        have hw : |(2640968547/5000000000 : ℝ)|=(2640968547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_box_5 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1340610273/2500000000 : ℝ)*x 0 + (-430892161/2000000000 : ℝ)*x 1 + (5281936793/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1340610273/2500000000 : ℝ)^4201 ≤ (2193317870613/5000000000000 : ℝ)^3177 := by
    have hnat : (1340610273 : ℕ)^4201*5000000000000^3177 ≤ 2193317870613^3177*2500000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1340610273 2500000000 2193317870613 5000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (430892161/2000000000 : ℝ)^4201 ≤ (65679907339/500000000000 : ℝ)^3177 := by
    have hnat : (430892161 : ℕ)^4201*500000000000^3177 ≤ 65679907339^3177*2000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430892161 2000000000 65679907339 500000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5281936793/10000000000 : ℝ)^4201 ≤ (21498830553763/50000000000000 : ℝ)^3177 := by
    have hnat : (5281936793 : ℕ)^4201*50000000000000^3177 ≤ 21498830553763^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281936793 10000000000 21498830553763 50000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1340610273/2500000000 : ℝ), (-430892161/2000000000 : ℝ), (5281936793/10000000000 : ℝ)] ![(2193317870613/5000000000000 : ℝ), (65679907339/500000000000 : ℝ), (21498830553763/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1340610273/2500000000 : ℝ)|^4201 ≤ (2193317870613/5000000000000 : ℝ)^3177
        have hw : |(1340610273/2500000000 : ℝ)|=(1340610273/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-430892161/2000000000 : ℝ)|^4201 ≤ (65679907339/500000000000 : ℝ)^3177
        have hw : |(-430892161/2000000000 : ℝ)|=(430892161/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5281936793/10000000000 : ℝ)|^4201 ≤ (21498830553763/50000000000000 : ℝ)^3177
        have hw : |(5281936793/10000000000 : ℝ)|=(5281936793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_box_6 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5362440707/10000000000 : ℝ)*x 0 + (2640968611/5000000000 : ℝ)*x 1 + (-2154460749/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362440707/10000000000 : ℝ)^4201 ≤ (43866353247737/100000000000000 : ℝ)^3177 := by
    have hnat : (5362440707 : ℕ)^4201*100000000000000^3177 ≤ 43866353247737^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362440707 10000000000 43866353247737 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2640968611/5000000000 : ℝ)^4201 ≤ (2687354107839/6250000000000 : ℝ)^3177 := by
    have hnat : (2640968611 : ℕ)^4201*6250000000000^3177 ≤ 2687354107839^3177*5000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640968611 5000000000 2687354107839 6250000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2154460749/10000000000 : ℝ)^4201 ≤ (13135981016311/100000000000000 : ℝ)^3177 := by
    have hnat : (2154460749 : ℕ)^4201*100000000000000^3177 ≤ 13135981016311^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2154460749 10000000000 13135981016311 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362440707/10000000000 : ℝ), (2640968611/5000000000 : ℝ), (-2154460749/10000000000 : ℝ)] ![(43866353247737/100000000000000 : ℝ), (2687354107839/6250000000000 : ℝ), (13135981016311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362440707/10000000000 : ℝ)|^4201 ≤ (43866353247737/100000000000000 : ℝ)^3177
        have hw : |(5362440707/10000000000 : ℝ)|=(5362440707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2640968611/5000000000 : ℝ)|^4201 ≤ (2687354107839/6250000000000 : ℝ)^3177
        have hw : |(2640968611/5000000000 : ℝ)|=(2640968611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2154460749/10000000000 : ℝ)|^4201 ≤ (13135981016311/100000000000000 : ℝ)^3177
        have hw : |(-2154460749/10000000000 : ℝ)|=(2154460749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_box_7 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (265505091/625000000 : ℝ)*x 0 + (4410983707/10000000000 : ℝ)*x 1 + (4410983627/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265505091/625000000 : ℝ)^4201 ≤ (16118447164747/50000000000000 : ℝ)^3177 := by
    have hnat : (265505091 : ℕ)^4201*50000000000000^3177 ≤ 16118447164747^3177*625000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265505091 625000000 16118447164747 50000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4410983707/10000000000 : ℝ)^4201 ≤ (8470388308419/25000000000000 : ℝ)^3177 := by
    have hnat : (4410983707 : ℕ)^4201*25000000000000^3177 ≤ 8470388308419^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4410983707 10000000000 8470388308419 25000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4410983627/10000000000 : ℝ)^4201 ≤ (26469962829/78125000000 : ℝ)^3177 := by
    have hnat : (4410983627 : ℕ)^4201*78125000000^3177 ≤ 26469962829^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4410983627 10000000000 26469962829 78125000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265505091/625000000 : ℝ), (4410983707/10000000000 : ℝ), (4410983627/10000000000 : ℝ)] ![(16118447164747/50000000000000 : ℝ), (8470388308419/25000000000000 : ℝ), (26469962829/78125000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265505091/625000000 : ℝ)|^4201 ≤ (16118447164747/50000000000000 : ℝ)^3177
        have hw : |(265505091/625000000 : ℝ)|=(265505091/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4410983707/10000000000 : ℝ)|^4201 ≤ (8470388308419/25000000000000 : ℝ)^3177
        have hw : |(4410983707/10000000000 : ℝ)|=(4410983707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4410983627/10000000000 : ℝ)|^4201 ≤ (26469962829/78125000000 : ℝ)^3177
        have hw : |(4410983627/10000000000 : ℝ)|=(4410983627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_box_8 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-220883543/1000000000 : ℝ)*x 0 + (2609145721/5000000000 : ℝ)*x 1 + (5384946823/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (220883543/1000000000 : ℝ)^4201 ≤ (6788069727097/50000000000000 : ℝ)^3177 := by
    have hnat : (220883543 : ℕ)^4201*50000000000000^3177 ≤ 6788069727097^3177*1000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220883543 1000000000 6788069727097 50000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609145721/5000000000 : ℝ)^4201 ≤ (42313895427997/100000000000000 : ℝ)^3177 := by
    have hnat : (2609145721 : ℕ)^4201*100000000000000^3177 ≤ 42313895427997^3177*5000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609145721 5000000000 42313895427997 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5384946823/10000000000 : ℝ)^4201 ≤ (44109965102927/100000000000000 : ℝ)^3177 := by
    have hnat : (5384946823 : ℕ)^4201*100000000000000^3177 ≤ 44109965102927^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384946823 10000000000 44109965102927 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-220883543/1000000000 : ℝ), (2609145721/5000000000 : ℝ), (5384946823/10000000000 : ℝ)] ![(6788069727097/50000000000000 : ℝ), (42313895427997/100000000000000 : ℝ), (44109965102927/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-220883543/1000000000 : ℝ)|^4201 ≤ (6788069727097/50000000000000 : ℝ)^3177
        have hw : |(-220883543/1000000000 : ℝ)|=(220883543/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609145721/5000000000 : ℝ)|^4201 ≤ (42313895427997/100000000000000 : ℝ)^3177
        have hw : |(2609145721/5000000000 : ℝ)|=(2609145721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5384946823/10000000000 : ℝ)|^4201 ≤ (44109965102927/100000000000000 : ℝ)^3177
        have hw : |(5384946823/10000000000 : ℝ)|=(5384946823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_box_9 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1057954049/2000000000 : ℝ)*x 0 + (-132103677/625000000 : ℝ)*x 1 + (215397873/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057954049/2000000000 : ℝ)^4201 ≤ (21541001567691/50000000000000 : ℝ)^3177 := by
    have hnat : (1057954049 : ℕ)^4201*50000000000000^3177 ≤ 21541001567691^3177*2000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057954049 2000000000 21541001567691 50000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (132103677/625000000 : ℝ)^4201 ≤ (3202007930213/25000000000000 : ℝ)^3177 := by
    have hnat : (132103677 : ℕ)^4201*25000000000000^3177 ≤ 3202007930213^3177*625000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132103677 625000000 3202007930213 25000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215397873/400000000 : ℝ)^4201 ≤ (4410996512459/10000000000000 : ℝ)^3177 := by
    have hnat : (215397873 : ℕ)^4201*10000000000000^3177 ≤ 4410996512459^3177*400000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215397873 400000000 4410996512459 10000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057954049/2000000000 : ℝ), (-132103677/625000000 : ℝ), (215397873/400000000 : ℝ)] ![(21541001567691/50000000000000 : ℝ), (3202007930213/25000000000000 : ℝ), (4410996512459/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057954049/2000000000 : ℝ)|^4201 ≤ (21541001567691/50000000000000 : ℝ)^3177
        have hw : |(1057954049/2000000000 : ℝ)|=(1057954049/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-132103677/625000000 : ℝ)|^4201 ≤ (3202007930213/25000000000000 : ℝ)^3177
        have hw : |(-132103677/625000000 : ℝ)|=(132103677/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(215397873/400000000 : ℝ)|^4201 ≤ (4410996512459/10000000000000 : ℝ)^3177
        have hw : |(215397873/400000000 : ℝ)|=(215397873/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_box_10 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5289770237/10000000000 : ℝ)*x 0 + (215397873/400000000 : ℝ)*x 1 + (-528414711/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289770237/10000000000 : ℝ)^4201 ≤ (21541001524613/50000000000000 : ℝ)^3177 := by
    have hnat : (5289770237 : ℕ)^4201*50000000000000^3177 ≤ 21541001524613^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289770237 10000000000 21541001524613 50000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215397873/400000000 : ℝ)^4201 ≤ (4410996512459/10000000000000 : ℝ)^3177 := by
    have hnat : (215397873 : ℕ)^4201*10000000000000^3177 ≤ 4410996512459^3177*400000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215397873 400000000 4410996512459 10000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (528414711/2500000000 : ℝ)^4201 ≤ (2561606363401/20000000000000 : ℝ)^3177 := by
    have hnat : (528414711 : ℕ)^4201*20000000000000^3177 ≤ 2561606363401^3177*2500000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528414711 2500000000 2561606363401 20000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289770237/10000000000 : ℝ), (215397873/400000000 : ℝ), (-528414711/2500000000 : ℝ)] ![(21541001524613/50000000000000 : ℝ), (4410996512459/10000000000000 : ℝ), (2561606363401/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289770237/10000000000 : ℝ)|^4201 ≤ (21541001524613/50000000000000 : ℝ)^3177
        have hw : |(5289770237/10000000000 : ℝ)|=(5289770237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(215397873/400000000 : ℝ)|^4201 ≤ (4410996512459/10000000000000 : ℝ)^3177
        have hw : |(215397873/400000000 : ℝ)|=(215397873/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-528414711/2500000000 : ℝ)|^4201 ≤ (2561606363401/20000000000000 : ℝ)^3177
        have hw : |(-528414711/2500000000 : ℝ)|=(528414711/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_box_11 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (35871457/80000000 : ℝ)*x 0 + (2146469077/5000000000 : ℝ)*x 1 + (107323453/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (35871457/80000000 : ℝ)^4201 ≤ (2164028381849/6250000000000 : ℝ)^3177 := by
    have hnat : (35871457 : ℕ)^4201*6250000000000^3177 ≤ 2164028381849^3177*80000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35871457 80000000 2164028381849 6250000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2146469077/5000000000 : ℝ)^4201 ≤ (8171943276683/25000000000000 : ℝ)^3177 := by
    have hnat : (2146469077 : ℕ)^4201*25000000000000^3177 ≤ 8171943276683^3177*5000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2146469077 5000000000 8171943276683 25000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (107323453/250000000 : ℝ)^4201 ≤ (16343886382201/50000000000000 : ℝ)^3177 := by
    have hnat : (107323453 : ℕ)^4201*50000000000000^3177 ≤ 16343886382201^3177*250000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107323453 250000000 16343886382201 50000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(35871457/80000000 : ℝ), (2146469077/5000000000 : ℝ), (107323453/250000000 : ℝ)] ![(2164028381849/6250000000000 : ℝ), (8171943276683/25000000000000 : ℝ), (16343886382201/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(35871457/80000000 : ℝ)|^4201 ≤ (2164028381849/6250000000000 : ℝ)^3177
        have hw : |(35871457/80000000 : ℝ)|=(35871457/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2146469077/5000000000 : ℝ)|^4201 ≤ (8171943276683/25000000000000 : ℝ)^3177
        have hw : |(2146469077/5000000000 : ℝ)|=(2146469077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(107323453/250000000 : ℝ)|^4201 ≤ (16343886382201/50000000000000 : ℝ)^3177
        have hw : |(107323453/250000000 : ℝ)|=(107323453/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_box_12 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-206333403/1000000000 : ℝ)*x 0 + (2718874717/5000000000 : ℝ)*x 1 + (2636935179/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (206333403/1000000000 : ℝ)^4201 ≤ (6203173027283/50000000000000 : ℝ)^3177 := by
    have hnat : (206333403 : ℕ)^4201*50000000000000^3177 ≤ 6203173027283^3177*1000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206333403 1000000000 6203173027283 50000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2718874717/5000000000 : ℝ)^4201 ≤ (1117070030829/2500000000000 : ℝ)^3177 := by
    have hnat : (2718874717 : ℕ)^4201*2500000000000^3177 ≤ 1117070030829^3177*5000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718874717 5000000000 1117070030829 2500000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2636935179/5000000000 : ℝ)^4201 ≤ (10727713174433/25000000000000 : ℝ)^3177 := by
    have hnat : (2636935179 : ℕ)^4201*25000000000000^3177 ≤ 10727713174433^3177*5000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636935179 5000000000 10727713174433 25000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-206333403/1000000000 : ℝ), (2718874717/5000000000 : ℝ), (2636935179/5000000000 : ℝ)] ![(6203173027283/50000000000000 : ℝ), (1117070030829/2500000000000 : ℝ), (10727713174433/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-206333403/1000000000 : ℝ)|^4201 ≤ (6203173027283/50000000000000 : ℝ)^3177
        have hw : |(-206333403/1000000000 : ℝ)|=(206333403/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2718874717/5000000000 : ℝ)|^4201 ≤ (1117070030829/2500000000000 : ℝ)^3177
        have hw : |(2718874717/5000000000 : ℝ)|=(2718874717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2636935179/5000000000 : ℝ)|^4201 ≤ (10727713174433/25000000000000 : ℝ)^3177
        have hw : |(2636935179/5000000000 : ℝ)|=(2636935179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_box_13 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5368129257/10000000000 : ℝ)*x 0 + (-2157594279/10000000000 : ℝ)*x 1 + (2636935197/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368129257/10000000000 : ℝ)^4201 ≤ (68637338249/156250000000 : ℝ)^3177 := by
    have hnat : (5368129257 : ℕ)^4201*156250000000^3177 ≤ 68637338249^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368129257 10000000000 68637338249 156250000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2157594279/10000000000 : ℝ)^4201 ≤ (1645156302551/12500000000000 : ℝ)^3177 := by
    have hnat : (2157594279 : ℕ)^4201*12500000000000^3177 ≤ 1645156302551^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2157594279 10000000000 1645156302551 12500000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2636935197/5000000000 : ℝ)^4201 ≤ (42910853085057/100000000000000 : ℝ)^3177 := by
    have hnat : (2636935197 : ℕ)^4201*100000000000000^3177 ≤ 42910853085057^3177*5000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636935197 5000000000 42910853085057 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368129257/10000000000 : ℝ), (-2157594279/10000000000 : ℝ), (2636935197/5000000000 : ℝ)] ![(68637338249/156250000000 : ℝ), (1645156302551/12500000000000 : ℝ), (42910853085057/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368129257/10000000000 : ℝ)|^4201 ≤ (68637338249/156250000000 : ℝ)^3177
        have hw : |(5368129257/10000000000 : ℝ)|=(5368129257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2157594279/10000000000 : ℝ)|^4201 ≤ (1645156302551/12500000000000 : ℝ)^3177
        have hw : |(-2157594279/10000000000 : ℝ)|=(2157594279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2636935197/5000000000 : ℝ)|^4201 ≤ (42910853085057/100000000000000 : ℝ)^3177
        have hw : |(2636935197/5000000000 : ℝ)|=(2636935197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_box_14 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (67101621/125000000 : ℝ)*x 0 + (5273870229/10000000000 : ℝ)*x 1 + (-539398483/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (67101621/125000000 : ℝ)^4201 ≤ (4392790105649/10000000000000 : ℝ)^3177 := by
    have hnat : (67101621 : ℕ)^4201*10000000000000^3177 ≤ 4392790105649^3177*125000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67101621 125000000 4392790105649 10000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5273870229/10000000000 : ℝ)^4201 ≤ (42910851309817/100000000000000 : ℝ)^3177 := by
    have hnat : (5273870229 : ℕ)^4201*100000000000000^3177 ≤ 42910851309817^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5273870229 10000000000 42910851309817 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539398483/2500000000 : ℝ)^4201 ≤ (3290311905369/25000000000000 : ℝ)^3177 := by
    have hnat : (539398483 : ℕ)^4201*25000000000000^3177 ≤ 3290311905369^3177*2500000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539398483 2500000000 3290311905369 25000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(67101621/125000000 : ℝ), (5273870229/10000000000 : ℝ), (-539398483/2500000000 : ℝ)] ![(4392790105649/10000000000000 : ℝ), (42910851309817/100000000000000 : ℝ), (3290311905369/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(67101621/125000000 : ℝ)|^4201 ≤ (4392790105649/10000000000000 : ℝ)^3177
        have hw : |(67101621/125000000 : ℝ)|=(67101621/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5273870229/10000000000 : ℝ)|^4201 ≤ (42910851309817/100000000000000 : ℝ)^3177
        have hw : |(5273870229/10000000000 : ℝ)|=(5273870229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-539398483/2500000000 : ℝ)|^4201 ≤ (3290311905369/25000000000000 : ℝ)^3177
        have hw : |(-539398483/2500000000 : ℝ)|=(539398483/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_box_15 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (422935881/1000000000 : ℝ)*x 0 + (2210111467/5000000000 : ℝ)*x 1 + (1105055487/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (422935881/1000000000 : ℝ)^4201 ≤ (2003072217119/6250000000000 : ℝ)^3177 := by
    have hnat : (422935881 : ℕ)^4201*6250000000000^3177 ≤ 2003072217119^3177*1000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422935881 1000000000 2003072217119 6250000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2210111467/5000000000 : ℝ)^4201 ≤ (8493856816281/25000000000000 : ℝ)^3177 := by
    have hnat : (2210111467 : ℕ)^4201*25000000000000^3177 ≤ 8493856816281^3177*5000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2210111467 5000000000 8493856816281 25000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1105055487/2500000000 : ℝ)^4201 ≤ (6795083448723/20000000000000 : ℝ)^3177 := by
    have hnat : (1105055487 : ℕ)^4201*20000000000000^3177 ≤ 6795083448723^3177*2500000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1105055487 2500000000 6795083448723 20000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(422935881/1000000000 : ℝ), (2210111467/5000000000 : ℝ), (1105055487/2500000000 : ℝ)] ![(2003072217119/6250000000000 : ℝ), (8493856816281/25000000000000 : ℝ), (6795083448723/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(422935881/1000000000 : ℝ)|^4201 ≤ (2003072217119/6250000000000 : ℝ)^3177
        have hw : |(422935881/1000000000 : ℝ)|=(422935881/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2210111467/5000000000 : ℝ)|^4201 ≤ (8493856816281/25000000000000 : ℝ)^3177
        have hw : |(2210111467/5000000000 : ℝ)|=(2210111467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1105055487/2500000000 : ℝ)|^4201 ≤ (6795083448723/20000000000000 : ℝ)^3177
        have hw : |(1105055487/2500000000 : ℝ)|=(1105055487/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1209_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150782627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7043/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11439/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62241/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59351/100000 : ℝ) ∧ (80011/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (83273/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7043/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11439/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7043/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11439/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7043/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11439/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7043/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11439/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7043/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11439/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7043/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11439/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11439/100000 : ℝ) ^ (8401/2048 : ℝ) ≤ (13723345770240177/100000000000000000000 : ℝ) := by
    have hpowers : (11439/100000 : ℝ)^8401 ≤ (13723345770240177/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11439 : ℕ)^8401*100000000000000000000^2048 ≤ 13723345770240177^2048*100000^8401 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11439 100000 13723345770240177 100000000000000000000 8401 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11439/100000 : ℝ)) (X := (13723345770240177/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8401 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7043/50000 : ℝ) ^ (8401/2048 : ℝ) ≤ (16115873831474897/50000000000000000000 : ℝ) := by
    have hpowers : (7043/50000 : ℝ)^8401 ≤ (16115873831474897/50000000000000000000 : ℝ)^2048 := by
      have hnat : (7043 : ℕ)^8401*50000000000000000000^2048 ≤ 16115873831474897^2048*50000^8401 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7043 50000 16115873831474897 50000000000000000000 8401 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7043/50000 : ℝ)) (X := (16115873831474897/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8401 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013723345770240177/50000000000000000000 : ℝ) ≤ (2500167256849573/2500000000000000 : ℝ) ^ (8401/2048 : ℝ) := by
    have hpowers : (50013723345770240177/50000000000000000000 : ℝ)^2048 ≤ (2500167256849573/2500000000000000 : ℝ)^8401 := by
      have hnat : (50013723345770240177 : ℕ)^2048*2500000000000000^8401 ≤ 2500167256849573^8401*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013723345770240177 50000000000000000000 2500167256849573 2500000000000000 2048 8401 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500167256849573/2500000000000000 : ℝ)) (X := (50013723345770240177/50000000000000000000 : ℝ)) (by norm_num) 8401 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045955093433189971/100000000000000000000 : ℝ) ≤ (5000560050482579/5000000000000000 : ℝ) ^ (8401/2048 : ℝ) := by
    have hpowers : (100045955093433189971/100000000000000000000 : ℝ)^2048 ≤ (5000560050482579/5000000000000000 : ℝ)^8401 := by
      have hnat : (100045955093433189971 : ℕ)^2048*5000000000000000^8401 ≤ 5000560050482579^8401*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045955093433189971 100000000000000000000 5000560050482579 5000000000000000 2048 8401 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000560050482579/5000000000000000 : ℝ)) (X := (100045955093433189971/100000000000000000000 : ℝ)) (by norm_num) 8401 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016115873831474897/25000000000000000000 : ℝ) ≤ (1250196396816503/1250000000000000 : ℝ) ^ (8401/2048 : ℝ) := by
    have hpowers : (25016115873831474897/25000000000000000000 : ℝ)^2048 ≤ (1250196396816503/1250000000000000 : ℝ)^8401 := by
      have hnat : (25016115873831474897 : ℕ)^2048*1250000000000000^8401 ≤ 1250196396816503^8401*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016115873831474897 25000000000000000000 1250196396816503 1250000000000000 2048 8401 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250196396816503/1250000000000000 : ℝ)) (X := (25016115873831474897/25000000000000000000 : ℝ)) (by norm_num) 8401 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13723345770240177/100000000000000000000 : ℝ) ≤ ((1653840703403782411/1654375000000000000 : ℝ)+2*(225536783433/132350000000000 : ℝ)*(11439/100000 : ℝ))^(8401/2048 : ℝ) := by
    rw [show (1653840703403782411/1654375000000000000 : ℝ)+2*(225536783433/132350000000000 : ℝ)*(11439/100000 : ℝ)=(2500167256849573/2500000000000000 : ℝ) by norm_num, show 1+2*(13723345770240177/100000000000000000000 : ℝ)=(50013723345770240177/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16115873831474897/50000000000000000000 : ℝ)+(13723345770240177/100000000000000000000 : ℝ) ≤ ((1653840703403782411/1654375000000000000 : ℝ)+(225536783433/132350000000000 : ℝ)*((7043/50000 : ℝ)+(11439/100000 : ℝ)))^(8401/2048 : ℝ) := by
    rw [show (1653840703403782411/1654375000000000000 : ℝ)+(225536783433/132350000000000 : ℝ)*((7043/50000 : ℝ)+(11439/100000 : ℝ))=(5000560050482579/5000000000000000 : ℝ) by norm_num, show 1+(16115873831474897/50000000000000000000 : ℝ)+(13723345770240177/100000000000000000000 : ℝ)=(100045955093433189971/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16115873831474897/50000000000000000000 : ℝ) ≤ ((1653840703403782411/1654375000000000000 : ℝ)+2*(225536783433/132350000000000 : ℝ)*(7043/50000 : ℝ))^(8401/2048 : ℝ) := by
    rw [show (1653840703403782411/1654375000000000000 : ℝ)+2*(225536783433/132350000000000 : ℝ)*(7043/50000 : ℝ)=(1250196396816503/1250000000000000 : ℝ) by norm_num, show 1+2*(16115873831474897/50000000000000000000 : ℝ)=(25016115873831474897/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1653840703403782411/1654375000000000000 : ℝ)*(X 1 0+X 2 0)+(225536783433/132350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8401/2048 : ℝ)) (lo := (11439/100000 : ℝ)) (hi := (7043/50000 : ℝ)) (c := (1653840703403782411/1654375000000000000 : ℝ)) (alpha := (225536783433/132350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1653840703403782411/1654375000000000000 : ℝ)*(X 0 1+X 2 1)+(225536783433/132350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8401/2048 : ℝ)) (lo := (11439/100000 : ℝ)) (hi := (7043/50000 : ℝ)) (c := (1653840703403782411/1654375000000000000 : ℝ)) (alpha := (225536783433/132350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1653840703403782411/1654375000000000000 : ℝ)*(X 0 2+X 1 2)+(225536783433/132350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8401/2048 : ℝ)) (lo := (11439/100000 : ℝ)) (hi := (7043/50000 : ℝ)) (c := (1653840703403782411/1654375000000000000 : ℝ)) (alpha := (225536783433/132350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2010527741/10000000000 : ℝ)*X 0 0+(1075066979/2000000000 : ℝ)*X 0 1+(2687667333/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1059310787/2000000000 : ℝ)*X 1 0+(-2117528471/10000000000 : ℝ)*X 1 1+(5375334397/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5296554641/10000000000 : ℝ)*X 2 0+(5375334367/10000000000 : ℝ)*X 2 1+(-2117527563/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((278885687/625000000 : ℝ)*X 0 0+(860791667/2000000000 : ℝ)*X 0 1+(2151980071/5000000000 : ℝ)*X 0 2+(278885687/625000000 : ℝ)*X 1 0+(860791667/2000000000 : ℝ)*X 1 1+(2151980071/5000000000 : ℝ)*X 1 2+(278885687/625000000 : ℝ)*X 2 0+(860791667/2000000000 : ℝ)*X 2 1+(2151980071/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2261362459/10000000000 : ℝ)*X 0 0+(1320484261/2500000000 : ℝ)*X 0 1+(2640968547/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1340610273/2500000000 : ℝ)*X 1 0+(-430892161/2000000000 : ℝ)*X 1 1+(5281936793/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5362440707/10000000000 : ℝ)*X 2 0+(2640968611/5000000000 : ℝ)*X 2 1+(-2154460749/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((265505091/625000000 : ℝ)*X 0 0+(4410983707/10000000000 : ℝ)*X 0 1+(4410983627/10000000000 : ℝ)*X 0 2+(265505091/625000000 : ℝ)*X 1 0+(4410983707/10000000000 : ℝ)*X 1 1+(4410983627/10000000000 : ℝ)*X 1 2+(265505091/625000000 : ℝ)*X 2 0+(4410983707/10000000000 : ℝ)*X 2 1+(4410983627/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-220883543/1000000000 : ℝ)*X 0 0+(2609145721/5000000000 : ℝ)*X 0 1+(5384946823/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1057954049/2000000000 : ℝ)*X 1 0+(-132103677/625000000 : ℝ)*X 1 1+(215397873/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5289770237/10000000000 : ℝ)*X 2 0+(215397873/400000000 : ℝ)*X 2 1+(-528414711/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((35871457/80000000 : ℝ)*X 0 0+(2146469077/5000000000 : ℝ)*X 0 1+(107323453/250000000 : ℝ)*X 0 2+(35871457/80000000 : ℝ)*X 1 0+(2146469077/5000000000 : ℝ)*X 1 1+(107323453/250000000 : ℝ)*X 1 2+(35871457/80000000 : ℝ)*X 2 0+(2146469077/5000000000 : ℝ)*X 2 1+(107323453/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-206333403/1000000000 : ℝ)*X 0 0+(2718874717/5000000000 : ℝ)*X 0 1+(2636935179/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5368129257/10000000000 : ℝ)*X 1 0+(-2157594279/10000000000 : ℝ)*X 1 1+(2636935197/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((67101621/125000000 : ℝ)*X 2 0+(5273870229/10000000000 : ℝ)*X 2 1+(-539398483/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((422935881/1000000000 : ℝ)*X 0 0+(2210111467/5000000000 : ℝ)*X 0 1+(1105055487/2500000000 : ℝ)*X 0 2+(422935881/1000000000 : ℝ)*X 1 0+(2210111467/5000000000 : ℝ)*X 1 1+(1105055487/2500000000 : ℝ)*X 1 2+(422935881/1000000000 : ℝ)*X 2 0+(2210111467/5000000000 : ℝ)*X 2 1+(1105055487/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62241/100000 : ℝ) ≤ (-51482628508380091724470792879431/82718750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9093829/12500000000000 : ℝ)*(upper1) + (17507289/20000000000000 : ℝ)*(upper2) + (8503663/20000000000000 : ℝ)*(upper3) + (727783/1250000000000 : ℝ)*(upper5) + (3976139020589119/100000000000000 : ℝ)*(major0) + (3976139020589119/100000000000000 : ℝ)*(major1) + (3976139020589119/100000000000000 : ℝ)*(major2) + (13959885433/100000000000000 : ℝ)*(sp1) + (5142107669/50000000000000 : ℝ)*(sp3) + (66700291678683/1250000000000 : ℝ)*(sp4) + (5336009374409207/100000000000000 : ℝ)*(sp5) + (666997220957127/12500000000000 : ℝ)*(sp6) + (41202976190883/1562500000000 : ℝ)*(sp7) + (5695829703/12500000000000 : ℝ)*(sp14) + (2637000760431849/100000000000000 : ℝ)*(f.failure) + (66700291678683/1250000000000 : ℝ)*(f.sum) + (53872643234913/6617500000000000000000000000 : ℝ)*base66 + (2828296705805648409/165437500000000000000000000000000 : ℝ)*base67 + (5073858177338023409/165437500000000000000000000000000 : ℝ)*base69 + (1300252544769960909/165437500000000000000000000000000 : ℝ)*base71 + (3463622559297/6617500000000000000000000000 : ℝ)*base73 + (5415649423205273409/165437500000000000000000000000000 : ℝ)*base75 + (1190010332941773409/165437500000000000000000000000000 : ℝ)*base77 + (1710253323972148409/165437500000000000000000000000000 : ℝ)*base79 + (291878579748537/6617500000000000000000000000 : ℝ)*base81 + (53312677/10000000000000000000000 : ℝ)*base90 + (53312677/10000000000000000000000 : ℝ)*base92 + (53312677/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (59351/100000 : ℝ) ≤ (24548217720664820064594182811867/41359375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (75818951/20000000000000 : ℝ)*(upper0) + (247080319/100000000000000 : ℝ)*(lower1) + (6008093/4000000000000 : ℝ)*(lower3) + (545239173/100000000000000 : ℝ)*(upper4) + (51221109/50000000000000 : ℝ)*(upper5) + (1010339283174169/25000000000000 : ℝ)*(major0) + (1010339283174169/25000000000000 : ℝ)*(major1) + (1010339283174169/25000000000000 : ℝ)*(major2) + (5382675952263601/100000000000000 : ℝ)*(sp0) + (538242453610133/10000000000000 : ℝ)*(sp1) + (1076533619001461/20000000000000 : ℝ)*(sp2) + (268025382837817/10000000000000 : ℝ)*(sp3) + (251416162271/100000000000000 : ℝ)*(sp9) + (982157037/12500000000000 : ℝ)*(sp10) + (268025382837817/10000000000000 : ℝ)*(f.failure) + (5382675952263601/100000000000000 : ℝ)*(f.sum) + (38689151434849/13235000000000000000000000000 : ℝ)*base66 + (48697561469914271/10339843750000000000000000000000 : ℝ)*base67 + (282435370552047709/41359375000000000000000000000000 : ℝ)*base69 + (2252534442753431/646240234375000000000000000000 : ℝ)*base71 + (2870964754777/413593750000000000000000000 : ℝ)*base74 + (208052298070070521/10339843750000000000000000000000 : ℝ)*base75 + (33061363388386823/5169921875000000000000000000000 : ℝ)*base77 + (89291316160085729/10339843750000000000000000000000 : ℝ)*base80 + (7382131033181/13235000000000000000000000000 : ℝ)*base81 + (2205259/1000000000000000000000 : ℝ)*base89 + (2205259/1000000000000000000000 : ℝ)*base91 + (2205259/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (80011/100000 : ℝ) ≤ (66186041149668293384135262239841/82718750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5526063/100000000000000 : ℝ)*(upper1) + (1496139/50000000000000 : ℝ)*(upper2) + (3486601/50000000000000 : ℝ)*(upper3) + (5898491/100000000000000 : ℝ)*(lower5) + (4508607238012041/100000000000000 : ℝ)*(major0) + (4508607238012041/100000000000000 : ℝ)*(major1) + (4508607238012041/100000000000000 : ℝ)*(major2) + (257025949/100000000000000 : ℝ)*(sp0) + (266500379/10000000000000 : ℝ)*(sp2) + (577526783/50000000000000 : ℝ)*(sp3) + (1500101506114897/25000000000000 : ℝ)*(sp8) + (6000406281485537/100000000000000 : ℝ)*(sp9) + (1500100904120437/25000000000000 : ℝ)*(sp10) + (1495067961772523/50000000000000 : ℝ)*(sp11) + (2990137078598611/100000000000000 : ℝ)*(f.failure) + (6000406281485537/100000000000000 : ℝ)*(f.sum) + (46591609066149/13235000000000000000000000000 : ℝ)*base66 + (2288550800195485851/165437500000000000000000000000000 : ℝ)*base67 + (1649554593349548351/165437500000000000000000000000000 : ℝ)*base69 + (323432419397110851/165437500000000000000000000000000 : ℝ)*base71 + (1607840531293/1654375000000000000000000000 : ℝ)*base74 + (2255414335327735851/165437500000000000000000000000000 : ℝ)*base75 + (751786982750423351/165437500000000000000000000000000 : ℝ)*base77 + (2226920819673351/165437500000000000000000000000000 : ℝ)*base79 + (5081565763289/3308750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (54868903/10000000000000000000000 : ℝ)*base90 + (54868903/10000000000000000000000 : ℝ)*base92 + (54868903/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-83273/100000 : ℝ) ≤ (-34440293392868456122167624698673/41359375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (116101739/100000000000000 : ℝ)*(lower0) + (16613179/12500000000000 : ℝ)*(upper1) + (258116231/100000000000000 : ℝ)*(lower2) + (73557603/50000000000000 : ℝ)*(upper3) + (62149491/20000000000000 : ℝ)*(upper5) + (4543918770601681/100000000000000 : ℝ)*(major0) + (4543918770601681/100000000000000 : ℝ)*(major1) + (4543918770601681/100000000000000 : ℝ)*(major2) + (9616733587/100000000000000 : ℝ)*(sp4) + (57812661667/25000000000000 : ℝ)*(sp7) + (3051014477192139/50000000000000 : ℝ)*(sp12) + (1220407714223573/20000000000000 : ℝ)*(sp13) + (1220407714223573/20000000000000 : ℝ)*(sp14) + (188332791350097/6250000000000 : ℝ)*(sp15) + (150677795612411/5000000000000 : ℝ)*(f.failure) + (1220407714223573/20000000000000 : ℝ)*(f.sum) + (2194154412321/13235000000000000000000000000 : ℝ)*base65 + (16033017484646495391/165437500000000000000000000000000 : ℝ)*base67 + (1104607753023370391/165437500000000000000000000000000 : ℝ)*base69 + (1555613175476307891/165437500000000000000000000000000 : ℝ)*base71 + (54243413429869/13235000000000000000000000000 : ℝ)*base74 + (1512976803468620391/165437500000000000000000000000000 : ℝ)*base75 + (631999287909745391/165437500000000000000000000000000 : ℝ)*base77 + (12505984522630692109/165437500000000000000000000000000 : ℝ)*base80 + (53697586241013/6617500000000000000000000000 : ℝ)*base81 + (616303/500000000000000000000 : ℝ)*base90 + (616303/500000000000000000000 : ℝ)*base92 + (616303/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1209_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150782627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7043/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11439/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62241/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59351/100000 : ℝ) else (80011/100000 : ℝ) ≤ X j i ∧ X j i ≤ (83273/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1209_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1209_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150782627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7043/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11439/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62241/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59351/100000 : ℝ) else (80011/100000 : ℝ) ≤ X j i ∧ X j i ≤ (83273/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1209_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150782627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7043/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11439/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62241/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59351/100000 : ℝ) else (80011/100000 : ℝ) ≤ X j i ∧ X j i ≤ (83273/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1209_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
