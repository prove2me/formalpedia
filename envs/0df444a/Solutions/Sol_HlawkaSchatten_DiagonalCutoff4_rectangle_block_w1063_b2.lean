-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1063_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:04:54.707098+00:00
-- url     : https://prove2.me/submissions/b5a75795-2fe4-498e-b7ae-ca0dc3b35dfc

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
theorem support_rectangle_w1063_s6_0 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-2205196119/10000000000 : ℝ)*x 0 + (2697488113/5000000000 : ℝ)*x 1 + (5263863809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2205196119/10000000000 : ℝ)^129 ≤ (1339221730801/10000000000000 : ℝ)^97 := by
    have hnat : (2205196119 : ℕ)^129*10000000000000^97 ≤ 1339221730801^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2205196119 10000000000 1339221730801 10000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697488113/5000000000 : ℝ)^129 ≤ (2200613212429/5000000000000 : ℝ)^97 := by
    have hnat : (2697488113 : ℕ)^129*5000000000000^97 ≤ 2200613212429^97*5000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697488113 5000000000 2200613212429 5000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263863809/10000000000 : ℝ)^129 ≤ (4259551843261/10000000000000 : ℝ)^97 := by
    have hnat : (5263863809 : ℕ)^129*10000000000000^97 ≤ 4259551843261^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263863809 10000000000 4259551843261 10000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2205196119/10000000000 : ℝ), (2697488113/5000000000 : ℝ), (5263863809/10000000000 : ℝ)] ![(1339221730801/10000000000000 : ℝ), (2200613212429/5000000000000 : ℝ), (4259551843261/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2205196119/10000000000 : ℝ)|^129 ≤ (1339221730801/10000000000000 : ℝ)^97
        have hw : |(-2205196119/10000000000 : ℝ)|=(2205196119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697488113/5000000000 : ℝ)|^129 ≤ (2200613212429/5000000000000 : ℝ)^97
        have hw : |(2697488113/5000000000 : ℝ)|=(2697488113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263863809/10000000000 : ℝ)|^129 ≤ (4259551843261/10000000000000 : ℝ)^97
        have hw : |(5263863809/10000000000 : ℝ)|=(5263863809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_s6_1 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (83517621/156250000 : ℝ)*x 0 + (-454345459/2000000000 : ℝ)*x 1 + (2631931919/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83517621/156250000 : ℝ)^129 ≤ (4347226854071/10000000000000 : ℝ)^97 := by
    have hnat : (83517621 : ℕ)^129*10000000000000^97 ≤ 4347226854071^97*156250000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83517621 156250000 4347226854071 10000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (454345459/2000000000 : ℝ)^129 ≤ (6966106346687/50000000000000 : ℝ)^97 := by
    have hnat : (454345459 : ℕ)^129*50000000000000^97 ≤ 6966106346687^97*2000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      454345459 2000000000 6966106346687 50000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2631931919/5000000000 : ℝ)^129 ≤ (42595518744697/100000000000000 : ℝ)^97 := by
    have hnat : (2631931919 : ℕ)^129*100000000000000^97 ≤ 42595518744697^97*5000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631931919 5000000000 42595518744697 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(83517621/156250000 : ℝ), (-454345459/2000000000 : ℝ), (2631931919/5000000000 : ℝ)] ![(4347226854071/10000000000000 : ℝ), (6966106346687/50000000000000 : ℝ), (42595518744697/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(83517621/156250000 : ℝ)|^129 ≤ (4347226854071/10000000000000 : ℝ)^97
        have hw : |(83517621/156250000 : ℝ)|=(83517621/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-454345459/2000000000 : ℝ)|^129 ≤ (6966106346687/50000000000000 : ℝ)^97
        have hw : |(-454345459/2000000000 : ℝ)|=(454345459/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2631931919/5000000000 : ℝ)|^129 ≤ (42595518744697/100000000000000 : ℝ)^97
        have hw : |(2631931919/5000000000 : ℝ)|=(2631931919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_s6_2 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2672563791/5000000000 : ℝ)*x 0 + (5263863933/10000000000 : ℝ)*x 1 + (-454345477/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672563791/5000000000 : ℝ)^129 ≤ (8694453357699/20000000000000 : ℝ)^97 := by
    have hnat : (2672563791 : ℕ)^129*20000000000000^97 ≤ 8694453357699^97*5000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672563791 5000000000 8694453357699 20000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263863933/10000000000 : ℝ)^129 ≤ (851910395341/2000000000000 : ℝ)^97 := by
    have hnat : (5263863933 : ℕ)^129*2000000000000^97 ≤ 851910395341^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263863933 10000000000 851910395341 2000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (454345477/2000000000 : ℝ)^129 ≤ (6966106713711/50000000000000 : ℝ)^97 := by
    have hnat : (454345477 : ℕ)^129*50000000000000^97 ≤ 6966106713711^97*2000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      454345477 2000000000 6966106713711 50000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672563791/5000000000 : ℝ), (5263863933/10000000000 : ℝ), (-454345477/2000000000 : ℝ)] ![(8694453357699/20000000000000 : ℝ), (851910395341/2000000000000 : ℝ), (6966106713711/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672563791/5000000000 : ℝ)|^129 ≤ (8694453357699/20000000000000 : ℝ)^97
        have hw : |(2672563791/5000000000 : ℝ)|=(2672563791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263863933/10000000000 : ℝ)|^129 ≤ (851910395341/2000000000000 : ℝ)^97
        have hw : |(5263863933/10000000000 : ℝ)|=(5263863933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-454345477/2000000000 : ℝ)|^129 ≤ (6966106713711/50000000000000 : ℝ)^97
        have hw : |(-454345477/2000000000 : ℝ)|=(454345477/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_s6_3 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4375895663/10000000000 : ℝ)*x 0 + (4249401001/10000000000 : ℝ)*x 1 + (1126552533/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4375895663/10000000000 : ℝ)^129 ≤ (33316245831549/100000000000000 : ℝ)^97 := by
    have hnat : (4375895663 : ℕ)^129*100000000000000^97 ≤ 33316245831549^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4375895663 10000000000 33316245831549 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4249401001/10000000000 : ℝ)^129 ≤ (8010399711219/25000000000000 : ℝ)^97 := by
    have hnat : (4249401001 : ℕ)^129*25000000000000^97 ≤ 8010399711219^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4249401001 10000000000 8010399711219 25000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1126552533/2500000000 : ℝ)^129 ≤ (1082567353329/3125000000000 : ℝ)^97 := by
    have hnat : (1126552533 : ℕ)^129*3125000000000^97 ≤ 1082567353329^97*2500000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126552533 2500000000 1082567353329 3125000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4375895663/10000000000 : ℝ), (4249401001/10000000000 : ℝ), (1126552533/2500000000 : ℝ)] ![(33316245831549/100000000000000 : ℝ), (8010399711219/25000000000000 : ℝ), (1082567353329/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4375895663/10000000000 : ℝ)|^129 ≤ (33316245831549/100000000000000 : ℝ)^97
        have hw : |(4375895663/10000000000 : ℝ)|=(4375895663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4249401001/10000000000 : ℝ)|^129 ≤ (8010399711219/25000000000000 : ℝ)^97
        have hw : |(4249401001/10000000000 : ℝ)|=(4249401001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1126552533/2500000000 : ℝ)|^129 ≤ (1082567353329/3125000000000 : ℝ)^97
        have hw : |(1126552533/2500000000 : ℝ)|=(1126552533/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_s6_4 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1102600703/5000000000 : ℝ)*x 0 + (5264195069/10000000000 : ℝ)*x 1 + (5394643701/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1102600703/5000000000 : ℝ)^129 ≤ (13392260008487/100000000000000 : ℝ)^97 := by
    have hnat : (1102600703 : ℕ)^129*100000000000000^97 ≤ 13392260008487^97*5000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102600703 5000000000 13392260008487 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264195069/10000000000 : ℝ)^129 ≤ (42599083360469/100000000000000 : ℝ)^97 := by
    have hnat : (5264195069 : ℕ)^129*100000000000000^97 ≤ 42599083360469^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264195069 10000000000 42599083360469 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394643701/10000000000 : ℝ)^129 ≤ (5501082077271/12500000000000 : ℝ)^97 := by
    have hnat : (5394643701 : ℕ)^129*12500000000000^97 ≤ 5501082077271^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394643701 10000000000 5501082077271 12500000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1102600703/5000000000 : ℝ), (5264195069/10000000000 : ℝ), (5394643701/10000000000 : ℝ)] ![(13392260008487/100000000000000 : ℝ), (42599083360469/100000000000000 : ℝ), (5501082077271/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1102600703/5000000000 : ℝ)|^129 ≤ (13392260008487/100000000000000 : ℝ)^97
        have hw : |(-1102600703/5000000000 : ℝ)|=(1102600703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264195069/10000000000 : ℝ)|^129 ≤ (42599083360469/100000000000000 : ℝ)^97
        have hw : |(5264195069/10000000000 : ℝ)|=(5264195069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394643701/10000000000 : ℝ)|^129 ≤ (5501082077271/12500000000000 : ℝ)^97
        have hw : |(5394643701/10000000000 : ℝ)|=(5394643701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_s6_5 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5312111047/10000000000 : ℝ)*x 0 + (-2140947317/10000000000 : ℝ)*x 1 + (5394643849/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312111047/10000000000 : ℝ)^129 ≤ (10778879943163/25000000000000 : ℝ)^97 := by
    have hnat : (5312111047 : ℕ)^129*25000000000000^97 ≤ 10778879943163^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312111047 10000000000 10778879943163 25000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2140947317/10000000000 : ℝ)^129 ≤ (1609477748799/12500000000000 : ℝ)^97 := by
    have hnat : (2140947317 : ℕ)^129*12500000000000^97 ≤ 1609477748799^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2140947317 10000000000 1609477748799 12500000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394643849/10000000000 : ℝ)^129 ≤ (22004329111917/50000000000000 : ℝ)^97 := by
    have hnat : (5394643849 : ℕ)^129*50000000000000^97 ≤ 22004329111917^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394643849 10000000000 22004329111917 50000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312111047/10000000000 : ℝ), (-2140947317/10000000000 : ℝ), (5394643849/10000000000 : ℝ)] ![(10778879943163/25000000000000 : ℝ), (1609477748799/12500000000000 : ℝ), (22004329111917/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312111047/10000000000 : ℝ)|^129 ≤ (10778879943163/25000000000000 : ℝ)^97
        have hw : |(5312111047/10000000000 : ℝ)|=(5312111047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2140947317/10000000000 : ℝ)|^129 ≤ (1609477748799/12500000000000 : ℝ)^97
        have hw : |(-2140947317/10000000000 : ℝ)|=(2140947317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394643849/10000000000 : ℝ)|^129 ≤ (22004329111917/50000000000000 : ℝ)^97
        have hw : |(5394643849/10000000000 : ℝ)|=(5394643849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_s6_6 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2656055377/5000000000 : ℝ)*x 0 + (5394644191/10000000000 : ℝ)*x 1 + (-2140947249/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656055377/5000000000 : ℝ)^129 ≤ (8623103321999/20000000000000 : ℝ)^97 := by
    have hnat : (2656055377 : ℕ)^129*20000000000000^97 ≤ 8623103321999^97*5000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656055377 5000000000 8623103321999 20000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394644191/10000000000 : ℝ)^129 ≤ (22004330967111/50000000000000 : ℝ)^97 := by
    have hnat : (5394644191 : ℕ)^129*50000000000000^97 ≤ 22004330967111^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394644191 10000000000 22004330967111 50000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2140947249/10000000000 : ℝ)^129 ≤ (12875821446521/100000000000000 : ℝ)^97 := by
    have hnat : (2140947249 : ℕ)^129*100000000000000^97 ≤ 12875821446521^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2140947249 10000000000 12875821446521 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656055377/5000000000 : ℝ), (5394644191/10000000000 : ℝ), (-2140947249/10000000000 : ℝ)] ![(8623103321999/20000000000000 : ℝ), (22004330967111/50000000000000 : ℝ), (12875821446521/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656055377/5000000000 : ℝ)|^129 ≤ (8623103321999/20000000000000 : ℝ)^97
        have hw : |(2656055377/5000000000 : ℝ)|=(2656055377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394644191/10000000000 : ℝ)|^129 ≤ (22004330967111/50000000000000 : ℝ)^97
        have hw : |(5394644191/10000000000 : ℝ)|=(5394644191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2140947249/10000000000 : ℝ)|^129 ≤ (12875821446521/100000000000000 : ℝ)^97
        have hw : |(-2140947249/10000000000 : ℝ)|=(2140947249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_s6_7 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4375905921/10000000000 : ℝ)*x 0 + (4505561433/10000000000 : ℝ)*x 1 + (425005199/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4375905921/10000000000 : ℝ)^129 ≤ (33316349696719/100000000000000 : ℝ)^97 := by
    have hnat : (4375905921 : ℕ)^129*100000000000000^97 ≤ 33316349696719^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4375905921 10000000000 33316349696719 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4505561433/10000000000 : ℝ)^129 ≤ (34635523308993/100000000000000 : ℝ)^97 := by
    have hnat : (4505561433 : ℕ)^129*100000000000000^97 ≤ 34635523308993^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4505561433 10000000000 34635523308993 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (425005199/1000000000 : ℝ)^129 ≤ (8012031744729/25000000000000 : ℝ)^97 := by
    have hnat : (425005199 : ℕ)^129*25000000000000^97 ≤ 8012031744729^97*1000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425005199 1000000000 8012031744729 25000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4375905921/10000000000 : ℝ), (4505561433/10000000000 : ℝ), (425005199/1000000000 : ℝ)] ![(33316349696719/100000000000000 : ℝ), (34635523308993/100000000000000 : ℝ), (8012031744729/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4375905921/10000000000 : ℝ)|^129 ≤ (33316349696719/100000000000000 : ℝ)^97
        have hw : |(4375905921/10000000000 : ℝ)|=(4375905921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4505561433/10000000000 : ℝ)|^129 ≤ (34635523308993/100000000000000 : ℝ)^97
        have hw : |(4505561433/10000000000 : ℝ)|=(4505561433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(425005199/1000000000 : ℝ)|^129 ≤ (8012031744729/25000000000000 : ℝ)^97
        have hw : |(425005199/1000000000 : ℝ)|=(425005199/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1063_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147934681/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14057/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5597/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2809/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14013/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14057/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5597/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14057/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5597/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14057/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5597/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14057/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5597/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14057/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5597/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14057/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5597/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5597/50000 : ℝ) ^ (8255/2048 : ℝ) ≤ (7339329198072773/50000000000000000000 : ℝ) := by
    have hpowers : (5597/50000 : ℝ)^8255 ≤ (7339329198072773/50000000000000000000 : ℝ)^2048 := by
      have hnat : (5597 : ℕ)^8255*50000000000000000000^2048 ≤ 7339329198072773^2048*50000^8255 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5597 50000 7339329198072773 50000000000000000000 8255 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5597/50000 : ℝ)) (X := (7339329198072773/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8255 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14057/100000 : ℝ) ^ (8255/2048 : ℝ) ≤ (3675854330651143/10000000000000000000 : ℝ) := by
    have hpowers : (14057/100000 : ℝ)^8255 ≤ (3675854330651143/10000000000000000000 : ℝ)^2048 := by
      have hnat : (14057 : ℕ)^8255*10000000000000000000^2048 ≤ 3675854330651143^2048*100000^8255 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14057 100000 3675854330651143 10000000000000000000 8255 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14057/100000 : ℝ)) (X := (3675854330651143/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8255 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007339329198072773/25000000000000000000 : ℝ) ≤ (10000728251363611/10000000000000000 : ℝ) ^ (8255/2048 : ℝ) := by
    have hpowers : (25007339329198072773/25000000000000000000 : ℝ)^2048 ≤ (10000728251363611/10000000000000000 : ℝ)^8255 := by
      have hnat : (25007339329198072773 : ℕ)^2048*10000000000000000^8255 ≤ 10000728251363611^8255*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007339329198072773 25000000000000000000 10000728251363611 10000000000000000 2048 8255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000728251363611/10000000000000000 : ℝ)) (X := (25007339329198072773/25000000000000000000 : ℝ)) (by norm_num) 8255 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (6253214825106416061/6250000000000000000 : ℝ) ≤ (10001275869459459/10000000000000000 : ℝ) ^ (8255/2048 : ℝ) := by
    have hpowers : (6253214825106416061/6250000000000000000 : ℝ)^2048 ≤ (10001275869459459/10000000000000000 : ℝ)^8255 := by
      have hnat : (6253214825106416061 : ℕ)^2048*10000000000000000^8255 ≤ 10001275869459459^8255*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253214825106416061 6250000000000000000 10001275869459459 10000000000000000 2048 8255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001275869459459/10000000000000000 : ℝ)) (X := (6253214825106416061/6250000000000000000 : ℝ)) (by norm_num) 8255 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003675854330651143/5000000000000000000 : ℝ) ≤ (10001823487555307/10000000000000000 : ℝ) ^ (8255/2048 : ℝ) := by
    have hpowers : (5003675854330651143/5000000000000000000 : ℝ)^2048 ≤ (10001823487555307/10000000000000000 : ℝ)^8255 := by
      have hnat : (5003675854330651143 : ℕ)^2048*10000000000000000^8255 ≤ 10001823487555307^8255*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003675854330651143 5000000000000000000 10001823487555307 10000000000000000 2048 8255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001823487555307/10000000000000000 : ℝ)) (X := (5003675854330651143/5000000000000000000 : ℝ)) (by norm_num) 8255 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7339329198072773/50000000000000000000 : ℝ) ≤ ((28619824909724173269/28630000000000000000 : ℝ)+2*(68452261981/35787500000000 : ℝ)*(5597/50000 : ℝ))^(8255/2048 : ℝ) := by
    rw [show (28619824909724173269/28630000000000000000 : ℝ)+2*(68452261981/35787500000000 : ℝ)*(5597/50000 : ℝ)=(10000728251363611/10000000000000000 : ℝ) by norm_num, show 1+2*(7339329198072773/50000000000000000000 : ℝ)=(25007339329198072773/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3675854330651143/10000000000000000000 : ℝ)+(7339329198072773/50000000000000000000 : ℝ) ≤ ((28619824909724173269/28630000000000000000 : ℝ)+(68452261981/35787500000000 : ℝ)*((14057/100000 : ℝ)+(5597/50000 : ℝ)))^(8255/2048 : ℝ) := by
    rw [show (28619824909724173269/28630000000000000000 : ℝ)+(68452261981/35787500000000 : ℝ)*((14057/100000 : ℝ)+(5597/50000 : ℝ))=(10001275869459459/10000000000000000 : ℝ) by norm_num, show 1+(3675854330651143/10000000000000000000 : ℝ)+(7339329198072773/50000000000000000000 : ℝ)=(6253214825106416061/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3675854330651143/10000000000000000000 : ℝ) ≤ ((28619824909724173269/28630000000000000000 : ℝ)+2*(68452261981/35787500000000 : ℝ)*(14057/100000 : ℝ))^(8255/2048 : ℝ) := by
    rw [show (28619824909724173269/28630000000000000000 : ℝ)+2*(68452261981/35787500000000 : ℝ)*(14057/100000 : ℝ)=(10001823487555307/10000000000000000 : ℝ) by norm_num, show 1+2*(3675854330651143/10000000000000000000 : ℝ)=(5003675854330651143/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (28619824909724173269/28630000000000000000 : ℝ)*(X 1 0+X 2 0)+(68452261981/35787500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8255/2048 : ℝ)) (lo := (5597/50000 : ℝ)) (hi := (14057/100000 : ℝ)) (c := (28619824909724173269/28630000000000000000 : ℝ)) (alpha := (68452261981/35787500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (28619824909724173269/28630000000000000000 : ℝ)*(X 0 1+X 2 1)+(68452261981/35787500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8255/2048 : ℝ)) (lo := (5597/50000 : ℝ)) (hi := (14057/100000 : ℝ)) (c := (28619824909724173269/28630000000000000000 : ℝ)) (alpha := (68452261981/35787500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (28619824909724173269/28630000000000000000 : ℝ)*(X 0 2+X 1 2)+(68452261981/35787500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8255/2048 : ℝ)) (lo := (5597/50000 : ℝ)) (hi := (14057/100000 : ℝ)) (c := (28619824909724173269/28630000000000000000 : ℝ)) (alpha := (68452261981/35787500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2205196119/10000000000 : ℝ)*X 0 0+(2697488113/5000000000 : ℝ)*X 0 1+(5263863809/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((83517621/156250000 : ℝ)*X 1 0+(-454345459/2000000000 : ℝ)*X 1 1+(2631931919/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672563791/5000000000 : ℝ)*X 2 0+(5263863933/10000000000 : ℝ)*X 2 1+(-454345477/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4375895663/10000000000 : ℝ)*X 0 0+(4249401001/10000000000 : ℝ)*X 0 1+(1126552533/2500000000 : ℝ)*X 0 2+(4375895663/10000000000 : ℝ)*X 1 0+(4249401001/10000000000 : ℝ)*X 1 1+(1126552533/2500000000 : ℝ)*X 1 2+(4375895663/10000000000 : ℝ)*X 2 0+(4249401001/10000000000 : ℝ)*X 2 1+(1126552533/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1102600703/5000000000 : ℝ)*X 0 0+(5264195069/10000000000 : ℝ)*X 0 1+(5394643701/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312111047/10000000000 : ℝ)*X 1 0+(-2140947317/10000000000 : ℝ)*X 1 1+(5394643849/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656055377/5000000000 : ℝ)*X 2 0+(5394644191/10000000000 : ℝ)*X 2 1+(-2140947249/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4375905921/10000000000 : ℝ)*X 0 0+(4505561433/10000000000 : ℝ)*X 0 1+(425005199/1000000000 : ℝ)*X 0 2+(4375905921/10000000000 : ℝ)*X 1 0+(4505561433/10000000000 : ℝ)*X 1 1+(425005199/1000000000 : ℝ)*X 1 2+(4375905921/10000000000 : ℝ)*X 2 0+(4505561433/10000000000 : ℝ)*X 2 1+(425005199/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2668893870377842211799/511250000000000000000000000 : ℝ) := by norm_num
    linear_combination (1181029889/100000000000000 : ℝ)*(base19) + (235541501/25000000000000 : ℝ)*(base23) + (1029163/25000000000000 : ℝ)*(lower2) + (223081009/100000000000000 : ℝ)*(upper3) + (16641457/50000000000000 : ℝ)*(upper5) + (5760543199634139/100000000000000 : ℝ)*(major0) + (5760543199634139/100000000000000 : ℝ)*(major1) + (5760543199634139/100000000000000 : ℝ)*(major2) + (1906770329161271/25000000000000 : ℝ)*(sp0) + (762710753963253/10000000000000 : ℝ)*(sp1) + (1525421555699283/20000000000000 : ℝ)*(sp2) + (973489668142459/25000000000000 : ℝ)*(sp3) + (5480803467/20000000000000 : ℝ)*(sp4) + (3766405001/20000000000000 : ℝ)*(sp7) + (1946988752297421/50000000000000 : ℝ)*(f.failure) + (7627108720662419/100000000000000 : ℝ)*(f.sum) + (17397396292681/2045000000000000000000000000 : ℝ)*base65 + (177943268824167087/409000000000000000000000000000000 : ℝ)*base68 + (319532432038832913/409000000000000000000000000000000 : ℝ)*base69 + (6419530989138832913/409000000000000000000000000000000 : ℝ)*base71 + (1445255624401/2045000000000000000000000000 : ℝ)*base73 + (153896662702167087/409000000000000000000000000000000 : ℝ)*base76 + (6977118149248832913/409000000000000000000000000000000 : ℝ)*base77 + (149724762088167087/409000000000000000000000000000000 : ℝ)*base80 + (9376927437981/2045000000000000000000000000 : ℝ)*base81 + (42757701/5000000000000000000000 : ℝ)*base89 + (42757701/5000000000000000000000 : ℝ)*base91 + (42757701/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8876851975924446375252629937/1431500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1387569753/100000000000000 : ℝ)*(base19) + (1077358093/100000000000000 : ℝ)*(base23) + (27056231/100000000000000 : ℝ)*(upper2) + (285911201/100000000000000 : ℝ)*(upper3) + (101667121/100000000000000 : ℝ)*(upper5) + (5789795425844197/100000000000000 : ℝ)*(major0) + (5789795425844197/100000000000000 : ℝ)*(major1) + (5789795425844197/100000000000000 : ℝ)*(major2) + (17837913821/50000000000000 : ℝ)*(sp1) + (44530663/97656250000 : ℝ)*(sp2) + (3832919697822941/50000000000000 : ℝ)*(sp4) + (7665802332248487/100000000000000 : ℝ)*(sp5) + (3832896359444439/50000000000000 : ℝ)*(sp6) + (1956875624669849/50000000000000 : ℝ)*(sp7) + (1956875624669849/50000000000000 : ℝ)*(f.failure) + (3832919697822941/50000000000000 : ℝ)*(f.sum) + (24818976356883/7157500000000000000000000000 : ℝ)*base65 + (6356400540764230007/2863000000000000000000000000000000 : ℝ)*base68 + (60416325836994230007/2863000000000000000000000000000000 : ℝ)*base70 + (36188185740253230007/2863000000000000000000000000000000 : ℝ)*base72 + (40994874952581/14315000000000000000000000000 : ℝ)*base73 + (20393954044745230007/2863000000000000000000000000000000 : ℝ)*base76 + (17145654868770230007/2863000000000000000000000000000000 : ℝ)*base78 + (31948450443932230007/2863000000000000000000000000000000 : ℝ)*base80 + (14521903970257/7157500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (7866831/5000000000000000000000 : ℝ)*base90 + (7866831/5000000000000000000000 : ℝ)*base92 + (7866831/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1063_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147934681/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14057/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5597/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2809/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14013/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1063_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1063_s7_0 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-2205236971/10000000000 : ℝ)*x 0 + (5394507739/10000000000 : ℝ)*x 1 + (2632152721/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2205236971/10000000000 : ℝ)^129 ≤ (1674068406279/12500000000000 : ℝ)^97 := by
    have hnat : (2205236971 : ℕ)^129*12500000000000^97 ≤ 1674068406279^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2205236971 10000000000 1674068406279 12500000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394507739/10000000000 : ℝ)^129 ≤ (44007181560293/100000000000000 : ℝ)^97 := by
    have hnat : (5394507739 : ℕ)^129*100000000000000^97 ≤ 44007181560293^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394507739 10000000000 44007181560293 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632152721/5000000000 : ℝ)^129 ≤ (42600271180391/100000000000000 : ℝ)^97 := by
    have hnat : (2632152721 : ℕ)^129*100000000000000^97 ≤ 42600271180391^97*5000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632152721 5000000000 42600271180391 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2205236971/10000000000 : ℝ), (5394507739/10000000000 : ℝ), (2632152721/5000000000 : ℝ)] ![(1674068406279/12500000000000 : ℝ), (44007181560293/100000000000000 : ℝ), (42600271180391/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2205236971/10000000000 : ℝ)|^129 ≤ (1674068406279/12500000000000 : ℝ)^97
        have hw : |(-2205236971/10000000000 : ℝ)|=(2205236971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394507739/10000000000 : ℝ)|^129 ≤ (44007181560293/100000000000000 : ℝ)^97
        have hw : |(5394507739/10000000000 : ℝ)|=(5394507739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632152721/5000000000 : ℝ)|^129 ≤ (42600271180391/100000000000000 : ℝ)^97
        have hw : |(2632152721/5000000000 : ℝ)|=(2632152721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_s7_1 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2672505307/5000000000 : ℝ)*x 0 + (-2271300367/10000000000 : ℝ)*x 1 + (5264305109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672505307/5000000000 : ℝ)^129 ≤ (43471001651129/100000000000000 : ℝ)^97 := by
    have hnat : (2672505307 : ℕ)^129*100000000000000^97 ≤ 43471001651129^97*5000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672505307 5000000000 43471001651129 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2271300367/10000000000 : ℝ)^129 ≤ (13928730739199/100000000000000 : ℝ)^97 := by
    have hnat : (2271300367 : ℕ)^129*100000000000000^97 ≤ 13928730739199^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2271300367 10000000000 13928730739199 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264305109/10000000000 : ℝ)^129 ≤ (10650066899169/25000000000000 : ℝ)^97 := by
    have hnat : (5264305109 : ℕ)^129*25000000000000^97 ≤ 10650066899169^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264305109 10000000000 10650066899169 25000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672505307/5000000000 : ℝ), (-2271300367/10000000000 : ℝ), (5264305109/10000000000 : ℝ)] ![(43471001651129/100000000000000 : ℝ), (13928730739199/100000000000000 : ℝ), (10650066899169/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672505307/5000000000 : ℝ)|^129 ≤ (43471001651129/100000000000000 : ℝ)^97
        have hw : |(2672505307/5000000000 : ℝ)|=(2672505307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2271300367/10000000000 : ℝ)|^129 ≤ (13928730739199/100000000000000 : ℝ)^97
        have hw : |(-2271300367/10000000000 : ℝ)|=(2271300367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264305109/10000000000 : ℝ)|^129 ≤ (10650066899169/25000000000000 : ℝ)^97
        have hw : |(5264305109/10000000000 : ℝ)|=(5264305109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_s7_2 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5345010537/10000000000 : ℝ)*x 0 + (20563693/39062500 : ℝ)*x 1 + (-1135650037/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345010537/10000000000 : ℝ)^129 ≤ (10867750204573/25000000000000 : ℝ)^97 := by
    have hnat : (5345010537 : ℕ)^129*25000000000000^97 ≤ 10867750204573^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345010537 10000000000 10867750204573 25000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (20563693/39062500 : ℝ)^129 ≤ (21300135407243/50000000000000 : ℝ)^97 := by
    have hnat : (20563693 : ℕ)^129*50000000000000^97 ≤ 21300135407243^97*39062500^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20563693 39062500 21300135407243 50000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1135650037/5000000000 : ℝ)^129 ≤ (6964364174807/50000000000000 : ℝ)^97 := by
    have hnat : (1135650037 : ℕ)^129*50000000000000^97 ≤ 6964364174807^97*5000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1135650037 5000000000 6964364174807 50000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345010537/10000000000 : ℝ), (20563693/39062500 : ℝ), (-1135650037/5000000000 : ℝ)] ![(10867750204573/25000000000000 : ℝ), (21300135407243/50000000000000 : ℝ), (6964364174807/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345010537/10000000000 : ℝ)|^129 ≤ (10867750204573/25000000000000 : ℝ)^97
        have hw : |(5345010537/10000000000 : ℝ)|=(5345010537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(20563693/39062500 : ℝ)|^129 ≤ (21300135407243/50000000000000 : ℝ)^97
        have hw : |(20563693/39062500 : ℝ)|=(20563693/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1135650037/5000000000 : ℝ)|^129 ≤ (6964364174807/50000000000000 : ℝ)^97
        have hw : |(-1135650037/5000000000 : ℝ)|=(1135650037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_s7_3 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2187959621/5000000000 : ℝ)*x 0 + (2125144223/5000000000 : ℝ)*x 1 + (450531629/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2187959621/5000000000 : ℝ)^129 ≤ (33316484575757/100000000000000 : ℝ)^97 := by
    have hnat : (2187959621 : ℕ)^129*100000000000000^97 ≤ 33316484575757^97*5000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187959621 5000000000 33316484575757 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2125144223/5000000000 : ℝ)^129 ≤ (6410099649459/20000000000000 : ℝ)^97 := by
    have hnat : (2125144223 : ℕ)^129*20000000000000^97 ≤ 6410099649459^97*5000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125144223 5000000000 6410099649459 20000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (450531629/1000000000 : ℝ)^129 ≤ (34633017162733/100000000000000 : ℝ)^97 := by
    have hnat : (450531629 : ℕ)^129*100000000000000^97 ≤ 34633017162733^97*1000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450531629 1000000000 34633017162733 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2187959621/5000000000 : ℝ), (2125144223/5000000000 : ℝ), (450531629/1000000000 : ℝ)] ![(33316484575757/100000000000000 : ℝ), (6410099649459/20000000000000 : ℝ), (34633017162733/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2187959621/5000000000 : ℝ)|^129 ≤ (33316484575757/100000000000000 : ℝ)^97
        have hw : |(2187959621/5000000000 : ℝ)|=(2187959621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2125144223/5000000000 : ℝ)|^129 ≤ (6410099649459/20000000000000 : ℝ)^97
        have hw : |(2125144223/5000000000 : ℝ)|=(2125144223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(450531629/1000000000 : ℝ)|^129 ≤ (34633017162733/100000000000000 : ℝ)^97
        have hw : |(450531629/1000000000 : ℝ)|=(450531629/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_s7_4 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-2205242217/10000000000 : ℝ)*x 0 + (5264631689/10000000000 : ℝ)*x 1 + (2697090099/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2205242217/10000000000 : ℝ)^129 ≤ (13392589619831/100000000000000 : ℝ)^97 := by
    have hnat : (2205242217 : ℕ)^129*100000000000000^97 ≤ 13392589619831^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2205242217 10000000000 13392589619831 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264631689/10000000000 : ℝ)^129 ≤ (1065094556409/2500000000000 : ℝ)^97 := by
    have hnat : (5264631689 : ℕ)^129*2500000000000^97 ≤ 1065094556409^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264631689 10000000000 1065094556409 2500000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697090099/5000000000 : ℝ)^129 ≤ (22001814051781/50000000000000 : ℝ)^97 := by
    have hnat : (2697090099 : ℕ)^129*50000000000000^97 ≤ 22001814051781^97*5000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697090099 5000000000 22001814051781 50000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2205242217/10000000000 : ℝ), (5264631689/10000000000 : ℝ), (2697090099/5000000000 : ℝ)] ![(13392589619831/100000000000000 : ℝ), (1065094556409/2500000000000 : ℝ), (22001814051781/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2205242217/10000000000 : ℝ)|^129 ≤ (13392589619831/100000000000000 : ℝ)^97
        have hw : |(-2205242217/10000000000 : ℝ)|=(2205242217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264631689/10000000000 : ℝ)|^129 ≤ (1065094556409/2500000000000 : ℝ)^97
        have hw : |(5264631689/10000000000 : ℝ)|=(5264631689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697090099/5000000000 : ℝ)|^129 ≤ (22001814051781/50000000000000 : ℝ)^97
        have hw : |(2697090099/5000000000 : ℝ)|=(2697090099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_s7_5 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5312223027/10000000000 : ℝ)*x 0 + (-1070712543/5000000000 : ℝ)*x 1 + (5394180199/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312223027/10000000000 : ℝ)^129 ≤ (43116728494661/100000000000000 : ℝ)^97 := by
    have hnat : (5312223027 : ℕ)^129*100000000000000^97 ≤ 43116728494661^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312223027 10000000000 43116728494661 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1070712543/5000000000 : ℝ)^129 ≤ (6439821688211/50000000000000 : ℝ)^97 := by
    have hnat : (1070712543 : ℕ)^129*50000000000000^97 ≤ 6439821688211^97*5000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070712543 5000000000 6439821688211 50000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394180199/10000000000 : ℝ)^129 ≤ (44003628114411/100000000000000 : ℝ)^97 := by
    have hnat : (5394180199 : ℕ)^129*100000000000000^97 ≤ 44003628114411^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394180199 10000000000 44003628114411 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312223027/10000000000 : ℝ), (-1070712543/5000000000 : ℝ), (5394180199/10000000000 : ℝ)] ![(43116728494661/100000000000000 : ℝ), (6439821688211/50000000000000 : ℝ), (44003628114411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312223027/10000000000 : ℝ)|^129 ≤ (43116728494661/100000000000000 : ℝ)^97
        have hw : |(5312223027/10000000000 : ℝ)|=(5312223027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1070712543/5000000000 : ℝ)|^129 ≤ (6439821688211/50000000000000 : ℝ)^97
        have hw : |(-1070712543/5000000000 : ℝ)|=(1070712543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394180199/10000000000 : ℝ)|^129 ≤ (44003628114411/100000000000000 : ℝ)^97
        have hw : |(5394180199/10000000000 : ℝ)|=(5394180199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_s7_6 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5312223027/10000000000 : ℝ)*x 0 + (5394180199/10000000000 : ℝ)*x 1 + (-428285017/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312223027/10000000000 : ℝ)^129 ≤ (43116728494661/100000000000000 : ℝ)^97 := by
    have hnat : (5312223027 : ℕ)^129*100000000000000^97 ≤ 43116728494661^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312223027 10000000000 43116728494661 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394180199/10000000000 : ℝ)^129 ≤ (44003628114411/100000000000000 : ℝ)^97 := by
    have hnat : (5394180199 : ℕ)^129*100000000000000^97 ≤ 44003628114411^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394180199 10000000000 44003628114411 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (428285017/2000000000 : ℝ)^129 ≤ (12879643368423/100000000000000 : ℝ)^97 := by
    have hnat : (428285017 : ℕ)^129*100000000000000^97 ≤ 12879643368423^97*2000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      428285017 2000000000 12879643368423 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312223027/10000000000 : ℝ), (5394180199/10000000000 : ℝ), (-428285017/2000000000 : ℝ)] ![(43116728494661/100000000000000 : ℝ), (44003628114411/100000000000000 : ℝ), (12879643368423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312223027/10000000000 : ℝ)|^129 ≤ (43116728494661/100000000000000 : ℝ)^97
        have hw : |(5312223027/10000000000 : ℝ)|=(5312223027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394180199/10000000000 : ℝ)|^129 ≤ (44003628114411/100000000000000 : ℝ)^97
        have hw : |(5394180199/10000000000 : ℝ)|=(5394180199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-428285017/2000000000 : ℝ)|^129 ≤ (12879643368423/100000000000000 : ℝ)^97
        have hw : |(-428285017/2000000000 : ℝ)|=(428285017/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_s7_7 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1093982237/2500000000 : ℝ)*x 0 + (4504676581/10000000000 : ℝ)*x 1 + (212546537/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1093982237/2500000000 : ℝ)^129 ≤ (16658291425971/50000000000000 : ℝ)^97 := by
    have hnat : (1093982237 : ℕ)^129*50000000000000^97 ≤ 16658291425971^97*2500000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093982237 2500000000 16658291425971 50000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4504676581/10000000000 : ℝ)^129 ≤ (1731323875033/5000000000000 : ℝ)^97 := by
    have hnat : (4504676581 : ℕ)^129*5000000000000^97 ≤ 1731323875033^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4504676581 10000000000 1731323875033 5000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (212546537/500000000 : ℝ)^129 ≤ (32056939629171/100000000000000 : ℝ)^97 := by
    have hnat : (212546537 : ℕ)^129*100000000000000^97 ≤ 32056939629171^97*500000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212546537 500000000 32056939629171 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1093982237/2500000000 : ℝ), (4504676581/10000000000 : ℝ), (212546537/500000000 : ℝ)] ![(16658291425971/50000000000000 : ℝ), (1731323875033/5000000000000 : ℝ), (32056939629171/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1093982237/2500000000 : ℝ)|^129 ≤ (16658291425971/50000000000000 : ℝ)^97
        have hw : |(1093982237/2500000000 : ℝ)|=(1093982237/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4504676581/10000000000 : ℝ)|^129 ≤ (1731323875033/5000000000000 : ℝ)^97
        have hw : |(4504676581/10000000000 : ℝ)|=(4504676581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(212546537/500000000 : ℝ)|^129 ≤ (32056939629171/100000000000000 : ℝ)^97
        have hw : |(212546537/500000000 : ℝ)|=(212546537/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1063_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147934681/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14013/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2809/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2249/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14003/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14013/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2809/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14013/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2809/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14013/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2809/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14013/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2809/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14013/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2809/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14013/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2809/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2809/25000 : ℝ) ^ (8255/2048 : ℝ) ≤ (14901915868803649/100000000000000000000 : ℝ) := by
    have hpowers : (2809/25000 : ℝ)^8255 ≤ (14901915868803649/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2809 : ℕ)^8255*100000000000000000000^2048 ≤ 14901915868803649^2048*25000^8255 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2809 25000 14901915868803649 100000000000000000000 8255 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2809/25000 : ℝ)) (X := (14901915868803649/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8255 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14013/100000 : ℝ) ^ (8255/2048 : ℝ) ≤ (18148482741211133/50000000000000000000 : ℝ) := by
    have hpowers : (14013/100000 : ℝ)^8255 ≤ (18148482741211133/50000000000000000000 : ℝ)^2048 := by
      have hnat : (14013 : ℕ)^8255*50000000000000000000^2048 ≤ 18148482741211133^2048*100000^8255 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14013 100000 18148482741211133 50000000000000000000 8255 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14013/100000 : ℝ)) (X := (18148482741211133/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8255 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014901915868803649/50000000000000000000 : ℝ) ≤ (2500184831645467/2500000000000000 : ℝ) ^ (8255/2048 : ℝ) := by
    have hpowers : (50014901915868803649/50000000000000000000 : ℝ)^2048 ≤ (2500184831645467/2500000000000000 : ℝ)^8255 := by
      have hnat : (50014901915868803649 : ℕ)^2048*2500000000000000^8255 ≤ 2500184831645467^8255*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014901915868803649 50000000000000000000 2500184831645467 2500000000000000 2048 8255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500184831645467/2500000000000000 : ℝ)) (X := (50014901915868803649/50000000000000000000 : ℝ)) (by norm_num) 8255 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20010239776270245183/20000000000000000000 : ℝ) ≤ (200025399184021/200000000000000 : ℝ) ^ (8255/2048 : ℝ) := by
    have hpowers : (20010239776270245183/20000000000000000000 : ℝ)^2048 ≤ (200025399184021/200000000000000 : ℝ)^8255 := by
      have hnat : (20010239776270245183 : ℕ)^2048*200000000000000^8255 ≤ 200025399184021^8255*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20010239776270245183 20000000000000000000 200025399184021 200000000000000 2048 8255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200025399184021/200000000000000 : ℝ)) (X := (20010239776270245183/20000000000000000000 : ℝ)) (by norm_num) 8255 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018148482741211133/25000000000000000000 : ℝ) ≤ (1250225073977529/1250000000000000 : ℝ) ^ (8255/2048 : ℝ) := by
    have hpowers : (25018148482741211133/25000000000000000000 : ℝ)^2048 ≤ (1250225073977529/1250000000000000 : ℝ)^8255 := by
      have hnat : (25018148482741211133 : ℕ)^2048*1250000000000000^8255 ≤ 1250225073977529^8255*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018148482741211133 25000000000000000000 1250225073977529 1250000000000000 2048 8255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250225073977529/1250000000000000 : ℝ)) (X := (25018148482741211133/25000000000000000000 : ℝ)) (by norm_num) 8255 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14901915868803649/100000000000000000000 : ℝ) ≤ ((6940032183424897383/6942500000000000000 : ℝ)+2*(265316309591/138850000000000 : ℝ)*(2809/25000 : ℝ))^(8255/2048 : ℝ) := by
    rw [show (6940032183424897383/6942500000000000000 : ℝ)+2*(265316309591/138850000000000 : ℝ)*(2809/25000 : ℝ)=(2500184831645467/2500000000000000 : ℝ) by norm_num, show 1+2*(14901915868803649/100000000000000000000 : ℝ)=(50014901915868803649/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18148482741211133/50000000000000000000 : ℝ)+(14901915868803649/100000000000000000000 : ℝ) ≤ ((6940032183424897383/6942500000000000000 : ℝ)+(265316309591/138850000000000 : ℝ)*((14013/100000 : ℝ)+(2809/25000 : ℝ)))^(8255/2048 : ℝ) := by
    rw [show (6940032183424897383/6942500000000000000 : ℝ)+(265316309591/138850000000000 : ℝ)*((14013/100000 : ℝ)+(2809/25000 : ℝ))=(200025399184021/200000000000000 : ℝ) by norm_num, show 1+(18148482741211133/50000000000000000000 : ℝ)+(14901915868803649/100000000000000000000 : ℝ)=(20010239776270245183/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18148482741211133/50000000000000000000 : ℝ) ≤ ((6940032183424897383/6942500000000000000 : ℝ)+2*(265316309591/138850000000000 : ℝ)*(14013/100000 : ℝ))^(8255/2048 : ℝ) := by
    rw [show (6940032183424897383/6942500000000000000 : ℝ)+2*(265316309591/138850000000000 : ℝ)*(14013/100000 : ℝ)=(1250225073977529/1250000000000000 : ℝ) by norm_num, show 1+2*(18148482741211133/50000000000000000000 : ℝ)=(25018148482741211133/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6940032183424897383/6942500000000000000 : ℝ)*(X 1 0+X 2 0)+(265316309591/138850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8255/2048 : ℝ)) (lo := (2809/25000 : ℝ)) (hi := (14013/100000 : ℝ)) (c := (6940032183424897383/6942500000000000000 : ℝ)) (alpha := (265316309591/138850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6940032183424897383/6942500000000000000 : ℝ)*(X 0 1+X 2 1)+(265316309591/138850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8255/2048 : ℝ)) (lo := (2809/25000 : ℝ)) (hi := (14013/100000 : ℝ)) (c := (6940032183424897383/6942500000000000000 : ℝ)) (alpha := (265316309591/138850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6940032183424897383/6942500000000000000 : ℝ)*(X 0 2+X 1 2)+(265316309591/138850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8255/2048 : ℝ)) (lo := (2809/25000 : ℝ)) (hi := (14013/100000 : ℝ)) (c := (6940032183424897383/6942500000000000000 : ℝ)) (alpha := (265316309591/138850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2205236971/10000000000 : ℝ)*X 0 0+(5394507739/10000000000 : ℝ)*X 0 1+(2632152721/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672505307/5000000000 : ℝ)*X 1 0+(-2271300367/10000000000 : ℝ)*X 1 1+(5264305109/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345010537/10000000000 : ℝ)*X 2 0+(20563693/39062500 : ℝ)*X 2 1+(-1135650037/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2187959621/5000000000 : ℝ)*X 0 0+(2125144223/5000000000 : ℝ)*X 0 1+(450531629/1000000000 : ℝ)*X 0 2+(2187959621/5000000000 : ℝ)*X 1 0+(2125144223/5000000000 : ℝ)*X 1 1+(450531629/1000000000 : ℝ)*X 1 2+(2187959621/5000000000 : ℝ)*X 2 0+(2125144223/5000000000 : ℝ)*X 2 1+(450531629/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2205242217/10000000000 : ℝ)*X 0 0+(5264631689/10000000000 : ℝ)*X 0 1+(2697090099/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312223027/10000000000 : ℝ)*X 1 0+(-1070712543/5000000000 : ℝ)*X 1 1+(5394180199/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312223027/10000000000 : ℝ)*X 2 0+(5394180199/10000000000 : ℝ)*X 2 1+(-428285017/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1093982237/2500000000 : ℝ)*X 0 0+(4504676581/10000000000 : ℝ)*X 0 1+(212546537/500000000 : ℝ)*X 0 2+(1093982237/2500000000 : ℝ)*X 1 0+(4504676581/10000000000 : ℝ)*X 1 1+(212546537/500000000 : ℝ)*X 1 2+(1093982237/2500000000 : ℝ)*X 2 0+(4504676581/10000000000 : ℝ)*X 2 1+(212546537/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (912408818952970545543479073/86781250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (852419513/50000000000000 : ℝ)*(base19) + (1031370897/100000000000000 : ℝ)*(base23) + (150415171/50000000000000 : ℝ)*(lower2) + (199796249/100000000000000 : ℝ)*(upper3) + (219080819/100000000000000 : ℝ)*(upper5) + (2900397039776477/50000000000000 : ℝ)*(major0) + (2900397039776477/50000000000000 : ℝ)*(major1) + (2900397039776477/50000000000000 : ℝ)*(major2) + (3840187333554993/50000000000000 : ℝ)*(sp0) + (7680400050377273/100000000000000 : ℝ)*(sp1) + (3840200361922701/50000000000000 : ℝ)*(sp2) + (3921162166594491/100000000000000 : ℝ)*(sp3) + (27088106313/100000000000000 : ℝ)*(sp4) + (2388683199/10000000000000 : ℝ)*(sp7) + (1960593026713241/50000000000000 : ℝ)*(f.failure) + (7680401755216299/100000000000000 : ℝ)*(f.sum) + (108845129134647/13885000000000000000000000000 : ℝ)*base66 + (3752946934897265309/347125000000000000000000000000000 : ℝ)*base68 + (4959328945341390309/347125000000000000000000000000000 : ℝ)*base70 + (1535618820725890309/347125000000000000000000000000000 : ℝ)*base72 + (84915497558097/13885000000000000000000000000 : ℝ)*base74 + (2534887830024765309/347125000000000000000000000000000 : ℝ)*base76 + (9158353736326390309/347125000000000000000000000000000 : ℝ)*base78 + (1230865642504609691/347125000000000000000000000000000 : ℝ)*base79 + (4335025734229/6942500000000000000000000000 : ℝ)*base81 + (85811121/5000000000000000000000 : ℝ)*base89 + (85811121/5000000000000000000000 : ℝ)*base91 + (85811121/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1591850661620176664870065839/347125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3336331/390625000000 : ℝ)*(base19) + (7434729/800000000000 : ℝ)*(base23) + (92599799/100000000000000 : ℝ)*(upper3) + (8502783/25000000000000 : ℝ)*(lower4) + (5824879/6250000000000 : ℝ)*(upper5) + (5830033296107189/100000000000000 : ℝ)*(major0) + (5830033296107189/100000000000000 : ℝ)*(major1) + (5830033296107189/100000000000000 : ℝ)*(major2) + (11609444029/50000000000000 : ℝ)*(sp1) + (25036171589/100000000000000 : ℝ)*(sp2) + (308764617414873/4000000000000 : ℝ)*(sp4) + (7719091362383031/100000000000000 : ℝ)*(sp5) + (7719089469859111/100000000000000 : ℝ)*(sp6) + (3940951003982081/100000000000000 : ℝ)*(sp7) + (3940951003982081/100000000000000 : ℝ)*(f.failure) + (308764617414873/4000000000000 : ℝ)*(f.sum) + (41367170034857/13885000000000000000000000000 : ℝ)*base66 + (4974109763976963613/694250000000000000000000000000000 : ℝ)*base68 + (3726381330096036387/694250000000000000000000000000000 : ℝ)*base69 + (5715343745891286387/694250000000000000000000000000000 : ℝ)*base71 + (87105295134067/13885000000000000000000000000 : ℝ)*base74 + (17878796790293213613/694250000000000000000000000000000 : ℝ)*base76 + (796665916277036387/694250000000000000000000000000000 : ℝ)*base77 + (6084019498185036387/694250000000000000000000000000000 : ℝ)*base79 + (15119356980917/13885000000000000000000000000 : ℝ)*base82 + (17548839/10000000000000000000000 : ℝ)*base90 + (17548839/10000000000000000000000 : ℝ)*base92 + (17548839/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1063_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147934681/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14013/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2809/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2249/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14003/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1063_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1063_s8_0 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-2205248009/10000000000 : ℝ)*x 0 + (2697202551/5000000000 : ℝ)*x 1 + (329025039/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2205248009/10000000000 : ℝ)^129 ≤ (13392636399267/100000000000000 : ℝ)^97 := by
    have hnat : (2205248009 : ℕ)^129*100000000000000^97 ≤ 13392636399267^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2205248009 10000000000 13392636399267 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697202551/5000000000 : ℝ)^129 ≤ (44006068054971/100000000000000 : ℝ)^97 := by
    have hnat : (2697202551 : ℕ)^129*100000000000000^97 ≤ 44006068054971^97*5000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697202551 5000000000 44006068054971 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (329025039/625000000 : ℝ)^129 ≤ (21300647761669/50000000000000 : ℝ)^97 := by
    have hnat : (329025039 : ℕ)^129*50000000000000^97 ≤ 21300647761669^97*625000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329025039 625000000 21300647761669 50000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2205248009/10000000000 : ℝ), (2697202551/5000000000 : ℝ), (329025039/625000000 : ℝ)] ![(13392636399267/100000000000000 : ℝ), (44006068054971/100000000000000 : ℝ), (21300647761669/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2205248009/10000000000 : ℝ)|^129 ≤ (13392636399267/100000000000000 : ℝ)^97
        have hw : |(-2205248009/10000000000 : ℝ)|=(2205248009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697202551/5000000000 : ℝ)|^129 ≤ (44006068054971/100000000000000 : ℝ)^97
        have hw : |(2697202551/5000000000 : ℝ)|=(2697202551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(329025039/625000000 : ℝ)|^129 ≤ (21300647761669/50000000000000 : ℝ)^97
        have hw : |(329025039/625000000 : ℝ)|=(329025039/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_s8_1 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5344984501/10000000000 : ℝ)*x 0 + (-2271208937/10000000000 : ℝ)*x 1 + (4112813/7812500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344984501/10000000000 : ℝ)^129 ≤ (8694143842321/20000000000000 : ℝ)^97 := by
    have hnat : (5344984501 : ℕ)^129*20000000000000^97 ≤ 8694143842321^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344984501 10000000000 8694143842321 20000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2271208937/10000000000 : ℝ)^129 ≤ (13927985079307/100000000000000 : ℝ)^97 := by
    have hnat : (2271208937 : ℕ)^129*100000000000000^97 ≤ 13927985079307^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2271208937 10000000000 13927985079307 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4112813/7812500 : ℝ)^129 ≤ (4260129569553/10000000000000 : ℝ)^97 := by
    have hnat : (4112813 : ℕ)^129*10000000000000^97 ≤ 4260129569553^97*7812500^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4112813 7812500 4260129569553 10000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344984501/10000000000 : ℝ), (-2271208937/10000000000 : ℝ), (4112813/7812500 : ℝ)] ![(8694143842321/20000000000000 : ℝ), (13927985079307/100000000000000 : ℝ), (4260129569553/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344984501/10000000000 : ℝ)|^129 ≤ (8694143842321/20000000000000 : ℝ)^97
        have hw : |(5344984501/10000000000 : ℝ)|=(5344984501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2271208937/10000000000 : ℝ)|^129 ≤ (13927985079307/100000000000000 : ℝ)^97
        have hw : |(-2271208937/10000000000 : ℝ)|=(2271208937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4112813/7812500 : ℝ)|^129 ≤ (4260129569553/10000000000000 : ℝ)^97
        have hw : |(4112813/7812500 : ℝ)|=(4112813/7812500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_s8_2 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1336246123/2500000000 : ℝ)*x 0 + (2632200337/5000000000 : ℝ)*x 1 + (-283901113/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336246123/2500000000 : ℝ)^129 ≤ (43470719114261/100000000000000 : ℝ)^97 := by
    have hnat : (1336246123 : ℕ)^129*100000000000000^97 ≤ 43470719114261^97*2500000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336246123 2500000000 43470719114261 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632200337/5000000000 : ℝ)^129 ≤ (42601296061437/100000000000000 : ℝ)^97 := by
    have hnat : (2632200337 : ℕ)^129*100000000000000^97 ≤ 42601296061437^97*5000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632200337 5000000000 42601296061437 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (283901113/1250000000 : ℝ)^129 ≤ (217624762659/1562500000000 : ℝ)^97 := by
    have hnat : (283901113 : ℕ)^129*1562500000000^97 ≤ 217624762659^97*1250000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283901113 1250000000 217624762659 1562500000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336246123/2500000000 : ℝ), (2632200337/5000000000 : ℝ), (-283901113/1250000000 : ℝ)] ![(43470719114261/100000000000000 : ℝ), (42601296061437/100000000000000 : ℝ), (217624762659/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336246123/2500000000 : ℝ)|^129 ≤ (43470719114261/100000000000000 : ℝ)^97
        have hw : |(1336246123/2500000000 : ℝ)|=(1336246123/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632200337/5000000000 : ℝ)|^129 ≤ (42601296061437/100000000000000 : ℝ)^97
        have hw : |(2632200337/5000000000 : ℝ)|=(2632200337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-283901113/1250000000 : ℝ)|^129 ≤ (217624762659/1562500000000 : ℝ)^97
        have hw : |(-283901113/1250000000 : ℝ)|=(283901113/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_s8_3 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4375924003/10000000000 : ℝ)*x 0 + (4250482413/10000000000 : ℝ)*x 1 + (2252560649/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4375924003/10000000000 : ℝ)^129 ≤ (33316532782313/100000000000000 : ℝ)^97 := by
    have hnat : (4375924003 : ℕ)^129*100000000000000^97 ≤ 33316532782313^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4375924003 10000000000 33316532782313 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4250482413/10000000000 : ℝ)^129 ≤ (8013110863183/25000000000000 : ℝ)^97 := by
    have hnat : (4250482413 : ℕ)^129*25000000000000^97 ≤ 8013110863183^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4250482413 10000000000 8013110863183 25000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2252560649/5000000000 : ℝ)^129 ≤ (2164438984523/6250000000000 : ℝ)^97 := by
    have hnat : (2252560649 : ℕ)^129*6250000000000^97 ≤ 2164438984523^97*5000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252560649 5000000000 2164438984523 6250000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4375924003/10000000000 : ℝ), (4250482413/10000000000 : ℝ), (2252560649/5000000000 : ℝ)] ![(33316532782313/100000000000000 : ℝ), (8013110863183/25000000000000 : ℝ), (2164438984523/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4375924003/10000000000 : ℝ)|^129 ≤ (33316532782313/100000000000000 : ℝ)^97
        have hw : |(4375924003/10000000000 : ℝ)|=(4375924003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4250482413/10000000000 : ℝ)|^129 ≤ (8013110863183/25000000000000 : ℝ)^97
        have hw : |(4250482413/10000000000 : ℝ)|=(4250482413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2252560649/5000000000 : ℝ)|^129 ≤ (2164438984523/6250000000000 : ℝ)^97
        have hw : |(2252560649/5000000000 : ℝ)|=(2252560649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_s8_4 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-2205252677/10000000000 : ℝ)*x 0 + (1052945281/2000000000 : ℝ)*x 1 + (5394078451/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2205252677/10000000000 : ℝ)^129 ≤ (13392674100679/100000000000000 : ℝ)^97 := by
    have hnat : (2205252677 : ℕ)^129*100000000000000^97 ≤ 13392674100679^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2205252677 10000000000 13392674100679 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052945281/2000000000 : ℝ)^129 ≤ (42604801605067/100000000000000 : ℝ)^97 := by
    have hnat : (1052945281 : ℕ)^129*100000000000000^97 ≤ 42604801605067^97*2000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052945281 2000000000 42604801605067 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394078451/10000000000 : ℝ)^129 ≤ (44002524275901/100000000000000 : ℝ)^97 := by
    have hnat : (5394078451 : ℕ)^129*100000000000000^97 ≤ 44002524275901^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394078451 10000000000 44002524275901 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2205252677/10000000000 : ℝ), (1052945281/2000000000 : ℝ), (5394078451/10000000000 : ℝ)] ![(13392674100679/100000000000000 : ℝ), (42604801605067/100000000000000 : ℝ), (44002524275901/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2205252677/10000000000 : ℝ)|^129 ≤ (13392674100679/100000000000000 : ℝ)^97
        have hw : |(-2205252677/10000000000 : ℝ)|=(2205252677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1052945281/2000000000 : ℝ)|^129 ≤ (42604801605067/100000000000000 : ℝ)^97
        have hw : |(1052945281/2000000000 : ℝ)|=(1052945281/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394078451/10000000000 : ℝ)|^129 ≤ (44002524275901/100000000000000 : ℝ)^97
        have hw : |(5394078451/10000000000 : ℝ)|=(5394078451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_s8_5 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5312246593/10000000000 : ℝ)*x 0 + (-214153189/1000000000 : ℝ)*x 1 + (2697039003/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312246593/10000000000 : ℝ)^129 ≤ (43116982869217/100000000000000 : ℝ)^97 := by
    have hnat : (5312246593 : ℕ)^129*100000000000000^97 ≤ 43116982869217^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312246593 10000000000 43116982869217 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (214153189/1000000000 : ℝ)^129 ≤ (644024883783/5000000000000 : ℝ)^97 := by
    have hnat : (214153189 : ℕ)^129*5000000000000^97 ≤ 644024883783^97*1000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214153189 1000000000 644024883783 5000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697039003/5000000000 : ℝ)^129 ≤ (44002519448223/100000000000000 : ℝ)^97 := by
    have hnat : (2697039003 : ℕ)^129*100000000000000^97 ≤ 44002519448223^97*5000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697039003 5000000000 44002519448223 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312246593/10000000000 : ℝ), (-214153189/1000000000 : ℝ), (2697039003/5000000000 : ℝ)] ![(43116982869217/100000000000000 : ℝ), (644024883783/5000000000000 : ℝ), (44002519448223/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312246593/10000000000 : ℝ)|^129 ≤ (43116982869217/100000000000000 : ℝ)^97
        have hw : |(5312246593/10000000000 : ℝ)|=(5312246593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-214153189/1000000000 : ℝ)|^129 ≤ (644024883783/5000000000000 : ℝ)^97
        have hw : |(-214153189/1000000000 : ℝ)|=(214153189/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697039003/5000000000 : ℝ)|^129 ≤ (44002519448223/100000000000000 : ℝ)^97
        have hw : |(2697039003/5000000000 : ℝ)|=(2697039003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_s8_6 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5312247657/10000000000 : ℝ)*x 0 + (2697038959/5000000000 : ℝ)*x 1 + (-2141530573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312247657/10000000000 : ℝ)^129 ≤ (5389624294273/12500000000000 : ℝ)^97 := by
    have hnat : (5312247657 : ℕ)^129*12500000000000^97 ≤ 5389624294273^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312247657 10000000000 5389624294273 12500000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697038959/5000000000 : ℝ)^129 ≤ (1375078702923/3125000000000 : ℝ)^97 := by
    have hnat : (2697038959 : ℕ)^129*3125000000000^97 ≤ 1375078702923^97*5000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697038959 5000000000 1375078702923 3125000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2141530573/10000000000 : ℝ)^129 ≤ (12880487141211/100000000000000 : ℝ)^97 := by
    have hnat : (2141530573 : ℕ)^129*100000000000000^97 ≤ 12880487141211^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2141530573 10000000000 12880487141211 100000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312247657/10000000000 : ℝ), (2697038959/5000000000 : ℝ), (-2141530573/10000000000 : ℝ)] ![(5389624294273/12500000000000 : ℝ), (1375078702923/3125000000000 : ℝ), (12880487141211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312247657/10000000000 : ℝ)|^129 ≤ (5389624294273/12500000000000 : ℝ)^97
        have hw : |(5312247657/10000000000 : ℝ)|=(5312247657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697038959/5000000000 : ℝ)|^129 ≤ (1375078702923/3125000000000 : ℝ)^97
        have hw : |(2697038959/5000000000 : ℝ)|=(2697038959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2141530573/10000000000 : ℝ)|^129 ≤ (12880487141211/100000000000000 : ℝ)^97
        have hw : |(-2141530573/10000000000 : ℝ)|=(2141530573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1063_s8_7 (p : ℝ) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4375934161/10000000000 : ℝ)*x 0 + (4504483811/10000000000 : ℝ)*x 1 + (4251121967/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4375934161/10000000000 : ℝ)^129 ≤ (16658317817587/50000000000000 : ℝ)^97 := by
    have hnat : (4375934161 : ℕ)^129*50000000000000^97 ≤ 16658317817587^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4375934161 10000000000 16658317817587 50000000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4504483811/10000000000 : ℝ)^129 ≤ (865612672451/2500000000000 : ℝ)^97 := by
    have hnat : (4504483811 : ℕ)^129*2500000000000^97 ≤ 865612672451^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4504483811 10000000000 865612672451 2500000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4251121967/10000000000 : ℝ)^129 ≤ (1001839295369/3125000000000 : ℝ)^97 := by
    have hnat : (4251121967 : ℕ)^129*3125000000000^97 ≤ 1001839295369^97*10000000000^129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4251121967 10000000000 1001839295369 3125000000000 129 97 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (129/32 : ℝ)) 129 97 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4375934161/10000000000 : ℝ), (4504483811/10000000000 : ℝ), (4251121967/10000000000 : ℝ)] ![(16658317817587/50000000000000 : ℝ), (865612672451/2500000000000 : ℝ), (1001839295369/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4375934161/10000000000 : ℝ)|^129 ≤ (16658317817587/50000000000000 : ℝ)^97
        have hw : |(4375934161/10000000000 : ℝ)|=(4375934161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4504483811/10000000000 : ℝ)|^129 ≤ (865612672451/2500000000000 : ℝ)^97
        have hw : |(4504483811/10000000000 : ℝ)|=(4504483811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4251121967/10000000000 : ℝ)|^129 ≤ (1001839295369/3125000000000 : ℝ)^97
        have hw : |(4251121967/10000000000 : ℝ)|=(4251121967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1063_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147934681/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14003/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2249/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (11247/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14001/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14003/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2249/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14003/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2249/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14003/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2249/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14003/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2249/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14003/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2249/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14003/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2249/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2249/20000 : ℝ) ^ (8255/2048 : ℝ) ≤ (14950087031677521/100000000000000000000 : ℝ) := by
    have hpowers : (2249/20000 : ℝ)^8255 ≤ (14950087031677521/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2249 : ℕ)^8255*100000000000000000000^2048 ≤ 14950087031677521^2048*20000^8255 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2249 20000 14950087031677521 100000000000000000000 8255 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2249/20000 : ℝ)) (X := (14950087031677521/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8255 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14003/100000 : ℝ) ^ (8255/2048 : ℝ) ≤ (1809633606304843/5000000000000000000 : ℝ) := by
    have hpowers : (14003/100000 : ℝ)^8255 ≤ (1809633606304843/5000000000000000000 : ℝ)^2048 := by
      have hnat : (14003 : ℕ)^8255*5000000000000000000^2048 ≤ 1809633606304843^2048*100000^8255 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14003 100000 1809633606304843 5000000000000000000 8255 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14003/100000 : ℝ)) (X := (1809633606304843/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8255 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014950087031677521/50000000000000000000 : ℝ) ≤ (10000741716222169/10000000000000000 : ℝ) ^ (8255/2048 : ℝ) := by
    have hpowers : (50014950087031677521/50000000000000000000 : ℝ)^2048 ≤ (10000741716222169/10000000000000000 : ℝ)^8255 := by
      have hnat : (50014950087031677521 : ℕ)^2048*10000000000000000^8255 ≤ 10000741716222169^8255*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014950087031677521 50000000000000000000 10000741716222169 10000000000000000 2048 8255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000741716222169/10000000000000000 : ℝ)) (X := (50014950087031677521/50000000000000000000 : ℝ)) (by norm_num) 8255 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051142759157774381/100000000000000000000 : ℝ) ≤ (10001268567389437/10000000000000000 : ℝ) ^ (8255/2048 : ℝ) := by
    have hpowers : (100051142759157774381/100000000000000000000 : ℝ)^2048 ≤ (10001268567389437/10000000000000000 : ℝ)^8255 := by
      have hnat : (100051142759157774381 : ℕ)^2048*10000000000000000^8255 ≤ 10001268567389437^8255*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051142759157774381 100000000000000000000 10001268567389437 10000000000000000 2048 8255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001268567389437/10000000000000000 : ℝ)) (X := (100051142759157774381/100000000000000000000 : ℝ)) (by norm_num) 8255 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501809633606304843/2500000000000000000 : ℝ) ≤ (2000359083711341/2000000000000000 : ℝ) ^ (8255/2048 : ℝ) := by
    have hpowers : (2501809633606304843/2500000000000000000 : ℝ)^2048 ≤ (2000359083711341/2000000000000000 : ℝ)^8255 := by
      have hnat : (2501809633606304843 : ℕ)^2048*2000000000000000^8255 ≤ 2000359083711341^8255*2500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501809633606304843 2500000000000000000 2000359083711341 2000000000000000 2048 8255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000359083711341/2000000000000000 : ℝ)) (X := (2501809633606304843/2500000000000000000 : ℝ)) (by norm_num) 8255 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14950087031677521/100000000000000000000 : ℝ) ≤ ((13785098385294442391/13790000000000000000 : ℝ)+2*(131712791817/68950000000000 : ℝ)*(2249/20000 : ℝ))^(8255/2048 : ℝ) := by
    rw [show (13785098385294442391/13790000000000000000 : ℝ)+2*(131712791817/68950000000000 : ℝ)*(2249/20000 : ℝ)=(10000741716222169/10000000000000000 : ℝ) by norm_num, show 1+2*(14950087031677521/100000000000000000000 : ℝ)=(50014950087031677521/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1809633606304843/5000000000000000000 : ℝ)+(14950087031677521/100000000000000000000 : ℝ) ≤ ((13785098385294442391/13790000000000000000 : ℝ)+(131712791817/68950000000000 : ℝ)*((14003/100000 : ℝ)+(2249/20000 : ℝ)))^(8255/2048 : ℝ) := by
    rw [show (13785098385294442391/13790000000000000000 : ℝ)+(131712791817/68950000000000 : ℝ)*((14003/100000 : ℝ)+(2249/20000 : ℝ))=(10001268567389437/10000000000000000 : ℝ) by norm_num, show 1+(1809633606304843/5000000000000000000 : ℝ)+(14950087031677521/100000000000000000000 : ℝ)=(100051142759157774381/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1809633606304843/5000000000000000000 : ℝ) ≤ ((13785098385294442391/13790000000000000000 : ℝ)+2*(131712791817/68950000000000 : ℝ)*(14003/100000 : ℝ))^(8255/2048 : ℝ) := by
    rw [show (13785098385294442391/13790000000000000000 : ℝ)+2*(131712791817/68950000000000 : ℝ)*(14003/100000 : ℝ)=(2000359083711341/2000000000000000 : ℝ) by norm_num, show 1+2*(1809633606304843/5000000000000000000 : ℝ)=(2501809633606304843/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13785098385294442391/13790000000000000000 : ℝ)*(X 1 0+X 2 0)+(131712791817/68950000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8255/2048 : ℝ)) (lo := (2249/20000 : ℝ)) (hi := (14003/100000 : ℝ)) (c := (13785098385294442391/13790000000000000000 : ℝ)) (alpha := (131712791817/68950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13785098385294442391/13790000000000000000 : ℝ)*(X 0 1+X 2 1)+(131712791817/68950000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8255/2048 : ℝ)) (lo := (2249/20000 : ℝ)) (hi := (14003/100000 : ℝ)) (c := (13785098385294442391/13790000000000000000 : ℝ)) (alpha := (131712791817/68950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13785098385294442391/13790000000000000000 : ℝ)*(X 0 2+X 1 2)+(131712791817/68950000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8255/2048 : ℝ)) (lo := (2249/20000 : ℝ)) (hi := (14003/100000 : ℝ)) (c := (13785098385294442391/13790000000000000000 : ℝ)) (alpha := (131712791817/68950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2205248009/10000000000 : ℝ)*X 0 0+(2697202551/5000000000 : ℝ)*X 0 1+(329025039/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344984501/10000000000 : ℝ)*X 1 0+(-2271208937/10000000000 : ℝ)*X 1 1+(4112813/7812500 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336246123/2500000000 : ℝ)*X 2 0+(2632200337/5000000000 : ℝ)*X 2 1+(-283901113/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4375924003/10000000000 : ℝ)*X 0 0+(4250482413/10000000000 : ℝ)*X 0 1+(2252560649/5000000000 : ℝ)*X 0 2+(4375924003/10000000000 : ℝ)*X 1 0+(4250482413/10000000000 : ℝ)*X 1 1+(2252560649/5000000000 : ℝ)*X 1 2+(4375924003/10000000000 : ℝ)*X 2 0+(4250482413/10000000000 : ℝ)*X 2 1+(2252560649/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2205252677/10000000000 : ℝ)*X 0 0+(1052945281/2000000000 : ℝ)*X 0 1+(5394078451/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312246593/10000000000 : ℝ)*X 1 0+(-214153189/1000000000 : ℝ)*X 1 1+(2697039003/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312247657/10000000000 : ℝ)*X 2 0+(2697038959/5000000000 : ℝ)*X 2 1+(-2141530573/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4375934161/10000000000 : ℝ)*X 0 0+(4504483811/10000000000 : ℝ)*X 0 1+(4251121967/10000000000 : ℝ)*X 0 2+(4375934161/10000000000 : ℝ)*X 1 0+(4504483811/10000000000 : ℝ)*X 1 1+(4251121967/10000000000 : ℝ)*X 1 2+(4375934161/10000000000 : ℝ)*X 2 0+(4504483811/10000000000 : ℝ)*X 2 1+(4251121967/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1063_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (408433730435983680441706461/43093750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (922312361/50000000000000 : ℝ)*(base19) + (1774824013/100000000000000 : ℝ)*(base23) + (30385441/100000000000000 : ℝ)*(lower2) + (195993751/100000000000000 : ℝ)*(upper3) + (203024467/100000000000000 : ℝ)*(upper5) + (726208188111243/12500000000000 : ℝ)*(major0) + (726208188111243/12500000000000 : ℝ)*(major1) + (726208188111243/12500000000000 : ℝ)*(major2) + (384604729495317/5000000000000 : ℝ)*(sp0) + (961518242851843/12500000000000 : ℝ)*(sp1) + (3846073006307727/50000000000000 : ℝ)*(sp2) + (3927156328731651/100000000000000 : ℝ)*(sp3) + (53197533127/100000000000000 : ℝ)*(sp4) + (26577682257/100000000000000 : ℝ)*(sp7) + (3927182906413909/100000000000000 : ℝ)*(f.failure) + (7692147787439467/100000000000000 : ℝ)*(f.sum) + (4424628269949/6895000000000000000000000000 : ℝ)*base66 + (866842964557227013/172375000000000000000000000000000 : ℝ)*base67 + (2675817827923352013/172375000000000000000000000000000 : ℝ)*base69 + (231879193011647987/172375000000000000000000000000000 : ℝ)*base72 + (28437199753/3447500000000000000000000000 : ℝ)*base73 + (1881490777421227013/172375000000000000000000000000000 : ℝ)*base75 + (1665063446426352013/172375000000000000000000000000000 : ℝ)*base77 + (5044669831444852013/172375000000000000000000000000000 : ℝ)*base79 + (19013905080101/6895000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (81878029/10000000000000000000000 : ℝ)*base89 + (81878029/10000000000000000000000 : ℝ)*base91 + (81878029/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (231975753600098714151504621/49250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (37345797/5000000000000 : ℝ)*(base19) + (2243054809/100000000000000 : ℝ)*(base23) + (169029033/50000000000000 : ℝ)*(lower2) + (11523697/20000000000000 : ℝ)*(lower4) + (740917/6250000000000 : ℝ)*(lower5) + (5838910186193761/100000000000000 : ℝ)*(major0) + (5838910186193761/100000000000000 : ℝ)*(major1) + (5838910186193761/100000000000000 : ℝ)*(major2) + (9647437349/12500000000000 : ℝ)*(sp2) + (3373539717/50000000000000 : ℝ)*(sp3) + (3865434332191853/50000000000000 : ℝ)*(sp4) + (3865433958733883/50000000000000 : ℝ)*(sp5) + (1546157848366021/20000000000000 : ℝ)*(sp6) + (197347240195939/5000000000000 : ℝ)*(sp7) + (1973475775499107/50000000000000 : ℝ)*(f.failure) + (3865434332191853/50000000000000 : ℝ)*(f.sum) + (84882321077963/3447500000000000000000000000 : ℝ)*base66 + (34810109385917522551/1379000000000000000000000000000000 : ℝ)*base67 + (16768896129683522551/1379000000000000000000000000000000 : ℝ)*base69 + (12260259284554477449/1379000000000000000000000000000000 : ℝ)*base72 + (10967871169271/1723750000000000000000000000 : ℝ)*base73 + (16680040002673522551/1379000000000000000000000000000000 : ℝ)*base75 + (28930158494676522551/1379000000000000000000000000000000 : ℝ)*base77 + (6064647166345522551/1379000000000000000000000000000000 : ℝ)*base79 + (21715647152331/6895000000000000000000000000 : ℝ)*base82 + (40170133/5000000000000000000000 : ℝ)*base90 + (40170133/5000000000000000000000 : ℝ)*base92 + (40170133/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1063_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147934681/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14003/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2249/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11247/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14001/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1063_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1063_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147934681/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14057/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5597/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11247/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14001/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1063_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1063_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1063_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8255/2048 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147934681/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14057/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5597/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11247/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14001/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1063_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
