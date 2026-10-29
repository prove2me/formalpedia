-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1605_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:48:43.225459+00:00
-- url     : https://prove2.me/submissions/6bb634e1-789d-4359-8ed8-686ab340a3e6

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
theorem support_rectangle_w1605_s0_0 (p : ℝ) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-315003151/2000000000 : ℝ)*x 0 + (730491137/1250000000 : ℝ)*x 1 + (1222311137/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (315003151/2000000000 : ℝ)^4739 ≤ (9462917955429/100000000000000 : ℝ)^3715 := by
    have hnat : (315003151 : ℕ)^4739*100000000000000^3715 ≤ 9462917955429^3715*2000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      315003151 2000000000 9462917955429 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (730491137/1250000000 : ℝ)^4739 ≤ (12599103948867/25000000000000 : ℝ)^3715 := by
    have hnat : (730491137 : ℕ)^4739*25000000000000^3715 ≤ 12599103948867^3715*1250000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      730491137 1250000000 12599103948867 25000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1222311137/2500000000 : ℝ)^4739 ≤ (20070333117023/50000000000000 : ℝ)^3715 := by
    have hnat : (1222311137 : ℕ)^4739*50000000000000^3715 ≤ 20070333117023^3715*2500000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1222311137 2500000000 20070333117023 50000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4739/1024 : ℝ)) 4739 3715 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-315003151/2000000000 : ℝ), (730491137/1250000000 : ℝ), (1222311137/2500000000 : ℝ)] ![(9462917955429/100000000000000 : ℝ), (12599103948867/25000000000000 : ℝ), (20070333117023/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-315003151/2000000000 : ℝ)|^4739 ≤ (9462917955429/100000000000000 : ℝ)^3715
        have hw : |(-315003151/2000000000 : ℝ)|=(315003151/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(730491137/1250000000 : ℝ)|^4739 ≤ (12599103948867/25000000000000 : ℝ)^3715
        have hw : |(730491137/1250000000 : ℝ)|=(730491137/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1222311137/2500000000 : ℝ)|^4739 ≤ (20070333117023/50000000000000 : ℝ)^3715
        have hw : |(1222311137/2500000000 : ℝ)|=(1222311137/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1605_s0_1 (p : ℝ) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (681972933/1250000000 : ℝ)*x 0 + (-2104192767/10000000000 : ℝ)*x 1 + (152788887/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (681972933/1250000000 : ℝ)^4739 ≤ (46166250879291/100000000000000 : ℝ)^3715 := by
    have hnat : (681972933 : ℕ)^4739*100000000000000^3715 ≤ 46166250879291^3715*1250000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      681972933 1250000000 46166250879291 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2104192767/10000000000 : ℝ)^4739 ≤ (13693084583283/100000000000000 : ℝ)^3715 := by
    have hnat : (2104192767 : ℕ)^4739*100000000000000^3715 ≤ 13693084583283^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2104192767 10000000000 13693084583283 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (152788887/312500000 : ℝ)^4739 ≤ (10035166129119/25000000000000 : ℝ)^3715 := by
    have hnat : (152788887 : ℕ)^4739*25000000000000^3715 ≤ 10035166129119^3715*312500000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      152788887 312500000 10035166129119 25000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4739/1024 : ℝ)) 4739 3715 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(681972933/1250000000 : ℝ), (-2104192767/10000000000 : ℝ), (152788887/312500000 : ℝ)] ![(46166250879291/100000000000000 : ℝ), (13693084583283/100000000000000 : ℝ), (10035166129119/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(681972933/1250000000 : ℝ)|^4739 ≤ (46166250879291/100000000000000 : ℝ)^3715
        have hw : |(681972933/1250000000 : ℝ)|=(681972933/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2104192767/10000000000 : ℝ)|^4739 ≤ (13693084583283/100000000000000 : ℝ)^3715
        have hw : |(-2104192767/10000000000 : ℝ)|=(2104192767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(152788887/312500000 : ℝ)|^4739 ≤ (10035166129119/25000000000000 : ℝ)^3715
        have hw : |(152788887/312500000 : ℝ)|=(152788887/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1605_s0_2 (p : ℝ) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1363945831/2500000000 : ℝ)*x 0 + (244462223/500000000 : ℝ)*x 1 + (-2104192853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1363945831/2500000000 : ℝ)^4739 ≤ (23083124684043/50000000000000 : ℝ)^3715 := by
    have hnat : (1363945831 : ℕ)^4739*50000000000000^3715 ≤ 23083124684043^3715*2500000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1363945831 2500000000 23083124684043 50000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (244462223/500000000 : ℝ)^4739 ≤ (40140665312423/100000000000000 : ℝ)^3715 := by
    have hnat : (244462223 : ℕ)^4739*100000000000000^3715 ≤ 40140665312423^3715*500000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      244462223 500000000 40140665312423 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2104192853/10000000000 : ℝ)^4739 ≤ (13693085297191/100000000000000 : ℝ)^3715 := by
    have hnat : (2104192853 : ℕ)^4739*100000000000000^3715 ≤ 13693085297191^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2104192853 10000000000 13693085297191 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4739/1024 : ℝ)) 4739 3715 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1363945831/2500000000 : ℝ), (244462223/500000000 : ℝ), (-2104192853/10000000000 : ℝ)] ![(23083124684043/50000000000000 : ℝ), (40140665312423/100000000000000 : ℝ), (13693085297191/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1363945831/2500000000 : ℝ)|^4739 ≤ (23083124684043/50000000000000 : ℝ)^3715
        have hw : |(1363945831/2500000000 : ℝ)|=(1363945831/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(244462223/500000000 : ℝ)|^4739 ≤ (40140665312423/100000000000000 : ℝ)^3715
        have hw : |(244462223/500000000 : ℝ)|=(244462223/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2104192853/10000000000 : ℝ)|^4739 ≤ (13693085297191/100000000000000 : ℝ)^3715
        have hw : |(-2104192853/10000000000 : ℝ)|=(2104192853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1605_s0_3 (p : ℝ) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4112241869/10000000000 : ℝ)*x 0 + (3073505131/10000000000 : ℝ)*x 1 + (5404053697/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4112241869/10000000000 : ℝ)^4739 ≤ (6437741817901/20000000000000 : ℝ)^3715 := by
    have hnat : (4112241869 : ℕ)^4739*20000000000000^3715 ≤ 6437741817901^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4112241869 10000000000 6437741817901 20000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3073505131/10000000000 : ℝ)^4739 ≤ (22202696428317/100000000000000 : ℝ)^3715 := by
    have hnat : (3073505131 : ℕ)^4739*100000000000000^3715 ≤ 22202696428317^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3073505131 10000000000 22202696428317 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5404053697/10000000000 : ℝ)^4739 ≤ (11402148616667/25000000000000 : ℝ)^3715 := by
    have hnat : (5404053697 : ℕ)^4739*25000000000000^3715 ≤ 11402148616667^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404053697 10000000000 11402148616667 25000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4739/1024 : ℝ)) 4739 3715 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4112241869/10000000000 : ℝ), (3073505131/10000000000 : ℝ), (5404053697/10000000000 : ℝ)] ![(6437741817901/20000000000000 : ℝ), (22202696428317/100000000000000 : ℝ), (11402148616667/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4112241869/10000000000 : ℝ)|^4739 ≤ (6437741817901/20000000000000 : ℝ)^3715
        have hw : |(4112241869/10000000000 : ℝ)|=(4112241869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3073505131/10000000000 : ℝ)|^4739 ≤ (22202696428317/100000000000000 : ℝ)^3715
        have hw : |(3073505131/10000000000 : ℝ)|=(3073505131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5404053697/10000000000 : ℝ)|^4739 ≤ (11402148616667/25000000000000 : ℝ)^3715
        have hw : |(5404053697/10000000000 : ℝ)|=(5404053697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1605_s0_4 (p : ℝ) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-315575511/2000000000 : ℝ)*x 0 + (4913466303/10000000000 : ℝ)*x 1 + (5818844499/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (315575511/2000000000 : ℝ)^4739 ≤ (4742428457709/50000000000000 : ℝ)^3715 := by
    have hnat : (315575511 : ℕ)^4739*50000000000000^3715 ≤ 4742428457709^3715*2000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      315575511 2000000000 4742428457709 50000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4913466303/10000000000 : ℝ)^4739 ≤ (10098628359271/25000000000000 : ℝ)^3715 := by
    have hnat : (4913466303 : ℕ)^4739*25000000000000^3715 ≤ 10098628359271^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4913466303 10000000000 10098628359271 25000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5818844499/10000000000 : ℝ)^4739 ≤ (25060314817553/50000000000000 : ℝ)^3715 := by
    have hnat : (5818844499 : ℕ)^4739*50000000000000^3715 ≤ 25060314817553^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5818844499 10000000000 25060314817553 50000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4739/1024 : ℝ)) 4739 3715 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-315575511/2000000000 : ℝ), (4913466303/10000000000 : ℝ), (5818844499/10000000000 : ℝ)] ![(4742428457709/50000000000000 : ℝ), (10098628359271/25000000000000 : ℝ), (25060314817553/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-315575511/2000000000 : ℝ)|^4739 ≤ (4742428457709/50000000000000 : ℝ)^3715
        have hw : |(-315575511/2000000000 : ℝ)|=(315575511/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4913466303/10000000000 : ℝ)|^4739 ≤ (10098628359271/25000000000000 : ℝ)^3715
        have hw : |(4913466303/10000000000 : ℝ)|=(4913466303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5818844499/10000000000 : ℝ)|^4739 ≤ (25060314817553/50000000000000 : ℝ)^3715
        have hw : |(5818844499/10000000000 : ℝ)|=(5818844499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1605_s0_5 (p : ℝ) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2597517747/5000000000 : ℝ)*x 0 + (-1174591889/10000000000 : ℝ)*x 1 + (2909422427/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2597517747/5000000000 : ℝ)^4739 ≤ (21685205491509/50000000000000 : ℝ)^3715 := by
    have hnat : (2597517747 : ℕ)^4739*50000000000000^3715 ≤ 21685205491509^3715*5000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2597517747 5000000000 21685205491509 50000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1174591889/10000000000 : ℝ)^4739 ≤ (1301791094343/20000000000000 : ℝ)^3715 := by
    have hnat : (1174591889 : ℕ)^4739*20000000000000^3715 ≤ 1301791094343^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1174591889 10000000000 1301791094343 20000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2909422427/5000000000 : ℝ)^4739 ≤ (12530158383937/25000000000000 : ℝ)^3715 := by
    have hnat : (2909422427 : ℕ)^4739*25000000000000^3715 ≤ 12530158383937^3715*5000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2909422427 5000000000 12530158383937 25000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4739/1024 : ℝ)) 4739 3715 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2597517747/5000000000 : ℝ), (-1174591889/10000000000 : ℝ), (2909422427/5000000000 : ℝ)] ![(21685205491509/50000000000000 : ℝ), (1301791094343/20000000000000 : ℝ), (12530158383937/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2597517747/5000000000 : ℝ)|^4739 ≤ (21685205491509/50000000000000 : ℝ)^3715
        have hw : |(2597517747/5000000000 : ℝ)|=(2597517747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1174591889/10000000000 : ℝ)|^4739 ≤ (1301791094343/20000000000000 : ℝ)^3715
        have hw : |(-1174591889/10000000000 : ℝ)|=(1174591889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2909422427/5000000000 : ℝ)|^4739 ≤ (12530158383937/25000000000000 : ℝ)^3715
        have hw : |(2909422427/5000000000 : ℝ)|=(2909422427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1605_s0_6 (p : ℝ) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2597517819/5000000000 : ℝ)*x 0 + (5818844501/10000000000 : ℝ)*x 1 + (-58729611/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2597517819/5000000000 : ℝ)^4739 ≤ (43370412516559/100000000000000 : ℝ)^3715 := by
    have hnat : (2597517819 : ℕ)^4739*100000000000000^3715 ≤ 43370412516559^3715*5000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2597517819 5000000000 43370412516559 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5818844501/10000000000 : ℝ)^4739 ≤ (25060314828541/50000000000000 : ℝ)^3715 := by
    have hnat : (5818844501 : ℕ)^4739*50000000000000^3715 ≤ 25060314828541^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5818844501 10000000000 25060314828541 50000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (58729611/500000000 : ℝ)^4739 ≤ (6508957811523/100000000000000 : ℝ)^3715 := by
    have hnat : (58729611 : ℕ)^4739*100000000000000^3715 ≤ 6508957811523^3715*500000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58729611 500000000 6508957811523 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4739/1024 : ℝ)) 4739 3715 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2597517819/5000000000 : ℝ), (5818844501/10000000000 : ℝ), (-58729611/500000000 : ℝ)] ![(43370412516559/100000000000000 : ℝ), (25060314828541/50000000000000 : ℝ), (6508957811523/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2597517819/5000000000 : ℝ)|^4739 ≤ (43370412516559/100000000000000 : ℝ)^3715
        have hw : |(2597517819/5000000000 : ℝ)|=(2597517819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5818844501/10000000000 : ℝ)|^4739 ≤ (25060314828541/50000000000000 : ℝ)^3715
        have hw : |(5818844501/10000000000 : ℝ)|=(5818844501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-58729611/500000000 : ℝ)|^4739 ≤ (6508957811523/100000000000000 : ℝ)^3715
        have hw : |(-58729611/500000000 : ℝ)|=(58729611/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1605_s0_7 (p : ℝ) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4119229613/10000000000 : ℝ)*x 0 + (334057821/625000000 : ℝ)*x 1 + (6122539/19531250 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4119229613/10000000000 : ℝ)^4739 ≤ (8064624701737/25000000000000 : ℝ)^3715 := by
    have hnat : (4119229613 : ℕ)^4739*25000000000000^3715 ≤ 8064624701737^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4119229613 10000000000 8064624701737 25000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (334057821/625000000 : ℝ)^4739 ≤ (22486489028433/50000000000000 : ℝ)^3715 := by
    have hnat : (334057821 : ℕ)^4739*50000000000000^3715 ≤ 22486489028433^3715*625000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334057821 625000000 22486489028433 50000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6122539/19531250 : ℝ)^4739 ≤ (22768523123583/100000000000000 : ℝ)^3715 := by
    have hnat : (6122539 : ℕ)^4739*100000000000000^3715 ≤ 22768523123583^3715*19531250^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6122539 19531250 22768523123583 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4739/1024 : ℝ)) 4739 3715 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4119229613/10000000000 : ℝ), (334057821/625000000 : ℝ), (6122539/19531250 : ℝ)] ![(8064624701737/25000000000000 : ℝ), (22486489028433/50000000000000 : ℝ), (22768523123583/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4119229613/10000000000 : ℝ)|^4739 ≤ (8064624701737/25000000000000 : ℝ)^3715
        have hw : |(4119229613/10000000000 : ℝ)|=(4119229613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(334057821/625000000 : ℝ)|^4739 ≤ (22486489028433/50000000000000 : ℝ)^3715
        have hw : |(334057821/625000000 : ℝ)|=(334057821/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6122539/19531250 : ℝ)|^4739 ≤ (22768523123583/100000000000000 : ℝ)^3715
        have hw : |(6122539/19531250 : ℝ)|=(6122539/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1605_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (172058521/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (3913/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (12179/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4735/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4735 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4735*1^1024 ≤ 0^1024*1^4735 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4735 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4735 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4735/1024 : ℝ) ≤ (722580234231367191/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4735 ≤ (722580234231367191/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4735*50000000000000000000^1024 ≤ 722580234231367191^1024*5^4735 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 722580234231367191 50000000000000000000 4735 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (722580234231367191/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4735 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4735/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4735 := by
      have hnat : (1 : ℕ)^1024*1^4735 ≤ 1^4735*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4735 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4735 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50722580234231367191/50000000000000000000 : ℝ) ≤ (5015538912920527/5000000000000000 : ℝ) ^ (4735/1024 : ℝ) := by
    have hpowers : (50722580234231367191/50000000000000000000 : ℝ)^1024 ≤ (5015538912920527/5000000000000000 : ℝ)^4735 := by
      have hnat : (50722580234231367191 : ℕ)^1024*5000000000000000^4735 ≤ 5015538912920527^4735*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50722580234231367191 50000000000000000000 5015538912920527 5000000000000000 1024 4735 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5015538912920527/5000000000000000 : ℝ)) (X := (50722580234231367191/50000000000000000000 : ℝ)) (by norm_num) 4735 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25722580234231367191/25000000000000000000 : ℝ) ≤ (2515538912920527/2500000000000000 : ℝ) ^ (4735/1024 : ℝ) := by
    have hpowers : (25722580234231367191/25000000000000000000 : ℝ)^1024 ≤ (2515538912920527/2500000000000000 : ℝ)^4735 := by
      have hnat : (25722580234231367191 : ℕ)^1024*2500000000000000^4735 ≤ 2515538912920527^4735*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25722580234231367191 25000000000000000000 2515538912920527 2500000000000000 1024 4735 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2515538912920527/2500000000000000 : ℝ)) (X := (25722580234231367191/25000000000000000000 : ℝ)) (by norm_num) 4735 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(15538912920527/2000000000000000 : ℝ)*(0 : ℝ))^(4735/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(15538912920527/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(722580234231367191/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(15538912920527/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4735/1024 : ℝ) := by
    rw [show (1 : ℝ)+(15538912920527/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5015538912920527/5000000000000000 : ℝ) by norm_num, show 1+(722580234231367191/50000000000000000000 : ℝ)+(0 : ℝ)=(50722580234231367191/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(722580234231367191/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(15538912920527/2000000000000000 : ℝ)*(2/5 : ℝ))^(4735/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(15538912920527/2000000000000000 : ℝ)*(2/5 : ℝ)=(2515538912920527/2500000000000000 : ℝ) by norm_num, show 1+2*(722580234231367191/50000000000000000000 : ℝ)=(25722580234231367191/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(15538912920527/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4735/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (15538912920527/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(15538912920527/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4735/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (15538912920527/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(15538912920527/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4735/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (15538912920527/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-315003151/2000000000 : ℝ)*X 0 0+(730491137/1250000000 : ℝ)*X 0 1+(1222311137/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1605_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((681972933/1250000000 : ℝ)*X 1 0+(-2104192767/10000000000 : ℝ)*X 1 1+(152788887/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1605_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1363945831/2500000000 : ℝ)*X 2 0+(244462223/500000000 : ℝ)*X 2 1+(-2104192853/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1605_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4112241869/10000000000 : ℝ)*X 0 0+(3073505131/10000000000 : ℝ)*X 0 1+(5404053697/10000000000 : ℝ)*X 0 2+(4112241869/10000000000 : ℝ)*X 1 0+(3073505131/10000000000 : ℝ)*X 1 1+(5404053697/10000000000 : ℝ)*X 1 2+(4112241869/10000000000 : ℝ)*X 2 0+(3073505131/10000000000 : ℝ)*X 2 1+(5404053697/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1605_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-315575511/2000000000 : ℝ)*X 0 0+(4913466303/10000000000 : ℝ)*X 0 1+(5818844499/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1605_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2597517747/5000000000 : ℝ)*X 1 0+(-1174591889/10000000000 : ℝ)*X 1 1+(2909422427/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1605_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2597517819/5000000000 : ℝ)*X 2 0+(5818844501/10000000000 : ℝ)*X 2 1+(-58729611/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1605_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4119229613/10000000000 : ℝ)*X 0 0+(334057821/625000000 : ℝ)*X 0 1+(6122539/19531250 : ℝ)*X 0 2+(4119229613/10000000000 : ℝ)*X 1 0+(334057821/625000000 : ℝ)*X 1 1+(6122539/19531250 : ℝ)*X 1 2+(4119229613/10000000000 : ℝ)*X 2 0+(334057821/625000000 : ℝ)*X 2 1+(6122539/19531250 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1605_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11065353842878515619023/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4590597/20000000000000 : ℝ)*(base1) + (866109161/100000000000000 : ℝ)*(base19) + (104903769/12500000000000 : ℝ)*(base23) + (65118961/50000000000000 : ℝ)*(upper3) + (48085179/50000000000000 : ℝ)*(upper5) + (18456988615461/2500000000000 : ℝ)*(major0) + (18456988615461/2500000000000 : ℝ)*(major1) + (18456988615461/2500000000000 : ℝ)*(major2) + (523734803862493/50000000000000 : ℝ)*(sp0) + (209494354766329/20000000000000 : ℝ)*(sp1) + (523735900355327/50000000000000 : ℝ)*(sp2) + (42908482401949/10000000000000 : ℝ)*(sp3) + (763792201/25000000000000 : ℝ)*(sp4) + (727392771/50000000000000 : ℝ)*(sp7) + (429086301758017/100000000000000 : ℝ)*(f.failure) + (523736319970403/50000000000000 : ℝ)*(f.sum) + (2311677047053/2500000000000000000000000000 : ℝ)*base66 + (16844700617947/5000000000000000000000000000 : ℝ)*base67 + (22653257082053/5000000000000000000000000000 : ℝ)*base70 + (20980345212053/5000000000000000000000000000 : ℝ)*base72 + (11178968500447/2500000000000000000000000000 : ℝ)*base73 + (39263487862053/5000000000000000000000000000 : ℝ)*base76 + (24637423292053/5000000000000000000000000000 : ℝ)*base78 + (26405662242053/5000000000000000000000000000 : ℝ)*base80 + (3929196842053/2500000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (104912857/10000000000000000000000 : ℝ)*base89 + (104912857/10000000000000000000000 : ℝ)*base91 + (104912857/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7852663397775656790027/1000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (101806239/6250000000000 : ℝ)*(base19) + (10543011/625000000000 : ℝ)*(base23) + (249849259/100000000000000 : ℝ)*(base32) + (155694181/50000000000000 : ℝ)*(upper3) + (68278943/100000000000000 : ℝ)*(upper5) + (31139194763167/4000000000000 : ℝ)*(major0) + (31139194763167/4000000000000 : ℝ)*(major1) + (31139194763167/4000000000000 : ℝ)*(major2) + (1099639049/25000000000000 : ℝ)*(sp1) + (2471898791/50000000000000 : ℝ)*(sp2) + (55225442121201/5000000000000 : ℝ)*(sp4) + (138062851871/12500000000 : ℝ)*(sp5) + (1104502211744679/100000000000000 : ℝ)*(sp6) + (28278149008101/6250000000000 : ℝ)*(sp7) + (226225316989437/50000000000000 : ℝ)*(f.failure) + (55225442121201/5000000000000 : ℝ)*(f.sum) + (3634532202991/4000000000000000000000000000 : ℝ)*base66 + (13206251141009/8000000000000000000000000000 : ℝ)*base67 + (15769208314991/8000000000000000000000000000 : ℝ)*base70 + (5953970586991/8000000000000000000000000000 : ℝ)*base72 + (3926507946991/4000000000000000000000000000 : ℝ)*base74 + (37241917413009/8000000000000000000000000000 : ℝ)*base75 + (10620033194991/8000000000000000000000000000 : ℝ)*base78 + (91291811570991/8000000000000000000000000000 : ℝ)*base80 + (13067196018991/4000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (47157323/5000000000000000000000 : ℝ)*base90 + (47157323/5000000000000000000000 : ℝ)*base92 + (47157323/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1605_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (172058521/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3913/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (12179/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1605_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1605_s1_0 (p : ℝ) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1700753661/10000000000 : ℝ)*x 0 + (5534658861/10000000000 : ℝ)*x 1 + (639655103/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1700753661/10000000000 : ℝ)^4739 ≤ (5218503231763/50000000000000 : ℝ)^3715 := by
    have hnat : (1700753661 : ℕ)^4739*50000000000000^3715 ≤ 5218503231763^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1700753661 10000000000 5218503231763 50000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5534658861/10000000000 : ℝ)^4739 ≤ (47019347850889/100000000000000 : ℝ)^3715 := by
    have hnat : (5534658861 : ℕ)^4739*100000000000000^3715 ≤ 47019347850889^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5534658861 10000000000 47019347850889 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (639655103/1250000000 : ℝ)^4739 ≤ (42543645664943/100000000000000 : ℝ)^3715 := by
    have hnat : (639655103 : ℕ)^4739*100000000000000^3715 ≤ 42543645664943^3715*1250000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      639655103 1250000000 42543645664943 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4739/1024 : ℝ)) 4739 3715 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1700753661/10000000000 : ℝ), (5534658861/10000000000 : ℝ), (639655103/1250000000 : ℝ)] ![(5218503231763/50000000000000 : ℝ), (47019347850889/100000000000000 : ℝ), (42543645664943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1700753661/10000000000 : ℝ)|^4739 ≤ (5218503231763/50000000000000 : ℝ)^3715
        have hw : |(-1700753661/10000000000 : ℝ)|=(1700753661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5534658861/10000000000 : ℝ)|^4739 ≤ (47019347850889/100000000000000 : ℝ)^3715
        have hw : |(5534658861/10000000000 : ℝ)|=(5534658861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(639655103/1250000000 : ℝ)|^4739 ≤ (42543645664943/100000000000000 : ℝ)^3715
        have hw : |(639655103/1250000000 : ℝ)|=(639655103/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1605_s1_1 (p : ℝ) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5373467909/10000000000 : ℝ)*x 0 + (-1919244547/10000000000 : ℝ)*x 1 + (5117240683/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5373467909/10000000000 : ℝ)^4739 ≤ (22639782331513/50000000000000 : ℝ)^3715 := by
    have hnat : (5373467909 : ℕ)^4739*50000000000000^3715 ≤ 22639782331513^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5373467909 10000000000 22639782331513 50000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1919244547/10000000000 : ℝ)^4739 ≤ (3044197786677/25000000000000 : ℝ)^3715 := by
    have hnat : (1919244547 : ℕ)^4739*25000000000000^3715 ≤ 3044197786677^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1919244547 10000000000 3044197786677 25000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5117240683/10000000000 : ℝ)^4739 ≤ (42543644169583/100000000000000 : ℝ)^3715 := by
    have hnat : (5117240683 : ℕ)^4739*100000000000000^3715 ≤ 42543644169583^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5117240683 10000000000 42543644169583 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4739/1024 : ℝ)) 4739 3715 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5373467909/10000000000 : ℝ), (-1919244547/10000000000 : ℝ), (5117240683/10000000000 : ℝ)] ![(22639782331513/50000000000000 : ℝ), (3044197786677/25000000000000 : ℝ), (42543644169583/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5373467909/10000000000 : ℝ)|^4739 ≤ (22639782331513/50000000000000 : ℝ)^3715
        have hw : |(5373467909/10000000000 : ℝ)|=(5373467909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1919244547/10000000000 : ℝ)|^4739 ≤ (3044197786677/25000000000000 : ℝ)^3715
        have hw : |(-1919244547/10000000000 : ℝ)|=(1919244547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5117240683/10000000000 : ℝ)|^4739 ≤ (42543644169583/100000000000000 : ℝ)^3715
        have hw : |(5117240683/10000000000 : ℝ)|=(5117240683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1605_s1_2 (p : ℝ) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5373467543/10000000000 : ℝ)*x 0 + (2558620499/5000000000 : ℝ)*x 1 + (-959622311/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5373467543/10000000000 : ℝ)^4739 ≤ (1811182429153/4000000000000 : ℝ)^3715 := by
    have hnat : (5373467543 : ℕ)^4739*4000000000000^3715 ≤ 1811182429153^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5373467543 10000000000 1811182429153 4000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2558620499/5000000000 : ℝ)^4739 ≤ (21271823755141/50000000000000 : ℝ)^3715 := by
    have hnat : (2558620499 : ℕ)^4739*50000000000000^3715 ≤ 21271823755141^3715*5000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2558620499 5000000000 21271823755141 50000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (959622311/5000000000 : ℝ)^4739 ≤ (761049484607/6250000000000 : ℝ)^3715 := by
    have hnat : (959622311 : ℕ)^4739*6250000000000^3715 ≤ 761049484607^3715*5000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      959622311 5000000000 761049484607 6250000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4739/1024 : ℝ)) 4739 3715 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5373467543/10000000000 : ℝ), (2558620499/5000000000 : ℝ), (-959622311/5000000000 : ℝ)] ![(1811182429153/4000000000000 : ℝ), (21271823755141/50000000000000 : ℝ), (761049484607/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5373467543/10000000000 : ℝ)|^4739 ≤ (1811182429153/4000000000000 : ℝ)^3715
        have hw : |(5373467543/10000000000 : ℝ)|=(5373467543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2558620499/5000000000 : ℝ)|^4739 ≤ (21271823755141/50000000000000 : ℝ)^3715
        have hw : |(2558620499/5000000000 : ℝ)|=(2558620499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-959622311/5000000000 : ℝ)|^4739 ≤ (761049484607/6250000000000 : ℝ)^3715
        have hw : |(-959622311/5000000000 : ℝ)|=(959622311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1605_s1_3 (p : ℝ) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (262804139/625000000 : ℝ)*x 0 + (1859625861/5000000000 : ℝ)*x 1 + (4738240411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (262804139/625000000 : ℝ)^4739 ≤ (33116428900783/100000000000000 : ℝ)^3715 := by
    have hnat : (262804139 : ℕ)^4739*100000000000000^3715 ≤ 33116428900783^3715*625000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262804139 625000000 33116428900783 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1859625861/5000000000 : ℝ)^4739 ≤ (5663517452067/20000000000000 : ℝ)^3715 := by
    have hnat : (1859625861 : ℕ)^4739*20000000000000^3715 ≤ 5663517452067^3715*5000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1859625861 5000000000 5663517452067 20000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4738240411/10000000000 : ℝ)^4739 ≤ (19282991911437/50000000000000 : ℝ)^3715 := by
    have hnat : (4738240411 : ℕ)^4739*50000000000000^3715 ≤ 19282991911437^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4738240411 10000000000 19282991911437 50000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4739/1024 : ℝ)) 4739 3715 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(262804139/625000000 : ℝ), (1859625861/5000000000 : ℝ), (4738240411/10000000000 : ℝ)] ![(33116428900783/100000000000000 : ℝ), (5663517452067/20000000000000 : ℝ), (19282991911437/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(262804139/625000000 : ℝ)|^4739 ≤ (33116428900783/100000000000000 : ℝ)^3715
        have hw : |(262804139/625000000 : ℝ)|=(262804139/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1859625861/5000000000 : ℝ)|^4739 ≤ (5663517452067/20000000000000 : ℝ)^3715
        have hw : |(1859625861/5000000000 : ℝ)|=(1859625861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4738240411/10000000000 : ℝ)|^4739 ≤ (19282991911437/50000000000000 : ℝ)^3715
        have hw : |(4738240411/10000000000 : ℝ)|=(4738240411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1605_s1_4 (p : ℝ) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-340197449/2000000000 : ℝ)*x 0 + (1024365431/2000000000 : ℝ)*x 1 + (5530000769/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (340197449/2000000000 : ℝ)^4739 ≤ (10438835042577/100000000000000 : ℝ)^3715 := by
    have hnat : (340197449 : ℕ)^4739*100000000000000^3715 ≤ 10438835042577^3715*2000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340197449 2000000000 10438835042577 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1024365431/2000000000 : ℝ)^4739 ≤ (42592291511111/100000000000000 : ℝ)^3715 := by
    have hnat : (1024365431 : ℕ)^4739*100000000000000^3715 ≤ 42592291511111^3715*2000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1024365431 2000000000 42592291511111 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5530000769/10000000000 : ℝ)^4739 ≤ (23484436717121/50000000000000 : ℝ)^3715 := by
    have hnat : (5530000769 : ℕ)^4739*50000000000000^3715 ≤ 23484436717121^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5530000769 10000000000 23484436717121 50000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4739/1024 : ℝ)) 4739 3715 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-340197449/2000000000 : ℝ), (1024365431/2000000000 : ℝ), (5530000769/10000000000 : ℝ)] ![(10438835042577/100000000000000 : ℝ), (42592291511111/100000000000000 : ℝ), (23484436717121/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-340197449/2000000000 : ℝ)|^4739 ≤ (10438835042577/100000000000000 : ℝ)^3715
        have hw : |(-340197449/2000000000 : ℝ)|=(340197449/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1024365431/2000000000 : ℝ)|^4739 ≤ (42592291511111/100000000000000 : ℝ)^3715
        have hw : |(1024365431/2000000000 : ℝ)|=(1024365431/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5530000769/10000000000 : ℝ)|^4739 ≤ (23484436717121/50000000000000 : ℝ)^3715
        have hw : |(5530000769/10000000000 : ℝ)|=(5530000769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1605_s1_5 (p : ℝ) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5262509347/10000000000 : ℝ)*x 0 + (-301296857/2000000000 : ℝ)*x 1 + (5530001081/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5262509347/10000000000 : ℝ)^4739 ≤ (44090262129967/100000000000000 : ℝ)^3715 := by
    have hnat : (5262509347 : ℕ)^4739*100000000000000^3715 ≤ 44090262129967^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262509347 10000000000 44090262129967 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (301296857/2000000000 : ℝ)^4739 ≤ (8940861035963/100000000000000 : ℝ)^3715 := by
    have hnat : (301296857 : ℕ)^4739*100000000000000^3715 ≤ 8940861035963^3715*2000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      301296857 2000000000 8940861035963 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5530001081/10000000000 : ℝ)^4739 ≤ (46968876814637/100000000000000 : ℝ)^3715 := by
    have hnat : (5530001081 : ℕ)^4739*100000000000000^3715 ≤ 46968876814637^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5530001081 10000000000 46968876814637 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4739/1024 : ℝ)) 4739 3715 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5262509347/10000000000 : ℝ), (-301296857/2000000000 : ℝ), (5530001081/10000000000 : ℝ)] ![(44090262129967/100000000000000 : ℝ), (8940861035963/100000000000000 : ℝ), (46968876814637/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5262509347/10000000000 : ℝ)|^4739 ≤ (44090262129967/100000000000000 : ℝ)^3715
        have hw : |(5262509347/10000000000 : ℝ)|=(5262509347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-301296857/2000000000 : ℝ)|^4739 ≤ (8940861035963/100000000000000 : ℝ)^3715
        have hw : |(-301296857/2000000000 : ℝ)|=(301296857/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5530001081/10000000000 : ℝ)|^4739 ≤ (46968876814637/100000000000000 : ℝ)^3715
        have hw : |(5530001081/10000000000 : ℝ)|=(5530001081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1605_s1_6 (p : ℝ) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (263125437/500000000 : ℝ)*x 0 + (5530001309/10000000000 : ℝ)*x 1 + (-1506484817/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (263125437/500000000 : ℝ)^4739 ≤ (5511281955329/12500000000000 : ℝ)^3715 := by
    have hnat : (263125437 : ℕ)^4739*12500000000000^3715 ≤ 5511281955329^3715*500000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263125437 500000000 5511281955329 12500000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5530001309/10000000000 : ℝ)^4739 ≤ (23484439642463/50000000000000 : ℝ)^3715 := by
    have hnat : (5530001309 : ℕ)^4739*50000000000000^3715 ≤ 23484439642463^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5530001309 10000000000 23484439642463 50000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1506484817/10000000000 : ℝ)^4739 ≤ (8940865063637/100000000000000 : ℝ)^3715 := by
    have hnat : (1506484817 : ℕ)^4739*100000000000000^3715 ≤ 8940865063637^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1506484817 10000000000 8940865063637 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4739/1024 : ℝ)) 4739 3715 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(263125437/500000000 : ℝ), (5530001309/10000000000 : ℝ), (-1506484817/10000000000 : ℝ)] ![(5511281955329/12500000000000 : ℝ), (23484439642463/50000000000000 : ℝ), (8940865063637/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(263125437/500000000 : ℝ)|^4739 ≤ (5511281955329/12500000000000 : ℝ)^3715
        have hw : |(263125437/500000000 : ℝ)|=(263125437/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5530001309/10000000000 : ℝ)|^4739 ≤ (23484439642463/50000000000000 : ℝ)^3715
        have hw : |(5530001309/10000000000 : ℝ)|=(5530001309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1506484817/10000000000 : ℝ)|^4739 ≤ (8940865063637/100000000000000 : ℝ)^3715
        have hw : |(-1506484817/10000000000 : ℝ)|=(1506484817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1605_s1_7 (p : ℝ) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2102717723/5000000000 : ℝ)*x 0 + (472704547/1000000000 : ℝ)*x 1 + (3730621857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2102717723/5000000000 : ℝ)^4739 ≤ (16561073877231/50000000000000 : ℝ)^3715 := by
    have hnat : (2102717723 : ℕ)^4739*50000000000000^3715 ≤ 16561073877231^3715*5000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2102717723 5000000000 16561073877231 50000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (472704547/1000000000 : ℝ)^4739 ≤ (38449786666027/100000000000000 : ℝ)^3715 := by
    have hnat : (472704547 : ℕ)^4739*100000000000000^3715 ≤ 38449786666027^3715*1000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      472704547 1000000000 38449786666027 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3730621857/10000000000 : ℝ)^4739 ≤ (7107016390787/25000000000000 : ℝ)^3715 := by
    have hnat : (3730621857 : ℕ)^4739*25000000000000^3715 ≤ 7107016390787^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3730621857 10000000000 7107016390787 25000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4739/1024 : ℝ)) 4739 3715 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2102717723/5000000000 : ℝ), (472704547/1000000000 : ℝ), (3730621857/10000000000 : ℝ)] ![(16561073877231/50000000000000 : ℝ), (38449786666027/100000000000000 : ℝ), (7107016390787/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2102717723/5000000000 : ℝ)|^4739 ≤ (16561073877231/50000000000000 : ℝ)^3715
        have hw : |(2102717723/5000000000 : ℝ)|=(2102717723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(472704547/1000000000 : ℝ)|^4739 ≤ (38449786666027/100000000000000 : ℝ)^3715
        have hw : |(472704547/1000000000 : ℝ)|=(472704547/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3730621857/10000000000 : ℝ)|^4739 ≤ (7107016390787/25000000000000 : ℝ)^3715
        have hw : |(3730621857/10000000000 : ℝ)|=(3730621857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1605_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (172058521/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (12179/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3913/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (113/1250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17883/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (12179/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3913/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (12179/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3913/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (12179/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3913/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (12179/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3913/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (12179/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3913/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (12179/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3913/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3913/100000 : ℝ) ^ (4735/1024 : ℝ) ≤ (7756620743239/25000000000000000000 : ℝ) := by
    have hpowers : (3913/100000 : ℝ)^4735 ≤ (7756620743239/25000000000000000000 : ℝ)^1024 := by
      have hnat : (3913 : ℕ)^4735*25000000000000000000^1024 ≤ 7756620743239^1024*100000^4735 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3913 100000 7756620743239 25000000000000000000 4735 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3913/100000 : ℝ)) (X := (7756620743239/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4735 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (12179/50000 : ℝ) ^ (4735/1024 : ℝ) ≤ (36454950455265283/25000000000000000000 : ℝ) := by
    have hpowers : (12179/50000 : ℝ)^4735 ≤ (36454950455265283/25000000000000000000 : ℝ)^1024 := by
      have hnat : (12179 : ℕ)^4735*25000000000000000000^1024 ≤ 36454950455265283^1024*50000^4735 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12179 50000 36454950455265283 25000000000000000000 4735 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (12179/50000 : ℝ)) (X := (36454950455265283/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4735 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500007756620743239/12500000000000000000 : ℝ) ≤ (10000001341968779/10000000000000000 : ℝ) ^ (4735/1024 : ℝ) := by
    have hpowers : (12500007756620743239/12500000000000000000 : ℝ)^1024 ≤ (10000001341968779/10000000000000000 : ℝ)^4735 := by
      have hnat : (12500007756620743239 : ℕ)^1024*10000000000000000^4735 ≤ 10000001341968779^4735*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500007756620743239 12500000000000000000 10000001341968779 10000000000000000 1024 4735 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000001341968779/10000000000000000 : ℝ)) (X := (12500007756620743239/12500000000000000000 : ℝ)) (by norm_num) 4735 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12518231353538004261/12500000000000000000 : ℝ) ≤ (5001576198112809/5000000000000000 : ℝ) ^ (4735/1024 : ℝ) := by
    have hpowers : (12518231353538004261/12500000000000000000 : ℝ)^1024 ≤ (5001576198112809/5000000000000000 : ℝ)^4735 := by
      have hnat : (12518231353538004261 : ℕ)^1024*5000000000000000^4735 ≤ 5001576198112809^4735*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12518231353538004261 12500000000000000000 5001576198112809 5000000000000000 1024 4735 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001576198112809/5000000000000000 : ℝ)) (X := (12518231353538004261/12500000000000000000 : ℝ)) (by norm_num) 4735 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12536454950455265283/12500000000000000000 : ℝ) ≤ (10006303450482457/10000000000000000 : ℝ) ^ (4735/1024 : ℝ) := by
    have hpowers : (12536454950455265283/12500000000000000000 : ℝ)^1024 ≤ (10006303450482457/10000000000000000 : ℝ)^4735 := by
      have hnat : (12536454950455265283 : ℕ)^1024*10000000000000000^4735 ≤ 10006303450482457^4735*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12536454950455265283 12500000000000000000 10006303450482457 10000000000000000 1024 4735 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006303450482457/10000000000000000 : ℝ)) (X := (12536454950455265283/12500000000000000000 : ℝ)) (by norm_num) 4735 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7756620743239/25000000000000000000 : ℝ) ≤ ((204425367285937664641/204450000000000000000 : ℝ)+2*(3151054256839/2044500000000000 : ℝ)*(3913/100000 : ℝ))^(4735/1024 : ℝ) := by
    rw [show (204425367285937664641/204450000000000000000 : ℝ)+2*(3151054256839/2044500000000000 : ℝ)*(3913/100000 : ℝ)=(10000001341968779/10000000000000000 : ℝ) by norm_num, show 1+2*(7756620743239/25000000000000000000 : ℝ)=(12500007756620743239/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36454950455265283/25000000000000000000 : ℝ)+(7756620743239/25000000000000000000 : ℝ) ≤ ((204425367285937664641/204450000000000000000 : ℝ)+(3151054256839/2044500000000000 : ℝ)*((12179/50000 : ℝ)+(3913/100000 : ℝ)))^(4735/1024 : ℝ) := by
    rw [show (204425367285937664641/204450000000000000000 : ℝ)+(3151054256839/2044500000000000 : ℝ)*((12179/50000 : ℝ)+(3913/100000 : ℝ))=(5001576198112809/5000000000000000 : ℝ) by norm_num, show 1+(36454950455265283/25000000000000000000 : ℝ)+(7756620743239/25000000000000000000 : ℝ)=(12518231353538004261/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36454950455265283/25000000000000000000 : ℝ) ≤ ((204425367285937664641/204450000000000000000 : ℝ)+2*(3151054256839/2044500000000000 : ℝ)*(12179/50000 : ℝ))^(4735/1024 : ℝ) := by
    rw [show (204425367285937664641/204450000000000000000 : ℝ)+2*(3151054256839/2044500000000000 : ℝ)*(12179/50000 : ℝ)=(10006303450482457/10000000000000000 : ℝ) by norm_num, show 1+2*(36454950455265283/25000000000000000000 : ℝ)=(12536454950455265283/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (204425367285937664641/204450000000000000000 : ℝ)*(X 1 0+X 2 0)+(3151054256839/2044500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4735/1024 : ℝ)) (lo := (3913/100000 : ℝ)) (hi := (12179/50000 : ℝ)) (c := (204425367285937664641/204450000000000000000 : ℝ)) (alpha := (3151054256839/2044500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (204425367285937664641/204450000000000000000 : ℝ)*(X 0 1+X 2 1)+(3151054256839/2044500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4735/1024 : ℝ)) (lo := (3913/100000 : ℝ)) (hi := (12179/50000 : ℝ)) (c := (204425367285937664641/204450000000000000000 : ℝ)) (alpha := (3151054256839/2044500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (204425367285937664641/204450000000000000000 : ℝ)*(X 0 2+X 1 2)+(3151054256839/2044500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4735/1024 : ℝ)) (lo := (3913/100000 : ℝ)) (hi := (12179/50000 : ℝ)) (c := (204425367285937664641/204450000000000000000 : ℝ)) (alpha := (3151054256839/2044500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1700753661/10000000000 : ℝ)*X 0 0+(5534658861/10000000000 : ℝ)*X 0 1+(639655103/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1605_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5373467909/10000000000 : ℝ)*X 1 0+(-1919244547/10000000000 : ℝ)*X 1 1+(5117240683/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1605_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5373467543/10000000000 : ℝ)*X 2 0+(2558620499/5000000000 : ℝ)*X 2 1+(-959622311/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1605_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((262804139/625000000 : ℝ)*X 0 0+(1859625861/5000000000 : ℝ)*X 0 1+(4738240411/10000000000 : ℝ)*X 0 2+(262804139/625000000 : ℝ)*X 1 0+(1859625861/5000000000 : ℝ)*X 1 1+(4738240411/10000000000 : ℝ)*X 1 2+(262804139/625000000 : ℝ)*X 2 0+(1859625861/5000000000 : ℝ)*X 2 1+(4738240411/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1605_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-340197449/2000000000 : ℝ)*X 0 0+(1024365431/2000000000 : ℝ)*X 0 1+(5530000769/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1605_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5262509347/10000000000 : ℝ)*X 1 0+(-301296857/2000000000 : ℝ)*X 1 1+(5530001081/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1605_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((263125437/500000000 : ℝ)*X 2 0+(5530001309/10000000000 : ℝ)*X 2 1+(-1506484817/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1605_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2102717723/5000000000 : ℝ)*X 0 0+(472704547/1000000000 : ℝ)*X 0 1+(3730621857/10000000000 : ℝ)*X 0 2+(2102717723/5000000000 : ℝ)*X 1 0+(472704547/1000000000 : ℝ)*X 1 1+(3730621857/10000000000 : ℝ)*X 1 2+(2102717723/5000000000 : ℝ)*X 2 0+(472704547/1000000000 : ℝ)*X 2 1+(3730621857/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1605_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (44920026274160976886539/34075000000000000000000000000 : ℝ) := by norm_num
    linear_combination (43262537/100000000000000 : ℝ)*(base1) + (575371261/100000000000000 : ℝ)*(base19) + (51398311/12500000000000 : ℝ)*(base23) + (66299029/100000000000000 : ℝ)*(upper3) + (422132256190473/25000000000000 : ℝ)*(major0) + (422132256190473/25000000000000 : ℝ)*(major1) + (422132256190473/25000000000000 : ℝ)*(major2) + (59892129536427/2500000000000 : ℝ)*(sp0) + (149730525514717/6250000000000 : ℝ)*(sp1) + (239568852357699/10000000000000 : ℝ)*(sp2) + (490683477799641/50000000000000 : ℝ)*(sp3) + (3845412191/100000000000000 : ℝ)*(sp4) + (9768651/20000000000000 : ℝ)*(sp6) + (1011556457/50000000000000 : ℝ)*(sp7) + (490684510987367/50000000000000 : ℝ)*(f.failure) + (1197844491803367/50000000000000 : ℝ)*(f.sum) + (28442941333479/34075000000000000000000000000 : ℝ)*base66 + (6249657038733871731/1703750000000000000000000000000000 : ℝ)*base67 + (6229731294753628269/1703750000000000000000000000000000 : ℝ)*base70 + (9632668714567621731/1703750000000000000000000000000000 : ℝ)*base71 + (19387658510051/8518750000000000000000000000 : ℝ)*base74 + (3896102495317378269/1703750000000000000000000000000000 : ℝ)*base76 + (5804825951335121731/1703750000000000000000000000000000 : ℝ)*base77 + (868992663503628269/1703750000000000000000000000000000 : ℝ)*base80 + (196705698461579/34075000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (15704207/5000000000000000000000 : ℝ)*base89 + (15704207/5000000000000000000000 : ℝ)*base91 + (15704207/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (347898964640260504620601/34075000000000000000000000000 : ℝ) := by norm_num
    linear_combination (996481163/50000000000000 : ℝ)*(base19) + (865695451/50000000000000 : ℝ)*(base23) + (23644603/100000000000000 : ℝ)*(upper2) + (69142359/20000000000000 : ℝ)*(upper3) + (6270577/4000000000000 : ℝ)*(upper5) + (863380957454567/50000000000000 : ℝ)*(major0) + (863380957454567/50000000000000 : ℝ)*(major1) + (863380957454567/50000000000000 : ℝ)*(major2) + (941193851/6250000000000 : ℝ)*(sp1) + (6962389491/50000000000000 : ℝ)*(sp2) + (489986720680651/20000000000000 : ℝ)*(sp4) + (1224958275669657/50000000000000 : ℝ)*(sp5) + (612479486808343/25000000000000 : ℝ)*(sp6) + (125448735761039/12500000000000 : ℝ)*(sp7) + (125448735761039/12500000000000 : ℝ)*(f.failure) + (489986720680651/20000000000000 : ℝ)*(f.sum) + (417321674538899/102225000000000000000000000000 : ℝ)*base66 + (31103294174498665447/10222500000000000000000000000000000 : ℝ)*base67 + (2010035519633665447/10222500000000000000000000000000000 : ℝ)*base69 + (49911857240803834553/10222500000000000000000000000000000 : ℝ)*base72 + (9028071694219/25556250000000000000000000000 : ℝ)*base73 + (60111474092773834553/10222500000000000000000000000000000 : ℝ)*base76 + (1654076017306165447/10222500000000000000000000000000000 : ℝ)*base77 + (101719677072628834553/10222500000000000000000000000000000 : ℝ)*base80 + (52203582533587/51112500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (4763319/1250000000000000000000 : ℝ)*base89 + (4763319/1250000000000000000000 : ℝ)*base91 + (4763319/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1605_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (172058521/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (12179/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3913/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (113/1250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17883/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1605_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1605_s2_0 (p : ℝ) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-107210073/625000000 : ℝ)*x 0 + (2734458367/5000000000 : ℝ)*x 1 + (1034685847/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107210073/625000000 : ℝ)^4739 ≤ (1055149216409/10000000000000 : ℝ)^3715 := by
    have hnat : (107210073 : ℕ)^4739*10000000000000^3715 ≤ 1055149216409^3715*625000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107210073 625000000 1055149216409 10000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2734458367/5000000000 : ℝ)^4739 ≤ (9261612526127/20000000000000 : ℝ)^3715 := by
    have hnat : (2734458367 : ℕ)^4739*20000000000000^3715 ≤ 9261612526127^3715*5000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2734458367 5000000000 9261612526127 20000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1034685847/2000000000 : ℝ)^4739 ≤ (8628089039137/20000000000000 : ℝ)^3715 := by
    have hnat : (1034685847 : ℕ)^4739*20000000000000^3715 ≤ 8628089039137^3715*2000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034685847 2000000000 8628089039137 20000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4739/1024 : ℝ)) 4739 3715 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-107210073/625000000 : ℝ), (2734458367/5000000000 : ℝ), (1034685847/2000000000 : ℝ)] ![(1055149216409/10000000000000 : ℝ), (9261612526127/20000000000000 : ℝ), (8628089039137/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-107210073/625000000 : ℝ)|^4739 ≤ (1055149216409/10000000000000 : ℝ)^3715
        have hw : |(-107210073/625000000 : ℝ)|=(107210073/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2734458367/5000000000 : ℝ)|^4739 ≤ (9261612526127/20000000000000 : ℝ)^3715
        have hw : |(2734458367/5000000000 : ℝ)|=(2734458367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1034685847/2000000000 : ℝ)|^4739 ≤ (8628089039137/20000000000000 : ℝ)^3715
        have hw : |(1034685847/2000000000 : ℝ)|=(1034685847/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1605_s2_1 (p : ℝ) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5356374667/10000000000 : ℝ)*x 0 + (-1868007927/10000000000 : ℝ)*x 1 + (2586714571/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5356374667/10000000000 : ℝ)^4739 ≤ (45095906884249/100000000000000 : ℝ)^3715 := by
    have hnat : (5356374667 : ℕ)^4739*100000000000000^3715 ≤ 45095906884249^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5356374667 10000000000 45095906884249 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1868007927/10000000000 : ℝ)^4739 ≤ (11763648893333/100000000000000 : ℝ)^3715 := by
    have hnat : (1868007927 : ℕ)^4739*100000000000000^3715 ≤ 11763648893333^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1868007927 10000000000 11763648893333 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2586714571/5000000000 : ℝ)^4739 ≤ (4314044420641/10000000000000 : ℝ)^3715 := by
    have hnat : (2586714571 : ℕ)^4739*10000000000000^3715 ≤ 4314044420641^3715*5000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2586714571 5000000000 4314044420641 10000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4739/1024 : ℝ)) 4739 3715 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5356374667/10000000000 : ℝ), (-1868007927/10000000000 : ℝ), (2586714571/5000000000 : ℝ)] ![(45095906884249/100000000000000 : ℝ), (11763648893333/100000000000000 : ℝ), (4314044420641/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5356374667/10000000000 : ℝ)|^4739 ≤ (45095906884249/100000000000000 : ℝ)^3715
        have hw : |(5356374667/10000000000 : ℝ)|=(5356374667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1868007927/10000000000 : ℝ)|^4739 ≤ (11763648893333/100000000000000 : ℝ)^3715
        have hw : |(-1868007927/10000000000 : ℝ)|=(1868007927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2586714571/5000000000 : ℝ)|^4739 ≤ (4314044420641/10000000000000 : ℝ)^3715
        have hw : |(2586714571/5000000000 : ℝ)|=(2586714571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1605_s2_2 (p : ℝ) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (10461669/19531250 : ℝ)*x 0 + (646678663/1250000000 : ℝ)*x 1 + (-1868007899/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10461669/19531250 : ℝ)^4739 ≤ (704623521741/1562500000000 : ℝ)^3715 := by
    have hnat : (10461669 : ℕ)^4739*1562500000000^3715 ≤ 704623521741^3715*19531250^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10461669 19531250 704623521741 1562500000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (646678663/1250000000 : ℝ)^4739 ≤ (43140445929663/100000000000000 : ℝ)^3715 := by
    have hnat : (646678663 : ℕ)^4739*100000000000000^3715 ≤ 43140445929663^3715*1250000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      646678663 1250000000 43140445929663 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1868007899/10000000000 : ℝ)^4739 ≤ (5881824334201/50000000000000 : ℝ)^3715 := by
    have hnat : (1868007899 : ℕ)^4739*50000000000000^3715 ≤ 5881824334201^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1868007899 10000000000 5881824334201 50000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4739/1024 : ℝ)) 4739 3715 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(10461669/19531250 : ℝ), (646678663/1250000000 : ℝ), (-1868007899/10000000000 : ℝ)] ![(704623521741/1562500000000 : ℝ), (43140445929663/100000000000000 : ℝ), (5881824334201/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(10461669/19531250 : ℝ)|^4739 ≤ (704623521741/1562500000000 : ℝ)^3715
        have hw : |(10461669/19531250 : ℝ)|=(10461669/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(646678663/1250000000 : ℝ)|^4739 ≤ (43140445929663/100000000000000 : ℝ)^3715
        have hw : |(646678663/1250000000 : ℝ)|=(646678663/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1868007899/10000000000 : ℝ)|^4739 ≤ (5881824334201/50000000000000 : ℝ)^3715
        have hw : |(-1868007899/10000000000 : ℝ)|=(1868007899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1605_s2_3 (p : ℝ) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1053907657/2500000000 : ℝ)*x 0 + (3866932187/10000000000 : ℝ)*x 1 + (573533421/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1053907657/2500000000 : ℝ)^4739 ≤ (16612306358769/50000000000000 : ℝ)^3715 := by
    have hnat : (1053907657 : ℕ)^4739*50000000000000^3715 ≤ 16612306358769^3715*2500000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053907657 2500000000 16612306358769 50000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3866932187/10000000000 : ℝ)^4739 ≤ (14879850462347/50000000000000 : ℝ)^3715 := by
    have hnat : (3866932187 : ℕ)^4739*50000000000000^3715 ≤ 14879850462347^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3866932187 10000000000 14879850462347 50000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (573533421/1250000000 : ℝ)^4739 ≤ (37015686340963/100000000000000 : ℝ)^3715 := by
    have hnat : (573533421 : ℕ)^4739*100000000000000^3715 ≤ 37015686340963^3715*1250000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      573533421 1250000000 37015686340963 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4739/1024 : ℝ)) 4739 3715 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1053907657/2500000000 : ℝ), (3866932187/10000000000 : ℝ), (573533421/1250000000 : ℝ)] ![(16612306358769/50000000000000 : ℝ), (14879850462347/50000000000000 : ℝ), (37015686340963/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1053907657/2500000000 : ℝ)|^4739 ≤ (16612306358769/50000000000000 : ℝ)^3715
        have hw : |(1053907657/2500000000 : ℝ)|=(1053907657/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3866932187/10000000000 : ℝ)|^4739 ≤ (14879850462347/50000000000000 : ℝ)^3715
        have hw : |(3866932187/10000000000 : ℝ)|=(3866932187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(573533421/1250000000 : ℝ)|^4739 ≤ (37015686340963/100000000000000 : ℝ)^3715
        have hw : |(573533421/1250000000 : ℝ)|=(573533421/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1605_s2_4 (p : ℝ) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-107215239/625000000 : ℝ)*x 0 + (2587867513/5000000000 : ℝ)*x 1 + (2733292827/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107215239/625000000 : ℝ)^4739 ≤ (10552140743961/100000000000000 : ℝ)^3715 := by
    have hnat : (107215239 : ℕ)^4739*100000000000000^3715 ≤ 10552140743961^3715*625000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107215239 625000000 10552140743961 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2587867513/5000000000 : ℝ)^4739 ≤ (5395621779897/12500000000000 : ℝ)^3715 := by
    have hnat : (2587867513 : ℕ)^4739*12500000000000^3715 ≤ 5395621779897^3715*5000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587867513 5000000000 5395621779897 12500000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2733292827/5000000000 : ℝ)^4739 ≤ (11570721250059/25000000000000 : ℝ)^3715 := by
    have hnat : (2733292827 : ℕ)^4739*25000000000000^3715 ≤ 11570721250059^3715*5000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2733292827 5000000000 11570721250059 25000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4739/1024 : ℝ)) 4739 3715 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-107215239/625000000 : ℝ), (2587867513/5000000000 : ℝ), (2733292827/5000000000 : ℝ)] ![(10552140743961/100000000000000 : ℝ), (5395621779897/12500000000000 : ℝ), (11570721250059/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-107215239/625000000 : ℝ)|^4739 ≤ (10552140743961/100000000000000 : ℝ)^3715
        have hw : |(-107215239/625000000 : ℝ)|=(107215239/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2587867513/5000000000 : ℝ)|^4739 ≤ (5395621779897/12500000000000 : ℝ)^3715
        have hw : |(2587867513/5000000000 : ℝ)|=(2587867513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2733292827/5000000000 : ℝ)|^4739 ≤ (11570721250059/25000000000000 : ℝ)^3715
        have hw : |(2733292827/5000000000 : ℝ)|=(2733292827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1605_s2_5 (p : ℝ) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1319489947/2500000000 : ℝ)*x 0 + (-787425693/5000000000 : ℝ)*x 1 + (2733292859/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1319489947/2500000000 : ℝ)^4739 ≤ (43218218829/97656250000 : ℝ)^3715 := by
    have hnat : (1319489947 : ℕ)^4739*97656250000^3715 ≤ 43218218829^3715*2500000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319489947 2500000000 43218218829 97656250000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (787425693/5000000000 : ℝ)^4739 ≤ (236541455327/2500000000000 : ℝ)^3715 := by
    have hnat : (787425693 : ℕ)^4739*2500000000000^3715 ≤ 236541455327^3715*5000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      787425693 5000000000 236541455327 2500000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2733292859/5000000000 : ℝ)^4739 ≤ (46282885691449/100000000000000 : ℝ)^3715 := by
    have hnat : (2733292859 : ℕ)^4739*100000000000000^3715 ≤ 46282885691449^3715*5000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2733292859 5000000000 46282885691449 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4739/1024 : ℝ)) 4739 3715 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1319489947/2500000000 : ℝ), (-787425693/5000000000 : ℝ), (2733292859/5000000000 : ℝ)] ![(43218218829/97656250000 : ℝ), (236541455327/2500000000000 : ℝ), (46282885691449/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1319489947/2500000000 : ℝ)|^4739 ≤ (43218218829/97656250000 : ℝ)^3715
        have hw : |(1319489947/2500000000 : ℝ)|=(1319489947/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-787425693/5000000000 : ℝ)|^4739 ≤ (236541455327/2500000000000 : ℝ)^3715
        have hw : |(-787425693/5000000000 : ℝ)|=(787425693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2733292859/5000000000 : ℝ)|^4739 ≤ (46282885691449/100000000000000 : ℝ)^3715
        have hw : |(2733292859/5000000000 : ℝ)|=(2733292859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1605_s2_6 (p : ℝ) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (659744991/1250000000 : ℝ)*x 0 + (273329261/500000000 : ℝ)*x 1 + (-393712973/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (659744991/1250000000 : ℝ)^4739 ≤ (44255457578361/100000000000000 : ℝ)^3715 := by
    have hnat : (659744991 : ℕ)^4739*100000000000000^3715 ≤ 44255457578361^3715*1250000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659744991 1250000000 44255457578361 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (273329261/500000000 : ℝ)^4739 ≤ (9256576062589/20000000000000 : ℝ)^3715 := by
    have hnat : (273329261 : ℕ)^4739*20000000000000^3715 ≤ 9256576062589^3715*500000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273329261 500000000 9256576062589 20000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (393712973/2500000000 : ℝ)^4739 ≤ (1892332418213/20000000000000 : ℝ)^3715 := by
    have hnat : (393712973 : ℕ)^4739*20000000000000^3715 ≤ 1892332418213^3715*2500000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      393712973 2500000000 1892332418213 20000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4739/1024 : ℝ)) 4739 3715 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(659744991/1250000000 : ℝ), (273329261/500000000 : ℝ), (-393712973/2500000000 : ℝ)] ![(44255457578361/100000000000000 : ℝ), (9256576062589/20000000000000 : ℝ), (1892332418213/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(659744991/1250000000 : ℝ)|^4739 ≤ (44255457578361/100000000000000 : ℝ)^3715
        have hw : |(659744991/1250000000 : ℝ)|=(659744991/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(273329261/500000000 : ℝ)|^4739 ≤ (9256576062589/20000000000000 : ℝ)^3715
        have hw : |(273329261/500000000 : ℝ)|=(273329261/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-393712973/2500000000 : ℝ)|^4739 ≤ (1892332418213/20000000000000 : ℝ)^3715
        have hw : |(-393712973/2500000000 : ℝ)|=(393712973/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1605_s2_7 (p : ℝ) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (843166619/2000000000 : ℝ)*x 0 + (4582638931/10000000000 : ℝ)*x 1 + (3872622839/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (843166619/2000000000 : ℝ)^4739 ≤ (33226648270419/100000000000000 : ℝ)^3715 := by
    have hnat : (843166619 : ℕ)^4739*100000000000000^3715 ≤ 33226648270419^3715*2000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      843166619 2000000000 33226648270419 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4582638931/10000000000 : ℝ)^4739 ≤ (18478886452121/50000000000000 : ℝ)^3715 := by
    have hnat : (4582638931 : ℕ)^4739*50000000000000^3715 ≤ 18478886452121^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4582638931 10000000000 18478886452121 50000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3872622839/10000000000 : ℝ)^4739 ≤ (186347367567/625000000000 : ℝ)^3715 := by
    have hnat : (3872622839 : ℕ)^4739*625000000000^3715 ≤ 186347367567^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3872622839 10000000000 186347367567 625000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4739/1024 : ℝ)) 4739 3715 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(843166619/2000000000 : ℝ), (4582638931/10000000000 : ℝ), (3872622839/10000000000 : ℝ)] ![(33226648270419/100000000000000 : ℝ), (18478886452121/50000000000000 : ℝ), (186347367567/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(843166619/2000000000 : ℝ)|^4739 ≤ (33226648270419/100000000000000 : ℝ)^3715
        have hw : |(843166619/2000000000 : ℝ)|=(843166619/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4582638931/10000000000 : ℝ)|^4739 ≤ (18478886452121/50000000000000 : ℝ)^3715
        have hw : |(4582638931/10000000000 : ℝ)|=(4582638931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3872622839/10000000000 : ℝ)|^4739 ≤ (186347367567/625000000000 : ℝ)^3715
        have hw : |(3872622839/10000000000 : ℝ)|=(3872622839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1605_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (172058521/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17883/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (113/1250 : ℝ)*pair X i i ≤ pair X i h) :
    (10253/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3303/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17883/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (113/1250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17883/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (113/1250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17883/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (113/1250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17883/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (113/1250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17883/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (113/1250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17883/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (113/1250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (113/1250 : ℝ) ^ (4735/1024 : ℝ) ≤ (149038461141807/10000000000000000000 : ℝ) := by
    have hpowers : (113/1250 : ℝ)^4735 ≤ (149038461141807/10000000000000000000 : ℝ)^1024 := by
      have hnat : (113 : ℕ)^4735*10000000000000000000^1024 ≤ 149038461141807^1024*1250^4735 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        113 1250 149038461141807 10000000000000000000 4735 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (113/1250 : ℝ)) (X := (149038461141807/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4735 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17883/100000 : ℝ) ^ (4735/1024 : ℝ) ≤ (8733871318539143/25000000000000000000 : ℝ) := by
    have hpowers : (17883/100000 : ℝ)^4735 ≤ (8733871318539143/25000000000000000000 : ℝ)^1024 := by
      have hnat : (17883 : ℕ)^4735*25000000000000000000^1024 ≤ 8733871318539143^1024*100000^4735 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17883 100000 8733871318539143 25000000000000000000 4735 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17883/100000 : ℝ)) (X := (8733871318539143/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4735 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000149038461141807/5000000000000000000 : ℝ) ≤ (312502014435079/312500000000000 : ℝ) ^ (4735/1024 : ℝ) := by
    have hpowers : (5000149038461141807/5000000000000000000 : ℝ)^1024 ≤ (312502014435079/312500000000000 : ℝ)^4735 := by
      have hnat : (5000149038461141807 : ℕ)^1024*312500000000000^4735 ≤ 312502014435079^4735*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000149038461141807 5000000000000000000 312502014435079 312500000000000 1024 4735 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312502014435079/312500000000000 : ℝ)) (X := (5000149038461141807/5000000000000000000 : ℝ)) (by norm_num) 4735 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50018212934942787321/50000000000000000000 : ℝ) ≤ (312524613759/312500000000 : ℝ) ^ (4735/1024 : ℝ) := by
    have hpowers : (50018212934942787321/50000000000000000000 : ℝ)^1024 ≤ (312524613759/312500000000 : ℝ)^4735 := by
      have hnat : (50018212934942787321 : ℕ)^1024*312500000000^4735 ≤ 312524613759^4735*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018212934942787321 50000000000000000000 312524613759 312500000000 1024 4735 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312524613759/312500000000 : ℝ)) (X := (50018212934942787321/50000000000000000000 : ℝ)) (by norm_num) 4735 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508733871318539143/12500000000000000000 : ℝ) ≤ (312547213082921/312500000000000 : ℝ) ^ (4735/1024 : ℝ) := by
    have hpowers : (12508733871318539143/12500000000000000000 : ℝ)^1024 ≤ (312547213082921/312500000000000 : ℝ)^4735 := by
      have hnat : (12508733871318539143 : ℕ)^1024*312500000000000^4735 ≤ 312547213082921^4735*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508733871318539143 12500000000000000000 312547213082921 312500000000000 1024 4735 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312547213082921/312500000000000 : ℝ)) (X := (12508733871318539143/12500000000000000000 : ℝ)) (by norm_num) 4735 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(149038461141807/10000000000000000000 : ℝ) ≤ ((2763046717872911917/2763437500000000000 : ℝ)+2*(22599323921/27634375000000 : ℝ)*(113/1250 : ℝ))^(4735/1024 : ℝ) := by
    rw [show (2763046717872911917/2763437500000000000 : ℝ)+2*(22599323921/27634375000000 : ℝ)*(113/1250 : ℝ)=(312502014435079/312500000000000 : ℝ) by norm_num, show 1+2*(149038461141807/10000000000000000000 : ℝ)=(5000149038461141807/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8733871318539143/25000000000000000000 : ℝ)+(149038461141807/10000000000000000000 : ℝ) ≤ ((2763046717872911917/2763437500000000000 : ℝ)+(22599323921/27634375000000 : ℝ)*((17883/100000 : ℝ)+(113/1250 : ℝ)))^(4735/1024 : ℝ) := by
    rw [show (2763046717872911917/2763437500000000000 : ℝ)+(22599323921/27634375000000 : ℝ)*((17883/100000 : ℝ)+(113/1250 : ℝ))=(312524613759/312500000000 : ℝ) by norm_num, show 1+(8733871318539143/25000000000000000000 : ℝ)+(149038461141807/10000000000000000000 : ℝ)=(50018212934942787321/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8733871318539143/25000000000000000000 : ℝ) ≤ ((2763046717872911917/2763437500000000000 : ℝ)+2*(22599323921/27634375000000 : ℝ)*(17883/100000 : ℝ))^(4735/1024 : ℝ) := by
    rw [show (2763046717872911917/2763437500000000000 : ℝ)+2*(22599323921/27634375000000 : ℝ)*(17883/100000 : ℝ)=(312547213082921/312500000000000 : ℝ) by norm_num, show 1+2*(8733871318539143/25000000000000000000 : ℝ)=(12508733871318539143/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2763046717872911917/2763437500000000000 : ℝ)*(X 1 0+X 2 0)+(22599323921/27634375000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4735/1024 : ℝ)) (lo := (113/1250 : ℝ)) (hi := (17883/100000 : ℝ)) (c := (2763046717872911917/2763437500000000000 : ℝ)) (alpha := (22599323921/27634375000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2763046717872911917/2763437500000000000 : ℝ)*(X 0 1+X 2 1)+(22599323921/27634375000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4735/1024 : ℝ)) (lo := (113/1250 : ℝ)) (hi := (17883/100000 : ℝ)) (c := (2763046717872911917/2763437500000000000 : ℝ)) (alpha := (22599323921/27634375000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2763046717872911917/2763437500000000000 : ℝ)*(X 0 2+X 1 2)+(22599323921/27634375000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4735/1024 : ℝ)) (lo := (113/1250 : ℝ)) (hi := (17883/100000 : ℝ)) (c := (2763046717872911917/2763437500000000000 : ℝ)) (alpha := (22599323921/27634375000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-107210073/625000000 : ℝ)*X 0 0+(2734458367/5000000000 : ℝ)*X 0 1+(1034685847/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1605_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5356374667/10000000000 : ℝ)*X 1 0+(-1868007927/10000000000 : ℝ)*X 1 1+(2586714571/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1605_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((10461669/19531250 : ℝ)*X 2 0+(646678663/1250000000 : ℝ)*X 2 1+(-1868007899/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1605_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1053907657/2500000000 : ℝ)*X 0 0+(3866932187/10000000000 : ℝ)*X 0 1+(573533421/1250000000 : ℝ)*X 0 2+(1053907657/2500000000 : ℝ)*X 1 0+(3866932187/10000000000 : ℝ)*X 1 1+(573533421/1250000000 : ℝ)*X 1 2+(1053907657/2500000000 : ℝ)*X 2 0+(3866932187/10000000000 : ℝ)*X 2 1+(573533421/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1605_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-107215239/625000000 : ℝ)*X 0 0+(2587867513/5000000000 : ℝ)*X 0 1+(2733292827/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1605_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1319489947/2500000000 : ℝ)*X 1 0+(-787425693/5000000000 : ℝ)*X 1 1+(2733292859/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1605_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((659744991/1250000000 : ℝ)*X 2 0+(273329261/500000000 : ℝ)*X 2 1+(-393712973/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1605_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((843166619/2000000000 : ℝ)*X 0 0+(4582638931/10000000000 : ℝ)*X 0 1+(3872622839/10000000000 : ℝ)*X 0 2+(843166619/2000000000 : ℝ)*X 1 0+(4582638931/10000000000 : ℝ)*X 1 1+(3872622839/10000000000 : ℝ)*X 1 2+(843166619/2000000000 : ℝ)*X 2 0+(4582638931/10000000000 : ℝ)*X 2 1+(3872622839/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1605_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (266262565040373410129792739/34542968750000000000000000000000 : ℝ) := by norm_num
    linear_combination (274397129/20000000000000 : ℝ)*(base19) + (1233452109/100000000000000 : ℝ)*(base23) + (5432487/20000000000000 : ℝ)*(lower2) + (185793323/100000000000000 : ℝ)*(upper3) + (154148473/100000000000000 : ℝ)*(upper5) + (2385299720122081/100000000000000 : ℝ)*(major0) + (2385299720122081/100000000000000 : ℝ)*(major1) + (2385299720122081/100000000000000 : ℝ)*(major2) + (1692126762997141/50000000000000 : ℝ)*(sp0) + (846066832821009/25000000000000 : ℝ)*(sp1) + (846066867454393/25000000000000 : ℝ)*(sp2) + (1386324122289287/100000000000000 : ℝ)*(sp3) + (15177275399/100000000000000 : ℝ)*(sp4) + (3178873339/50000000000000 : ℝ)*(sp7) + (346582620008991/25000000000000 : ℝ)*(f.failure) + (3384268703269681/100000000000000 : ℝ)*(f.sum) + (86568091900011/22107500000000000000000000000 : ℝ)*base65 + (69581162787745527/276343750000000000000000000000000 : ℝ)*base67 + (482991219314598223/276343750000000000000000000000000 : ℝ)*base70 + (773312708111848223/276343750000000000000000000000000 : ℝ)*base72 + (105483474596507/44215000000000000000000000000 : ℝ)*base73 + (2196216600918598223/276343750000000000000000000000000 : ℝ)*base76 + (758822707345276777/276343750000000000000000000000000 : ℝ)*base77 + (2099272230287816973/276343750000000000000000000000000 : ℝ)*base80 + (46399693871109/22107500000000000000000000000 : ℝ)*base82 + (26837689/2500000000000000000000 : ℝ)*base90 + (26837689/2500000000000000000000 : ℝ)*base92 + (26837689/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (388783020582650591712741531/138171875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (225317351/100000000000000 : ℝ)*(base19) + (447914493/100000000000000 : ℝ)*(base23) + (955023/3125000000000 : ℝ)*(upper3) + (96033717/100000000000000 : ℝ)*(lower4) + (8152833/100000000000000 : ℝ)*(upper5) + (605826030246263/25000000000000 : ℝ)*(major0) + (605826030246263/25000000000000 : ℝ)*(major1) + (605826030246263/25000000000000 : ℝ)*(major2) + (210262699/100000000000000 : ℝ)*(sp0) + (3402732881/100000000000000 : ℝ)*(sp1) + (1719094695595043/50000000000000 : ℝ)*(sp4) + (429773246675319/12500000000000 : ℝ)*(sp5) + (859547288384573/25000000000000 : ℝ)*(sp6) + (352104636681297/25000000000000 : ℝ)*(sp7) + (352104636681297/25000000000000 : ℝ)*(f.failure) + (214886850090799/6250000000000 : ℝ)*(f.sum) + (49827158359429/11053750000000000000000000000 : ℝ)*base66 + (15719059430963213/8635742187500000000000000000000 : ℝ)*base68 + (367728073082489533/138171875000000000000000000000000 : ℝ)*base70 + (93968305991020783/138171875000000000000000000000000 : ℝ)*base72 + (35895020904291/44215000000000000000000000000 : ℝ)*base74 + (70339160182056963/8635742187500000000000000000000 : ℝ)*base76 + (409039949811440079/69085937500000000000000000000000 : ℝ)*base78 + (175493448047190079/69085937500000000000000000000000 : ℝ)*base80 + (9902612068731/11053750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (10181737/2500000000000000000000 : ℝ)*base89 + (10181737/2500000000000000000000 : ℝ)*base91 + (10181737/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1605_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (172058521/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17883/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (113/1250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10253/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3303/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1605_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1605_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (172058521/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10253/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3303/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1605_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1605_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1605_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (172058521/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10253/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3303/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1605_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
