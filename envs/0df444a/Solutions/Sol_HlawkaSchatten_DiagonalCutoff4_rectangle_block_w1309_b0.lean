-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1309_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:38:44.292646+00:00
-- url     : https://prove2.me/submissions/d8783e36-6402-4102-b30d-4314ac02aca5

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
theorem support_rectangle_w1309_s0_0 (p : ℝ) (hpa : (1067/256 : ℝ) ≤ p) (hpb : p ≤ (4269/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1828816603/10000000000 : ℝ)*x 0 + (375705739/625000000 : ℝ)*x 1 + (600371849/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1828816603/10000000000 : ℝ)^4269 ≤ (5349445915413/50000000000000 : ℝ)^3245 := by
    have hnat : (1828816603 : ℕ)^4269*50000000000000^3245 ≤ 5349445915413^3245*10000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1828816603 10000000000 5349445915413 50000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (375705739/625000000 : ℝ)^4269 ≤ (25596958683197/50000000000000 : ℝ)^3245 := by
    have hnat : (375705739 : ℕ)^4269*50000000000000^3245 ≤ 25596958683197^3245*625000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      375705739 625000000 25596958683197 50000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (600371849/1250000000 : ℝ)^4269 ≤ (38107190785227/100000000000000 : ℝ)^3245 := by
    have hnat : (600371849 : ℕ)^4269*100000000000000^3245 ≤ 38107190785227^3245*1250000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      600371849 1250000000 38107190785227 100000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4269/1024 : ℝ)) 4269 3245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1828816603/10000000000 : ℝ), (375705739/625000000 : ℝ), (600371849/1250000000 : ℝ)] ![(5349445915413/50000000000000 : ℝ), (25596958683197/50000000000000 : ℝ), (38107190785227/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1828816603/10000000000 : ℝ)|^4269 ≤ (5349445915413/50000000000000 : ℝ)^3245
        have hw : |(-1828816603/10000000000 : ℝ)|=(1828816603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(375705739/625000000 : ℝ)|^4269 ≤ (25596958683197/50000000000000 : ℝ)^3245
        have hw : |(375705739/625000000 : ℝ)|=(375705739/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(600371849/1250000000 : ℝ)|^4269 ≤ (38107190785227/100000000000000 : ℝ)^3245
        have hw : |(600371849/1250000000 : ℝ)|=(600371849/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1309_s0_1 (p : ℝ) (hpa : (1067/256 : ℝ) ≤ p) (hpb : p ≤ (4269/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2752755777/5000000000 : ℝ)*x 0 + (-251728293/1000000000 : ℝ)*x 1 + (4802974717/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2752755777/5000000000 : ℝ)^4269 ≤ (45604024544887/100000000000000 : ℝ)^3245 := by
    have hnat : (2752755777 : ℕ)^4269*100000000000000^3245 ≤ 45604024544887^3245*5000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2752755777 5000000000 45604024544887 100000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (251728293/1000000000 : ℝ)^4269 ≤ (3257757086363/20000000000000 : ℝ)^3245 := by
    have hnat : (251728293 : ℕ)^4269*20000000000000^3245 ≤ 3257757086363^3245*1000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      251728293 1000000000 3257757086363 20000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4802974717/10000000000 : ℝ)^4269 ≤ (38107190002393/100000000000000 : ℝ)^3245 := by
    have hnat : (4802974717 : ℕ)^4269*100000000000000^3245 ≤ 38107190002393^3245*10000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4802974717 10000000000 38107190002393 100000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4269/1024 : ℝ)) 4269 3245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2752755777/5000000000 : ℝ), (-251728293/1000000000 : ℝ), (4802974717/10000000000 : ℝ)] ![(45604024544887/100000000000000 : ℝ), (3257757086363/20000000000000 : ℝ), (38107190002393/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2752755777/5000000000 : ℝ)|^4269 ≤ (45604024544887/100000000000000 : ℝ)^3245
        have hw : |(2752755777/5000000000 : ℝ)|=(2752755777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-251728293/1000000000 : ℝ)|^4269 ≤ (3257757086363/20000000000000 : ℝ)^3245
        have hw : |(-251728293/1000000000 : ℝ)|=(251728293/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4802974717/10000000000 : ℝ)|^4269 ≤ (38107190002393/100000000000000 : ℝ)^3245
        have hw : |(4802974717/10000000000 : ℝ)|=(4802974717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1309_s0_2 (p : ℝ) (hpa : (1067/256 : ℝ) ≤ p) (hpb : p ≤ (4269/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (275275551/500000000 : ℝ)*x 0 + (4802975217/10000000000 : ℝ)*x 1 + (-2517283001/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (275275551/500000000 : ℝ)^4269 ≤ (9120803745151/20000000000000 : ℝ)^3245 := by
    have hnat : (275275551 : ℕ)^4269*20000000000000^3245 ≤ 9120803745151^3245*500000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275275551 500000000 9120803745151 20000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4802975217/10000000000 : ℝ)^4269 ≤ (38107195221283/100000000000000 : ℝ)^3245 := by
    have hnat : (4802975217 : ℕ)^4269*100000000000000^3245 ≤ 38107195221283^3245*10000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4802975217 10000000000 38107195221283 100000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2517283001/10000000000 : ℝ)^4269 ≤ (8144393018109/50000000000000 : ℝ)^3245 := by
    have hnat : (2517283001 : ℕ)^4269*50000000000000^3245 ≤ 8144393018109^3245*10000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2517283001 10000000000 8144393018109 50000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4269/1024 : ℝ)) 4269 3245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(275275551/500000000 : ℝ), (4802975217/10000000000 : ℝ), (-2517283001/10000000000 : ℝ)] ![(9120803745151/20000000000000 : ℝ), (38107195221283/100000000000000 : ℝ), (8144393018109/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(275275551/500000000 : ℝ)|^4269 ≤ (9120803745151/20000000000000 : ℝ)^3245
        have hw : |(275275551/500000000 : ℝ)|=(275275551/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4802975217/10000000000 : ℝ)|^4269 ≤ (38107195221283/100000000000000 : ℝ)^3245
        have hw : |(4802975217/10000000000 : ℝ)|=(4802975217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2517283001/10000000000 : ℝ)|^4269 ≤ (8144393018109/50000000000000 : ℝ)^3245
        have hw : |(-2517283001/10000000000 : ℝ)|=(2517283001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1309_s0_3 (p : ℝ) (hpa : (1067/256 : ℝ) ≤ p) (hpb : p ≤ (4269/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4183730039/10000000000 : ℝ)*x 0 + (777092541/2500000000 : ℝ)*x 1 + (1401972197/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4183730039/10000000000 : ℝ)^4269 ≤ (31779229993309/100000000000000 : ℝ)^3245 := by
    have hnat : (4183730039 : ℕ)^4269*100000000000000^3245 ≤ 31779229993309^3245*10000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4183730039 10000000000 31779229993309 100000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (777092541/2500000000 : ℝ)^4269 ≤ (268723194553/1250000000000 : ℝ)^3245 := by
    have hnat : (777092541 : ℕ)^4269*1250000000000^3245 ≤ 268723194553^3245*2500000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      777092541 2500000000 268723194553 1250000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1401972197/2500000000 : ℝ)^4269 ≤ (11680728606583/25000000000000 : ℝ)^3245 := by
    have hnat : (1401972197 : ℕ)^4269*25000000000000^3245 ≤ 11680728606583^3245*2500000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1401972197 2500000000 11680728606583 25000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4269/1024 : ℝ)) 4269 3245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4183730039/10000000000 : ℝ), (777092541/2500000000 : ℝ), (1401972197/2500000000 : ℝ)] ![(31779229993309/100000000000000 : ℝ), (268723194553/1250000000000 : ℝ), (11680728606583/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4183730039/10000000000 : ℝ)|^4269 ≤ (31779229993309/100000000000000 : ℝ)^3245
        have hw : |(4183730039/10000000000 : ℝ)|=(4183730039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(777092541/2500000000 : ℝ)|^4269 ≤ (268723194553/1250000000000 : ℝ)^3245
        have hw : |(777092541/2500000000 : ℝ)|=(777092541/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1401972197/2500000000 : ℝ)|^4269 ≤ (11680728606583/25000000000000 : ℝ)^3245
        have hw : |(1401972197/2500000000 : ℝ)|=(1401972197/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1309_s0_4 (p : ℝ) (hpa : (1067/256 : ℝ) ≤ p) (hpb : p ≤ (4269/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-458362261/2500000000 : ℝ)*x 0 + (2417065633/5000000000 : ℝ)*x 1 + (5979024843/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (458362261/2500000000 : ℝ)^4269 ≤ (5367279285921/50000000000000 : ℝ)^3245 := by
    have hnat : (458362261 : ℕ)^4269*50000000000000^3245 ≤ 5367279285921^3245*2500000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      458362261 2500000000 5367279285921 50000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2417065633/5000000000 : ℝ)^4269 ≤ (19216363761201/50000000000000 : ℝ)^3245 := by
    have hnat : (2417065633 : ℕ)^4269*50000000000000^3245 ≤ 19216363761201^3245*5000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2417065633 5000000000 19216363761201 50000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5979024843/10000000000 : ℝ)^4269 ≤ (10166542779059/20000000000000 : ℝ)^3245 := by
    have hnat : (5979024843 : ℕ)^4269*20000000000000^3245 ≤ 10166542779059^3245*10000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5979024843 10000000000 10166542779059 20000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4269/1024 : ℝ)) 4269 3245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-458362261/2500000000 : ℝ), (2417065633/5000000000 : ℝ), (5979024843/10000000000 : ℝ)] ![(5367279285921/50000000000000 : ℝ), (19216363761201/50000000000000 : ℝ), (10166542779059/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-458362261/2500000000 : ℝ)|^4269 ≤ (5367279285921/50000000000000 : ℝ)^3245
        have hw : |(-458362261/2500000000 : ℝ)|=(458362261/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2417065633/5000000000 : ℝ)|^4269 ≤ (19216363761201/50000000000000 : ℝ)^3245
        have hw : |(2417065633/5000000000 : ℝ)|=(2417065633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5979024843/10000000000 : ℝ)|^4269 ≤ (10166542779059/20000000000000 : ℝ)^3245
        have hw : |(5979024843/10000000000 : ℝ)|=(5979024843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1309_s0_5 (p : ℝ) (hpa : (1067/256 : ℝ) ≤ p) (hpb : p ≤ (4269/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2588215411/5000000000 : ℝ)*x 0 + (-53649343/400000000 : ℝ)*x 1 + (2989512367/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2588215411/5000000000 : ℝ)^4269 ≤ (5256530366899/12500000000000 : ℝ)^3245 := by
    have hnat : (2588215411 : ℕ)^4269*12500000000000^3245 ≤ 5256530366899^3245*5000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588215411 5000000000 5256530366899 12500000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (53649343/400000000 : ℝ)^4269 ≤ (7115044374939/100000000000000 : ℝ)^3245 := by
    have hnat : (53649343 : ℕ)^4269*100000000000000^3245 ≤ 7115044374939^3245*400000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53649343 400000000 7115044374939 100000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2989512367/5000000000 : ℝ)^4269 ≤ (50832712676163/100000000000000 : ℝ)^3245 := by
    have hnat : (2989512367 : ℕ)^4269*100000000000000^3245 ≤ 50832712676163^3245*5000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2989512367 5000000000 50832712676163 100000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4269/1024 : ℝ)) 4269 3245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2588215411/5000000000 : ℝ), (-53649343/400000000 : ℝ), (2989512367/5000000000 : ℝ)] ![(5256530366899/12500000000000 : ℝ), (7115044374939/100000000000000 : ℝ), (50832712676163/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2588215411/5000000000 : ℝ)|^4269 ≤ (5256530366899/12500000000000 : ℝ)^3245
        have hw : |(2588215411/5000000000 : ℝ)|=(2588215411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-53649343/400000000 : ℝ)|^4269 ≤ (7115044374939/100000000000000 : ℝ)^3245
        have hw : |(-53649343/400000000 : ℝ)|=(53649343/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2989512367/5000000000 : ℝ)|^4269 ≤ (50832712676163/100000000000000 : ℝ)^3245
        have hw : |(2989512367/5000000000 : ℝ)|=(2989512367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1309_s0_6 (p : ℝ) (hpa : (1067/256 : ℝ) ≤ p) (hpb : p ≤ (4269/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5176430851/10000000000 : ℝ)*x 0 + (5979024793/10000000000 : ℝ)*x 1 + (-268246687/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5176430851/10000000000 : ℝ)^4269 ≤ (336417945961/800000000000 : ℝ)^3245 := by
    have hnat : (5176430851 : ℕ)^4269*800000000000^3245 ≤ 336417945961^3245*10000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176430851 10000000000 336417945961 800000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5979024793/10000000000 : ℝ)^4269 ≤ (2541635666803/5000000000000 : ℝ)^3245 := by
    have hnat : (5979024793 : ℕ)^4269*5000000000000^3245 ≤ 2541635666803^3245*10000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5979024793 10000000000 2541635666803 5000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (268246687/2000000000 : ℝ)^4269 ≤ (3557521698949/50000000000000 : ℝ)^3245 := by
    have hnat : (268246687 : ℕ)^4269*50000000000000^3245 ≤ 3557521698949^3245*2000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268246687 2000000000 3557521698949 50000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4269/1024 : ℝ)) 4269 3245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5176430851/10000000000 : ℝ), (5979024793/10000000000 : ℝ), (-268246687/2000000000 : ℝ)] ![(336417945961/800000000000 : ℝ), (2541635666803/5000000000000 : ℝ), (3557521698949/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5176430851/10000000000 : ℝ)|^4269 ≤ (336417945961/800000000000 : ℝ)^3245
        have hw : |(5176430851/10000000000 : ℝ)|=(5176430851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5979024793/10000000000 : ℝ)|^4269 ≤ (2541635666803/5000000000000 : ℝ)^3245
        have hw : |(5979024793/10000000000 : ℝ)|=(5979024793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-268246687/2000000000 : ℝ)|^4269 ≤ (3557521698949/50000000000000 : ℝ)^3245
        have hw : |(-268246687/2000000000 : ℝ)|=(268246687/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1309_s0_7 (p : ℝ) (hpa : (1067/256 : ℝ) ≤ p) (hpb : p ≤ (4269/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2096655927/5000000000 : ℝ)*x 0 + (173232473/312500000 : ℝ)*x 1 + (3175117107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2096655927/5000000000 : ℝ)^4269 ≤ (7968753653189/25000000000000 : ℝ)^3245 := by
    have hnat : (2096655927 : ℕ)^4269*25000000000000^3245 ≤ 7968753653189^3245*5000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2096655927 5000000000 7968753653189 25000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (173232473/312500000 : ℝ)^4269 ≤ (1150444486513/2500000000000 : ℝ)^3245 := by
    have hnat : (173232473 : ℕ)^4269*2500000000000^3245 ≤ 1150444486513^3245*312500000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173232473 312500000 1150444486513 2500000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3175117107/10000000000 : ℝ)^4269 ≤ (22107205908383/100000000000000 : ℝ)^3245 := by
    have hnat : (3175117107 : ℕ)^4269*100000000000000^3245 ≤ 22107205908383^3245*10000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3175117107 10000000000 22107205908383 100000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4269/1024 : ℝ)) 4269 3245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2096655927/5000000000 : ℝ), (173232473/312500000 : ℝ), (3175117107/10000000000 : ℝ)] ![(7968753653189/25000000000000 : ℝ), (1150444486513/2500000000000 : ℝ), (22107205908383/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2096655927/5000000000 : ℝ)|^4269 ≤ (7968753653189/25000000000000 : ℝ)^3245
        have hw : |(2096655927/5000000000 : ℝ)|=(2096655927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(173232473/312500000 : ℝ)|^4269 ≤ (1150444486513/2500000000000 : ℝ)^3245
        have hw : |(173232473/312500000 : ℝ)|=(173232473/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3175117107/10000000000 : ℝ)|^4269 ≤ (22107205908383/100000000000000 : ℝ)^3245
        have hw : |(3175117107/10000000000 : ℝ)|=(3175117107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1309_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1067/256 : ℝ) ≤ p) (hpb : p ≤ (4269/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30685957/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (291/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27111/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (1067/256 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^1067 ≤ (0 : ℝ)^256 := by
      have hnat : (0 : ℕ)^1067*1^256 ≤ 0^256*1^1067 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 1067 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 1067 256 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (1067/256 : ℝ) ≤ (219481782935309907/10000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^1067 ≤ (219481782935309907/10000000000000000000 : ℝ)^256 := by
      have hnat : (2 : ℕ)^1067*10000000000000000000^256 ≤ 219481782935309907^256*5^1067 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 219481782935309907 10000000000000000000 1067 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (219481782935309907/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1067 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (1067/256 : ℝ) := by
    have hpowers : (1 : ℝ)^256 ≤ (1 : ℝ)^1067 := by
      have hnat : (1 : ℕ)^256*1^1067 ≤ 1^1067*1^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 256 1067 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 1067 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (10219481782935309907/10000000000000000000 : ℝ) ≤ (628264094161913/625000000000000 : ℝ) ^ (1067/256 : ℝ) := by
    have hpowers : (10219481782935309907/10000000000000000000 : ℝ)^256 ≤ (628264094161913/625000000000000 : ℝ)^1067 := by
      have hnat : (10219481782935309907 : ℕ)^256*625000000000000^1067 ≤ 628264094161913^1067*10000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10219481782935309907 10000000000000000000 628264094161913 625000000000000 256 1067 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (628264094161913/625000000000000 : ℝ)) (X := (10219481782935309907/10000000000000000000 : ℝ)) (by norm_num) 1067 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (5219481782935309907/5000000000000000000 : ℝ) ≤ (315764094161913/312500000000000 : ℝ) ^ (1067/256 : ℝ) := by
    have hpowers : (5219481782935309907/5000000000000000000 : ℝ)^256 ≤ (315764094161913/312500000000000 : ℝ)^1067 := by
      have hnat : (5219481782935309907 : ℕ)^256*312500000000000^1067 ≤ 315764094161913^1067*5000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5219481782935309907 5000000000000000000 315764094161913 312500000000000 256 1067 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (315764094161913/312500000000000 : ℝ)) (X := (5219481782935309907/5000000000000000000 : ℝ)) (by norm_num) 1067 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(3264094161913/250000000000000 : ℝ)*(0 : ℝ))^(1067/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(3264094161913/250000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(219481782935309907/10000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(3264094161913/250000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(1067/256 : ℝ) := by
    rw [show (1 : ℝ)+(3264094161913/250000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(628264094161913/625000000000000 : ℝ) by norm_num, show 1+(219481782935309907/10000000000000000000 : ℝ)+(0 : ℝ)=(10219481782935309907/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(219481782935309907/10000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(3264094161913/250000000000000 : ℝ)*(2/5 : ℝ))^(1067/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(3264094161913/250000000000000 : ℝ)*(2/5 : ℝ)=(315764094161913/312500000000000 : ℝ) by norm_num, show 1+2*(219481782935309907/10000000000000000000 : ℝ)=(5219481782935309907/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(3264094161913/250000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1067/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (3264094161913/250000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(3264094161913/250000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1067/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (3264094161913/250000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(3264094161913/250000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1067/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (3264094161913/250000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1828816603/10000000000 : ℝ)*X 0 0+(375705739/625000000 : ℝ)*X 0 1+(600371849/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1309_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2752755777/5000000000 : ℝ)*X 1 0+(-251728293/1000000000 : ℝ)*X 1 1+(4802974717/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1309_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((275275551/500000000 : ℝ)*X 2 0+(4802975217/10000000000 : ℝ)*X 2 1+(-2517283001/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1309_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4183730039/10000000000 : ℝ)*X 0 0+(777092541/2500000000 : ℝ)*X 0 1+(1401972197/2500000000 : ℝ)*X 0 2+(4183730039/10000000000 : ℝ)*X 1 0+(777092541/2500000000 : ℝ)*X 1 1+(1401972197/2500000000 : ℝ)*X 1 2+(4183730039/10000000000 : ℝ)*X 2 0+(777092541/2500000000 : ℝ)*X 2 1+(1401972197/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1309_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-458362261/2500000000 : ℝ)*X 0 0+(2417065633/5000000000 : ℝ)*X 0 1+(5979024843/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1309_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2588215411/5000000000 : ℝ)*X 1 0+(-53649343/400000000 : ℝ)*X 1 1+(2989512367/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1309_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5176430851/10000000000 : ℝ)*X 2 0+(5979024793/10000000000 : ℝ)*X 2 1+(-268246687/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1309_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2096655927/5000000000 : ℝ)*X 0 0+(173232473/312500000 : ℝ)*X 0 1+(3175117107/10000000000 : ℝ)*X 0 2+(2096655927/5000000000 : ℝ)*X 1 0+(173232473/312500000 : ℝ)*X 1 1+(3175117107/10000000000 : ℝ)*X 1 2+(2096655927/5000000000 : ℝ)*X 2 0+(173232473/312500000 : ℝ)*X 2 1+(3175117107/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1309_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14753125629348946335261/6250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13743449/25000000000000 : ℝ)*(base1) + (13769683/2000000000000 : ℝ)*(base19) + (152053013/25000000000000 : ℝ)*(base23) + (21159019/25000000000000 : ℝ)*(upper3) + (40602267/100000000000000 : ℝ)*(upper5) + (613840380466167/100000000000000 : ℝ)*(major0) + (613840380466167/100000000000000 : ℝ)*(major1) + (613840380466167/100000000000000 : ℝ)*(major2) + (206899917891969/25000000000000 : ℝ)*(sp0) + (165520194720373/20000000000000 : ℝ)*(sp1) + (827601053873963/100000000000000 : ℝ)*(sp2) + (16003117488129/4000000000000 : ℝ)*(sp3) + (409098387/20000000000000 : ℝ)*(sp4) + (1027985959/100000000000000 : ℝ)*(sp7) + (20003951008149/5000000000000 : ℝ)*(f.failure) + (165520332417203/20000000000000 : ℝ)*(f.sum) + (16746011584971/12500000000000000000000000000 : ℝ)*base65 + (116233720047471/25000000000000000000000000000 : ℝ)*base67 + (485993747471/25000000000000000000000000000 : ℝ)*base69 + (9083067222471/25000000000000000000000000000 : ℝ)*base71 + (55517543072471/12500000000000000000000000000 : ℝ)*base73 + (26662888547471/25000000000000000000000000000 : ℝ)*base75 + (3229965972471/25000000000000000000000000000 : ℝ)*base77 + (102823984122471/25000000000000000000000000000 : ℝ)*base79 + (1989629622471/12500000000000000000000000000 : ℝ)*base81 + (136407/100000000000000000000 : ℝ)*base90 + (136407/100000000000000000000 : ℝ)*base92 + (136407/100000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9239858776288274751/1000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1107422623/50000000000000 : ℝ)*(base19) + (2241504841/100000000000000 : ℝ)*(base23) + (97713461/100000000000000 : ℝ)*(base32) + (152831247/50000000000000 : ℝ)*(upper3) + (112117041/50000000000000 : ℝ)*(upper5) + (80980202495387/12500000000000 : ℝ)*(major0) + (80980202495387/12500000000000 : ℝ)*(major1) + (80980202495387/12500000000000 : ℝ)*(major2) + (4892655609/100000000000000 : ℝ)*(sp1) + (5235047913/100000000000000 : ℝ)*(sp2) + (27295097819097/3125000000000 : ℝ)*(sp4) + (3493744090841/400000000000 : ℝ)*(sp5) + (873435653658351/100000000000000 : ℝ)*(sp6) + (422239704006327/100000000000000 : ℝ)*(sp7) + (422239801719787/100000000000000 : ℝ)*(f.failure) + (27295097819097/3125000000000 : ℝ)*(f.sum) + (1551614828897/781250000000000000000000000 : ℝ)*base66 + (6166666295331/3125000000000000000000000000 : ℝ)*base67 + (217393264853/1562500000000000000000000000 : ℝ)*base69 + (16825961854669/3125000000000000000000000000 : ℝ)*base72 + (2788645857831/1562500000000000000000000000 : ℝ)*base73 + (14659289973419/3125000000000000000000000000 : ℝ)*base76 + (3590831147261/781250000000000000000000000 : ℝ)*base78 + (27271742454669/3125000000000000000000000000 : ℝ)*base80 + (364704093787/3125000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (10068841/2000000000000000000000 : ℝ)*base90 + (10068841/2000000000000000000000 : ℝ)*base92 + (10068841/2000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1309_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1067/256 : ℝ) ≤ p) (hpb : p ≤ (4269/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30685957/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (291/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27111/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1309_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1309_s1_0 (p : ℝ) (hpa : (1067/256 : ℝ) ≤ p) (hpb : p ≤ (4269/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-252299481/1250000000 : ℝ)*x 0 + (113145427/200000000 : ℝ)*x 1 + (629451889/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (252299481/1250000000 : ℝ)^4269 ≤ (6090633681959/50000000000000 : ℝ)^3245 := by
    have hnat : (252299481 : ℕ)^4269*50000000000000^3245 ≤ 6090633681959^3245*1250000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      252299481 1250000000 6090633681959 50000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (113145427/200000000 : ℝ)^4269 ≤ (47264937020761/100000000000000 : ℝ)^3245 := by
    have hnat : (113145427 : ℕ)^4269*100000000000000^3245 ≤ 47264937020761^3245*200000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      113145427 200000000 47264937020761 100000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (629451889/1250000000 : ℝ)^4269 ≤ (8110759118749/20000000000000 : ℝ)^3245 := by
    have hnat : (629451889 : ℕ)^4269*20000000000000^3245 ≤ 8110759118749^3245*1250000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      629451889 1250000000 8110759118749 20000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4269/1024 : ℝ)) 4269 3245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-252299481/1250000000 : ℝ), (113145427/200000000 : ℝ), (629451889/1250000000 : ℝ)] ![(6090633681959/50000000000000 : ℝ), (47264937020761/100000000000000 : ℝ), (8110759118749/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-252299481/1250000000 : ℝ)|^4269 ≤ (6090633681959/50000000000000 : ℝ)^3245
        have hw : |(-252299481/1250000000 : ℝ)|=(252299481/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(113145427/200000000 : ℝ)|^4269 ≤ (47264937020761/100000000000000 : ℝ)^3245
        have hw : |(113145427/200000000 : ℝ)|=(113145427/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(629451889/1250000000 : ℝ)|^4269 ≤ (8110759118749/20000000000000 : ℝ)^3245
        have hw : |(629451889/1250000000 : ℝ)|=(629451889/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1309_s1_1 (p : ℝ) (hpa : (1067/256 : ℝ) ≤ p) (hpb : p ≤ (4269/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5409186281/10000000000 : ℝ)*x 0 + (-2351084211/10000000000 : ℝ)*x 1 + (20142461/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5409186281/10000000000 : ℝ)^4269 ≤ (2784828328171/6250000000000 : ℝ)^3245 := by
    have hnat : (5409186281 : ℕ)^4269*6250000000000^3245 ≤ 2784828328171^3245*10000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409186281 10000000000 2784828328171 6250000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2351084211/10000000000 : ℝ)^4269 ≤ (1488894967851/10000000000000 : ℝ)^3245 := by
    have hnat : (2351084211 : ℕ)^4269*10000000000000^3245 ≤ 1488894967851^3245*10000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2351084211 10000000000 1488894967851 10000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (20142461/40000000 : ℝ)^4269 ≤ (2027689852791/5000000000000 : ℝ)^3245 := by
    have hnat : (20142461 : ℕ)^4269*5000000000000^3245 ≤ 2027689852791^3245*40000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20142461 40000000 2027689852791 5000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4269/1024 : ℝ)) 4269 3245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5409186281/10000000000 : ℝ), (-2351084211/10000000000 : ℝ), (20142461/40000000 : ℝ)] ![(2784828328171/6250000000000 : ℝ), (1488894967851/10000000000000 : ℝ), (2027689852791/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5409186281/10000000000 : ℝ)|^4269 ≤ (2784828328171/6250000000000 : ℝ)^3245
        have hw : |(5409186281/10000000000 : ℝ)|=(5409186281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2351084211/10000000000 : ℝ)|^4269 ≤ (1488894967851/10000000000000 : ℝ)^3245
        have hw : |(-2351084211/10000000000 : ℝ)|=(2351084211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(20142461/40000000 : ℝ)|^4269 ≤ (2027689852791/5000000000000 : ℝ)^3245
        have hw : |(20142461/40000000 : ℝ)|=(20142461/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1309_s1_2 (p : ℝ) (hpa : (1067/256 : ℝ) ≤ p) (hpb : p ≤ (4269/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5409186523/10000000000 : ℝ)*x 0 + (5035614833/10000000000 : ℝ)*x 1 + (-2351084427/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5409186523/10000000000 : ℝ)^4269 ≤ (44557255873223/100000000000000 : ℝ)^3245 := by
    have hnat : (5409186523 : ℕ)^4269*100000000000000^3245 ≤ 44557255873223^3245*10000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409186523 10000000000 44557255873223 100000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5035614833/10000000000 : ℝ)^4269 ≤ (10138448159453/25000000000000 : ℝ)^3245 := by
    have hnat : (5035614833 : ℕ)^4269*25000000000000^3245 ≤ 10138448159453^3245*10000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5035614833 10000000000 10138448159453 25000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2351084427/10000000000 : ℝ)^4269 ≤ (465279733689/3125000000000 : ℝ)^3245 := by
    have hnat : (2351084427 : ℕ)^4269*3125000000000^3245 ≤ 465279733689^3245*10000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2351084427 10000000000 465279733689 3125000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4269/1024 : ℝ)) 4269 3245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5409186523/10000000000 : ℝ), (5035614833/10000000000 : ℝ), (-2351084427/10000000000 : ℝ)] ![(44557255873223/100000000000000 : ℝ), (10138448159453/25000000000000 : ℝ), (465279733689/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5409186523/10000000000 : ℝ)|^4269 ≤ (44557255873223/100000000000000 : ℝ)^3245
        have hw : |(5409186523/10000000000 : ℝ)|=(5409186523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5035614833/10000000000 : ℝ)|^4269 ≤ (10138448159453/25000000000000 : ℝ)^3245
        have hw : |(5035614833/10000000000 : ℝ)|=(5035614833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2351084427/10000000000 : ℝ)|^4269 ≤ (465279733689/3125000000000 : ℝ)^3245
        have hw : |(-2351084427/10000000000 : ℝ)|=(2351084427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1309_s1_3 (p : ℝ) (hpa : (1067/256 : ℝ) ≤ p) (hpb : p ≤ (4269/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4298153143/10000000000 : ℝ)*x 0 + (925098679/2500000000 : ℝ)*x 1 + (2493175157/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4298153143/10000000000 : ℝ)^4269 ≤ (32927551340613/100000000000000 : ℝ)^3245 := by
    have hnat : (4298153143 : ℕ)^4269*100000000000000^3245 ≤ 32927551340613^3245*10000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4298153143 10000000000 32927551340613 100000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (925098679/2500000000 : ℝ)^4269 ≤ (27039793440139/100000000000000 : ℝ)^3245 := by
    have hnat : (925098679 : ℕ)^4269*100000000000000^3245 ≤ 27039793440139^3245*2500000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      925098679 2500000000 27039793440139 100000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2493175157/5000000000 : ℝ)^4269 ≤ (20016327602409/50000000000000 : ℝ)^3245 := by
    have hnat : (2493175157 : ℕ)^4269*50000000000000^3245 ≤ 20016327602409^3245*5000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2493175157 5000000000 20016327602409 50000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4269/1024 : ℝ)) 4269 3245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4298153143/10000000000 : ℝ), (925098679/2500000000 : ℝ), (2493175157/5000000000 : ℝ)] ![(32927551340613/100000000000000 : ℝ), (27039793440139/100000000000000 : ℝ), (20016327602409/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4298153143/10000000000 : ℝ)|^4269 ≤ (32927551340613/100000000000000 : ℝ)^3245
        have hw : |(4298153143/10000000000 : ℝ)|=(4298153143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(925098679/2500000000 : ℝ)|^4269 ≤ (27039793440139/100000000000000 : ℝ)^3245
        have hw : |(925098679/2500000000 : ℝ)|=(925098679/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2493175157/5000000000 : ℝ)|^4269 ≤ (20016327602409/50000000000000 : ℝ)^3245
        have hw : |(2493175157/5000000000 : ℝ)|=(2493175157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1309_s1_4 (p : ℝ) (hpa : (1067/256 : ℝ) ≤ p) (hpb : p ≤ (4269/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2018996771/10000000000 : ℝ)*x 0 + (5043615353/10000000000 : ℝ)*x 1 + (1129824353/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2018996771/10000000000 : ℝ)^4269 ≤ (12186038664873/100000000000000 : ℝ)^3245 := by
    have hnat : (2018996771 : ℕ)^4269*100000000000000^3245 ≤ 12186038664873^3245*10000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2018996771 10000000000 12186038664873 100000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5043615353/10000000000 : ℝ)^4269 ≤ (20319288665909/50000000000000 : ℝ)^3245 := by
    have hnat : (5043615353 : ℕ)^4269*50000000000000^3245 ≤ 20319288665909^3245*10000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5043615353 10000000000 20319288665909 50000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1129824353/2000000000 : ℝ)^4269 ≤ (1179384599867/2500000000000 : ℝ)^3245 := by
    have hnat : (1129824353 : ℕ)^4269*2500000000000^3245 ≤ 1179384599867^3245*2000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1129824353 2000000000 1179384599867 2500000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4269/1024 : ℝ)) 4269 3245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2018996771/10000000000 : ℝ), (5043615353/10000000000 : ℝ), (1129824353/2000000000 : ℝ)] ![(12186038664873/100000000000000 : ℝ), (20319288665909/50000000000000 : ℝ), (1179384599867/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2018996771/10000000000 : ℝ)|^4269 ≤ (12186038664873/100000000000000 : ℝ)^3245
        have hw : |(-2018996771/10000000000 : ℝ)|=(2018996771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5043615353/10000000000 : ℝ)|^4269 ≤ (20319288665909/50000000000000 : ℝ)^3245
        have hw : |(5043615353/10000000000 : ℝ)|=(5043615353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1129824353/2000000000 : ℝ)|^4269 ≤ (1179384599867/2500000000000 : ℝ)^3245
        have hw : |(1129824353/2000000000 : ℝ)|=(1129824353/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1309_s1_5 (p : ℝ) (hpa : (1067/256 : ℝ) ≤ p) (hpb : p ≤ (4269/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5248330061/10000000000 : ℝ)*x 0 + (-868788847/5000000000 : ℝ)*x 1 + (2824560751/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5248330061/10000000000 : ℝ)^4269 ≤ (8564466854239/20000000000000 : ℝ)^3245 := by
    have hnat : (5248330061 : ℕ)^4269*20000000000000^3245 ≤ 8564466854239^3245*10000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5248330061 10000000000 8564466854239 20000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (868788847/5000000000 : ℝ)^4269 ≤ (2000456921277/20000000000000 : ℝ)^3245 := by
    have hnat : (868788847 : ℕ)^4269*20000000000000^3245 ≤ 2000456921277^3245*5000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      868788847 5000000000 2000456921277 20000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2824560751/5000000000 : ℝ)^4269 ≤ (1179384527633/2500000000000 : ℝ)^3245 := by
    have hnat : (2824560751 : ℕ)^4269*2500000000000^3245 ≤ 1179384527633^3245*5000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2824560751 5000000000 1179384527633 2500000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4269/1024 : ℝ)) 4269 3245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5248330061/10000000000 : ℝ), (-868788847/5000000000 : ℝ), (2824560751/5000000000 : ℝ)] ![(8564466854239/20000000000000 : ℝ), (2000456921277/20000000000000 : ℝ), (1179384527633/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5248330061/10000000000 : ℝ)|^4269 ≤ (8564466854239/20000000000000 : ℝ)^3245
        have hw : |(5248330061/10000000000 : ℝ)|=(5248330061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-868788847/5000000000 : ℝ)|^4269 ≤ (2000456921277/20000000000000 : ℝ)^3245
        have hw : |(-868788847/5000000000 : ℝ)|=(868788847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2824560751/5000000000 : ℝ)|^4269 ≤ (1179384527633/2500000000000 : ℝ)^3245
        have hw : |(2824560751/5000000000 : ℝ)|=(2824560751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1309_s1_6 (p : ℝ) (hpa : (1067/256 : ℝ) ≤ p) (hpb : p ≤ (4269/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5248330021/10000000000 : ℝ)*x 0 + (1412280339/2500000000 : ℝ)*x 1 + (-868788981/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5248330021/10000000000 : ℝ)^4269 ≤ (10705583460459/25000000000000 : ℝ)^3245 := by
    have hnat : (5248330021 : ℕ)^4269*25000000000000^3245 ≤ 10705583460459^3245*10000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5248330021 10000000000 10705583460459 25000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1412280339/2500000000 : ℝ)^4269 ≤ (2358768975067/5000000000000 : ℝ)^3245 := by
    have hnat : (1412280339 : ℕ)^4269*5000000000000^3245 ≤ 2358768975067^3245*2500000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1412280339 2500000000 2358768975067 5000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (868788981/5000000000 : ℝ)^4269 ≤ (5001143317971/50000000000000 : ℝ)^3245 := by
    have hnat : (868788981 : ℕ)^4269*50000000000000^3245 ≤ 5001143317971^3245*5000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      868788981 5000000000 5001143317971 50000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4269/1024 : ℝ)) 4269 3245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5248330021/10000000000 : ℝ), (1412280339/2500000000 : ℝ), (-868788981/5000000000 : ℝ)] ![(10705583460459/25000000000000 : ℝ), (2358768975067/5000000000000 : ℝ), (5001143317971/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5248330021/10000000000 : ℝ)|^4269 ≤ (10705583460459/25000000000000 : ℝ)^3245
        have hw : |(5248330021/10000000000 : ℝ)|=(5248330021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1412280339/2500000000 : ℝ)|^4269 ≤ (2358768975067/5000000000000 : ℝ)^3245
        have hw : |(1412280339/2500000000 : ℝ)|=(1412280339/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-868788981/5000000000 : ℝ)|^4269 ≤ (5001143317971/50000000000000 : ℝ)^3245
        have hw : |(-868788981/5000000000 : ℝ)|=(868788981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1309_s1_7 (p : ℝ) (hpa : (1067/256 : ℝ) ≤ p) (hpb : p ≤ (4269/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (429939567/1000000000 : ℝ)*x 0 + (993960093/2000000000 : ℝ)*x 1 + (371725357/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (429939567/1000000000 : ℝ)^4269 ≤ (32940074521277/100000000000000 : ℝ)^3245 := by
    have hnat : (429939567 : ℕ)^4269*100000000000000^3245 ≤ 32940074521277^3245*1000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429939567 1000000000 32940074521277 100000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (993960093/2000000000 : ℝ)^4269 ≤ (39857948555207/100000000000000 : ℝ)^3245 := by
    have hnat : (993960093 : ℕ)^4269*100000000000000^3245 ≤ 39857948555207^3245*2000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      993960093 2000000000 39857948555207 100000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (371725357/1000000000 : ℝ)^4269 ≤ (6800494226349/25000000000000 : ℝ)^3245 := by
    have hnat : (371725357 : ℕ)^4269*25000000000000^3245 ≤ 6800494226349^3245*1000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      371725357 1000000000 6800494226349 25000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4269/1024 : ℝ)) 4269 3245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(429939567/1000000000 : ℝ), (993960093/2000000000 : ℝ), (371725357/1000000000 : ℝ)] ![(32940074521277/100000000000000 : ℝ), (39857948555207/100000000000000 : ℝ), (6800494226349/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(429939567/1000000000 : ℝ)|^4269 ≤ (32940074521277/100000000000000 : ℝ)^3245
        have hw : |(429939567/1000000000 : ℝ)|=(429939567/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(993960093/2000000000 : ℝ)|^4269 ≤ (39857948555207/100000000000000 : ℝ)^3245
        have hw : |(993960093/2000000000 : ℝ)|=(993960093/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(371725357/1000000000 : ℝ)|^4269 ≤ (6800494226349/25000000000000 : ℝ)^3245
        have hw : |(371725357/1000000000 : ℝ)|=(371725357/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1309_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1067/256 : ℝ) ≤ p) (hpb : p ≤ (4269/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30685957/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27111/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (291/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (411/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3943/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27111/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (291/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27111/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (291/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27111/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (291/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27111/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (291/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27111/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (291/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27111/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (291/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (291/25000 : ℝ) ^ (1067/256 : ℝ) ≤ (434432657833/50000000000000000000 : ℝ) := by
    have hpowers : (291/25000 : ℝ)^1067 ≤ (434432657833/50000000000000000000 : ℝ)^256 := by
      have hnat : (291 : ℕ)^1067*50000000000000000000^256 ≤ 434432657833^256*25000^1067 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        291 25000 434432657833 50000000000000000000 1067 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (291/25000 : ℝ)) (X := (434432657833/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1067 256 (by norm_num) hpowers
    exact h
  have hpowhi : (27111/100000 : ℝ) ^ (1067/256 : ℝ) ≤ (108469670548877751/25000000000000000000 : ℝ) := by
    have hpowers : (27111/100000 : ℝ)^1067 ≤ (108469670548877751/25000000000000000000 : ℝ)^256 := by
      have hnat : (27111 : ℕ)^1067*25000000000000000000^256 ≤ 108469670548877751^256*100000^1067 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27111 100000 108469670548877751 25000000000000000000 1067 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27111/100000 : ℝ)) (X := (108469670548877751/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1067 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000000434432657833/25000000000000000000 : ℝ) ≤ (5000000020846253/5000000000000000 : ℝ) ^ (1067/256 : ℝ) := by
    have hpowers : (25000000434432657833/25000000000000000000 : ℝ)^256 ≤ (5000000020846253/5000000000000000 : ℝ)^1067 := by
      have hnat : (25000000434432657833 : ℕ)^256*5000000000000000^1067 ≤ 5000000020846253^1067*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000434432657833 25000000000000000000 5000000020846253 5000000000000000 256 1067 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000020846253/5000000000000000 : ℝ)) (X := (25000000434432657833/25000000000000000000 : ℝ)) (by norm_num) 1067 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (10043387955106082667/10000000000000000000 : ℝ) ≤ (2502598183711371/2500000000000000 : ℝ) ^ (1067/256 : ℝ) := by
    have hpowers : (10043387955106082667/10000000000000000000 : ℝ)^256 ≤ (2502598183711371/2500000000000000 : ℝ)^1067 := by
      have hnat : (10043387955106082667 : ℕ)^256*2500000000000000^1067 ≤ 2502598183711371^1067*10000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10043387955106082667 10000000000000000000 2502598183711371 2500000000000000 256 1067 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2502598183711371/2500000000000000 : ℝ)) (X := (10043387955106082667/10000000000000000000 : ℝ)) (by norm_num) 1067 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (12608469670548877751/12500000000000000000 : ℝ) ≤ (5010392713999231/5000000000000000 : ℝ) ^ (1067/256 : ℝ) := by
    have hpowers : (12608469670548877751/12500000000000000000 : ℝ)^256 ≤ (5010392713999231/5000000000000000 : ℝ)^1067 := by
      have hnat : (12608469670548877751 : ℕ)^256*5000000000000000^1067 ≤ 5010392713999231^1067*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12608469670548877751 12500000000000000000 5010392713999231 5000000000000000 256 1067 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5010392713999231/5000000000000000 : ℝ)) (X := (12608469670548877751/12500000000000000000 : ℝ)) (by norm_num) 1067 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(434432657833/50000000000000000000 : ℝ) ≤ ((43240967815355886733/43245000000000000000 : ℝ)+2*(5196346576489/1297350000000000 : ℝ)*(291/25000 : ℝ))^(1067/256 : ℝ) := by
    rw [show (43240967815355886733/43245000000000000000 : ℝ)+2*(5196346576489/1297350000000000 : ℝ)*(291/25000 : ℝ)=(5000000020846253/5000000000000000 : ℝ) by norm_num, show 1+2*(434432657833/50000000000000000000 : ℝ)=(25000000434432657833/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(108469670548877751/25000000000000000000 : ℝ)+(434432657833/50000000000000000000 : ℝ) ≤ ((43240967815355886733/43245000000000000000 : ℝ)+(5196346576489/1297350000000000 : ℝ)*((27111/100000 : ℝ)+(291/25000 : ℝ)))^(1067/256 : ℝ) := by
    rw [show (43240967815355886733/43245000000000000000 : ℝ)+(5196346576489/1297350000000000 : ℝ)*((27111/100000 : ℝ)+(291/25000 : ℝ))=(2502598183711371/2500000000000000 : ℝ) by norm_num, show 1+(108469670548877751/25000000000000000000 : ℝ)+(434432657833/50000000000000000000 : ℝ)=(10043387955106082667/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(108469670548877751/25000000000000000000 : ℝ) ≤ ((43240967815355886733/43245000000000000000 : ℝ)+2*(5196346576489/1297350000000000 : ℝ)*(27111/100000 : ℝ))^(1067/256 : ℝ) := by
    rw [show (43240967815355886733/43245000000000000000 : ℝ)+2*(5196346576489/1297350000000000 : ℝ)*(27111/100000 : ℝ)=(5010392713999231/5000000000000000 : ℝ) by norm_num, show 1+2*(108469670548877751/25000000000000000000 : ℝ)=(12608469670548877751/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (43240967815355886733/43245000000000000000 : ℝ)*(X 1 0+X 2 0)+(5196346576489/1297350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1067/256 : ℝ)) (lo := (291/25000 : ℝ)) (hi := (27111/100000 : ℝ)) (c := (43240967815355886733/43245000000000000000 : ℝ)) (alpha := (5196346576489/1297350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (43240967815355886733/43245000000000000000 : ℝ)*(X 0 1+X 2 1)+(5196346576489/1297350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1067/256 : ℝ)) (lo := (291/25000 : ℝ)) (hi := (27111/100000 : ℝ)) (c := (43240967815355886733/43245000000000000000 : ℝ)) (alpha := (5196346576489/1297350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (43240967815355886733/43245000000000000000 : ℝ)*(X 0 2+X 1 2)+(5196346576489/1297350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1067/256 : ℝ)) (lo := (291/25000 : ℝ)) (hi := (27111/100000 : ℝ)) (c := (43240967815355886733/43245000000000000000 : ℝ)) (alpha := (5196346576489/1297350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-252299481/1250000000 : ℝ)*X 0 0+(113145427/200000000 : ℝ)*X 0 1+(629451889/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1309_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5409186281/10000000000 : ℝ)*X 1 0+(-2351084211/10000000000 : ℝ)*X 1 1+(20142461/40000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1309_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5409186523/10000000000 : ℝ)*X 2 0+(5035614833/10000000000 : ℝ)*X 2 1+(-2351084427/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1309_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4298153143/10000000000 : ℝ)*X 0 0+(925098679/2500000000 : ℝ)*X 0 1+(2493175157/5000000000 : ℝ)*X 0 2+(4298153143/10000000000 : ℝ)*X 1 0+(925098679/2500000000 : ℝ)*X 1 1+(2493175157/5000000000 : ℝ)*X 1 2+(4298153143/10000000000 : ℝ)*X 2 0+(925098679/2500000000 : ℝ)*X 2 1+(2493175157/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1309_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2018996771/10000000000 : ℝ)*X 0 0+(5043615353/10000000000 : ℝ)*X 0 1+(1129824353/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1309_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5248330061/10000000000 : ℝ)*X 1 0+(-868788847/5000000000 : ℝ)*X 1 1+(2824560751/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1309_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5248330021/10000000000 : ℝ)*X 2 0+(1412280339/2500000000 : ℝ)*X 2 1+(-868788981/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1309_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((429939567/1000000000 : ℝ)*X 0 0+(993960093/2000000000 : ℝ)*X 0 1+(371725357/1000000000 : ℝ)*X 0 2+(429939567/1000000000 : ℝ)*X 1 0+(993960093/2000000000 : ℝ)*X 1 1+(371725357/1000000000 : ℝ)*X 1 2+(429939567/1000000000 : ℝ)*X 2 0+(993960093/2000000000 : ℝ)*X 2 1+(371725357/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1309_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (69798520631570540002331/14415000000000000000000000000 : ℝ) := by norm_num
    linear_combination (702519/1250000000000 : ℝ)*(base1) + (186778711/25000000000000 : ℝ)*(base19) + (409541053/50000000000000 : ℝ)*(base23) + (143030269/100000000000000 : ℝ)*(upper3) + (75560869/100000000000000 : ℝ)*(upper5) + (596562402376189/50000000000000 : ℝ)*(major0) + (596562402376189/50000000000000 : ℝ)*(major1) + (596562402376189/50000000000000 : ℝ)*(major2) + (201076271895191/12500000000000 : ℝ)*(sp0) + (804306493272431/50000000000000 : ℝ)*(sp1) + (1005383071611/62500000000 : ℝ)*(sp2) + (97204190176087/12500000000000 : ℝ)*(sp3) + (1807349849/50000000000000 : ℝ)*(sp4) + (2136832307/100000000000000 : ℝ)*(sp7) + (194408928610631/25000000000000 : ℝ)*(f.failure) + (804306866829853/50000000000000 : ℝ)*(f.sum) + (32531038687553/16216875000000000000000000000 : ℝ)*base65 + (5615173699911048389/6486750000000000000000000000000000 : ℝ)*base68 + (42430916331042701611/6486750000000000000000000000000000 : ℝ)*base69 + (5186425172892701611/6486750000000000000000000000000000 : ℝ)*base71 + (191687527402069/129735000000000000000000000000 : ℝ)*base73 + (43073281986798389/6486750000000000000000000000000000 : ℝ)*base76 + (11438052683051201611/6486750000000000000000000000000000 : ℝ)*base77 + (52291586215381548389/6486750000000000000000000000000000 : ℝ)*base80 + (222537637457597/64867500000000000000000000000 : ℝ)*base81 + (2608867/500000000000000000000 : ℝ)*base89 + (2608867/500000000000000000000 : ℝ)*base91 + (2608867/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1380061138667255356163577029/270281250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (235832349/25000000000000 : ℝ)*(base19) + (907973379/100000000000000 : ℝ)*(base23) + (5776533/100000000000000 : ℝ)*(upper2) + (5658483/6250000000000 : ℝ)*(upper3) + (75281733/50000000000000 : ℝ)*(upper5) + (306235478907829/25000000000000 : ℝ)*(major0) + (306235478907829/25000000000000 : ℝ)*(major1) + (306235478907829/25000000000000 : ℝ)*(major2) + (2253120469/50000000000000 : ℝ)*(sp1) + (3404226081/100000000000000 : ℝ)*(sp2) + (825755350659663/50000000000000 : ℝ)*(sp4) + (12902384779289/781250000000 : ℝ)*(sp5) + (330301277823973/20000000000000 : ℝ)*(sp6) + (79837295974267/10000000000000 : ℝ)*(sp7) + (79837295974267/10000000000000 : ℝ)*(f.failure) + (825755350659663/50000000000000 : ℝ)*(f.sum) + (377302332107929/64867500000000000000000000000 : ℝ)*base65 + (23890913405536397971/3243375000000000000000000000000000 : ℝ)*base67 + (5826908248922147971/3243375000000000000000000000000000 : ℝ)*base69 + (20180475014559647971/3243375000000000000000000000000000 : ℝ)*base71 + (105869003905351/16216875000000000000000000000 : ℝ)*base73 + (2798523530955102029/3243375000000000000000000000000000 : ℝ)*base76 + (34493315570086397971/3243375000000000000000000000000000 : ℝ)*base77 + (11516839913005772971/3243375000000000000000000000000000 : ℝ)*base79 + (464811231857543/129735000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (1731481/200000000000000000000 : ℝ)*base90 + (1731481/200000000000000000000 : ℝ)*base92 + (1731481/200000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1309_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1067/256 : ℝ) ≤ p) (hpb : p ≤ (4269/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30685957/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27111/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (291/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (411/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3943/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1309_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1309_s2_0 (p : ℝ) (hpa : (1067/256 : ℝ) ≤ p) (hpb : p ≤ (4269/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-412301971/2000000000 : ℝ)*x 0 + (1097826537/2000000000 : ℝ)*x 1 + (5176188543/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (412301971/2000000000 : ℝ)^4269 ≤ (12524722617991/100000000000000 : ℝ)^3245 := by
    have hnat : (412301971 : ℕ)^4269*100000000000000^3245 ≤ 12524722617991^3245*2000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      412301971 2000000000 12524722617991 100000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1097826537/2000000000 : ℝ)^4269 ≤ (9085124747801/20000000000000 : ℝ)^3245 := by
    have hnat : (1097826537 : ℕ)^4269*20000000000000^3245 ≤ 9085124747801^3245*2000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097826537 2000000000 9085124747801 20000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5176188543/10000000000 : ℝ)^4269 ≤ (2102482681641/5000000000000 : ℝ)^3245 := by
    have hnat : (5176188543 : ℕ)^4269*5000000000000^3245 ≤ 2102482681641^3245*10000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176188543 10000000000 2102482681641 5000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4269/1024 : ℝ)) 4269 3245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-412301971/2000000000 : ℝ), (1097826537/2000000000 : ℝ), (5176188543/10000000000 : ℝ)] ![(12524722617991/100000000000000 : ℝ), (9085124747801/20000000000000 : ℝ), (2102482681641/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-412301971/2000000000 : ℝ)|^4269 ≤ (12524722617991/100000000000000 : ℝ)^3245
        have hw : |(-412301971/2000000000 : ℝ)|=(412301971/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1097826537/2000000000 : ℝ)|^4269 ≤ (9085124747801/20000000000000 : ℝ)^3245
        have hw : |(1097826537/2000000000 : ℝ)|=(1097826537/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5176188543/10000000000 : ℝ)|^4269 ≤ (2102482681641/5000000000000 : ℝ)^3245
        have hw : |(5176188543/10000000000 : ℝ)|=(5176188543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1309_s2_1 (p : ℝ) (hpa : (1067/256 : ℝ) ≤ p) (hpb : p ≤ (4269/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2684162377/5000000000 : ℝ)*x 0 + (-138969789/625000000 : ℝ)*x 1 + (5176188203/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684162377/5000000000 : ℝ)^4269 ≤ (11028744234383/25000000000000 : ℝ)^3245 := by
    have hnat : (2684162377 : ℕ)^4269*25000000000000^3245 ≤ 11028744234383^3245*5000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684162377 5000000000 11028744234383 25000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (138969789/625000000 : ℝ)^4269 ≤ (13835373052687/100000000000000 : ℝ)^3245 := by
    have hnat : (138969789 : ℕ)^4269*100000000000000^3245 ≤ 13835373052687^3245*625000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138969789 625000000 13835373052687 100000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5176188203/10000000000 : ℝ)^4269 ≤ (42049649999173/100000000000000 : ℝ)^3245 := by
    have hnat : (5176188203 : ℕ)^4269*100000000000000^3245 ≤ 42049649999173^3245*10000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176188203 10000000000 42049649999173 100000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4269/1024 : ℝ)) 4269 3245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684162377/5000000000 : ℝ), (-138969789/625000000 : ℝ), (5176188203/10000000000 : ℝ)] ![(11028744234383/25000000000000 : ℝ), (13835373052687/100000000000000 : ℝ), (42049649999173/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684162377/5000000000 : ℝ)|^4269 ≤ (11028744234383/25000000000000 : ℝ)^3245
        have hw : |(2684162377/5000000000 : ℝ)|=(2684162377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-138969789/625000000 : ℝ)|^4269 ≤ (13835373052687/100000000000000 : ℝ)^3245
        have hw : |(-138969789/625000000 : ℝ)|=(138969789/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5176188203/10000000000 : ℝ)|^4269 ≤ (42049649999173/100000000000000 : ℝ)^3245
        have hw : |(5176188203/10000000000 : ℝ)|=(5176188203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1309_s2_2 (p : ℝ) (hpa : (1067/256 : ℝ) ≤ p) (hpb : p ≤ (4269/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5368324269/10000000000 : ℝ)*x 0 + (5176188643/10000000000 : ℝ)*x 1 + (-2223516689/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368324269/10000000000 : ℝ)^4269 ≤ (44114971694283/100000000000000 : ℝ)^3245 := by
    have hnat : (5368324269 : ℕ)^4269*100000000000000^3245 ≤ 44114971694283^3245*10000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368324269 10000000000 44114971694283 100000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5176188643/10000000000 : ℝ)^4269 ≤ (2102482735077/5000000000000 : ℝ)^3245 := by
    have hnat : (5176188643 : ℕ)^4269*5000000000000^3245 ≤ 2102482735077^3245*10000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176188643 10000000000 2102482735077 5000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2223516689/10000000000 : ℝ)^4269 ≤ (2767074716953/20000000000000 : ℝ)^3245 := by
    have hnat : (2223516689 : ℕ)^4269*20000000000000^3245 ≤ 2767074716953^3245*10000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2223516689 10000000000 2767074716953 20000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4269/1024 : ℝ)) 4269 3245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368324269/10000000000 : ℝ), (5176188643/10000000000 : ℝ), (-2223516689/10000000000 : ℝ)] ![(44114971694283/100000000000000 : ℝ), (2102482735077/5000000000000 : ℝ), (2767074716953/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368324269/10000000000 : ℝ)|^4269 ≤ (44114971694283/100000000000000 : ℝ)^3245
        have hw : |(5368324269/10000000000 : ℝ)|=(5368324269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5176188643/10000000000 : ℝ)|^4269 ≤ (2102482735077/5000000000000 : ℝ)^3245
        have hw : |(5176188643/10000000000 : ℝ)|=(5176188643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2223516689/10000000000 : ℝ)|^4269 ≤ (2767074716953/20000000000000 : ℝ)^3245
        have hw : |(-2223516689/10000000000 : ℝ)|=(2223516689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1309_s2_3 (p : ℝ) (hpa : (1067/256 : ℝ) ≤ p) (hpb : p ≤ (4269/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4328184509/10000000000 : ℝ)*x 0 + (125498367/312500000 : ℝ)*x 1 + (932662149/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4328184509/10000000000 : ℝ)^4269 ≤ (4153818849107/12500000000000 : ℝ)^3245 := by
    have hnat : (4328184509 : ℕ)^4269*12500000000000^3245 ≤ 4153818849107^3245*10000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4328184509 10000000000 4153818849107 12500000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (125498367/312500000 : ℝ)^4269 ≤ (15056653743079/50000000000000 : ℝ)^3245 := by
    have hnat : (125498367 : ℕ)^4269*50000000000000^3245 ≤ 15056653743079^3245*312500000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125498367 312500000 15056653743079 50000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (932662149/2000000000 : ℝ)^4269 ≤ (36656141708663/100000000000000 : ℝ)^3245 := by
    have hnat : (932662149 : ℕ)^4269*100000000000000^3245 ≤ 36656141708663^3245*2000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      932662149 2000000000 36656141708663 100000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4269/1024 : ℝ)) 4269 3245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4328184509/10000000000 : ℝ), (125498367/312500000 : ℝ), (932662149/2000000000 : ℝ)] ![(4153818849107/12500000000000 : ℝ), (15056653743079/50000000000000 : ℝ), (36656141708663/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4328184509/10000000000 : ℝ)|^4269 ≤ (4153818849107/12500000000000 : ℝ)^3245
        have hw : |(4328184509/10000000000 : ℝ)|=(4328184509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(125498367/312500000 : ℝ)|^4269 ≤ (15056653743079/50000000000000 : ℝ)^3245
        have hw : |(125498367/312500000 : ℝ)|=(125498367/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(932662149/2000000000 : ℝ)|^4269 ≤ (36656141708663/100000000000000 : ℝ)^3245
        have hw : |(932662149/2000000000 : ℝ)|=(932662149/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1309_s2_4 (p : ℝ) (hpa : (1067/256 : ℝ) ≤ p) (hpb : p ≤ (4269/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-103079301/500000000 : ℝ)*x 0 + (2589112619/5000000000 : ℝ)*x 1 + (5487077207/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (103079301/500000000 : ℝ)^4269 ≤ (3131332846609/25000000000000 : ℝ)^3245 := by
    have hnat : (103079301 : ℕ)^4269*25000000000000^3245 ≤ 3131332846609^3245*500000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103079301 500000000 3131332846609 25000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2589112619/5000000000 : ℝ)^4269 ≤ (21035710771719/50000000000000 : ℝ)^3245 := by
    have hnat : (2589112619 : ℕ)^4269*50000000000000^3245 ≤ 21035710771719^3245*5000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2589112619 5000000000 21035710771719 50000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5487077207/10000000000 : ℝ)^4269 ≤ (22701623525811/50000000000000 : ℝ)^3245 := by
    have hnat : (5487077207 : ℕ)^4269*50000000000000^3245 ≤ 22701623525811^3245*10000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5487077207 10000000000 22701623525811 50000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4269/1024 : ℝ)) 4269 3245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-103079301/500000000 : ℝ), (2589112619/5000000000 : ℝ), (5487077207/10000000000 : ℝ)] ![(3131332846609/25000000000000 : ℝ), (21035710771719/50000000000000 : ℝ), (22701623525811/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-103079301/500000000 : ℝ)|^4269 ≤ (3131332846609/25000000000000 : ℝ)^3245
        have hw : |(-103079301/500000000 : ℝ)|=(103079301/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2589112619/5000000000 : ℝ)|^4269 ≤ (21035710771719/50000000000000 : ℝ)^3245
        have hw : |(2589112619/5000000000 : ℝ)|=(2589112619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5487077207/10000000000 : ℝ)|^4269 ≤ (22701623525811/50000000000000 : ℝ)^3245
        have hw : |(5487077207/10000000000 : ℝ)|=(5487077207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1309_s2_5 (p : ℝ) (hpa : (1067/256 : ℝ) ≤ p) (hpb : p ≤ (4269/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2643979477/5000000000 : ℝ)*x 0 + (-1912627119/10000000000 : ℝ)*x 1 + (685884663/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643979477/5000000000 : ℝ)^4269 ≤ (43248215797253/100000000000000 : ℝ)^3245 := by
    have hnat : (2643979477 : ℕ)^4269*100000000000000^3245 ≤ 43248215797253^3245*5000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643979477 5000000000 43248215797253 100000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1912627119/10000000000 : ℝ)^4269 ≤ (2837134021619/25000000000000 : ℝ)^3245 := by
    have hnat : (1912627119 : ℕ)^4269*25000000000000^3245 ≤ 2837134021619^3245*10000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1912627119 10000000000 2837134021619 25000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (685884663/1250000000 : ℝ)^4269 ≤ (45403248107537/100000000000000 : ℝ)^3245 := by
    have hnat : (685884663 : ℕ)^4269*100000000000000^3245 ≤ 45403248107537^3245*1250000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      685884663 1250000000 45403248107537 100000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4269/1024 : ℝ)) 4269 3245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643979477/5000000000 : ℝ), (-1912627119/10000000000 : ℝ), (685884663/1250000000 : ℝ)] ![(43248215797253/100000000000000 : ℝ), (2837134021619/25000000000000 : ℝ), (45403248107537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643979477/5000000000 : ℝ)|^4269 ≤ (43248215797253/100000000000000 : ℝ)^3245
        have hw : |(2643979477/5000000000 : ℝ)|=(2643979477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1912627119/10000000000 : ℝ)|^4269 ≤ (2837134021619/25000000000000 : ℝ)^3245
        have hw : |(-1912627119/10000000000 : ℝ)|=(1912627119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(685884663/1250000000 : ℝ)|^4269 ≤ (45403248107537/100000000000000 : ℝ)^3245
        have hw : |(685884663/1250000000 : ℝ)|=(685884663/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1309_s2_6 (p : ℝ) (hpa : (1067/256 : ℝ) ≤ p) (hpb : p ≤ (4269/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2643979539/5000000000 : ℝ)*x 0 + (2743538607/5000000000 : ℝ)*x 1 + (-14942399/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643979539/5000000000 : ℝ)^4269 ≤ (43248217131429/100000000000000 : ℝ)^3245 := by
    have hnat : (2643979539 : ℕ)^4269*100000000000000^3245 ≤ 43248217131429^3245*5000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643979539 5000000000 43248217131429 100000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2743538607/5000000000 : ℝ)^4269 ≤ (22701623563911/50000000000000 : ℝ)^3245 := by
    have hnat : (2743538607 : ℕ)^4269*50000000000000^3245 ≤ 22701623563911^3245*5000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2743538607 5000000000 22701623563911 50000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (14942399/78125000 : ℝ)^4269 ≤ (28371339299/250000000000 : ℝ)^3245 := by
    have hnat : (14942399 : ℕ)^4269*250000000000^3245 ≤ 28371339299^3245*78125000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14942399 78125000 28371339299 250000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4269/1024 : ℝ)) 4269 3245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643979539/5000000000 : ℝ), (2743538607/5000000000 : ℝ), (-14942399/78125000 : ℝ)] ![(43248217131429/100000000000000 : ℝ), (22701623563911/50000000000000 : ℝ), (28371339299/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643979539/5000000000 : ℝ)|^4269 ≤ (43248217131429/100000000000000 : ℝ)^3245
        have hw : |(2643979539/5000000000 : ℝ)|=(2643979539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2743538607/5000000000 : ℝ)|^4269 ≤ (22701623563911/50000000000000 : ℝ)^3245
        have hw : |(2743538607/5000000000 : ℝ)|=(2743538607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-14942399/78125000 : ℝ)|^4269 ≤ (28371339299/250000000000 : ℝ)^3245
        have hw : |(-14942399/78125000 : ℝ)|=(14942399/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1309_s2_7 (p : ℝ) (hpa : (1067/256 : ℝ) ≤ p) (hpb : p ≤ (4269/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4328340917/10000000000 : ℝ)*x 0 + (4659095621/10000000000 : ℝ)*x 1 + (4020204931/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4328340917/10000000000 : ℝ)^4269 ≤ (8308032650539/25000000000000 : ℝ)^3245 := by
    have hnat : (4328340917 : ℕ)^4269*25000000000000^3245 ≤ 8308032650539^3245*10000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4328340917 10000000000 8308032650539 25000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4659095621/10000000000 : ℝ)^4269 ≤ (7322511839531/20000000000000 : ℝ)^3245 := by
    have hnat : (4659095621 : ℕ)^4269*20000000000000^3245 ≤ 7322511839531^3245*10000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4659095621 10000000000 7322511839531 20000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4020204931/10000000000 : ℝ)^4269 ≤ (6031062037121/20000000000000 : ℝ)^3245 := by
    have hnat : (4020204931 : ℕ)^4269*20000000000000^3245 ≤ 6031062037121^3245*10000000000^4269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4020204931 10000000000 6031062037121 20000000000000 4269 3245 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4269/1024 : ℝ)) 4269 3245 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4328340917/10000000000 : ℝ), (4659095621/10000000000 : ℝ), (4020204931/10000000000 : ℝ)] ![(8308032650539/25000000000000 : ℝ), (7322511839531/20000000000000 : ℝ), (6031062037121/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4328340917/10000000000 : ℝ)|^4269 ≤ (8308032650539/25000000000000 : ℝ)^3245
        have hw : |(4328340917/10000000000 : ℝ)|=(4328340917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4659095621/10000000000 : ℝ)|^4269 ≤ (7322511839531/20000000000000 : ℝ)^3245
        have hw : |(4659095621/10000000000 : ℝ)|=(4659095621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4020204931/10000000000 : ℝ)|^4269 ≤ (6031062037121/20000000000000 : ℝ)^3245
        have hw : |(4020204931/10000000000 : ℝ)|=(4020204931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1309_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1067/256 : ℝ) ≤ p) (hpb : p ≤ (4269/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30685957/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3943/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (411/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (9627/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16241/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3943/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (411/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3943/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (411/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3943/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (411/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3943/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (411/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3943/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (411/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3943/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (411/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (411/6250 : ℝ) ^ (1067/256 : ℝ) ≤ (591931898646933/50000000000000000000 : ℝ) := by
    have hpowers : (411/6250 : ℝ)^1067 ≤ (591931898646933/50000000000000000000 : ℝ)^256 := by
      have hnat : (411 : ℕ)^1067*50000000000000000000^256 ≤ 591931898646933^256*6250^1067 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        411 6250 591931898646933 50000000000000000000 1067 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (411/6250 : ℝ)) (X := (591931898646933/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1067 256 (by norm_num) hpowers
    exact h
  have hpowhi : (3943/20000 : ℝ) ^ (1067/256 : ℝ) ≤ (57504923078355353/50000000000000000000 : ℝ) := by
    have hpowers : (3943/20000 : ℝ)^1067 ≤ (57504923078355353/50000000000000000000 : ℝ)^256 := by
      have hnat : (3943 : ℕ)^1067*50000000000000000000^256 ≤ 57504923078355353^256*20000^1067 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3943 20000 57504923078355353 50000000000000000000 1067 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3943/20000 : ℝ)) (X := (57504923078355353/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1067 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000591931898646933/25000000000000000000 : ℝ) ≤ (5000028403599349/5000000000000000 : ℝ) ^ (1067/256 : ℝ) := by
    have hpowers : (25000591931898646933/25000000000000000000 : ℝ)^256 ≤ (5000028403599349/5000000000000000 : ℝ)^1067 := by
      have hnat : (25000591931898646933 : ℕ)^256*5000000000000000^1067 ≤ 5000028403599349^1067*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000591931898646933 25000000000000000000 5000028403599349 5000000000000000 256 1067 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000028403599349/5000000000000000 : ℝ)) (X := (25000591931898646933/25000000000000000000 : ℝ)) (by norm_num) 1067 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (25029048427488501143/25000000000000000000 : ℝ) ≤ (10002786547670843/10000000000000000 : ℝ) ^ (1067/256 : ℝ) := by
    have hpowers : (25029048427488501143/25000000000000000000 : ℝ)^256 ≤ (10002786547670843/10000000000000000 : ℝ)^1067 := by
      have hnat : (25029048427488501143 : ℕ)^256*10000000000000000^1067 ≤ 10002786547670843^1067*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25029048427488501143 25000000000000000000 10002786547670843 10000000000000000 256 1067 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002786547670843/10000000000000000 : ℝ)) (X := (25029048427488501143/25000000000000000000 : ℝ)) (by norm_num) 1067 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (25057504923078355353/25000000000000000000 : ℝ) ≤ (2501379072035747/2500000000000000 : ℝ) ^ (1067/256 : ℝ) := by
    have hpowers : (25057504923078355353/25000000000000000000 : ℝ)^256 ≤ (2501379072035747/2500000000000000 : ℝ)^1067 := by
      have hnat : (25057504923078355353 : ℕ)^256*2500000000000000^1067 ≤ 2501379072035747^1067*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25057504923078355353 25000000000000000000 2501379072035747 2500000000000000 256 1067 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2501379072035747/2500000000000000 : ℝ)) (X := (25057504923078355353/25000000000000000000 : ℝ)) (by norm_num) 1067 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(591931898646933/50000000000000000000 : ℝ) ≤ ((65677422421547020991/65695000000000000000 : ℝ)+2*(545948094429/262780000000000 : ℝ)*(411/6250 : ℝ))^(1067/256 : ℝ) := by
    rw [show (65677422421547020991/65695000000000000000 : ℝ)+2*(545948094429/262780000000000 : ℝ)*(411/6250 : ℝ)=(5000028403599349/5000000000000000 : ℝ) by norm_num, show 1+2*(591931898646933/50000000000000000000 : ℝ)=(25000591931898646933/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(57504923078355353/50000000000000000000 : ℝ)+(591931898646933/50000000000000000000 : ℝ) ≤ ((65677422421547020991/65695000000000000000 : ℝ)+(545948094429/262780000000000 : ℝ)*((3943/20000 : ℝ)+(411/6250 : ℝ)))^(1067/256 : ℝ) := by
    rw [show (65677422421547020991/65695000000000000000 : ℝ)+(545948094429/262780000000000 : ℝ)*((3943/20000 : ℝ)+(411/6250 : ℝ))=(10002786547670843/10000000000000000 : ℝ) by norm_num, show 1+(57504923078355353/50000000000000000000 : ℝ)+(591931898646933/50000000000000000000 : ℝ)=(25029048427488501143/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(57504923078355353/50000000000000000000 : ℝ) ≤ ((65677422421547020991/65695000000000000000 : ℝ)+2*(545948094429/262780000000000 : ℝ)*(3943/20000 : ℝ))^(1067/256 : ℝ) := by
    rw [show (65677422421547020991/65695000000000000000 : ℝ)+2*(545948094429/262780000000000 : ℝ)*(3943/20000 : ℝ)=(2501379072035747/2500000000000000 : ℝ) by norm_num, show 1+2*(57504923078355353/50000000000000000000 : ℝ)=(25057504923078355353/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (65677422421547020991/65695000000000000000 : ℝ)*(X 1 0+X 2 0)+(545948094429/262780000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1067/256 : ℝ)) (lo := (411/6250 : ℝ)) (hi := (3943/20000 : ℝ)) (c := (65677422421547020991/65695000000000000000 : ℝ)) (alpha := (545948094429/262780000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (65677422421547020991/65695000000000000000 : ℝ)*(X 0 1+X 2 1)+(545948094429/262780000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1067/256 : ℝ)) (lo := (411/6250 : ℝ)) (hi := (3943/20000 : ℝ)) (c := (65677422421547020991/65695000000000000000 : ℝ)) (alpha := (545948094429/262780000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (65677422421547020991/65695000000000000000 : ℝ)*(X 0 2+X 1 2)+(545948094429/262780000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1067/256 : ℝ)) (lo := (411/6250 : ℝ)) (hi := (3943/20000 : ℝ)) (c := (65677422421547020991/65695000000000000000 : ℝ)) (alpha := (545948094429/262780000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-412301971/2000000000 : ℝ)*X 0 0+(1097826537/2000000000 : ℝ)*X 0 1+(5176188543/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1309_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2684162377/5000000000 : ℝ)*X 1 0+(-138969789/625000000 : ℝ)*X 1 1+(5176188203/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1309_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5368324269/10000000000 : ℝ)*X 2 0+(5176188643/10000000000 : ℝ)*X 2 1+(-2223516689/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1309_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4328184509/10000000000 : ℝ)*X 0 0+(125498367/312500000 : ℝ)*X 0 1+(932662149/2000000000 : ℝ)*X 0 2+(4328184509/10000000000 : ℝ)*X 1 0+(125498367/312500000 : ℝ)*X 1 1+(932662149/2000000000 : ℝ)*X 1 2+(4328184509/10000000000 : ℝ)*X 2 0+(125498367/312500000 : ℝ)*X 2 1+(932662149/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1309_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-103079301/500000000 : ℝ)*X 0 0+(2589112619/5000000000 : ℝ)*X 0 1+(5487077207/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1309_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2643979477/5000000000 : ℝ)*X 1 0+(-1912627119/10000000000 : ℝ)*X 1 1+(685884663/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1309_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2643979539/5000000000 : ℝ)*X 2 0+(2743538607/5000000000 : ℝ)*X 2 1+(-14942399/78125000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1309_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4328340917/10000000000 : ℝ)*X 0 0+(4659095621/10000000000 : ℝ)*X 0 1+(4020204931/10000000000 : ℝ)*X 0 2+(4328340917/10000000000 : ℝ)*X 1 0+(4659095621/10000000000 : ℝ)*X 1 1+(4020204931/10000000000 : ℝ)*X 1 2+(4328340917/10000000000 : ℝ)*X 2 0+(4659095621/10000000000 : ℝ)*X 2 1+(4020204931/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1309_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2665262409259414733857385169/469250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (527505151/25000000000000 : ℝ)*(base19) + (270941549/20000000000000 : ℝ)*(base23) + (250495633/100000000000000 : ℝ)*(lower2) + (66609889/10000000000000 : ℝ)*(upper3) + (10804233/6250000000000 : ℝ)*(upper5) + (2370121118828771/100000000000000 : ℝ)*(major0) + (2370121118828771/100000000000000 : ℝ)*(major1) + (2370121118828771/100000000000000 : ℝ)*(major2) + (3195474768785843/100000000000000 : ℝ)*(sp0) + (3195480477928737/100000000000000 : ℝ)*(sp1) + (798870308310399/25000000000000 : ℝ)*(sp2) + (772370725259907/50000000000000 : ℝ)*(sp3) + (3909581749/50000000000000 : ℝ)*(sp4) + (9004930281/50000000000000 : ℝ)*(sp7) + (193094932547547/12500000000000 : ℝ)*(f.failure) + (3195482587949341/100000000000000 : ℝ)*(f.sum) + (4326782476001/938500000000000000000000000 : ℝ)*base65 + (1100272920604288277/938500000000000000000000000000000 : ℝ)*base68 + (4123343102630711723/938500000000000000000000000000000 : ℝ)*base69 + (4776276795572788277/938500000000000000000000000000000 : ℝ)*base72 + (7776858091327/1877000000000000000000000000 : ℝ)*base73 + (3473535452645288277/938500000000000000000000000000000 : ℝ)*base76 + (4738200892426211723/938500000000000000000000000000000 : ℝ)*base77 + (463832194790788277/938500000000000000000000000000000 : ℝ)*base80 + (7640095595521/1877000000000000000000000000 : ℝ)*base81 + (197479/250000000000000000000 : ℝ)*base89 + (197479/250000000000000000000 : ℝ)*base91 + (197479/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6025107948073081753403709/1877000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (660869929/100000000000000 : ℝ)*(base19) + (224552221/25000000000000 : ℝ)*(base23) + (118445683/100000000000000 : ℝ)*(upper3) + (56633143/100000000000000 : ℝ)*(lower4) + (385013/4000000000000 : ℝ)*(upper5) + (19212034469369/800000000000 : ℝ)*(major0) + (19212034469369/800000000000 : ℝ)*(major1) + (19212034469369/800000000000 : ℝ)*(major2) + (3396812789/50000000000000 : ℝ)*(sp1) + (2073524481/20000000000000 : ℝ)*(sp2) + (3237794618743927/100000000000000 : ℝ)*(sp4) + (161889358212421/5000000000000 : ℝ)*(sp5) + (1618891676456319/50000000000000 : ℝ)*(sp6) + (1565213891599421/100000000000000 : ℝ)*(sp7) + (1565213891599421/100000000000000 : ℝ)*(f.failure) + (3237794618743927/100000000000000 : ℝ)*(f.sum) + (4135925746983/938500000000000000000000000 : ℝ)*base65 + (6411426607646097/7508000000000000000000000000000 : ℝ)*base67 + (25119472295962097/7508000000000000000000000000000 : ℝ)*base69 + (7847297956790097/7508000000000000000000000000000 : ℝ)*base71 + (4902664975711/938500000000000000000000000 : ℝ)*base73 + (15876042205462097/7508000000000000000000000000000 : ℝ)*base75 + (12064059415554097/7508000000000000000000000000000 : ℝ)*base77 + (20055379478421903/7508000000000000000000000000000 : ℝ)*base80 + (1317004530537/375400000000000000000000000 : ℝ)*base81 + (5969103/2000000000000000000000 : ℝ)*base90 + (5969103/2000000000000000000000 : ℝ)*base92 + (5969103/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1309_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1067/256 : ℝ) ≤ p) (hpb : p ≤ (4269/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30685957/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3943/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (411/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9627/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16241/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1309_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1309_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1067/256 : ℝ) ≤ p) (hpb : p ≤ (4269/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30685957/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9627/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16241/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1309_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1309_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1309_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1067/256 : ℝ) ≤ p) (hpb : p ≤ (4269/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30685957/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9627/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16241/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1309_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
