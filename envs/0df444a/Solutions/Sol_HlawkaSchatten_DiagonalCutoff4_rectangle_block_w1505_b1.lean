-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1505_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:53:42.706832+00:00
-- url     : https://prove2.me/submissions/d66938c3-945d-4dab-9001-32c310b6d5f4

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
theorem support_rectangle_w1505_s3_0 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-93893327/500000000 : ℝ)*x 0 + (5437696623/10000000000 : ℝ)*x 1 + (651760209/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (93893327/500000000 : ℝ)^4507 ≤ (11484777069931/100000000000000 : ℝ)^3483 := by
    have hnat : (93893327 : ℕ)^4507*100000000000000^3483 ≤ 11484777069931^3483*500000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      93893327 500000000 11484777069931 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5437696623/10000000000 : ℝ)^4507 ≤ (22729879461503/50000000000000 : ℝ)^3483 := by
    have hnat : (5437696623 : ℕ)^4507*50000000000000^3483 ≤ 22729879461503^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437696623 10000000000 22729879461503 50000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (651760209/1250000000 : ℝ)^4507 ≤ (21527731997821/50000000000000 : ℝ)^3483 := by
    have hnat : (651760209 : ℕ)^4507*50000000000000^3483 ≤ 21527731997821^3483*1250000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      651760209 1250000000 21527731997821 50000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-93893327/500000000 : ℝ), (5437696623/10000000000 : ℝ), (651760209/1250000000 : ℝ)] ![(11484777069931/100000000000000 : ℝ), (22729879461503/50000000000000 : ℝ), (21527731997821/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-93893327/500000000 : ℝ)|^4507 ≤ (11484777069931/100000000000000 : ℝ)^3483
        have hw : |(-93893327/500000000 : ℝ)|=(93893327/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5437696623/10000000000 : ℝ)|^4507 ≤ (22729879461503/50000000000000 : ℝ)^3483
        have hw : |(5437696623/10000000000 : ℝ)|=(5437696623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(651760209/1250000000 : ℝ)|^4507 ≤ (21527731997821/50000000000000 : ℝ)^3483
        have hw : |(651760209/1250000000 : ℝ)|=(651760209/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1505_s3_1 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338226191/2500000000 : ℝ)*x 0 + (-996246241/5000000000 : ℝ)*x 1 + (521408163/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338226191/2500000000 : ℝ)^4507 ≤ (22272296259131/50000000000000 : ℝ)^3483 := by
    have hnat : (1338226191 : ℕ)^4507*50000000000000^3483 ≤ 22272296259131^3483*2500000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338226191 2500000000 22272296259131 50000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (996246241/5000000000 : ℝ)^4507 ≤ (3099985979669/25000000000000 : ℝ)^3483 := by
    have hnat : (996246241 : ℕ)^4507*25000000000000^3483 ≤ 3099985979669^3483*5000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      996246241 5000000000 3099985979669 25000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (521408163/1000000000 : ℝ)^4507 ≤ (21527731773431/50000000000000 : ℝ)^3483 := by
    have hnat : (521408163 : ℕ)^4507*50000000000000^3483 ≤ 21527731773431^3483*1000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521408163 1000000000 21527731773431 50000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338226191/2500000000 : ℝ), (-996246241/5000000000 : ℝ), (521408163/1000000000 : ℝ)] ![(22272296259131/50000000000000 : ℝ), (3099985979669/25000000000000 : ℝ), (21527731773431/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338226191/2500000000 : ℝ)|^4507 ≤ (22272296259131/50000000000000 : ℝ)^3483
        have hw : |(1338226191/2500000000 : ℝ)|=(1338226191/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-996246241/5000000000 : ℝ)|^4507 ≤ (3099985979669/25000000000000 : ℝ)^3483
        have hw : |(-996246241/5000000000 : ℝ)|=(996246241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(521408163/1000000000 : ℝ)|^4507 ≤ (21527731773431/50000000000000 : ℝ)^3483
        have hw : |(521408163/1000000000 : ℝ)|=(521408163/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1505_s3_2 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352904739/10000000000 : ℝ)*x 0 + (651760207/1250000000 : ℝ)*x 1 + (-6226539/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352904739/10000000000 : ℝ)^4507 ≤ (44544592249059/100000000000000 : ℝ)^3483 := by
    have hnat : (5352904739 : ℕ)^4507*100000000000000^3483 ≤ 44544592249059^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352904739 10000000000 44544592249059 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (651760207/1250000000 : ℝ)^4507 ≤ (21527731912339/50000000000000 : ℝ)^3483 := by
    have hnat : (651760207 : ℕ)^4507*50000000000000^3483 ≤ 21527731912339^3483*1250000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      651760207 1250000000 21527731912339 50000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6226539/31250000 : ℝ)^4507 ≤ (1239994390257/10000000000000 : ℝ)^3483 := by
    have hnat : (6226539 : ℕ)^4507*10000000000000^3483 ≤ 1239994390257^3483*31250000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6226539 31250000 1239994390257 10000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352904739/10000000000 : ℝ), (651760207/1250000000 : ℝ), (-6226539/31250000 : ℝ)] ![(44544592249059/100000000000000 : ℝ), (21527731912339/50000000000000 : ℝ), (1239994390257/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352904739/10000000000 : ℝ)|^4507 ≤ (44544592249059/100000000000000 : ℝ)^3483
        have hw : |(5352904739/10000000000 : ℝ)|=(5352904739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(651760207/1250000000 : ℝ)|^4507 ≤ (21527731912339/50000000000000 : ℝ)^3483
        have hw : |(651760207/1250000000 : ℝ)|=(651760207/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6226539/31250000 : ℝ)|^4507 ≤ (1239994390257/10000000000000 : ℝ)^3483
        have hw : |(-6226539/31250000 : ℝ)|=(6226539/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1505_s3_3 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (85454097/200000000 : ℝ)*x 0 + (503347699/1250000000 : ℝ)*x 1 + (2265673677/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (85454097/200000000 : ℝ)^4507 ≤ (33275895858207/100000000000000 : ℝ)^3483 := by
    have hnat : (85454097 : ℕ)^4507*100000000000000^3483 ≤ 33275895858207^3483*200000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85454097 200000000 33275895858207 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (503347699/1250000000 : ℝ)^4507 ≤ (15409408903023/50000000000000 : ℝ)^3483 := by
    have hnat : (503347699 : ℕ)^4507*50000000000000^3483 ≤ 15409408903023^3483*1250000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      503347699 1250000000 15409408903023 50000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2265673677/5000000000 : ℝ)^4507 ≤ (17952643161167/50000000000000 : ℝ)^3483 := by
    have hnat : (2265673677 : ℕ)^4507*50000000000000^3483 ≤ 17952643161167^3483*5000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2265673677 5000000000 17952643161167 50000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(85454097/200000000 : ℝ), (503347699/1250000000 : ℝ), (2265673677/5000000000 : ℝ)] ![(33275895858207/100000000000000 : ℝ), (15409408903023/50000000000000 : ℝ), (17952643161167/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(85454097/200000000 : ℝ)|^4507 ≤ (33275895858207/100000000000000 : ℝ)^3483
        have hw : |(85454097/200000000 : ℝ)|=(85454097/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(503347699/1250000000 : ℝ)|^4507 ≤ (15409408903023/50000000000000 : ℝ)^3483
        have hw : |(503347699/1250000000 : ℝ)|=(503347699/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2265673677/5000000000 : ℝ)|^4507 ≤ (17952643161167/50000000000000 : ℝ)^3483
        have hw : |(2265673677/5000000000 : ℝ)|=(2265673677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1505_s3_4 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-375579701/2000000000 : ℝ)*x 0 + (260763339/500000000 : ℝ)*x 1 + (2718251297/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (375579701/2000000000 : ℝ)^4507 ≤ (1435628754897/12500000000000 : ℝ)^3483 := by
    have hnat : (375579701 : ℕ)^4507*12500000000000^3483 ≤ 1435628754897^3483*2000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      375579701 2000000000 1435628754897 12500000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (260763339/500000000 : ℝ)^4507 ≤ (43068127589313/100000000000000 : ℝ)^3483 := by
    have hnat : (260763339 : ℕ)^4507*100000000000000^3483 ≤ 43068127589313^3483*500000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260763339 500000000 43068127589313 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2718251297/5000000000 : ℝ)^4507 ≤ (11361710589059/25000000000000 : ℝ)^3483 := by
    have hnat : (2718251297 : ℕ)^4507*25000000000000^3483 ≤ 11361710589059^3483*5000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718251297 5000000000 11361710589059 25000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-375579701/2000000000 : ℝ), (260763339/500000000 : ℝ), (2718251297/5000000000 : ℝ)] ![(1435628754897/12500000000000 : ℝ), (43068127589313/100000000000000 : ℝ), (11361710589059/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-375579701/2000000000 : ℝ)|^4507 ≤ (1435628754897/12500000000000 : ℝ)^3483
        have hw : |(-375579701/2000000000 : ℝ)|=(375579701/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(260763339/500000000 : ℝ)|^4507 ≤ (43068127589313/100000000000000 : ℝ)^3483
        have hw : |(260763339/500000000 : ℝ)|=(260763339/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2718251297/5000000000 : ℝ)|^4507 ≤ (11361710589059/25000000000000 : ℝ)^3483
        have hw : |(2718251297/5000000000 : ℝ)|=(2718251297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1505_s3_5 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323566079/2500000000 : ℝ)*x 0 + (-1770071199/10000000000 : ℝ)*x 1 + (5436502729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323566079/2500000000 : ℝ)^4507 ≤ (8782833021961/20000000000000 : ℝ)^3483 := by
    have hnat : (1323566079 : ℕ)^4507*20000000000000^3483 ≤ 8782833021961^3483*2500000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323566079 2500000000 8782833021961 20000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1770071199/10000000000 : ℝ)^4507 ≤ (10638991056311/100000000000000 : ℝ)^3483 := by
    have hnat : (1770071199 : ℕ)^4507*100000000000000^3483 ≤ 10638991056311^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1770071199 10000000000 10638991056311 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5436502729/10000000000 : ℝ)^4507 ≤ (45446843816569/100000000000000 : ℝ)^3483 := by
    have hnat : (5436502729 : ℕ)^4507*100000000000000^3483 ≤ 45446843816569^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436502729 10000000000 45446843816569 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323566079/2500000000 : ℝ), (-1770071199/10000000000 : ℝ), (5436502729/10000000000 : ℝ)] ![(8782833021961/20000000000000 : ℝ), (10638991056311/100000000000000 : ℝ), (45446843816569/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323566079/2500000000 : ℝ)|^4507 ≤ (8782833021961/20000000000000 : ℝ)^3483
        have hw : |(1323566079/2500000000 : ℝ)|=(1323566079/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1770071199/10000000000 : ℝ)|^4507 ≤ (10638991056311/100000000000000 : ℝ)^3483
        have hw : |(-1770071199/10000000000 : ℝ)|=(1770071199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5436502729/10000000000 : ℝ)|^4507 ≤ (45446843816569/100000000000000 : ℝ)^3483
        have hw : |(5436502729/10000000000 : ℝ)|=(5436502729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1505_s3_6 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294264317/10000000000 : ℝ)*x 0 + (5436502593/10000000000 : ℝ)*x 1 + (-442517847/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294264317/10000000000 : ℝ)^4507 ≤ (43914165120539/100000000000000 : ℝ)^3483 := by
    have hnat : (5294264317 : ℕ)^4507*100000000000000^3483 ≤ 43914165120539^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294264317 10000000000 43914165120539 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5436502593/10000000000 : ℝ)^4507 ≤ (22723421172709/50000000000000 : ℝ)^3483 := by
    have hnat : (5436502593 : ℕ)^4507*50000000000000^3483 ≤ 22723421172709^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436502593 10000000000 22723421172709 50000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (442517847/2500000000 : ℝ)^4507 ≤ (10638992526271/100000000000000 : ℝ)^3483 := by
    have hnat : (442517847 : ℕ)^4507*100000000000000^3483 ≤ 10638992526271^3483*2500000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442517847 2500000000 10638992526271 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294264317/10000000000 : ℝ), (5436502593/10000000000 : ℝ), (-442517847/2500000000 : ℝ)] ![(43914165120539/100000000000000 : ℝ), (22723421172709/50000000000000 : ℝ), (10638992526271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294264317/10000000000 : ℝ)|^4507 ≤ (43914165120539/100000000000000 : ℝ)^3483
        have hw : |(5294264317/10000000000 : ℝ)|=(5294264317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5436502593/10000000000 : ℝ)|^4507 ≤ (22723421172709/50000000000000 : ℝ)^3483
        have hw : |(5436502593/10000000000 : ℝ)|=(5436502593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-442517847/2500000000 : ℝ)|^4507 ≤ (10638992526271/100000000000000 : ℝ)^3483
        have hw : |(-442517847/2500000000 : ℝ)|=(442517847/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1505_s3_7 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2136388729/5000000000 : ℝ)*x 0 + (226433673/500000000 : ℝ)*x 1 + (503684441/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2136388729/5000000000 : ℝ)^4507 ≤ (33276627580869/100000000000000 : ℝ)^3483 := by
    have hnat : (2136388729 : ℕ)^4507*100000000000000^3483 ≤ 33276627580869^3483*5000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2136388729 5000000000 33276627580869 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (226433673/500000000 : ℝ)^4507 ≤ (17938936185697/50000000000000 : ℝ)^3483 := by
    have hnat : (226433673 : ℕ)^4507*50000000000000^3483 ≤ 17938936185697^3483*500000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226433673 500000000 17938936185697 50000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (503684441/1250000000 : ℝ)^4507 ≤ (3855687503247/12500000000000 : ℝ)^3483 := by
    have hnat : (503684441 : ℕ)^4507*12500000000000^3483 ≤ 3855687503247^3483*1250000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      503684441 1250000000 3855687503247 12500000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2136388729/5000000000 : ℝ), (226433673/500000000 : ℝ), (503684441/1250000000 : ℝ)] ![(33276627580869/100000000000000 : ℝ), (17938936185697/50000000000000 : ℝ), (3855687503247/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2136388729/5000000000 : ℝ)|^4507 ≤ (33276627580869/100000000000000 : ℝ)^3483
        have hw : |(2136388729/5000000000 : ℝ)|=(2136388729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(226433673/500000000 : ℝ)|^4507 ≤ (17938936185697/50000000000000 : ℝ)^3483
        have hw : |(226433673/500000000 : ℝ)|=(226433673/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(503684441/1250000000 : ℝ)|^4507 ≤ (3855687503247/12500000000000 : ℝ)^3483
        have hw : |(503684441/1250000000 : ℝ)|=(503684441/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1505_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162820231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2003/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10389/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (541/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3111/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2003/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10389/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2003/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10389/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2003/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10389/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2003/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10389/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2003/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10389/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2003/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10389/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10389/100000 : ℝ) ^ (4505/1024 : ℝ) ≤ (471520642090981/10000000000000000000 : ℝ) := by
    have hpowers : (10389/100000 : ℝ)^4505 ≤ (471520642090981/10000000000000000000 : ℝ)^1024 := by
      have hnat : (10389 : ℕ)^4505*10000000000000000000^1024 ≤ 471520642090981^1024*100000^4505 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10389 100000 471520642090981 10000000000000000000 4505 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10389/100000 : ℝ)) (X := (471520642090981/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4505 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2003/12500 : ℝ) ^ (4505/1024 : ℝ) ≤ (15864561716084641/50000000000000000000 : ℝ) := by
    have hpowers : (2003/12500 : ℝ)^4505 ≤ (15864561716084641/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2003 : ℕ)^4505*50000000000000000000^1024 ≤ 15864561716084641^1024*12500^4505 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2003 12500 15864561716084641 50000000000000000000 4505 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2003/12500 : ℝ)) (X := (15864561716084641/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4505 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000471520642090981/5000000000000000000 : ℝ) ≤ (1250026793537551/1250000000000000 : ℝ) ^ (4505/1024 : ℝ) := by
    have hpowers : (5000471520642090981/5000000000000000000 : ℝ)^1024 ≤ (1250026793537551/1250000000000000 : ℝ)^4505 := by
      have hnat : (5000471520642090981 : ℕ)^1024*1250000000000000^4505 ≤ 1250026793537551^4505*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000471520642090981 5000000000000000000 1250026793537551 1250000000000000 1024 4505 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250026793537551/1250000000000000 : ℝ)) (X := (5000471520642090981/5000000000000000000 : ℝ)) (by norm_num) 4505 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25009111082463269773/25000000000000000000 : ℝ) ≤ (10000828273924691/10000000000000000 : ℝ) ^ (4505/1024 : ℝ) := by
    have hpowers : (25009111082463269773/25000000000000000000 : ℝ)^1024 ≤ (10000828273924691/10000000000000000 : ℝ)^4505 := by
      have hnat : (25009111082463269773 : ℕ)^1024*10000000000000000^4505 ≤ 10000828273924691^4505*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25009111082463269773 25000000000000000000 10000828273924691 10000000000000000 1024 4505 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000828273924691/10000000000000000 : ℝ)) (X := (25009111082463269773/25000000000000000000 : ℝ)) (by norm_num) 4505 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015864561716084641/25000000000000000000 : ℝ) ≤ (5000721099774487/5000000000000000 : ℝ) ^ (4505/1024 : ℝ) := by
    have hpowers : (25015864561716084641/25000000000000000000 : ℝ)^1024 ≤ (5000721099774487/5000000000000000 : ℝ)^4505 := by
      have hnat : (25015864561716084641 : ℕ)^1024*5000000000000000^4505 ≤ 5000721099774487^4505*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015864561716084641 25000000000000000000 5000721099774487 5000000000000000 1024 4505 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000721099774487/5000000000000000 : ℝ)) (X := (25015864561716084641/25000000000000000000 : ℝ)) (by norm_num) 4505 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(471520642090981/10000000000000000000 : ℝ) ≤ ((28169225853025723453/28175000000000000000 : ℝ)+2*(613925624283/563500000000000 : ℝ)*(10389/100000 : ℝ))^(4505/1024 : ℝ) := by
    rw [show (28169225853025723453/28175000000000000000 : ℝ)+2*(613925624283/563500000000000 : ℝ)*(10389/100000 : ℝ)=(1250026793537551/1250000000000000 : ℝ) by norm_num, show 1+2*(471520642090981/10000000000000000000 : ℝ)=(5000471520642090981/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15864561716084641/50000000000000000000 : ℝ)+(471520642090981/10000000000000000000 : ℝ) ≤ ((28169225853025723453/28175000000000000000 : ℝ)+(613925624283/563500000000000 : ℝ)*((2003/12500 : ℝ)+(10389/100000 : ℝ)))^(4505/1024 : ℝ) := by
    rw [show (28169225853025723453/28175000000000000000 : ℝ)+(613925624283/563500000000000 : ℝ)*((2003/12500 : ℝ)+(10389/100000 : ℝ))=(10000828273924691/10000000000000000 : ℝ) by norm_num, show 1+(15864561716084641/50000000000000000000 : ℝ)+(471520642090981/10000000000000000000 : ℝ)=(25009111082463269773/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15864561716084641/50000000000000000000 : ℝ) ≤ ((28169225853025723453/28175000000000000000 : ℝ)+2*(613925624283/563500000000000 : ℝ)*(2003/12500 : ℝ))^(4505/1024 : ℝ) := by
    rw [show (28169225853025723453/28175000000000000000 : ℝ)+2*(613925624283/563500000000000 : ℝ)*(2003/12500 : ℝ)=(5000721099774487/5000000000000000 : ℝ) by norm_num, show 1+2*(15864561716084641/50000000000000000000 : ℝ)=(25015864561716084641/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (28169225853025723453/28175000000000000000 : ℝ)*(X 1 0+X 2 0)+(613925624283/563500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4505/1024 : ℝ)) (lo := (10389/100000 : ℝ)) (hi := (2003/12500 : ℝ)) (c := (28169225853025723453/28175000000000000000 : ℝ)) (alpha := (613925624283/563500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (28169225853025723453/28175000000000000000 : ℝ)*(X 0 1+X 2 1)+(613925624283/563500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4505/1024 : ℝ)) (lo := (10389/100000 : ℝ)) (hi := (2003/12500 : ℝ)) (c := (28169225853025723453/28175000000000000000 : ℝ)) (alpha := (613925624283/563500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (28169225853025723453/28175000000000000000 : ℝ)*(X 0 2+X 1 2)+(613925624283/563500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4505/1024 : ℝ)) (lo := (10389/100000 : ℝ)) (hi := (2003/12500 : ℝ)) (c := (28169225853025723453/28175000000000000000 : ℝ)) (alpha := (613925624283/563500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-93893327/500000000 : ℝ)*X 0 0+(5437696623/10000000000 : ℝ)*X 0 1+(651760209/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338226191/2500000000 : ℝ)*X 1 0+(-996246241/5000000000 : ℝ)*X 1 1+(521408163/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352904739/10000000000 : ℝ)*X 2 0+(651760207/1250000000 : ℝ)*X 2 1+(-6226539/31250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((85454097/200000000 : ℝ)*X 0 0+(503347699/1250000000 : ℝ)*X 0 1+(2265673677/5000000000 : ℝ)*X 0 2+(85454097/200000000 : ℝ)*X 1 0+(503347699/1250000000 : ℝ)*X 1 1+(2265673677/5000000000 : ℝ)*X 1 2+(85454097/200000000 : ℝ)*X 2 0+(503347699/1250000000 : ℝ)*X 2 1+(2265673677/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-375579701/2000000000 : ℝ)*X 0 0+(260763339/500000000 : ℝ)*X 0 1+(2718251297/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1323566079/2500000000 : ℝ)*X 1 0+(-1770071199/10000000000 : ℝ)*X 1 1+(5436502729/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5294264317/10000000000 : ℝ)*X 2 0+(5436502593/10000000000 : ℝ)*X 2 1+(-442517847/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2136388729/5000000000 : ℝ)*X 0 0+(226433673/500000000 : ℝ)*X 0 1+(503684441/1250000000 : ℝ)*X 0 2+(2136388729/5000000000 : ℝ)*X 1 0+(226433673/500000000 : ℝ)*X 1 1+(503684441/1250000000 : ℝ)*X 1 2+(2136388729/5000000000 : ℝ)*X 2 0+(226433673/500000000 : ℝ)*X 2 1+(503684441/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6198347795278500379831130571/704375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (161201889/10000000000000 : ℝ)*(base19) + (739342121/50000000000000 : ℝ)*(base23) + (15048179/25000000000000 : ℝ)*(lower2) + (109717909/50000000000000 : ℝ)*(upper3) + (134167857/100000000000000 : ℝ)*(upper5) + (3226973159937461/100000000000000 : ℝ)*(major0) + (3226973159937461/100000000000000 : ℝ)*(major1) + (1613486579968731/50000000000000 : ℝ)*(major2) + (223599904824059/5000000000000 : ℝ)*(sp0) + (4472020460658667/100000000000000 : ℝ)*(sp1) + (894404118798663/20000000000000 : ℝ)*(sp2) + (19819124312723/1000000000000 : ℝ)*(sp3) + (11988098189/50000000000000 : ℝ)*(sp4) + (460903957/4000000000000 : ℝ)*(sp7) + (247740494233903/12500000000000 : ℝ)*(f.failure) + (4472022072677557/100000000000000 : ℝ)*(f.sum) + (35691865749209/56350000000000000000000000000 : ℝ)*base65 + (14331274075151727167/2817500000000000000000000000000000 : ℝ)*base68 + (15243246002674923143/1408750000000000000000000000000000 : ℝ)*base69 + (10439151457183272833/2817500000000000000000000000000000 : ℝ)*base71 + (256456684092891/56350000000000000000000000000 : ℝ)*base74 + (12815054462442423143/1408750000000000000000000000000000 : ℝ)*base75 + (17070067095921622833/2817500000000000000000000000000000 : ℝ)*base77 + (2864743658415877167/2817500000000000000000000000000000 : ℝ)*base80 + (54279878945463/28175000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (8008407/1250000000000000000000 : ℝ)*base90 + (8008407/1250000000000000000000 : ℝ)*base92 + (20508407/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (32826000063626857720780263/4025000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1554731661/100000000000000 : ℝ)*(base19) + (233258219/12500000000000 : ℝ)*(base23) + (99879517/50000000000000 : ℝ)*(upper3) + (152768771/100000000000000 : ℝ)*(lower4) + (135880829/100000000000000 : ℝ)*(upper5) + (65232727748067/2000000000000 : ℝ)*(major0) + (65232727748067/2000000000000 : ℝ)*(major1) + (65232727748067/2000000000000 : ℝ)*(major2) + (12830687793/50000000000000 : ℝ)*(sp1) + (27640861/100000000000 : ℝ)*(sp2) + (1130014821479507/25000000000000 : ℝ)*(sp4) + (226001603490539/5000000000000 : ℝ)*(sp5) + (180801191159651/4000000000000 : ℝ)*(sp6) + (2003213217037721/100000000000000 : ℝ)*(sp7) + (2003213217037721/100000000000000 : ℝ)*(f.failure) + (1130014821479507/25000000000000 : ℝ)*(f.sum) + (493078335123/140875000000000000000000000 : ℝ)*base66 + (810303300670365351/56350000000000000000000000000000 : ℝ)*base67 + (919816042113365351/56350000000000000000000000000000 : ℝ)*base69 + (230922918242665351/56350000000000000000000000000000 : ℝ)*base71 + (2828836315223/563500000000000000000000000 : ℝ)*base73 + (1450444879996565351/56350000000000000000000000000000 : ℝ)*base75 + (686890495499815351/56350000000000000000000000000000 : ℝ)*base77 + (1014505431728115351/56350000000000000000000000000000 : ℝ)*base79 + (1787794295723/563500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (131066449/10000000000000000000000 : ℝ)*base90 + (131066449/10000000000000000000000 : ℝ)*base92 + (131066449/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1505_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162820231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2003/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10389/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (541/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3111/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1505_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1505_s4_0 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-375668261/2000000000 : ℝ)*x 0 + (679323391/1250000000 : ℝ)*x 1 + (2608438833/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (375668261/2000000000 : ℝ)^4507 ≤ (2872133616039/25000000000000 : ℝ)^3483 := by
    have hnat : (375668261 : ℕ)^4507*25000000000000^3483 ≤ 2872133616039^3483*2000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      375668261 2000000000 2872133616039 25000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (679323391/1250000000 : ℝ)^4507 ≤ (9085224658279/20000000000000 : ℝ)^3483 := by
    have hnat : (679323391 : ℕ)^4507*20000000000000^3483 ≤ 9085224658279^3483*1250000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      679323391 1250000000 9085224658279 20000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2608438833/5000000000 : ℝ)^4507 ≤ (43085342234267/100000000000000 : ℝ)^3483 := by
    have hnat : (2608438833 : ℕ)^4507*100000000000000^3483 ≤ 43085342234267^3483*5000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608438833 5000000000 43085342234267 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-375668261/2000000000 : ℝ), (679323391/1250000000 : ℝ), (2608438833/5000000000 : ℝ)] ![(2872133616039/25000000000000 : ℝ), (9085224658279/20000000000000 : ℝ), (43085342234267/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-375668261/2000000000 : ℝ)|^4507 ≤ (2872133616039/25000000000000 : ℝ)^3483
        have hw : |(-375668261/2000000000 : ℝ)|=(375668261/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(679323391/1250000000 : ℝ)|^4507 ≤ (9085224658279/20000000000000 : ℝ)^3483
        have hw : |(679323391/1250000000 : ℝ)|=(679323391/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2608438833/5000000000 : ℝ)|^4507 ≤ (43085342234267/100000000000000 : ℝ)^3483
        have hw : |(2608438833/5000000000 : ℝ)|=(2608438833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1505_s4_1 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352092631/10000000000 : ℝ)*x 0 + (-1989867641/10000000000 : ℝ)*x 1 + (163027427/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352092631/10000000000 : ℝ)^4507 ≤ (22267923787169/50000000000000 : ℝ)^3483 := by
    have hnat : (5352092631 : ℕ)^4507*50000000000000^3483 ≤ 22267923787169^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352092631 10000000000 22267923787169 50000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1989867641/10000000000 : ℝ)^4507 ≤ (6189405098639/50000000000000 : ℝ)^3483 := by
    have hnat : (1989867641 : ℕ)^4507*50000000000000^3483 ≤ 6189405098639^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1989867641 10000000000 6189405098639 50000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (163027427/312500000 : ℝ)^4507 ≤ (43085342212893/100000000000000 : ℝ)^3483 := by
    have hnat : (163027427 : ℕ)^4507*100000000000000^3483 ≤ 43085342212893^3483*312500000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163027427 312500000 43085342212893 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352092631/10000000000 : ℝ), (-1989867641/10000000000 : ℝ), (163027427/312500000 : ℝ)] ![(22267923787169/50000000000000 : ℝ), (6189405098639/50000000000000 : ℝ), (43085342212893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352092631/10000000000 : ℝ)|^4507 ≤ (22267923787169/50000000000000 : ℝ)^3483
        have hw : |(5352092631/10000000000 : ℝ)|=(5352092631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1989867641/10000000000 : ℝ)|^4507 ≤ (6189405098639/50000000000000 : ℝ)^3483
        have hw : |(-1989867641/10000000000 : ℝ)|=(1989867641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(163027427/312500000 : ℝ)|^4507 ≤ (43085342212893/100000000000000 : ℝ)^3483
        have hw : |(163027427/312500000 : ℝ)|=(163027427/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1505_s4_2 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070418489/2000000000 : ℝ)*x 0 + (52168777/100000000 : ℝ)*x 1 + (-1989867843/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070418489/2000000000 : ℝ)^4507 ≤ (44535845571559/100000000000000 : ℝ)^3483 := by
    have hnat : (1070418489 : ℕ)^4507*100000000000000^3483 ≤ 44535845571559^3483*2000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070418489 2000000000 44535845571559 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (52168777/100000000 : ℝ)^4507 ≤ (43085342597623/100000000000000 : ℝ)^3483 := by
    have hnat : (52168777 : ℕ)^4507*100000000000000^3483 ≤ 43085342597623^3483*100000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52168777 100000000 43085342597623 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1989867843/10000000000 : ℝ)^4507 ≤ (1547351477919/12500000000000 : ℝ)^3483 := by
    have hnat : (1989867843 : ℕ)^4507*12500000000000^3483 ≤ 1547351477919^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1989867843 10000000000 1547351477919 12500000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070418489/2000000000 : ℝ), (52168777/100000000 : ℝ), (-1989867843/10000000000 : ℝ)] ![(44535845571559/100000000000000 : ℝ), (43085342597623/100000000000000 : ℝ), (1547351477919/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070418489/2000000000 : ℝ)|^4507 ≤ (44535845571559/100000000000000 : ℝ)^3483
        have hw : |(1070418489/2000000000 : ℝ)|=(1070418489/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(52168777/100000000 : ℝ)|^4507 ≤ (43085342597623/100000000000000 : ℝ)^3483
        have hw : |(52168777/100000000 : ℝ)|=(52168777/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1989867843/10000000000 : ℝ)|^4507 ≤ (1547351477919/12500000000000 : ℝ)^3483
        have hw : |(-1989867843/10000000000 : ℝ)|=(1989867843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1505_s4_3 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (854600297/2000000000 : ℝ)*x 0 + (4033410331/10000000000 : ℝ)*x 1 + (4524650173/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (854600297/2000000000 : ℝ)^4507 ≤ (6655777056791/20000000000000 : ℝ)^3483 := by
    have hnat : (854600297 : ℕ)^4507*20000000000000^3483 ≤ 6655777056791^3483*2000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      854600297 2000000000 6655777056791 20000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4033410331/10000000000 : ℝ)^4507 ≤ (30884481898071/100000000000000 : ℝ)^3483 := by
    have hnat : (4033410331 : ℕ)^4507*100000000000000^3483 ≤ 30884481898071^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4033410331 10000000000 30884481898071 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4524650173/10000000000 : ℝ)^4507 ≤ (17918316404941/50000000000000 : ℝ)^3483 := by
    have hnat : (4524650173 : ℕ)^4507*50000000000000^3483 ≤ 17918316404941^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4524650173 10000000000 17918316404941 50000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(854600297/2000000000 : ℝ), (4033410331/10000000000 : ℝ), (4524650173/10000000000 : ℝ)] ![(6655777056791/20000000000000 : ℝ), (30884481898071/100000000000000 : ℝ), (17918316404941/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(854600297/2000000000 : ℝ)|^4507 ≤ (6655777056791/20000000000000 : ℝ)^3483
        have hw : |(854600297/2000000000 : ℝ)|=(854600297/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4033410331/10000000000 : ℝ)|^4507 ≤ (30884481898071/100000000000000 : ℝ)^3483
        have hw : |(4033410331/10000000000 : ℝ)|=(4033410331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4524650173/10000000000 : ℝ)|^4507 ≤ (17918316404941/50000000000000 : ℝ)^3483
        have hw : |(4524650173/10000000000 : ℝ)|=(4524650173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1505_s4_4 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-469592803/2500000000 : ℝ)*x 0 + (5218000993/10000000000 : ℝ)*x 1 + (1358363817/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (469592803/2500000000 : ℝ)^4507 ≤ (1436096395507/12500000000000 : ℝ)^3483 := by
    have hnat : (469592803 : ℕ)^4507*12500000000000^3483 ≤ 1436096395507^3483*2500000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      469592803 2500000000 1436096395507 12500000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5218000993/10000000000 : ℝ)^4507 ≤ (21548673765807/50000000000000 : ℝ)^3483 := by
    have hnat : (5218000993 : ℕ)^4507*50000000000000^3483 ≤ 21548673765807^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218000993 10000000000 21548673765807 50000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1358363817/2500000000 : ℝ)^4507 ≤ (22706940642271/50000000000000 : ℝ)^3483 := by
    have hnat : (1358363817 : ℕ)^4507*50000000000000^3483 ≤ 22706940642271^3483*2500000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358363817 2500000000 22706940642271 50000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-469592803/2500000000 : ℝ), (5218000993/10000000000 : ℝ), (1358363817/2500000000 : ℝ)] ![(1436096395507/12500000000000 : ℝ), (21548673765807/50000000000000 : ℝ), (22706940642271/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-469592803/2500000000 : ℝ)|^4507 ≤ (1436096395507/12500000000000 : ℝ)^3483
        have hw : |(-469592803/2500000000 : ℝ)|=(469592803/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5218000993/10000000000 : ℝ)|^4507 ≤ (21548673765807/50000000000000 : ℝ)^3483
        have hw : |(5218000993/10000000000 : ℝ)|=(5218000993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1358363817/2500000000 : ℝ)|^4507 ≤ (22706940642271/50000000000000 : ℝ)^3483
        have hw : |(1358363817/2500000000 : ℝ)|=(1358363817/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1505_s4_5 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295001441/10000000000 : ℝ)*x 0 + (-7093163/40000000 : ℝ)*x 1 + (1358363901/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295001441/10000000000 : ℝ)^4507 ≤ (1756883082093/4000000000000 : ℝ)^3483 := by
    have hnat : (5295001441 : ℕ)^4507*4000000000000^3483 ≤ 1756883082093^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295001441 10000000000 1756883082093 4000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7093163/40000000 : ℝ)^4507 ≤ (1333004752997/12500000000000 : ℝ)^3483 := by
    have hnat : (7093163 : ℕ)^4507*12500000000000^3483 ≤ 1333004752997^3483*40000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7093163 40000000 1333004752997 12500000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1358363901/2500000000 : ℝ)^4507 ≤ (908277698371/2000000000000 : ℝ)^3483 := by
    have hnat : (1358363901 : ℕ)^4507*2000000000000^3483 ≤ 908277698371^3483*2500000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358363901 2500000000 908277698371 2000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295001441/10000000000 : ℝ), (-7093163/40000000 : ℝ), (1358363901/2500000000 : ℝ)] ![(1756883082093/4000000000000 : ℝ), (1333004752997/12500000000000 : ℝ), (908277698371/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295001441/10000000000 : ℝ)|^4507 ≤ (1756883082093/4000000000000 : ℝ)^3483
        have hw : |(5295001441/10000000000 : ℝ)|=(5295001441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7093163/40000000 : ℝ)|^4507 ≤ (1333004752997/12500000000000 : ℝ)^3483
        have hw : |(-7093163/40000000 : ℝ)|=(7093163/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1358363901/2500000000 : ℝ)|^4507 ≤ (908277698371/2000000000000 : ℝ)^3483
        have hw : |(1358363901/2500000000 : ℝ)|=(1358363901/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1505_s4_6 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295002861/10000000000 : ℝ)*x 0 + (1358363617/2500000000 : ℝ)*x 1 + (-13853831/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295002861/10000000000 : ℝ)^4507 ≤ (43922092294229/100000000000000 : ℝ)^3483 := by
    have hnat : (5295002861 : ℕ)^4507*100000000000000^3483 ≤ 43922092294229^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295002861 10000000000 43922092294229 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1358363617/2500000000 : ℝ)^4507 ≤ (22706936316071/50000000000000 : ℝ)^3483 := by
    have hnat : (1358363617 : ℕ)^4507*50000000000000^3483 ≤ 22706936316071^3483*2500000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358363617 2500000000 22706936316071 50000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (13853831/78125000 : ℝ)^4507 ≤ (5332017525679/50000000000000 : ℝ)^3483 := by
    have hnat : (13853831 : ℕ)^4507*50000000000000^3483 ≤ 5332017525679^3483*78125000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13853831 78125000 5332017525679 50000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295002861/10000000000 : ℝ), (1358363617/2500000000 : ℝ), (-13853831/78125000 : ℝ)] ![(43922092294229/100000000000000 : ℝ), (22706936316071/50000000000000 : ℝ), (5332017525679/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295002861/10000000000 : ℝ)|^4507 ≤ (43922092294229/100000000000000 : ℝ)^3483
        have hw : |(5295002861/10000000000 : ℝ)|=(5295002861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1358363617/2500000000 : ℝ)|^4507 ≤ (22706936316071/50000000000000 : ℝ)^3483
        have hw : |(1358363617/2500000000 : ℝ)|=(1358363617/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-13853831/78125000 : ℝ)|^4507 ≤ (5332017525679/50000000000000 : ℝ)^3483
        have hw : |(-13853831/78125000 : ℝ)|=(13853831/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1505_s4_7 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2136534113/5000000000 : ℝ)*x 0 + (2261057939/5000000000 : ℝ)*x 1 + (4035963383/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2136534113/5000000000 : ℝ)^4507 ≤ (1663977894713/5000000000000 : ℝ)^3483 := by
    have hnat : (2136534113 : ℕ)^4507*5000000000000^3483 ≤ 1663977894713^3483*5000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2136534113 5000000000 1663977894713 5000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2261057939/5000000000 : ℝ)^4507 ≤ (17905330635723/50000000000000 : ℝ)^3483 := by
    have hnat : (2261057939 : ℕ)^4507*50000000000000^3483 ≤ 17905330635723^3483*5000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2261057939 5000000000 17905330635723 50000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4035963383/10000000000 : ℝ)^4507 ≤ (15454890411317/50000000000000 : ℝ)^3483 := by
    have hnat : (4035963383 : ℕ)^4507*50000000000000^3483 ≤ 15454890411317^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4035963383 10000000000 15454890411317 50000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2136534113/5000000000 : ℝ), (2261057939/5000000000 : ℝ), (4035963383/10000000000 : ℝ)] ![(1663977894713/5000000000000 : ℝ), (17905330635723/50000000000000 : ℝ), (15454890411317/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2136534113/5000000000 : ℝ)|^4507 ≤ (1663977894713/5000000000000 : ℝ)^3483
        have hw : |(2136534113/5000000000 : ℝ)|=(2136534113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2261057939/5000000000 : ℝ)|^4507 ≤ (17905330635723/50000000000000 : ℝ)^3483
        have hw : |(2261057939/5000000000 : ℝ)|=(2261057939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4035963383/10000000000 : ℝ)|^4507 ≤ (15454890411317/50000000000000 : ℝ)^3483
        have hw : |(4035963383/10000000000 : ℝ)|=(4035963383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1505_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162820231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3111/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (541/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (68/625 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1549/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3111/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (541/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3111/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (541/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3111/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (541/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3111/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (541/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3111/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (541/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3111/20000 : ℝ)*(X 0 2+X 1 2) := by
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
  have hpowlo : (541/5000 : ℝ) ^ (4505/1024 : ℝ) ≤ (1127705829660211/20000000000000000000 : ℝ) := by
    have hpowers : (541/5000 : ℝ)^4505 ≤ (1127705829660211/20000000000000000000 : ℝ)^1024 := by
      have hnat : (541 : ℕ)^4505*20000000000000000000^1024 ≤ 1127705829660211^1024*5000^4505 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        541 5000 1127705829660211 20000000000000000000 4505 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (541/5000 : ℝ)) (X := (1127705829660211/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4505 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3111/20000 : ℝ) ^ (4505/1024 : ℝ) ≤ (27842073884297697/100000000000000000000 : ℝ) := by
    have hpowers : (3111/20000 : ℝ)^4505 ≤ (27842073884297697/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3111 : ℕ)^4505*100000000000000000000^1024 ≤ 27842073884297697^1024*20000^4505 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3111 20000 27842073884297697 100000000000000000000 4505 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3111/20000 : ℝ)) (X := (27842073884297697/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4505 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001127705829660211/10000000000000000000 : ℝ) ≤ (10000256319747173/10000000000000000 : ℝ) ^ (4505/1024 : ℝ) := by
    have hpowers : (10001127705829660211/10000000000000000000 : ℝ)^1024 ≤ (10000256319747173/10000000000000000 : ℝ)^4505 := by
      have hnat : (10001127705829660211 : ℕ)^1024*10000000000000000^4505 ≤ 10000256319747173^4505*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001127705829660211 10000000000000000000 10000256319747173 10000000000000000 1024 4505 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000256319747173/10000000000000000 : ℝ)) (X := (10001127705829660211/10000000000000000000 : ℝ)) (by norm_num) 4505 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (3126046268844768711/3125000000000000000 : ℝ) ≤ (5000380462859793/5000000000000000 : ℝ) ^ (4505/1024 : ℝ) := by
    have hpowers : (3126046268844768711/3125000000000000000 : ℝ)^1024 ≤ (5000380462859793/5000000000000000 : ℝ)^4505 := by
      have hnat : (3126046268844768711 : ℕ)^1024*5000000000000000^4505 ≤ 5000380462859793^4505*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126046268844768711 3125000000000000000 5000380462859793 5000000000000000 1024 4505 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000380462859793/5000000000000000 : ℝ)) (X := (3126046268844768711/3125000000000000000 : ℝ)) (by norm_num) 4505 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50027842073884297697/50000000000000000000 : ℝ) ≤ (10001265531691999/10000000000000000 : ℝ) ^ (4505/1024 : ℝ) := by
    have hpowers : (50027842073884297697/50000000000000000000 : ℝ)^1024 ≤ (10001265531691999/10000000000000000 : ℝ)^4505 := by
      have hnat : (50027842073884297697 : ℕ)^1024*10000000000000000^4505 ≤ 10001265531691999^4505*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027842073884297697 50000000000000000000 10001265531691999 10000000000000000 1024 4505 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001265531691999/10000000000000000 : ℝ)) (X := (50027842073884297697/50000000000000000000 : ℝ)) (by norm_num) 4505 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1127705829660211/20000000000000000000 : ℝ) ≤ ((9468058800151969367/9470000000000000000 : ℝ)+2*(504605972413/473500000000000 : ℝ)*(541/5000 : ℝ))^(4505/1024 : ℝ) := by
    rw [show (9468058800151969367/9470000000000000000 : ℝ)+2*(504605972413/473500000000000 : ℝ)*(541/5000 : ℝ)=(10000256319747173/10000000000000000 : ℝ) by norm_num, show 1+2*(1127705829660211/20000000000000000000 : ℝ)=(10001127705829660211/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27842073884297697/100000000000000000000 : ℝ)+(1127705829660211/20000000000000000000 : ℝ) ≤ ((9468058800151969367/9470000000000000000 : ℝ)+(504605972413/473500000000000 : ℝ)*((3111/20000 : ℝ)+(541/5000 : ℝ)))^(4505/1024 : ℝ) := by
    rw [show (9468058800151969367/9470000000000000000 : ℝ)+(504605972413/473500000000000 : ℝ)*((3111/20000 : ℝ)+(541/5000 : ℝ))=(5000380462859793/5000000000000000 : ℝ) by norm_num, show 1+(27842073884297697/100000000000000000000 : ℝ)+(1127705829660211/20000000000000000000 : ℝ)=(3126046268844768711/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27842073884297697/100000000000000000000 : ℝ) ≤ ((9468058800151969367/9470000000000000000 : ℝ)+2*(504605972413/473500000000000 : ℝ)*(3111/20000 : ℝ))^(4505/1024 : ℝ) := by
    rw [show (9468058800151969367/9470000000000000000 : ℝ)+2*(504605972413/473500000000000 : ℝ)*(3111/20000 : ℝ)=(10001265531691999/10000000000000000 : ℝ) by norm_num, show 1+2*(27842073884297697/100000000000000000000 : ℝ)=(50027842073884297697/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9468058800151969367/9470000000000000000 : ℝ)*(X 1 0+X 2 0)+(504605972413/473500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4505/1024 : ℝ)) (lo := (541/5000 : ℝ)) (hi := (3111/20000 : ℝ)) (c := (9468058800151969367/9470000000000000000 : ℝ)) (alpha := (504605972413/473500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9468058800151969367/9470000000000000000 : ℝ)*(X 0 1+X 2 1)+(504605972413/473500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4505/1024 : ℝ)) (lo := (541/5000 : ℝ)) (hi := (3111/20000 : ℝ)) (c := (9468058800151969367/9470000000000000000 : ℝ)) (alpha := (504605972413/473500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9468058800151969367/9470000000000000000 : ℝ)*(X 0 2+X 1 2)+(504605972413/473500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4505/1024 : ℝ)) (lo := (541/5000 : ℝ)) (hi := (3111/20000 : ℝ)) (c := (9468058800151969367/9470000000000000000 : ℝ)) (alpha := (504605972413/473500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-375668261/2000000000 : ℝ)*X 0 0+(679323391/1250000000 : ℝ)*X 0 1+(2608438833/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352092631/10000000000 : ℝ)*X 1 0+(-1989867641/10000000000 : ℝ)*X 1 1+(163027427/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1070418489/2000000000 : ℝ)*X 2 0+(52168777/100000000 : ℝ)*X 2 1+(-1989867843/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((854600297/2000000000 : ℝ)*X 0 0+(4033410331/10000000000 : ℝ)*X 0 1+(4524650173/10000000000 : ℝ)*X 0 2+(854600297/2000000000 : ℝ)*X 1 0+(4033410331/10000000000 : ℝ)*X 1 1+(4524650173/10000000000 : ℝ)*X 1 2+(854600297/2000000000 : ℝ)*X 2 0+(4033410331/10000000000 : ℝ)*X 2 1+(4524650173/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-469592803/2500000000 : ℝ)*X 0 0+(5218000993/10000000000 : ℝ)*X 0 1+(1358363817/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5295001441/10000000000 : ℝ)*X 1 0+(-7093163/40000000 : ℝ)*X 1 1+(1358363901/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5295002861/10000000000 : ℝ)*X 2 0+(1358363617/2500000000 : ℝ)*X 2 1+(-13853831/78125000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2136534113/5000000000 : ℝ)*X 0 0+(2261057939/5000000000 : ℝ)*X 0 1+(4035963383/10000000000 : ℝ)*X 0 2+(2136534113/5000000000 : ℝ)*X 1 0+(2261057939/5000000000 : ℝ)*X 1 1+(4035963383/10000000000 : ℝ)*X 1 2+(2136534113/5000000000 : ℝ)*X 2 0+(2261057939/5000000000 : ℝ)*X 2 1+(4035963383/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3737877523561242571338271899/473500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (262798337/20000000000000 : ℝ)*(base19) + (117546527/10000000000000 : ℝ)*(base23) + (19061167/50000000000000 : ℝ)*(lower2) + (202848117/100000000000000 : ℝ)*(upper3) + (6177189/12500000000000 : ℝ)*(lower4) + (662900667740799/20000000000000 : ℝ)*(major0) + (662900667740799/20000000000000 : ℝ)*(major1) + (828625834675999/25000000000000 : ℝ)*(major2) + (1148326015956001/25000000000000 : ℝ)*(sp0) + (459332236088687/10000000000000 : ℝ)*(sp1) + (1148330624853321/25000000000000 : ℝ)*(sp2) + (2035673232214737/100000000000000 : ℝ)*(sp3) + (392221091/2000000000000 : ℝ)*(sp4) + (4753588267/50000000000000 : ℝ)*(sp7) + (2035682739391271/100000000000000 : ℝ)*(f.failure) + (918664734975711/20000000000000 : ℝ)*(f.sum) + (177515371428867/47350000000000000000000000000 : ℝ)*base66 + (330996129519903767/189400000000000000000000000000000 : ℝ)*base68 + (677960840570547633/236750000000000000000000000000000 : ℝ)*base69 + (1799907647957103767/189400000000000000000000000000000 : ℝ)*base72 + (101892820294133/47350000000000000000000000000 : ℝ)*base73 + (1014451812482547633/236750000000000000000000000000000 : ℝ)*base75 + (793822679100755767/189400000000000000000000000000000 : ℝ)*base78 + (2297679827253244233/189400000000000000000000000000000 : ℝ)*base79 + (3221466919951/2367500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (43603601/10000000000000000000000 : ℝ)*base89 + (43603601/10000000000000000000000 : ℝ)*base91 + (56396399/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (55726550857640728108731459/7398437500000000000000000000000 : ℝ) := by norm_num
    linear_combination (461115133/100000000000000 : ℝ)*(base19) + (2002331381/100000000000000 : ℝ)*(base23) + (66813681/100000000000000 : ℝ)*(upper2) + (102733531/50000000000000 : ℝ)*(upper3) + (31373597/25000000000000 : ℝ)*(upper5) + (52330717816467/1562500000000 : ℝ)*(major0) + (52330717816467/1562500000000 : ℝ)*(major1) + (52330717816467/1562500000000 : ℝ)*(major2) + (3718128129/50000000000000 : ℝ)*(sp1) + (23234042049/100000000000000 : ℝ)*(sp2) + (4641360011298003/100000000000000 : ℝ)*(sp4) + (4641352113926613/100000000000000 : ℝ)*(sp5) + (4641334774924573/100000000000000 : ℝ)*(sp6) + (411394323627251/20000000000000 : ℝ)*(sp7) + (411394323627251/20000000000000 : ℝ)*(f.failure) + (4641360011298003/100000000000000 : ℝ)*(f.sum) + (11096943783103/11837500000000000000000000000 : ℝ)*base66 + (7927089304136493/7398437500000000000000000000000 : ℝ)*base68 + (61399180616176007/7398437500000000000000000000000 : ℝ)*base69 + (27255092161355243/7398437500000000000000000000000 : ℝ)*base72 + (29118777186803/11837500000000000000000000000 : ℝ)*base74 + (42710009850386493/7398437500000000000000000000000 : ℝ)*base76 + (49874900862851111/14796875000000000000000000000000 : ℝ)*base78 + (29871738972257361/14796875000000000000000000000000 : ℝ)*base80 + (90095173285647/11837500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (5714981/2000000000000000000000 : ℝ)*base89 + (5714981/2000000000000000000000 : ℝ)*base91 + (5714981/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1505_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162820231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3111/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (541/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (68/625 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1505_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1505_s5_0 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1878401233/10000000000 : ℝ)*x 0 + (2717097189/5000000000 : ℝ)*x 1 + (208689231/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1878401233/10000000000 : ℝ)^4507 ≤ (5744504383663/50000000000000 : ℝ)^3483 := by
    have hnat : (1878401233 : ℕ)^4507*50000000000000^3483 ≤ 5744504383663^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1878401233 10000000000 5744504383663 50000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2717097189/5000000000 : ℝ)^4507 ≤ (9084375057741/20000000000000 : ℝ)^3483 := by
    have hnat : (2717097189 : ℕ)^4507*20000000000000^3483 ≤ 9084375057741^3483*5000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717097189 5000000000 9084375057741 20000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (208689231/400000000 : ℝ)^4507 ≤ (10772278980773/25000000000000 : ℝ)^3483 := by
    have hnat : (208689231 : ℕ)^4507*25000000000000^3483 ≤ 10772278980773^3483*400000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208689231 400000000 10772278980773 25000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1878401233/10000000000 : ℝ), (2717097189/5000000000 : ℝ), (208689231/400000000 : ℝ)] ![(5744504383663/50000000000000 : ℝ), (9084375057741/20000000000000 : ℝ), (10772278980773/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1878401233/10000000000 : ℝ)|^4507 ≤ (5744504383663/50000000000000 : ℝ)^3483
        have hw : |(-1878401233/10000000000 : ℝ)|=(1878401233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2717097189/5000000000 : ℝ)|^4507 ≤ (9084375057741/20000000000000 : ℝ)^3483
        have hw : |(2717097189/5000000000 : ℝ)|=(2717097189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(208689231/400000000 : ℝ)|^4507 ≤ (10772278980773/25000000000000 : ℝ)^3483
        have hw : |(208689231/400000000 : ℝ)|=(208689231/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1505_s5_1 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351989753/10000000000 : ℝ)*x 0 + (-1989536469/10000000000 : ℝ)*x 1 + (5217230763/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351989753/10000000000 : ℝ)^4507 ≤ (1781389593003/4000000000000 : ℝ)^3483 := by
    have hnat : (5351989753 : ℕ)^4507*4000000000000^3483 ≤ 1781389593003^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351989753 10000000000 1781389593003 4000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1989536469/10000000000 : ℝ)^4507 ≤ (12376144371377/100000000000000 : ℝ)^3483 := by
    have hnat : (1989536469 : ℕ)^4507*100000000000000^3483 ≤ 12376144371377^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1989536469 10000000000 12376144371377 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5217230763/10000000000 : ℝ)^4507 ≤ (21544557897423/50000000000000 : ℝ)^3483 := by
    have hnat : (5217230763 : ℕ)^4507*50000000000000^3483 ≤ 21544557897423^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217230763 10000000000 21544557897423 50000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351989753/10000000000 : ℝ), (-1989536469/10000000000 : ℝ), (5217230763/10000000000 : ℝ)] ![(1781389593003/4000000000000 : ℝ), (12376144371377/100000000000000 : ℝ), (21544557897423/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351989753/10000000000 : ℝ)|^4507 ≤ (1781389593003/4000000000000 : ℝ)^3483
        have hw : |(5351989753/10000000000 : ℝ)|=(5351989753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1989536469/10000000000 : ℝ)|^4507 ≤ (12376144371377/100000000000000 : ℝ)^3483
        have hw : |(-1989536469/10000000000 : ℝ)|=(1989536469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5217230763/10000000000 : ℝ)|^4507 ≤ (21544557897423/50000000000000 : ℝ)^3483
        have hw : |(5217230763/10000000000 : ℝ)|=(5217230763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1505_s5_2 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351989663/10000000000 : ℝ)*x 0 + (2608615441/5000000000 : ℝ)*x 1 + (-1989536431/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351989663/10000000000 : ℝ)^4507 ≤ (22267369427997/50000000000000 : ℝ)^3483 := by
    have hnat : (5351989663 : ℕ)^4507*50000000000000^3483 ≤ 22267369427997^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351989663 10000000000 22267369427997 50000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2608615441/5000000000 : ℝ)^4507 ≤ (43089117066617/100000000000000 : ℝ)^3483 := by
    have hnat : (2608615441 : ℕ)^4507*100000000000000^3483 ≤ 43089117066617^3483*5000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608615441 5000000000 43089117066617 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1989536431/10000000000 : ℝ)^4507 ≤ (12376144065497/100000000000000 : ℝ)^3483 := by
    have hnat : (1989536431 : ℕ)^4507*100000000000000^3483 ≤ 12376144065497^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1989536431 10000000000 12376144065497 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351989663/10000000000 : ℝ), (2608615441/5000000000 : ℝ), (-1989536431/10000000000 : ℝ)] ![(22267369427997/50000000000000 : ℝ), (43089117066617/100000000000000 : ℝ), (12376144065497/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351989663/10000000000 : ℝ)|^4507 ≤ (22267369427997/50000000000000 : ℝ)^3483
        have hw : |(5351989663/10000000000 : ℝ)|=(5351989663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2608615441/5000000000 : ℝ)|^4507 ≤ (43089117066617/100000000000000 : ℝ)^3483
        have hw : |(2608615441/5000000000 : ℝ)|=(2608615441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1989536431/10000000000 : ℝ)|^4507 ≤ (12376144065497/100000000000000 : ℝ)^3483
        have hw : |(-1989536431/10000000000 : ℝ)|=(1989536431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1505_s5_3 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (854607709/2000000000 : ℝ)*x 0 + (504280903/1250000000 : ℝ)*x 1 + (2261902297/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (854607709/2000000000 : ℝ)^4507 ≤ (33279258771203/100000000000000 : ℝ)^3483 := by
    have hnat : (854607709 : ℕ)^4507*100000000000000^3483 ≤ 33279258771203^3483*2000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      854607709 2000000000 33279258771203 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (504280903/1250000000 : ℝ)^4507 ≤ (30892774392309/100000000000000 : ℝ)^3483 := by
    have hnat : (504280903 : ℕ)^4507*100000000000000^3483 ≤ 30892774392309^3483*1250000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      504280903 1250000000 30892774392309 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2261902297/5000000000 : ℝ)^4507 ≤ (8956991703239/25000000000000 : ℝ)^3483 := by
    have hnat : (2261902297 : ℕ)^4507*25000000000000^3483 ≤ 8956991703239^3483*5000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2261902297 5000000000 8956991703239 25000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(854607709/2000000000 : ℝ), (504280903/1250000000 : ℝ), (2261902297/5000000000 : ℝ)] ![(33279258771203/100000000000000 : ℝ), (30892774392309/100000000000000 : ℝ), (8956991703239/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(854607709/2000000000 : ℝ)|^4507 ≤ (33279258771203/100000000000000 : ℝ)^3483
        have hw : |(854607709/2000000000 : ℝ)|=(854607709/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(504280903/1250000000 : ℝ)|^4507 ≤ (30892774392309/100000000000000 : ℝ)^3483
        have hw : |(504280903/1250000000 : ℝ)|=(504280903/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2261902297/5000000000 : ℝ)|^4507 ≤ (8956991703239/25000000000000 : ℝ)^3483
        have hw : |(2261902297/5000000000 : ℝ)|=(2261902297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1505_s5_4 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1878430473/10000000000 : ℝ)*x 0 + (1304586643/2500000000 : ℝ)*x 1 + (2716535201/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1878430473/10000000000 : ℝ)^4507 ≤ (11489240190391/100000000000000 : ℝ)^3483 := by
    have hnat : (1878430473 : ℕ)^4507*100000000000000^3483 ≤ 11489240190391^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1878430473 10000000000 11489240190391 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1304586643/2500000000 : ℝ)^4507 ≤ (8620208196009/20000000000000 : ℝ)^3483 := by
    have hnat : (1304586643 : ℕ)^4507*20000000000000^3483 ≤ 8620208196009^3483*2500000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304586643 2500000000 8620208196009 20000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2716535201/5000000000 : ℝ)^4507 ≤ (45409718809601/100000000000000 : ℝ)^3483 := by
    have hnat : (2716535201 : ℕ)^4507*100000000000000^3483 ≤ 45409718809601^3483*5000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716535201 5000000000 45409718809601 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1878430473/10000000000 : ℝ), (1304586643/2500000000 : ℝ), (2716535201/5000000000 : ℝ)] ![(11489240190391/100000000000000 : ℝ), (8620208196009/20000000000000 : ℝ), (45409718809601/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1878430473/10000000000 : ℝ)|^4507 ≤ (11489240190391/100000000000000 : ℝ)^3483
        have hw : |(-1878430473/10000000000 : ℝ)|=(1878430473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1304586643/2500000000 : ℝ)|^4507 ≤ (8620208196009/20000000000000 : ℝ)^3483
        have hw : |(1304586643/2500000000 : ℝ)|=(1304586643/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2716535201/5000000000 : ℝ)|^4507 ≤ (45409718809601/100000000000000 : ℝ)^3483
        have hw : |(2716535201/5000000000 : ℝ)|=(2716535201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1505_s5_5 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (132377379/250000000 : ℝ)*x 0 + (-27714013/156250000 : ℝ)*x 1 + (5433070403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132377379/250000000 : ℝ)^4507 ≤ (686298172029/1562500000000 : ℝ)^3483 := by
    have hnat : (132377379 : ℕ)^4507*1562500000000^3483 ≤ 686298172029^3483*250000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132377379 250000000 686298172029 1562500000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (27714013/156250000 : ℝ)^4507 ≤ (5333599074183/50000000000000 : ℝ)^3483 := by
    have hnat : (27714013 : ℕ)^4507*50000000000000^3483 ≤ 5333599074183^3483*156250000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27714013 156250000 5333599074183 50000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5433070403/10000000000 : ℝ)^4507 ≤ (709526856569/1562500000000 : ℝ)^3483 := by
    have hnat : (5433070403 : ℕ)^4507*1562500000000^3483 ≤ 709526856569^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433070403 10000000000 709526856569 1562500000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132377379/250000000 : ℝ), (-27714013/156250000 : ℝ), (5433070403/10000000000 : ℝ)] ![(686298172029/1562500000000 : ℝ), (5333599074183/50000000000000 : ℝ), (709526856569/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132377379/250000000 : ℝ)|^4507 ≤ (686298172029/1562500000000 : ℝ)^3483
        have hw : |(132377379/250000000 : ℝ)|=(132377379/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-27714013/156250000 : ℝ)|^4507 ≤ (5333599074183/50000000000000 : ℝ)^3483
        have hw : |(-27714013/156250000 : ℝ)|=(27714013/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5433070403/10000000000 : ℝ)|^4507 ≤ (709526856569/1562500000000 : ℝ)^3483
        have hw : |(5433070403/10000000000 : ℝ)|=(5433070403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1505_s5_6 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295095161/10000000000 : ℝ)*x 0 + (5433070403/10000000000 : ℝ)*x 1 + (-27714013/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295095161/10000000000 : ℝ)^4507 ≤ (4392308302059/10000000000000 : ℝ)^3483 := by
    have hnat : (5295095161 : ℕ)^4507*10000000000000^3483 ≤ 4392308302059^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295095161 10000000000 4392308302059 10000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5433070403/10000000000 : ℝ)^4507 ≤ (709526856569/1562500000000 : ℝ)^3483 := by
    have hnat : (5433070403 : ℕ)^4507*1562500000000^3483 ≤ 709526856569^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433070403 10000000000 709526856569 1562500000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (27714013/156250000 : ℝ)^4507 ≤ (5333599074183/50000000000000 : ℝ)^3483 := by
    have hnat : (27714013 : ℕ)^4507*50000000000000^3483 ≤ 5333599074183^3483*156250000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27714013 156250000 5333599074183 50000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295095161/10000000000 : ℝ), (5433070403/10000000000 : ℝ), (-27714013/156250000 : ℝ)] ![(4392308302059/10000000000000 : ℝ), (709526856569/1562500000000 : ℝ), (5333599074183/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295095161/10000000000 : ℝ)|^4507 ≤ (4392308302059/10000000000000 : ℝ)^3483
        have hw : |(5295095161/10000000000 : ℝ)|=(5295095161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5433070403/10000000000 : ℝ)|^4507 ≤ (709526856569/1562500000000 : ℝ)^3483
        have hw : |(5433070403/10000000000 : ℝ)|=(5433070403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-27714013/156250000 : ℝ)|^4507 ≤ (5333599074183/50000000000000 : ℝ)^3483
        have hw : |(-27714013/156250000 : ℝ)|=(27714013/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1505_s5_7 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4273104699/10000000000 : ℝ)*x 0 + (1130321769/2500000000 : ℝ)*x 1 + (4036783229/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4273104699/10000000000 : ℝ)^4507 ≤ (16639962733729/50000000000000 : ℝ)^3483 := by
    have hnat : (4273104699 : ℕ)^4507*50000000000000^3483 ≤ 16639962733729^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4273104699 10000000000 16639962733729 50000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1130321769/2500000000 : ℝ)^4507 ≤ (35802168609707/100000000000000 : ℝ)^3483 := by
    have hnat : (1130321769 : ℕ)^4507*100000000000000^3483 ≤ 35802168609707^3483*2500000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1130321769 2500000000 35802168609707 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4036783229/10000000000 : ℝ)^4507 ≤ (30917905910037/100000000000000 : ℝ)^3483 := by
    have hnat : (4036783229 : ℕ)^4507*100000000000000^3483 ≤ 30917905910037^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4036783229 10000000000 30917905910037 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4273104699/10000000000 : ℝ), (1130321769/2500000000 : ℝ), (4036783229/10000000000 : ℝ)] ![(16639962733729/50000000000000 : ℝ), (35802168609707/100000000000000 : ℝ), (30917905910037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4273104699/10000000000 : ℝ)|^4507 ≤ (16639962733729/50000000000000 : ℝ)^3483
        have hw : |(4273104699/10000000000 : ℝ)|=(4273104699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1130321769/2500000000 : ℝ)|^4507 ≤ (35802168609707/100000000000000 : ℝ)^3483
        have hw : |(1130321769/2500000000 : ℝ)|=(1130321769/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4036783229/10000000000 : ℝ)|^4507 ≤ (30917905910037/100000000000000 : ℝ)^3483
        have hw : |(4036783229/10000000000 : ℝ)|=(4036783229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1505_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162820231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (68/625 : ℝ)*pair X i i ≤ pair X i h) :
    (1361/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7741/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (68/625 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (68/625 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (68/625 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (68/625 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (68/625 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (68/625 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (68/625 : ℝ) ^ (4505/1024 : ℝ) ≤ (5777389061797829/100000000000000000000 : ℝ) := by
    have hpowers : (68/625 : ℝ)^4505 ≤ (5777389061797829/100000000000000000000 : ℝ)^1024 := by
      have hnat : (68 : ℕ)^4505*100000000000000000000^1024 ≤ 5777389061797829^1024*625^4505 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        68 625 5777389061797829 100000000000000000000 4505 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (68/625 : ℝ)) (X := (5777389061797829/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4505 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1549/10000 : ℝ) ^ (4505/1024 : ℝ) ≤ (27333850665668103/100000000000000000000 : ℝ) := by
    have hpowers : (1549/10000 : ℝ)^4505 ≤ (27333850665668103/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1549 : ℕ)^4505*100000000000000000000^1024 ≤ 27333850665668103^1024*10000^4505 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1549 10000 27333850665668103 100000000000000000000 4505 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1549/10000 : ℝ)) (X := (27333850665668103/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4505 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005777389061797829/50000000000000000000 : ℝ) ≤ (5000131315922639/5000000000000000 : ℝ) ^ (4505/1024 : ℝ) := by
    have hpowers : (50005777389061797829/50000000000000000000 : ℝ)^1024 ≤ (5000131315922639/5000000000000000 : ℝ)^4505 := by
      have hnat : (50005777389061797829 : ℕ)^1024*5000000000000000^4505 ≤ 5000131315922639^4505*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005777389061797829 50000000000000000000 5000131315922639 5000000000000000 1024 4505 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000131315922639/5000000000000000 : ℝ)) (X := (50005777389061797829/50000000000000000000 : ℝ)) (by norm_num) 4505 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25008277809931866483/25000000000000000000 : ℝ) ≤ (2000150506428073/2000000000000000 : ℝ) ^ (4505/1024 : ℝ) := by
    have hpowers : (25008277809931866483/25000000000000000000 : ℝ)^1024 ≤ (2000150506428073/2000000000000000 : ℝ)^4505 := by
      have hnat : (25008277809931866483 : ℕ)^1024*2000000000000000^4505 ≤ 2000150506428073^4505*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25008277809931866483 25000000000000000000 2000150506428073 2000000000000000 1024 4505 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000150506428073/2000000000000000 : ℝ)) (X := (25008277809931866483/25000000000000000000 : ℝ)) (by norm_num) 4505 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50027333850665668103/50000000000000000000 : ℝ) ≤ (2500310608108863/2500000000000000 : ℝ) ^ (4505/1024 : ℝ) := by
    have hpowers : (50027333850665668103/50000000000000000000 : ℝ)^1024 ≤ (2500310608108863/2500000000000000 : ℝ)^4505 := by
      have hnat : (50027333850665668103 : ℕ)^1024*2500000000000000^4505 ≤ 2500310608108863^4505*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027333850665668103 50000000000000000000 2500310608108863 2500000000000000 1024 4505 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500310608108863/2500000000000000 : ℝ)) (X := (50027333850665668103/50000000000000000000 : ℝ)) (by norm_num) 4505 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5777389061797829/100000000000000000000 : ℝ) ≤ ((2304527525119281923/2305000000000000000 : ℝ)+2*(489900295087/461000000000000 : ℝ)*(68/625 : ℝ))^(4505/1024 : ℝ) := by
    rw [show (2304527525119281923/2305000000000000000 : ℝ)+2*(489900295087/461000000000000 : ℝ)*(68/625 : ℝ)=(5000131315922639/5000000000000000 : ℝ) by norm_num, show 1+2*(5777389061797829/100000000000000000000 : ℝ)=(50005777389061797829/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27333850665668103/100000000000000000000 : ℝ)+(5777389061797829/100000000000000000000 : ℝ) ≤ ((2304527525119281923/2305000000000000000 : ℝ)+(489900295087/461000000000000 : ℝ)*((1549/10000 : ℝ)+(68/625 : ℝ)))^(4505/1024 : ℝ) := by
    rw [show (2304527525119281923/2305000000000000000 : ℝ)+(489900295087/461000000000000 : ℝ)*((1549/10000 : ℝ)+(68/625 : ℝ))=(2000150506428073/2000000000000000 : ℝ) by norm_num, show 1+(27333850665668103/100000000000000000000 : ℝ)+(5777389061797829/100000000000000000000 : ℝ)=(25008277809931866483/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27333850665668103/100000000000000000000 : ℝ) ≤ ((2304527525119281923/2305000000000000000 : ℝ)+2*(489900295087/461000000000000 : ℝ)*(1549/10000 : ℝ))^(4505/1024 : ℝ) := by
    rw [show (2304527525119281923/2305000000000000000 : ℝ)+2*(489900295087/461000000000000 : ℝ)*(1549/10000 : ℝ)=(2500310608108863/2500000000000000 : ℝ) by norm_num, show 1+2*(27333850665668103/100000000000000000000 : ℝ)=(50027333850665668103/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2304527525119281923/2305000000000000000 : ℝ)*(X 1 0+X 2 0)+(489900295087/461000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4505/1024 : ℝ)) (lo := (68/625 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (2304527525119281923/2305000000000000000 : ℝ)) (alpha := (489900295087/461000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2304527525119281923/2305000000000000000 : ℝ)*(X 0 1+X 2 1)+(489900295087/461000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4505/1024 : ℝ)) (lo := (68/625 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (2304527525119281923/2305000000000000000 : ℝ)) (alpha := (489900295087/461000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2304527525119281923/2305000000000000000 : ℝ)*(X 0 2+X 1 2)+(489900295087/461000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4505/1024 : ℝ)) (lo := (68/625 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (2304527525119281923/2305000000000000000 : ℝ)) (alpha := (489900295087/461000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1878401233/10000000000 : ℝ)*X 0 0+(2717097189/5000000000 : ℝ)*X 0 1+(208689231/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351989753/10000000000 : ℝ)*X 1 0+(-1989536469/10000000000 : ℝ)*X 1 1+(5217230763/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351989663/10000000000 : ℝ)*X 2 0+(2608615441/5000000000 : ℝ)*X 2 1+(-1989536431/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((854607709/2000000000 : ℝ)*X 0 0+(504280903/1250000000 : ℝ)*X 0 1+(2261902297/5000000000 : ℝ)*X 0 2+(854607709/2000000000 : ℝ)*X 1 0+(504280903/1250000000 : ℝ)*X 1 1+(2261902297/5000000000 : ℝ)*X 1 2+(854607709/2000000000 : ℝ)*X 2 0+(504280903/1250000000 : ℝ)*X 2 1+(2261902297/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1878430473/10000000000 : ℝ)*X 0 0+(1304586643/2500000000 : ℝ)*X 0 1+(2716535201/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((132377379/250000000 : ℝ)*X 1 0+(-27714013/156250000 : ℝ)*X 1 1+(5433070403/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5295095161/10000000000 : ℝ)*X 2 0+(5433070403/10000000000 : ℝ)*X 2 1+(-27714013/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4273104699/10000000000 : ℝ)*X 0 0+(1130321769/2500000000 : ℝ)*X 0 1+(4036783229/10000000000 : ℝ)*X 0 2+(4273104699/10000000000 : ℝ)*X 1 0+(1130321769/2500000000 : ℝ)*X 1 1+(4036783229/10000000000 : ℝ)*X 1 2+(4273104699/10000000000 : ℝ)*X 2 0+(1130321769/2500000000 : ℝ)*X 2 1+(4036783229/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (373794704677779844052829231/115250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (584044911/100000000000000 : ℝ)*(base19) + (95452607/20000000000000 : ℝ)*(base23) + (1133083/1562500000000 : ℝ)*(upper3) + (626711/4000000000000 : ℝ)*(upper4) + (1508887/2000000000000 : ℝ)*(upper5) + (1662938807917269/50000000000000 : ℝ)*(major0) + (1662938807917269/50000000000000 : ℝ)*(major1) + (3325877615834539/100000000000000 : ℝ)*(major2) + (2304538634901823/50000000000000 : ℝ)*(sp0) + (921817202304957/20000000000000 : ℝ)*(sp1) + (4609086118306661/100000000000000 : ℝ)*(sp2) + (255333134073391/12500000000000 : ℝ)*(sp3) + (186515321/2000000000000 : ℝ)*(sp4) + (3455400981/100000000000000 : ℝ)*(sp7) + (2042668527988109/100000000000000 : ℝ)*(f.failure) + (144033956111553/3125000000000 : ℝ)*(f.sum) + (52581650487599/46100000000000000000000000000 : ℝ)*base65 + (294587399901960787/115250000000000000000000000000000 : ℝ)*base67 + (2494393040790268497/230500000000000000000000000000000 : ℝ)*base69 + (534630537810039213/115250000000000000000000000000000 : ℝ)*base72 + (125500383020399/46100000000000000000000000000 : ℝ)*base73 + (537654752037768497/230500000000000000000000000000000 : ℝ)*base75 + (1170942388702256713/115250000000000000000000000000000 : ℝ)*base78 + (486525135999256713/115250000000000000000000000000000 : ℝ)*base80 + (17158966402653/11525000000000000000000000000 : ℝ)*base81 + (72633179/10000000000000000000000 : ℝ)*base89 + (72633179/10000000000000000000000 : ℝ)*base91 + (27366821/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (54199354387423002291342609/5762500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1538455619/100000000000000 : ℝ)*(base19) + (1670245177/100000000000000 : ℝ)*(base23) + (508145793/100000000000000 : ℝ)*(lower1) + (24365221/12500000000000 : ℝ)*(upper3) + (1844447/3125000000000 : ℝ)*(lower4) + (38753187/20000000000000 : ℝ)*(upper5) + (168026921757139/5000000000000 : ℝ)*(major0) + (168026921757139/5000000000000 : ℝ)*(major1) + (168026921757139/5000000000000 : ℝ)*(major2) + (1809631323/100000000000000 : ℝ)*(sp2) + (931424048928373/20000000000000 : ℝ)*(sp4) + (2328559353093123/50000000000000 : ℝ)*(sp5) + (931423352953073/20000000000000 : ℝ)*(sp6) + (2063956312126089/100000000000000 : ℝ)*(sp7) + (2063956312126089/100000000000000 : ℝ)*(f.failure) + (931424048928373/20000000000000 : ℝ)*(f.sum) + (1807371425007/288125000000000000000000000 : ℝ)*base65 + (17225798139763297/11525000000000000000000000000000 : ℝ)*base67 + (46838380155088297/11525000000000000000000000000000 : ℝ)*base69 + (217734365646411703/11525000000000000000000000000000 : ℝ)*base72 + (1468562062437/1152500000000000000000000000 : ℝ)*base74 + (72176807472111703/11525000000000000000000000000000 : ℝ)*base76 + (3594689893738297/11525000000000000000000000000000 : ℝ)*base77 + (205997551023238297/11525000000000000000000000000000 : ℝ)*base79 + (951730808827/1152500000000000000000000000 : ℝ)*base82 + (87893441/10000000000000000000000 : ℝ)*base90 + (87893441/10000000000000000000000 : ℝ)*base92 + (87893441/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1505_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162820231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (68/625 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1361/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1505_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1505_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162820231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2003/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10389/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1361/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1505_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1505_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1505_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162820231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2003/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10389/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1361/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1505_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
