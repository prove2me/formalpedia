-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1289_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:25:11.653899+00:00
-- url     : https://prove2.me/submissions/4c425877-b130-4334-909a-9375b0b81b57

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
theorem support_rectangle_w1289_s6_0 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-418130189/2000000000 : ℝ)*x 0 + (5415482129/10000000000 : ℝ)*x 1 + (163837261/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (418130189/2000000000 : ℝ)^4249 ≤ (12719139826691/100000000000000 : ℝ)^3225 := by
    have hnat : (418130189 : ℕ)^4249*100000000000000^3225 ≤ 12719139826691^3225*2000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      418130189 2000000000 12719139826691 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5415482129/10000000000 : ℝ)^4249 ≤ (44571962120577/100000000000000 : ℝ)^3225 := by
    have hnat : (5415482129 : ℕ)^4249*100000000000000^3225 ≤ 44571962120577^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415482129 10000000000 44571962120577 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (163837261/312500000 : ℝ)^4249 ≤ (42708898040309/100000000000000 : ℝ)^3225 := by
    have hnat : (163837261 : ℕ)^4249*100000000000000^3225 ≤ 42708898040309^3225*312500000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163837261 312500000 42708898040309 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-418130189/2000000000 : ℝ), (5415482129/10000000000 : ℝ), (163837261/312500000 : ℝ)] ![(12719139826691/100000000000000 : ℝ), (44571962120577/100000000000000 : ℝ), (42708898040309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-418130189/2000000000 : ℝ)|^4249 ≤ (12719139826691/100000000000000 : ℝ)^3225
        have hw : |(-418130189/2000000000 : ℝ)|=(418130189/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5415482129/10000000000 : ℝ)|^4249 ≤ (44571962120577/100000000000000 : ℝ)^3225
        have hw : |(5415482129/10000000000 : ℝ)|=(5415482129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(163837261/312500000 : ℝ)|^4249 ≤ (42708898040309/100000000000000 : ℝ)^3225
        have hw : |(163837261/312500000 : ℝ)|=(163837261/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_s6_1 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349852583/10000000000 : ℝ)*x 0 + (-2178683357/10000000000 : ℝ)*x 1 + (5242792361/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349852583/10000000000 : ℝ)^4249 ≤ (2193083063447/5000000000000 : ℝ)^3225 := by
    have hnat : (5349852583 : ℕ)^4249*5000000000000^3225 ≤ 2193083063447^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349852583 10000000000 2193083063447 5000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2178683357/10000000000 : ℝ)^4249 ≤ (1678680072299/12500000000000 : ℝ)^3225 := by
    have hnat : (2178683357 : ℕ)^4249*12500000000000^3225 ≤ 1678680072299^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178683357 10000000000 1678680072299 12500000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242792361/10000000000 : ℝ)^4249 ≤ (5338612267113/12500000000000 : ℝ)^3225 := by
    have hnat : (5242792361 : ℕ)^4249*12500000000000^3225 ≤ 5338612267113^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242792361 10000000000 5338612267113 12500000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349852583/10000000000 : ℝ), (-2178683357/10000000000 : ℝ), (5242792361/10000000000 : ℝ)] ![(2193083063447/5000000000000 : ℝ), (1678680072299/12500000000000 : ℝ), (5338612267113/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349852583/10000000000 : ℝ)|^4249 ≤ (2193083063447/5000000000000 : ℝ)^3225
        have hw : |(5349852583/10000000000 : ℝ)|=(5349852583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2178683357/10000000000 : ℝ)|^4249 ≤ (1678680072299/12500000000000 : ℝ)^3225
        have hw : |(-2178683357/10000000000 : ℝ)|=(2178683357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242792361/10000000000 : ℝ)|^4249 ≤ (5338612267113/12500000000000 : ℝ)^3225
        have hw : |(5242792361/10000000000 : ℝ)|=(5242792361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_s6_2 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (213994103/400000000 : ℝ)*x 0 + (2621396179/5000000000 : ℝ)*x 1 + (-2178683371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213994103/400000000 : ℝ)^4249 ≤ (1754466447301/4000000000000 : ℝ)^3225 := by
    have hnat : (213994103 : ℕ)^4249*4000000000000^3225 ≤ 1754466447301^3225*400000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213994103 400000000 1754466447301 4000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621396179/5000000000 : ℝ)^4249 ≤ (21354449052353/50000000000000 : ℝ)^3225 := by
    have hnat : (2621396179 : ℕ)^4249*50000000000000^3225 ≤ 21354449052353^3225*5000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621396179 5000000000 21354449052353 50000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2178683371/10000000000 : ℝ)^4249 ≤ (13429440692089/100000000000000 : ℝ)^3225 := by
    have hnat : (2178683371 : ℕ)^4249*100000000000000^3225 ≤ 13429440692089^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178683371 10000000000 13429440692089 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213994103/400000000 : ℝ), (2621396179/5000000000 : ℝ), (-2178683371/10000000000 : ℝ)] ![(1754466447301/4000000000000 : ℝ), (21354449052353/50000000000000 : ℝ), (13429440692089/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213994103/400000000 : ℝ)|^4249 ≤ (1754466447301/4000000000000 : ℝ)^3225
        have hw : |(213994103/400000000 : ℝ)|=(213994103/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621396179/5000000000 : ℝ)|^4249 ≤ (21354449052353/50000000000000 : ℝ)^3225
        have hw : |(2621396179/5000000000 : ℝ)|=(2621396179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2178683371/10000000000 : ℝ)|^4249 ≤ (13429440692089/100000000000000 : ℝ)^3225
        have hw : |(-2178683371/10000000000 : ℝ)|=(2178683371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_s6_3 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (868133211/2000000000 : ℝ)*x 0 + (4166874521/10000000000 : ℝ)*x 1 + (4521386173/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (868133211/2000000000 : ℝ)^4249 ≤ (33302244122097/100000000000000 : ℝ)^3225 := by
    have hnat : (868133211 : ℕ)^4249*100000000000000^3225 ≤ 33302244122097^3225*2000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      868133211 2000000000 33302244122097 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4166874521/10000000000 : ℝ)^4249 ≤ (15778396596229/50000000000000 : ℝ)^3225 := by
    have hnat : (4166874521 : ℕ)^4249*50000000000000^3225 ≤ 15778396596229^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4166874521 10000000000 15778396596229 50000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4521386173/10000000000 : ℝ)^4249 ≤ (8785240668203/25000000000000 : ℝ)^3225 := by
    have hnat : (4521386173 : ℕ)^4249*25000000000000^3225 ≤ 8785240668203^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4521386173 10000000000 8785240668203 25000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(868133211/2000000000 : ℝ), (4166874521/10000000000 : ℝ), (4521386173/10000000000 : ℝ)] ![(33302244122097/100000000000000 : ℝ), (15778396596229/50000000000000 : ℝ), (8785240668203/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(868133211/2000000000 : ℝ)|^4249 ≤ (33302244122097/100000000000000 : ℝ)^3225
        have hw : |(868133211/2000000000 : ℝ)|=(868133211/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4166874521/10000000000 : ℝ)|^4249 ≤ (15778396596229/50000000000000 : ℝ)^3225
        have hw : |(4166874521/10000000000 : ℝ)|=(4166874521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4521386173/10000000000 : ℝ)|^4249 ≤ (8785240668203/25000000000000 : ℝ)^3225
        have hw : |(4521386173/10000000000 : ℝ)|=(4521386173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_s6_4 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-6533323/31250000 : ℝ)*x 0 + (5243408633/10000000000 : ℝ)*x 1 + (2707431479/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6533323/31250000 : ℝ)^4249 ≤ (6359619669907/50000000000000 : ℝ)^3225 := by
    have hnat : (6533323 : ℕ)^4249*50000000000000^3225 ≤ 6359619669907^3225*31250000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6533323 31250000 6359619669907 50000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243408633/10000000000 : ℝ)^4249 ≤ (42715512579653/100000000000000 : ℝ)^3225 := by
    have hnat : (5243408633 : ℕ)^4249*100000000000000^3225 ≤ 42715512579653^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243408633 10000000000 42715512579653 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707431479/5000000000 : ℝ)^4249 ≤ (5570656009227/12500000000000 : ℝ)^3225 := by
    have hnat : (2707431479 : ℕ)^4249*12500000000000^3225 ≤ 5570656009227^3225*5000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707431479 5000000000 5570656009227 12500000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-6533323/31250000 : ℝ), (5243408633/10000000000 : ℝ), (2707431479/5000000000 : ℝ)] ![(6359619669907/50000000000000 : ℝ), (42715512579653/100000000000000 : ℝ), (5570656009227/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-6533323/31250000 : ℝ)|^4249 ≤ (6359619669907/50000000000000 : ℝ)^3225
        have hw : |(-6533323/31250000 : ℝ)|=(6533323/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243408633/10000000000 : ℝ)|^4249 ≤ (42715512579653/100000000000000 : ℝ)^3225
        have hw : |(5243408633/10000000000 : ℝ)|=(5243408633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707431479/5000000000 : ℝ)|^4249 ≤ (5570656009227/12500000000000 : ℝ)^3225
        have hw : |(2707431479/5000000000 : ℝ)|=(2707431479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_s6_5 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305656377/10000000000 : ℝ)*x 0 + (-401322513/2000000000 : ℝ)*x 1 + (2707431549/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305656377/10000000000 : ℝ)^4249 ≤ (21692442727443/50000000000000 : ℝ)^3225 := by
    have hnat : (5305656377 : ℕ)^4249*50000000000000^3225 ≤ 21692442727443^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305656377 10000000000 21692442727443 50000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (401322513/2000000000 : ℝ)^4249 ≤ (3012466234977/25000000000000 : ℝ)^3225 := by
    have hnat : (401322513 : ℕ)^4249*25000000000000^3225 ≤ 3012466234977^3225*2000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      401322513 2000000000 3012466234977 25000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707431549/5000000000 : ℝ)^4249 ≤ (22282624795947/50000000000000 : ℝ)^3225 := by
    have hnat : (2707431549 : ℕ)^4249*50000000000000^3225 ≤ 22282624795947^3225*5000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707431549 5000000000 22282624795947 50000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305656377/10000000000 : ℝ), (-401322513/2000000000 : ℝ), (2707431549/5000000000 : ℝ)] ![(21692442727443/50000000000000 : ℝ), (3012466234977/25000000000000 : ℝ), (22282624795947/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305656377/10000000000 : ℝ)|^4249 ≤ (21692442727443/50000000000000 : ℝ)^3225
        have hw : |(5305656377/10000000000 : ℝ)|=(5305656377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-401322513/2000000000 : ℝ)|^4249 ≤ (3012466234977/25000000000000 : ℝ)^3225
        have hw : |(-401322513/2000000000 : ℝ)|=(401322513/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707431549/5000000000 : ℝ)|^4249 ≤ (22282624795947/50000000000000 : ℝ)^3225
        have hw : |(2707431549/5000000000 : ℝ)|=(2707431549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_s6_6 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652828181/5000000000 : ℝ)*x 0 + (5414863047/10000000000 : ℝ)*x 1 + (-125413291/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652828181/5000000000 : ℝ)^4249 ≤ (10846221323321/25000000000000 : ℝ)^3225 := by
    have hnat : (2652828181 : ℕ)^4249*25000000000000^3225 ≤ 10846221323321^3225*5000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652828181 5000000000 10846221323321 25000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414863047/10000000000 : ℝ)^4249 ≤ (278532806493/625000000000 : ℝ)^3225 := by
    have hnat : (5414863047 : ℕ)^4249*625000000000^3225 ≤ 278532806493^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414863047 10000000000 278532806493 625000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (125413291/625000000 : ℝ)^4249 ≤ (6024932829941/50000000000000 : ℝ)^3225 := by
    have hnat : (125413291 : ℕ)^4249*50000000000000^3225 ≤ 6024932829941^3225*625000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125413291 625000000 6024932829941 50000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652828181/5000000000 : ℝ), (5414863047/10000000000 : ℝ), (-125413291/625000000 : ℝ)] ![(10846221323321/25000000000000 : ℝ), (278532806493/625000000000 : ℝ), (6024932829941/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652828181/5000000000 : ℝ)|^4249 ≤ (10846221323321/25000000000000 : ℝ)^3225
        have hw : |(2652828181/5000000000 : ℝ)|=(2652828181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414863047/10000000000 : ℝ)|^4249 ≤ (278532806493/625000000000 : ℝ)^3225
        have hw : |(5414863047/10000000000 : ℝ)|=(5414863047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-125413291/625000000 : ℝ)|^4249 ≤ (6024932829941/50000000000000 : ℝ)^3225
        have hw : |(-125413291/625000000 : ℝ)|=(125413291/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_s6_7 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (542586549/1250000000 : ℝ)*x 0 + (904024263/2000000000 : ℝ)*x 1 + (20840729/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (542586549/1250000000 : ℝ)^4249 ≤ (33302510342207/100000000000000 : ℝ)^3225 := by
    have hnat : (542586549 : ℕ)^4249*100000000000000^3225 ≤ 33302510342207^3225*1250000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542586549 1250000000 33302510342207 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (904024263/2000000000 : ℝ)^4249 ≤ (17564005564383/50000000000000 : ℝ)^3225 := by
    have hnat : (904024263 : ℕ)^4249*50000000000000^3225 ≤ 17564005564383^3225*2000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      904024263 2000000000 17564005564383 50000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (20840729/50000000 : ℝ)^4249 ≤ (31569478510493/100000000000000 : ℝ)^3225 := by
    have hnat : (20840729 : ℕ)^4249*100000000000000^3225 ≤ 31569478510493^3225*50000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20840729 50000000 31569478510493 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(542586549/1250000000 : ℝ), (904024263/2000000000 : ℝ), (20840729/50000000 : ℝ)] ![(33302510342207/100000000000000 : ℝ), (17564005564383/50000000000000 : ℝ), (31569478510493/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(542586549/1250000000 : ℝ)|^4249 ≤ (33302510342207/100000000000000 : ℝ)^3225
        have hw : |(542586549/1250000000 : ℝ)|=(542586549/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(904024263/2000000000 : ℝ)|^4249 ≤ (17564005564383/50000000000000 : ℝ)^3225
        have hw : |(904024263/2000000000 : ℝ)|=(904024263/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(20840729/50000000 : ℝ)|^4249 ≤ (31569478510493/100000000000000 : ℝ)^3225
        have hw : |(20840729/50000000 : ℝ)|=(20840729/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1289_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76322037/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2937/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5503/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5509/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14673/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2937/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5503/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2937/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5503/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2937/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5503/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2937/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5503/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2937/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5503/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2937/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5503/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5503/50000 : ℝ) ^ (531/128 : ℝ) ≤ (10574501765797519/100000000000000000000 : ℝ) := by
    have hpowers : (5503/50000 : ℝ)^531 ≤ (10574501765797519/100000000000000000000 : ℝ)^128 := by
      have hnat : (5503 : ℕ)^531*100000000000000000000^128 ≤ 10574501765797519^128*50000^531 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5503 50000 10574501765797519 100000000000000000000 531 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5503/50000 : ℝ)) (X := (10574501765797519/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 531 128 (by norm_num) hpowers
    exact h
  have hpowhi : (2937/20000 : ℝ) ^ (531/128 : ℝ) ≤ (34980712855499671/100000000000000000000 : ℝ) := by
    have hpowers : (2937/20000 : ℝ)^531 ≤ (34980712855499671/100000000000000000000 : ℝ)^128 := by
      have hnat : (2937 : ℕ)^531*100000000000000000000^128 ≤ 34980712855499671^128*20000^531 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2937 20000 34980712855499671 100000000000000000000 531 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2937/20000 : ℝ)) (X := (34980712855499671/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 531 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010574501765797519/50000000000000000000 : ℝ) ≤ (5000254882789427/5000000000000000 : ℝ) ^ (531/128 : ℝ) := by
    have hpowers : (50010574501765797519/50000000000000000000 : ℝ)^128 ≤ (5000254882789427/5000000000000000 : ℝ)^531 := by
      have hnat : (50010574501765797519 : ℕ)^128*5000000000000000^531 ≤ 5000254882789427^531*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010574501765797519 50000000000000000000 5000254882789427 5000000000000000 128 531 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000254882789427/5000000000000000 : ℝ)) (X := (50010574501765797519/50000000000000000000 : ℝ)) (by norm_num) 531 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (10004555521462129719/10000000000000000000 : ℝ) ≤ (5000548969842409/5000000000000000 : ℝ) ^ (531/128 : ℝ) := by
    have hpowers : (10004555521462129719/10000000000000000000 : ℝ)^128 ≤ (5000548969842409/5000000000000000 : ℝ)^531 := by
      have hnat : (10004555521462129719 : ℕ)^128*5000000000000000^531 ≤ 5000548969842409^531*10000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004555521462129719 10000000000000000000 5000548969842409 5000000000000000 128 531 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000548969842409/5000000000000000 : ℝ)) (X := (10004555521462129719/10000000000000000000 : ℝ)) (by norm_num) 531 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034980712855499671/50000000000000000000 : ℝ) ≤ (5000843056895391/5000000000000000 : ℝ) ^ (531/128 : ℝ) := by
    have hpowers : (50034980712855499671/50000000000000000000 : ℝ)^128 ≤ (5000843056895391/5000000000000000 : ℝ)^531 := by
      have hnat : (50034980712855499671 : ℕ)^128*5000000000000000^531 ≤ 5000843056895391^531*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034980712855499671 50000000000000000000 5000843056895391 5000000000000000 128 531 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000843056895391/5000000000000000 : ℝ)) (X := (50034980712855499671/50000000000000000000 : ℝ)) (by norm_num) 531 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10574501765797519/100000000000000000000 : ℝ) ≤ ((18389464269572062149/18395000000000000000 : ℝ)+2*(147043526491/91975000000000 : ℝ)*(5503/50000 : ℝ))^(531/128 : ℝ) := by
    rw [show (18389464269572062149/18395000000000000000 : ℝ)+2*(147043526491/91975000000000 : ℝ)*(5503/50000 : ℝ)=(5000254882789427/5000000000000000 : ℝ) by norm_num, show 1+2*(10574501765797519/100000000000000000000 : ℝ)=(50010574501765797519/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34980712855499671/100000000000000000000 : ℝ)+(10574501765797519/100000000000000000000 : ℝ) ≤ ((18389464269572062149/18395000000000000000 : ℝ)+(147043526491/91975000000000 : ℝ)*((2937/20000 : ℝ)+(5503/50000 : ℝ)))^(531/128 : ℝ) := by
    rw [show (18389464269572062149/18395000000000000000 : ℝ)+(147043526491/91975000000000 : ℝ)*((2937/20000 : ℝ)+(5503/50000 : ℝ))=(5000548969842409/5000000000000000 : ℝ) by norm_num, show 1+(34980712855499671/100000000000000000000 : ℝ)+(10574501765797519/100000000000000000000 : ℝ)=(10004555521462129719/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34980712855499671/100000000000000000000 : ℝ) ≤ ((18389464269572062149/18395000000000000000 : ℝ)+2*(147043526491/91975000000000 : ℝ)*(2937/20000 : ℝ))^(531/128 : ℝ) := by
    rw [show (18389464269572062149/18395000000000000000 : ℝ)+2*(147043526491/91975000000000 : ℝ)*(2937/20000 : ℝ)=(5000843056895391/5000000000000000 : ℝ) by norm_num, show 1+2*(34980712855499671/100000000000000000000 : ℝ)=(50034980712855499671/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18389464269572062149/18395000000000000000 : ℝ)*(X 1 0+X 2 0)+(147043526491/91975000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (531/128 : ℝ)) (lo := (5503/50000 : ℝ)) (hi := (2937/20000 : ℝ)) (c := (18389464269572062149/18395000000000000000 : ℝ)) (alpha := (147043526491/91975000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18389464269572062149/18395000000000000000 : ℝ)*(X 0 1+X 2 1)+(147043526491/91975000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (531/128 : ℝ)) (lo := (5503/50000 : ℝ)) (hi := (2937/20000 : ℝ)) (c := (18389464269572062149/18395000000000000000 : ℝ)) (alpha := (147043526491/91975000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18389464269572062149/18395000000000000000 : ℝ)*(X 0 2+X 1 2)+(147043526491/91975000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (531/128 : ℝ)) (lo := (5503/50000 : ℝ)) (hi := (2937/20000 : ℝ)) (c := (18389464269572062149/18395000000000000000 : ℝ)) (alpha := (147043526491/91975000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-418130189/2000000000 : ℝ)*X 0 0+(5415482129/10000000000 : ℝ)*X 0 1+(163837261/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349852583/10000000000 : ℝ)*X 1 0+(-2178683357/10000000000 : ℝ)*X 1 1+(5242792361/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((213994103/400000000 : ℝ)*X 2 0+(2621396179/5000000000 : ℝ)*X 2 1+(-2178683371/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((868133211/2000000000 : ℝ)*X 0 0+(4166874521/10000000000 : ℝ)*X 0 1+(4521386173/10000000000 : ℝ)*X 0 2+(868133211/2000000000 : ℝ)*X 1 0+(4166874521/10000000000 : ℝ)*X 1 1+(4521386173/10000000000 : ℝ)*X 1 2+(868133211/2000000000 : ℝ)*X 2 0+(4166874521/10000000000 : ℝ)*X 2 1+(4521386173/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-6533323/31250000 : ℝ)*X 0 0+(5243408633/10000000000 : ℝ)*X 0 1+(2707431479/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305656377/10000000000 : ℝ)*X 1 0+(-401322513/2000000000 : ℝ)*X 1 1+(2707431549/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652828181/5000000000 : ℝ)*X 2 0+(5414863047/10000000000 : ℝ)*X 2 1+(-125413291/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((542586549/1250000000 : ℝ)*X 0 0+(904024263/2000000000 : ℝ)*X 0 1+(20840729/50000000 : ℝ)*X 0 2+(542586549/1250000000 : ℝ)*X 1 0+(904024263/2000000000 : ℝ)*X 1 1+(20840729/50000000 : ℝ)*X 1 2+(542586549/1250000000 : ℝ)*X 2 0+(904024263/2000000000 : ℝ)*X 2 1+(20840729/50000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (85465559937105911017953/18395000000000000000000000000 : ℝ) := by norm_num
    linear_combination (898528283/100000000000000 : ℝ)*(base19) + (826350701/100000000000000 : ℝ)*(base23) + (33981329/100000000000000 : ℝ)*(lower2) + (32605261/25000000000000 : ℝ)*(upper3) + (64587483/100000000000000 : ℝ)*(upper5) + (2152891849608337/50000000000000 : ℝ)*(major0) + (2152891849608337/50000000000000 : ℝ)*(major1) + (2152891849608337/50000000000000 : ℝ)*(major2) + (579074990158089/10000000000000 : ℝ)*(sp0) + (5790766567889307/100000000000000 : ℝ)*(sp1) + (5790766640066889/100000000000000 : ℝ)*(sp2) + (2820790139362339/100000000000000 : ℝ)*(sp3) + (17564836699/100000000000000 : ℝ)*(sp4) + (602361401/6250000000000 : ℝ)*(sp7) + (564159955428951/20000000000000 : ℝ)*(f.failure) + (5790767466417589/100000000000000 : ℝ)*(f.sum) + (52097110692929/18395000000000000000000000000 : ℝ)*base66 + (2530244452779936213/919750000000000000000000000000000 : ℝ)*base67 + (7998815730221813787/919750000000000000000000000000000 : ℝ)*base70 + (5360578460069563787/919750000000000000000000000000000 : ℝ)*base72 + (4402657707509/4598750000000000000000000000 : ℝ)*base73 + (2028542590904436213/919750000000000000000000000000000 : ℝ)*base75 + (5707194703751063787/919750000000000000000000000000000 : ℝ)*base78 + (3594122050826186213/919750000000000000000000000000000 : ℝ)*base79 + (14374455042081/4598750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (9093187/1000000000000000000000 : ℝ)*base89 + (9093187/1000000000000000000000 : ℝ)*base91 + (9093187/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1074750603462489349720934439/91975000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (359253391/25000000000000 : ℝ)*(base19) + (211162199/10000000000000 : ℝ)*(base23) + (7229283/5000000000000 : ℝ)*(upper3) + (162336721/50000000000000 : ℝ)*(lower4) + (71763419/50000000000000 : ℝ)*(upper5) + (433677756340263/10000000000000 : ℝ)*(major0) + (433677756340263/10000000000000 : ℝ)*(major1) + (433677756340263/10000000000000 : ℝ)*(major2) + (34634537401/100000000000000 : ℝ)*(sp1) + (44137445561/100000000000000 : ℝ)*(sp2) + (5832450297564471/100000000000000 : ℝ)*(sp4) + (1166482845202701/20000000000000 : ℝ)*(sp5) + (145810101212423/2500000000000 : ℝ)*(sp6) + (44392256870821/1562500000000 : ℝ)*(sp7) + (44392256870821/1562500000000 : ℝ)*(f.failure) + (5832450297564471/100000000000000 : ℝ)*(f.sum) + (2198548764011/459875000000000000000000000 : ℝ)*base66 + (593644445776755187/183950000000000000000000000000000 : ℝ)*base67 + (740880965237494813/183950000000000000000000000000000 : ℝ)*base70 + (1576327435780405187/183950000000000000000000000000000 : ℝ)*base71 + (15398050072049/1839500000000000000000000000 : ℝ)*base74 + (2759509649042155187/183950000000000000000000000000000 : ℝ)*base75 + (1441630701854755187/183950000000000000000000000000000 : ℝ)*base77 + (1381548099266494813/183950000000000000000000000000000 : ℝ)*base80 + (7586318053707/3679000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (105123/78125000000000000000 : ℝ)*base90 + (105123/78125000000000000000 : ℝ)*base92 + (105123/78125000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1289_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76322037/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2937/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5503/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5509/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14673/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1289_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1289_s7_0 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1045330697/5000000000 : ℝ)*x 0 + (1353843541/2500000000 : ℝ)*x 1 + (5242893629/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1045330697/5000000000 : ℝ)^4249 ≤ (12719223581219/100000000000000 : ℝ)^3225 := by
    have hnat : (1045330697 : ℕ)^4249*100000000000000^3225 ≤ 12719223581219^3225*5000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045330697 5000000000 12719223581219 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353843541/2500000000 : ℝ)^4249 ≤ (22285395686521/50000000000000 : ℝ)^3225 := by
    have hnat : (1353843541 : ℕ)^4249*50000000000000^3225 ≤ 22285395686521^3225*2500000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353843541 2500000000 22285395686521 50000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242893629/10000000000 : ℝ)^4249 ≤ (21354992514319/50000000000000 : ℝ)^3225 := by
    have hnat : (5242893629 : ℕ)^4249*50000000000000^3225 ≤ 21354992514319^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242893629 10000000000 21354992514319 50000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1045330697/5000000000 : ℝ), (1353843541/2500000000 : ℝ), (5242893629/10000000000 : ℝ)] ![(12719223581219/100000000000000 : ℝ), (22285395686521/50000000000000 : ℝ), (21354992514319/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1045330697/5000000000 : ℝ)|^4249 ≤ (12719223581219/100000000000000 : ℝ)^3225
        have hw : |(-1045330697/5000000000 : ℝ)|=(1045330697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353843541/2500000000 : ℝ)|^4249 ≤ (22285395686521/50000000000000 : ℝ)^3225
        have hw : |(1353843541/2500000000 : ℝ)|=(1353843541/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242893629/10000000000 : ℝ)|^4249 ≤ (21354992514319/50000000000000 : ℝ)^3225
        have hw : |(5242893629/10000000000 : ℝ)|=(5242893629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_s7_1 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349825379/10000000000 : ℝ)*x 0 + (-2178584903/10000000000 : ℝ)*x 1 + (5242894237/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349825379/10000000000 : ℝ)^4249 ≤ (685333865847/1562500000000 : ℝ)^3225 := by
    have hnat : (5349825379 : ℕ)^4249*1562500000000^3225 ≤ 685333865847^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349825379 10000000000 685333865847 1562500000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2178584903/10000000000 : ℝ)^4249 ≤ (13428641018377/100000000000000 : ℝ)^3225 := by
    have hnat : (2178584903 : ℕ)^4249*100000000000000^3225 ≤ 13428641018377^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178584903 10000000000 13428641018377 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242894237/10000000000 : ℝ)^4249 ≤ (5338748944277/12500000000000 : ℝ)^3225 := by
    have hnat : (5242894237 : ℕ)^4249*12500000000000^3225 ≤ 5338748944277^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242894237 10000000000 5338748944277 12500000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349825379/10000000000 : ℝ), (-2178584903/10000000000 : ℝ), (5242894237/10000000000 : ℝ)] ![(685333865847/1562500000000 : ℝ), (13428641018377/100000000000000 : ℝ), (5338748944277/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349825379/10000000000 : ℝ)|^4249 ≤ (685333865847/1562500000000 : ℝ)^3225
        have hw : |(5349825379/10000000000 : ℝ)|=(5349825379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2178584903/10000000000 : ℝ)|^4249 ≤ (13428641018377/100000000000000 : ℝ)^3225
        have hw : |(-2178584903/10000000000 : ℝ)|=(2178584903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242894237/10000000000 : ℝ)|^4249 ≤ (5338748944277/12500000000000 : ℝ)^3225
        have hw : |(5242894237/10000000000 : ℝ)|=(5242894237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_s7_2 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337456397/2500000000 : ℝ)*x 0 + (5242892477/10000000000 : ℝ)*x 1 + (-272323369/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337456397/2500000000 : ℝ)^4249 ≤ (21930684835901/50000000000000 : ℝ)^3225 := by
    have hnat : (1337456397 : ℕ)^4249*50000000000000^3225 ≤ 21930684835901^3225*2500000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337456397 2500000000 21930684835901 50000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242892477/10000000000 : ℝ)^4249 ≤ (21354986332193/50000000000000 : ℝ)^3225 := by
    have hnat : (5242892477 : ℕ)^4249*50000000000000^3225 ≤ 21354986332193^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242892477 10000000000 21354986332193 50000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (272323369/1250000000 : ℝ)^4249 ≤ (6714328829251/50000000000000 : ℝ)^3225 := by
    have hnat : (272323369 : ℕ)^4249*50000000000000^3225 ≤ 6714328829251^3225*1250000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272323369 1250000000 6714328829251 50000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337456397/2500000000 : ℝ), (5242892477/10000000000 : ℝ), (-272323369/1250000000 : ℝ)] ![(21930684835901/50000000000000 : ℝ), (21354986332193/50000000000000 : ℝ), (6714328829251/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337456397/2500000000 : ℝ)|^4249 ≤ (21930684835901/50000000000000 : ℝ)^3225
        have hw : |(1337456397/2500000000 : ℝ)|=(1337456397/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242892477/10000000000 : ℝ)|^4249 ≤ (21354986332193/50000000000000 : ℝ)^3225
        have hw : |(5242892477/10000000000 : ℝ)|=(5242892477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-272323369/1250000000 : ℝ)|^4249 ≤ (6714328829251/50000000000000 : ℝ)^3225
        have hw : |(-272323369/1250000000 : ℝ)|=(272323369/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_s7_3 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (868134343/2000000000 : ℝ)*x 0 + (1041772321/2500000000 : ℝ)*x 1 + (1130292829/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (868134343/2000000000 : ℝ)^4249 ≤ (16651150667281/50000000000000 : ℝ)^3225 := by
    have hnat : (868134343 : ℕ)^4249*50000000000000^3225 ≤ 16651150667281^3225*2000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      868134343 2000000000 16651150667281 50000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1041772321/2500000000 : ℝ)^4249 ≤ (31558936095241/100000000000000 : ℝ)^3225 := by
    have hnat : (1041772321 : ℕ)^4249*100000000000000^3225 ≤ 31558936095241^3225*2500000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041772321 2500000000 31558936095241 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1130292829/2500000000 : ℝ)^4249 ≤ (4392345319781/12500000000000 : ℝ)^3225 := by
    have hnat : (1130292829 : ℕ)^4249*12500000000000^3225 ≤ 4392345319781^3225*2500000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1130292829 2500000000 4392345319781 12500000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(868134343/2000000000 : ℝ), (1041772321/2500000000 : ℝ), (1130292829/2500000000 : ℝ)] ![(16651150667281/50000000000000 : ℝ), (31558936095241/100000000000000 : ℝ), (4392345319781/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(868134343/2000000000 : ℝ)|^4249 ≤ (16651150667281/50000000000000 : ℝ)^3225
        have hw : |(868134343/2000000000 : ℝ)|=(868134343/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1041772321/2500000000 : ℝ)|^4249 ≤ (31558936095241/100000000000000 : ℝ)^3225
        have hw : |(1041772321/2500000000 : ℝ)|=(1041772321/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1130292829/2500000000 : ℝ)|^4249 ≤ (4392345319781/12500000000000 : ℝ)^3225
        have hw : |(1130292829/2500000000 : ℝ)|=(1130292829/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_s7_4 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-522668573/2500000000 : ℝ)*x 0 + (2621753963/5000000000 : ℝ)*x 1 + (338422287/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (522668573/2500000000 : ℝ)^4249 ≤ (1589915870753/12500000000000 : ℝ)^3225 := by
    have hnat : (522668573 : ℕ)^4249*12500000000000^3225 ≤ 1589915870753^3225*2500000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522668573 2500000000 1589915870753 12500000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621753963/5000000000 : ℝ)^4249 ≤ (42716578313767/100000000000000 : ℝ)^3225 := by
    have hnat : (2621753963 : ℕ)^4249*100000000000000^3225 ≤ 42716578313767^3225*5000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621753963 5000000000 42716578313767 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (338422287/625000000 : ℝ)^4249 ≤ (44564094707287/100000000000000 : ℝ)^3225 := by
    have hnat : (338422287 : ℕ)^4249*100000000000000^3225 ≤ 44564094707287^3225*625000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338422287 625000000 44564094707287 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-522668573/2500000000 : ℝ), (2621753963/5000000000 : ℝ), (338422287/625000000 : ℝ)] ![(1589915870753/12500000000000 : ℝ), (42716578313767/100000000000000 : ℝ), (44564094707287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-522668573/2500000000 : ℝ)|^4249 ≤ (1589915870753/12500000000000 : ℝ)^3225
        have hw : |(-522668573/2500000000 : ℝ)|=(522668573/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621753963/5000000000 : ℝ)|^4249 ≤ (42716578313767/100000000000000 : ℝ)^3225
        have hw : |(2621753963/5000000000 : ℝ)|=(2621753963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(338422287/625000000 : ℝ)|^4249 ≤ (44564094707287/100000000000000 : ℝ)^3225
        have hw : |(338422287/625000000 : ℝ)|=(338422287/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_s7_5 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652841509/5000000000 : ℝ)*x 0 + (-2006722257/10000000000 : ℝ)*x 1 + (338422287/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652841509/5000000000 : ℝ)^4249 ≤ (43385172471619/100000000000000 : ℝ)^3225 := by
    have hnat : (2652841509 : ℕ)^4249*100000000000000^3225 ≤ 43385172471619^3225*5000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652841509 5000000000 43385172471619 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2006722257/10000000000 : ℝ)^4249 ≤ (3012683202333/25000000000000 : ℝ)^3225 := by
    have hnat : (2006722257 : ℕ)^4249*25000000000000^3225 ≤ 3012683202333^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2006722257 10000000000 3012683202333 25000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (338422287/625000000 : ℝ)^4249 ≤ (44564094707287/100000000000000 : ℝ)^3225 := by
    have hnat : (338422287 : ℕ)^4249*100000000000000^3225 ≤ 44564094707287^3225*625000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338422287 625000000 44564094707287 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652841509/5000000000 : ℝ), (-2006722257/10000000000 : ℝ), (338422287/625000000 : ℝ)] ![(43385172471619/100000000000000 : ℝ), (3012683202333/25000000000000 : ℝ), (44564094707287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652841509/5000000000 : ℝ)|^4249 ≤ (43385172471619/100000000000000 : ℝ)^3225
        have hw : |(2652841509/5000000000 : ℝ)|=(2652841509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2006722257/10000000000 : ℝ)|^4249 ≤ (3012683202333/25000000000000 : ℝ)^3225
        have hw : |(-2006722257/10000000000 : ℝ)|=(2006722257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(338422287/625000000 : ℝ)|^4249 ≤ (44564094707287/100000000000000 : ℝ)^3225
        have hw : |(338422287/625000000 : ℝ)|=(338422287/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_s7_6 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652841509/5000000000 : ℝ)*x 0 + (338422287/625000000 : ℝ)*x 1 + (-2006722257/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652841509/5000000000 : ℝ)^4249 ≤ (43385172471619/100000000000000 : ℝ)^3225 := by
    have hnat : (2652841509 : ℕ)^4249*100000000000000^3225 ≤ 43385172471619^3225*5000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652841509 5000000000 43385172471619 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (338422287/625000000 : ℝ)^4249 ≤ (44564094707287/100000000000000 : ℝ)^3225 := by
    have hnat : (338422287 : ℕ)^4249*100000000000000^3225 ≤ 44564094707287^3225*625000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338422287 625000000 44564094707287 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2006722257/10000000000 : ℝ)^4249 ≤ (3012683202333/25000000000000 : ℝ)^3225 := by
    have hnat : (2006722257 : ℕ)^4249*25000000000000^3225 ≤ 3012683202333^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2006722257 10000000000 3012683202333 25000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652841509/5000000000 : ℝ), (338422287/625000000 : ℝ), (-2006722257/10000000000 : ℝ)] ![(43385172471619/100000000000000 : ℝ), (44564094707287/100000000000000 : ℝ), (3012683202333/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652841509/5000000000 : ℝ)|^4249 ≤ (43385172471619/100000000000000 : ℝ)^3225
        have hw : |(2652841509/5000000000 : ℝ)|=(2652841509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(338422287/625000000 : ℝ)|^4249 ≤ (44564094707287/100000000000000 : ℝ)^3225
        have hw : |(338422287/625000000 : ℝ)|=(338422287/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2006722257/10000000000 : ℝ)|^4249 ≤ (3012683202333/25000000000000 : ℝ)^3225
        have hw : |(-2006722257/10000000000 : ℝ)|=(2006722257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_s7_7 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1085174907/2500000000 : ℝ)*x 0 + (4519909263/10000000000 : ℝ)*x 1 + (260522253/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1085174907/2500000000 : ℝ)^4249 ≤ (6660516697071/20000000000000 : ℝ)^3225 := by
    have hnat : (1085174907 : ℕ)^4249*20000000000000^3225 ≤ 6660516697071^3225*2500000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085174907 2500000000 6660516697071 20000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4519909263/10000000000 : ℝ)^4249 ≤ (35125839929811/100000000000000 : ℝ)^3225 := by
    have hnat : (4519909263 : ℕ)^4249*100000000000000^3225 ≤ 35125839929811^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4519909263 10000000000 35125839929811 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (260522253/625000000 : ℝ)^4249 ≤ (15785788282747/50000000000000 : ℝ)^3225 := by
    have hnat : (260522253 : ℕ)^4249*50000000000000^3225 ≤ 15785788282747^3225*625000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260522253 625000000 15785788282747 50000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1085174907/2500000000 : ℝ), (4519909263/10000000000 : ℝ), (260522253/625000000 : ℝ)] ![(6660516697071/20000000000000 : ℝ), (35125839929811/100000000000000 : ℝ), (15785788282747/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1085174907/2500000000 : ℝ)|^4249 ≤ (6660516697071/20000000000000 : ℝ)^3225
        have hw : |(1085174907/2500000000 : ℝ)|=(1085174907/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4519909263/10000000000 : ℝ)|^4249 ≤ (35125839929811/100000000000000 : ℝ)^3225
        have hw : |(4519909263/10000000000 : ℝ)|=(4519909263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(260522253/625000000 : ℝ)|^4249 ≤ (15785788282747/50000000000000 : ℝ)^3225
        have hw : |(260522253/625000000 : ℝ)|=(260522253/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1289_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76322037/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14673/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5509/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (551/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1467/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14673/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5509/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14673/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5509/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14673/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5509/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14673/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5509/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14673/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5509/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14673/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5509/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
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
  have hpowlo : (5509/50000 : ℝ) ^ (531/128 : ℝ) ≤ (10622413464112017/100000000000000000000 : ℝ) := by
    have hpowers : (5509/50000 : ℝ)^531 ≤ (10622413464112017/100000000000000000000 : ℝ)^128 := by
      have hnat : (5509 : ℕ)^531*100000000000000000000^128 ≤ 10622413464112017^128*50000^531 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5509 50000 10622413464112017 100000000000000000000 531 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5509/50000 : ℝ)) (X := (10622413464112017/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 531 128 (by norm_num) hpowers
    exact h
  have hpowhi : (14673/100000 : ℝ) ^ (531/128 : ℝ) ≤ (34862282836744149/100000000000000000000 : ℝ) := by
    have hpowers : (14673/100000 : ℝ)^531 ≤ (34862282836744149/100000000000000000000 : ℝ)^128 := by
      have hnat : (14673 : ℕ)^531*100000000000000000000^128 ≤ 34862282836744149^128*100000^531 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14673 100000 34862282836744149 100000000000000000000 531 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14673/100000 : ℝ)) (X := (34862282836744149/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 531 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010622413464112017/50000000000000000000 : ℝ) ≤ (2500128018768629/2500000000000000 : ℝ) ^ (531/128 : ℝ) := by
    have hpowers : (50010622413464112017/50000000000000000000 : ℝ)^128 ≤ (2500128018768629/2500000000000000 : ℝ)^531 := by
      have hnat : (50010622413464112017 : ℕ)^128*2500000000000000^531 ≤ 2500128018768629^531*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010622413464112017 50000000000000000000 2500128018768629 2500000000000000 128 531 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500128018768629/2500000000000000 : ℝ)) (X := (50010622413464112017/50000000000000000000 : ℝ)) (by norm_num) 531 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022742348150428083/50000000000000000000 : ℝ) ≤ (10001096240395191/10000000000000000 : ℝ) ^ (531/128 : ℝ) := by
    have hpowers : (50022742348150428083/50000000000000000000 : ℝ)^128 ≤ (10001096240395191/10000000000000000 : ℝ)^531 := by
      have hnat : (50022742348150428083 : ℕ)^128*10000000000000000^531 ≤ 10001096240395191^531*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022742348150428083 50000000000000000000 10001096240395191 10000000000000000 128 531 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001096240395191/10000000000000000 : ℝ)) (X := (50022742348150428083/50000000000000000000 : ℝ)) (by norm_num) 531 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034862282836744149/50000000000000000000 : ℝ) ≤ (5000840202857933/5000000000000000 : ℝ) ^ (531/128 : ℝ) := by
    have hpowers : (50034862282836744149/50000000000000000000 : ℝ)^128 ≤ (5000840202857933/5000000000000000 : ℝ)^531 := by
      have hnat : (50034862282836744149 : ℕ)^128*5000000000000000^531 ≤ 5000840202857933^531*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034862282836744149 50000000000000000000 5000840202857933 5000000000000000 128 531 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000840202857933/5000000000000000 : ℝ)) (X := (50034862282836744149/50000000000000000000 : ℝ)) (by norm_num) 531 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10622413464112017/100000000000000000000 : ℝ) ≤ ((456737487092387021/456875000000000000 : ℝ)+2*(23366612827/14620000000000 : ℝ)*(5509/50000 : ℝ))^(531/128 : ℝ) := by
    rw [show (456737487092387021/456875000000000000 : ℝ)+2*(23366612827/14620000000000 : ℝ)*(5509/50000 : ℝ)=(2500128018768629/2500000000000000 : ℝ) by norm_num, show 1+2*(10622413464112017/100000000000000000000 : ℝ)=(50010622413464112017/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34862282836744149/100000000000000000000 : ℝ)+(10622413464112017/100000000000000000000 : ℝ) ≤ ((456737487092387021/456875000000000000 : ℝ)+(23366612827/14620000000000 : ℝ)*((14673/100000 : ℝ)+(5509/50000 : ℝ)))^(531/128 : ℝ) := by
    rw [show (456737487092387021/456875000000000000 : ℝ)+(23366612827/14620000000000 : ℝ)*((14673/100000 : ℝ)+(5509/50000 : ℝ))=(10001096240395191/10000000000000000 : ℝ) by norm_num, show 1+(34862282836744149/100000000000000000000 : ℝ)+(10622413464112017/100000000000000000000 : ℝ)=(50022742348150428083/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34862282836744149/100000000000000000000 : ℝ) ≤ ((456737487092387021/456875000000000000 : ℝ)+2*(23366612827/14620000000000 : ℝ)*(14673/100000 : ℝ))^(531/128 : ℝ) := by
    rw [show (456737487092387021/456875000000000000 : ℝ)+2*(23366612827/14620000000000 : ℝ)*(14673/100000 : ℝ)=(5000840202857933/5000000000000000 : ℝ) by norm_num, show 1+2*(34862282836744149/100000000000000000000 : ℝ)=(50034862282836744149/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (456737487092387021/456875000000000000 : ℝ)*(X 1 0+X 2 0)+(23366612827/14620000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (531/128 : ℝ)) (lo := (5509/50000 : ℝ)) (hi := (14673/100000 : ℝ)) (c := (456737487092387021/456875000000000000 : ℝ)) (alpha := (23366612827/14620000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (456737487092387021/456875000000000000 : ℝ)*(X 0 1+X 2 1)+(23366612827/14620000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (531/128 : ℝ)) (lo := (5509/50000 : ℝ)) (hi := (14673/100000 : ℝ)) (c := (456737487092387021/456875000000000000 : ℝ)) (alpha := (23366612827/14620000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (456737487092387021/456875000000000000 : ℝ)*(X 0 2+X 1 2)+(23366612827/14620000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (531/128 : ℝ)) (lo := (5509/50000 : ℝ)) (hi := (14673/100000 : ℝ)) (c := (456737487092387021/456875000000000000 : ℝ)) (alpha := (23366612827/14620000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1045330697/5000000000 : ℝ)*X 0 0+(1353843541/2500000000 : ℝ)*X 0 1+(5242893629/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349825379/10000000000 : ℝ)*X 1 0+(-2178584903/10000000000 : ℝ)*X 1 1+(5242894237/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337456397/2500000000 : ℝ)*X 2 0+(5242892477/10000000000 : ℝ)*X 2 1+(-272323369/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((868134343/2000000000 : ℝ)*X 0 0+(1041772321/2500000000 : ℝ)*X 0 1+(1130292829/2500000000 : ℝ)*X 0 2+(868134343/2000000000 : ℝ)*X 1 0+(1041772321/2500000000 : ℝ)*X 1 1+(1130292829/2500000000 : ℝ)*X 1 2+(868134343/2000000000 : ℝ)*X 2 0+(1041772321/2500000000 : ℝ)*X 2 1+(1130292829/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-522668573/2500000000 : ℝ)*X 0 0+(2621753963/5000000000 : ℝ)*X 0 1+(338422287/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652841509/5000000000 : ℝ)*X 1 0+(-2006722257/10000000000 : ℝ)*X 1 1+(338422287/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652841509/5000000000 : ℝ)*X 2 0+(338422287/625000000 : ℝ)*X 2 1+(-2006722257/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1085174907/2500000000 : ℝ)*X 0 0+(4519909263/10000000000 : ℝ)*X 0 1+(260522253/625000000 : ℝ)*X 0 2+(1085174907/2500000000 : ℝ)*X 1 0+(4519909263/10000000000 : ℝ)*X 1 1+(260522253/625000000 : ℝ)*X 1 2+(1085174907/2500000000 : ℝ)*X 2 0+(4519909263/10000000000 : ℝ)*X 2 1+(260522253/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3228645994165582653313623/335937500000000000000000000000 : ℝ) := by norm_num
    linear_combination (27000671/10000000000000 : ℝ)*(base15) + (298635581/100000000000000 : ℝ)*(upper2) + (3909999/10000000000000 : ℝ)*(upper4) + (198818013/100000000000000 : ℝ)*(lower5) + (269438229356339/6250000000000 : ℝ)*(major0) + (269438229356339/6250000000000 : ℝ)*(major1) + (269438229356339/6250000000000 : ℝ)*(major2) + (5797786026241939/100000000000000 : ℝ)*(sp0) + (1449449507556941/25000000000000 : ℝ)*(sp1) + (724717562311641/12500000000000 : ℝ)*(sp2) + (282421524989583/10000000000000 : ℝ)*(sp3) + (2454798507/20000000000000 : ℝ)*(sp4) + (28900870673/50000000000000 : ℝ)*(sp6) + (9468910761/100000000000000 : ℝ)*(sp7) + (282422471880659/10000000000000 : ℝ)*(f.failure) + (2898899150117237/50000000000000 : ℝ)*(f.sum) + (1532957036979/182750000000000000000000000 : ℝ)*base65 + (60870345492970101/11421875000000000000000000000000 : ℝ)*base67 + (214730644233751351/11421875000000000000000000000000 : ℝ)*base69 + (2283068391055363/5710937500000000000000000000000 : ℝ)*base71 + (2824227271153/731000000000000000000000000 : ℝ)*base74 + (347188681070843/356933593750000000000000000000 : ℝ)*base75 + (54140671342492863/5710937500000000000000000000000 : ℝ)*base77 + (66025557581376351/11421875000000000000000000000000 : ℝ)*base79 + (1522174113641/365500000000000000000000000 : ℝ)*base82 + (4217617/500000000000000000000 : ℝ)*base90 + (4217617/500000000000000000000 : ℝ)*base92 + (4217617/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (41489432431164229254104031/11421875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (644829681/100000000000000 : ℝ)*(base19) + (43864159/6250000000000 : ℝ)*(base23) + (110912841/50000000000000 : ℝ)*(lower1) + (73844421/100000000000000 : ℝ)*(upper3) + (12926463/50000000000000 : ℝ)*(lower4) + (74496937/100000000000000 : ℝ)*(upper5) + (1085495163102531/25000000000000 : ℝ)*(major0) + (1085495163102531/25000000000000 : ℝ)*(major1) + (1085495163102531/25000000000000 : ℝ)*(major2) + (497003579/50000000000000 : ℝ)*(sp2) + (1459862025666793/25000000000000 : ℝ)*(sp4) + (5839447457837491/100000000000000 : ℝ)*(sp5) + (583944640683347/10000000000000 : ℝ)*(sp6) + (35556413513391/1250000000000 : ℝ)*(sp7) + (35556413513391/1250000000000 : ℝ)*(f.failure) + (1459862025666793/25000000000000 : ℝ)*(f.sum) + (62164234813/182750000000000000000000000 : ℝ)*base65 + (152153356315193599/11421875000000000000000000000000 : ℝ)*base68 + (107593475023681401/11421875000000000000000000000000 : ℝ)*base69 + (22104025420025151/11421875000000000000000000000000 : ℝ)*base71 + (1463699993919/146200000000000000000000000 : ℝ)*base74 + (53317818287068599/11421875000000000000000000000000 : ℝ)*base76 + (5926895166006099/11421875000000000000000000000000 : ℝ)*base78 + (17022059333224849/11421875000000000000000000000000 : ℝ)*base80 + (879851938753/365500000000000000000000000 : ℝ)*base82 + (397467/62500000000000000000 : ℝ)*base89 + (397467/62500000000000000000 : ℝ)*base91 + (397467/62500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1289_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76322037/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14673/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5509/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (551/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1467/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1289_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1289_box_0 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-383812813/2000000000 : ℝ)*x 0 + (2696068111/5000000000 : ℝ)*x 1 + (1348034083/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (383812813/2000000000 : ℝ)^4249 ≤ (5681022269439/50000000000000 : ℝ)^3225 := by
    have hnat : (383812813 : ℕ)^4249*50000000000000^3225 ≤ 5681022269439^3225*2000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      383812813 2000000000 5681022269439 50000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696068111/5000000000 : ℝ)^4249 ≤ (44318977126687/100000000000000 : ℝ)^3225 := by
    have hnat : (2696068111 : ℕ)^4249*100000000000000^3225 ≤ 44318977126687^3225*5000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696068111 5000000000 44318977126687 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348034083/2500000000 : ℝ)^4249 ≤ (4431897831787/10000000000000 : ℝ)^3225 := by
    have hnat : (1348034083 : ℕ)^4249*10000000000000^3225 ≤ 4431897831787^3225*2500000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348034083 2500000000 4431897831787 10000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-383812813/2000000000 : ℝ), (2696068111/5000000000 : ℝ), (1348034083/2500000000 : ℝ)] ![(5681022269439/50000000000000 : ℝ), (44318977126687/100000000000000 : ℝ), (4431897831787/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-383812813/2000000000 : ℝ)|^4249 ≤ (5681022269439/50000000000000 : ℝ)^3225
        have hw : |(-383812813/2000000000 : ℝ)|=(383812813/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696068111/5000000000 : ℝ)|^4249 ≤ (44318977126687/100000000000000 : ℝ)^3225
        have hw : |(2696068111/5000000000 : ℝ)|=(2696068111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348034083/2500000000 : ℝ)|^4249 ≤ (4431897831787/10000000000000 : ℝ)^3225
        have hw : |(1348034083/2500000000 : ℝ)|=(1348034083/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_box_1 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5284313109/10000000000 : ℝ)*x 0 + (-2066501869/10000000000 : ℝ)*x 1 + (1348034153/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5284313109/10000000000 : ℝ)^4249 ≤ (43155090991313/100000000000000 : ℝ)^3225 := by
    have hnat : (5284313109 : ℕ)^4249*100000000000000^3225 ≤ 43155090991313^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5284313109 10000000000 43155090991313 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2066501869/10000000000 : ℝ)^4249 ≤ (12525927654791/100000000000000 : ℝ)^3225 := by
    have hnat : (2066501869 : ℕ)^4249*100000000000000^3225 ≤ 12525927654791^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2066501869 10000000000 12525927654791 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348034153/2500000000 : ℝ)^4249 ≤ (44318981349973/100000000000000 : ℝ)^3225 := by
    have hnat : (1348034153 : ℕ)^4249*100000000000000^3225 ≤ 44318981349973^3225*2500000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348034153 2500000000 44318981349973 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5284313109/10000000000 : ℝ), (-2066501869/10000000000 : ℝ), (1348034153/2500000000 : ℝ)] ![(43155090991313/100000000000000 : ℝ), (12525927654791/100000000000000 : ℝ), (44318981349973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5284313109/10000000000 : ℝ)|^4249 ≤ (43155090991313/100000000000000 : ℝ)^3225
        have hw : |(5284313109/10000000000 : ℝ)|=(5284313109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2066501869/10000000000 : ℝ)|^4249 ≤ (12525927654791/100000000000000 : ℝ)^3225
        have hw : |(-2066501869/10000000000 : ℝ)|=(2066501869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348034153/2500000000 : ℝ)|^4249 ≤ (44318981349973/100000000000000 : ℝ)^3225
        have hw : |(1348034153/2500000000 : ℝ)|=(1348034153/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_box_2 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2642156797/5000000000 : ℝ)*x 0 + (539213607/1000000000 : ℝ)*x 1 + (-2066501949/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642156797/5000000000 : ℝ)^4249 ≤ (43155096209771/100000000000000 : ℝ)^3225 := by
    have hnat : (2642156797 : ℕ)^4249*100000000000000^3225 ≤ 43155096209771^3225*5000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642156797 5000000000 43155096209771 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539213607/1000000000 : ℝ)^4249 ≤ (2769935967543/6250000000000 : ℝ)^3225 := by
    have hnat : (539213607 : ℕ)^4249*6250000000000^3225 ≤ 2769935967543^3225*1000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539213607 1000000000 2769935967543 6250000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2066501949/10000000000 : ℝ)^4249 ≤ (6262964146837/50000000000000 : ℝ)^3225 := by
    have hnat : (2066501949 : ℕ)^4249*50000000000000^3225 ≤ 6262964146837^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2066501949 10000000000 6262964146837 50000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642156797/5000000000 : ℝ), (539213607/1000000000 : ℝ), (-2066501949/10000000000 : ℝ)] ![(43155096209771/100000000000000 : ℝ), (2769935967543/6250000000000 : ℝ), (6262964146837/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642156797/5000000000 : ℝ)|^4249 ≤ (43155096209771/100000000000000 : ℝ)^3225
        have hw : |(2642156797/5000000000 : ℝ)|=(2642156797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539213607/1000000000 : ℝ)|^4249 ≤ (2769935967543/6250000000000 : ℝ)^3225
        have hw : |(539213607/1000000000 : ℝ)|=(539213607/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2066501949/10000000000 : ℝ)|^4249 ≤ (6262964146837/50000000000000 : ℝ)^3225
        have hw : |(-2066501949/10000000000 : ℝ)|=(2066501949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_box_3 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2245089183/5000000000 : ℝ)*x 0 + (4269933991/10000000000 : ℝ)*x 1 + (133435441/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2245089183/5000000000 : ℝ)^4249 ≤ (34821746119067/100000000000000 : ℝ)^3225 := by
    have hnat : (2245089183 : ℕ)^4249*100000000000000^3225 ≤ 34821746119067^3225*5000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245089183 5000000000 34821746119067 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4269933991/10000000000 : ℝ)^4249 ≤ (16294563159957/50000000000000 : ℝ)^3225 := by
    have hnat : (4269933991 : ℕ)^4249*50000000000000^3225 ≤ 16294563159957^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4269933991 10000000000 16294563159957 50000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (133435441/312500000 : ℝ)^4249 ≤ (32589127536643/100000000000000 : ℝ)^3225 := by
    have hnat : (133435441 : ℕ)^4249*100000000000000^3225 ≤ 32589127536643^3225*312500000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133435441 312500000 32589127536643 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2245089183/5000000000 : ℝ), (4269933991/10000000000 : ℝ), (133435441/312500000 : ℝ)] ![(34821746119067/100000000000000 : ℝ), (16294563159957/50000000000000 : ℝ), (32589127536643/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2245089183/5000000000 : ℝ)|^4249 ≤ (34821746119067/100000000000000 : ℝ)^3225
        have hw : |(2245089183/5000000000 : ℝ)|=(2245089183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4269933991/10000000000 : ℝ)|^4249 ≤ (16294563159957/50000000000000 : ℝ)^3225
        have hw : |(4269933991/10000000000 : ℝ)|=(4269933991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(133435441/312500000 : ℝ)|^4249 ≤ (32589127536643/100000000000000 : ℝ)^3225
        have hw : |(133435441/312500000 : ℝ)|=(133435441/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_box_4 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2265027329/10000000000 : ℝ)*x 0 + (2631805729/5000000000 : ℝ)*x 1 + (5263611187/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2265027329/10000000000 : ℝ)^4249 ≤ (14135031058271/100000000000000 : ℝ)^3225 := by
    have hnat : (2265027329 : ℕ)^4249*100000000000000^3225 ≤ 14135031058271^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2265027329 10000000000 14135031058271 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2631805729/5000000000 : ℝ)^4249 ≤ (42932485920429/100000000000000 : ℝ)^3225 := by
    have hnat : (2631805729 : ℕ)^4249*100000000000000^3225 ≤ 42932485920429^3225*5000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631805729 5000000000 42932485920429 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263611187/10000000000 : ℝ)^4249 ≤ (2146624150409/5000000000000 : ℝ)^3225 := by
    have hnat : (5263611187 : ℕ)^4249*5000000000000^3225 ≤ 2146624150409^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263611187 10000000000 2146624150409 5000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2265027329/10000000000 : ℝ), (2631805729/5000000000 : ℝ), (5263611187/10000000000 : ℝ)] ![(14135031058271/100000000000000 : ℝ), (42932485920429/100000000000000 : ℝ), (2146624150409/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2265027329/10000000000 : ℝ)|^4249 ≤ (14135031058271/100000000000000 : ℝ)^3225
        have hw : |(-2265027329/10000000000 : ℝ)|=(2265027329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2631805729/5000000000 : ℝ)|^4249 ≤ (42932485920429/100000000000000 : ℝ)^3225
        have hw : |(2631805729/5000000000 : ℝ)|=(2631805729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263611187/10000000000 : ℝ)|^4249 ≤ (2146624150409/5000000000000 : ℝ)^3225
        have hw : |(5263611187/10000000000 : ℝ)|=(5263611187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_box_5 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5374791183/10000000000 : ℝ)*x 0 + (-2117683363/10000000000 : ℝ)*x 1 + (5263612047/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5374791183/10000000000 : ℝ)^4249 ≤ (5516405594839/12500000000000 : ℝ)^3225 := by
    have hnat : (5374791183 : ℕ)^4249*12500000000000^3225 ≤ 5516405594839^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374791183 10000000000 5516405594839 12500000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2117683363/10000000000 : ℝ)^4249 ≤ (517450518763/4000000000000 : ℝ)^3225 := by
    have hnat : (2117683363 : ℕ)^4249*4000000000000^3225 ≤ 517450518763^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117683363 10000000000 517450518763 4000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263612047/10000000000 : ℝ)^4249 ≤ (42932492250003/100000000000000 : ℝ)^3225 := by
    have hnat : (5263612047 : ℕ)^4249*100000000000000^3225 ≤ 42932492250003^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263612047 10000000000 42932492250003 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5374791183/10000000000 : ℝ), (-2117683363/10000000000 : ℝ), (5263612047/10000000000 : ℝ)] ![(5516405594839/12500000000000 : ℝ), (517450518763/4000000000000 : ℝ), (42932492250003/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5374791183/10000000000 : ℝ)|^4249 ≤ (5516405594839/12500000000000 : ℝ)^3225
        have hw : |(5374791183/10000000000 : ℝ)|=(5374791183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2117683363/10000000000 : ℝ)|^4249 ≤ (517450518763/4000000000000 : ℝ)^3225
        have hw : |(-2117683363/10000000000 : ℝ)|=(2117683363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263612047/10000000000 : ℝ)|^4249 ≤ (42932492250003/100000000000000 : ℝ)^3225
        have hw : |(5263612047/10000000000 : ℝ)|=(5263612047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_box_6 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (268739551/500000000 : ℝ)*x 0 + (1052722451/2000000000 : ℝ)*x 1 + (-264710413/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268739551/500000000 : ℝ)^4249 ≤ (220656214977/500000000000 : ℝ)^3225 := by
    have hnat : (268739551 : ℕ)^4249*500000000000^3225 ≤ 220656214977^3225*500000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268739551 500000000 220656214977 500000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052722451/2000000000 : ℝ)^4249 ≤ (8586498897047/20000000000000 : ℝ)^3225 := by
    have hnat : (1052722451 : ℕ)^4249*20000000000000^3225 ≤ 8586498897047^3225*2000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052722451 2000000000 8586498897047 20000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (264710413/1250000000 : ℝ)^4249 ≤ (517450499769/4000000000000 : ℝ)^3225 := by
    have hnat : (264710413 : ℕ)^4249*4000000000000^3225 ≤ 517450499769^3225*1250000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264710413 1250000000 517450499769 4000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(268739551/500000000 : ℝ), (1052722451/2000000000 : ℝ), (-264710413/1250000000 : ℝ)] ![(220656214977/500000000000 : ℝ), (8586498897047/20000000000000 : ℝ), (517450499769/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(268739551/500000000 : ℝ)|^4249 ≤ (220656214977/500000000000 : ℝ)^3225
        have hw : |(268739551/500000000 : ℝ)|=(268739551/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1052722451/2000000000 : ℝ)|^4249 ≤ (8586498897047/20000000000000 : ℝ)^3225
        have hw : |(1052722451/2000000000 : ℝ)|=(1052722451/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-264710413/1250000000 : ℝ)|^4249 ≤ (517450499769/4000000000000 : ℝ)^3225
        have hw : |(-264710413/1250000000 : ℝ)|=(264710413/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_box_7 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4190322809/10000000000 : ℝ)*x 0 + (4419806399/10000000000 : ℝ)*x 1 + (4419806293/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4190322809/10000000000 : ℝ)^4249 ≤ (31790966785083/100000000000000 : ℝ)^3225 := by
    have hnat : (4190322809 : ℕ)^4249*100000000000000^3225 ≤ 31790966785083^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4190322809 10000000000 31790966785083 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4419806399/10000000000 : ℝ)^4249 ≤ (17052258568517/50000000000000 : ℝ)^3225 := by
    have hnat : (4419806399 : ℕ)^4249*50000000000000^3225 ≤ 17052258568517^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4419806399 10000000000 17052258568517 50000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4419806293/10000000000 : ℝ)^4249 ≤ (170522580297/500000000000 : ℝ)^3225 := by
    have hnat : (4419806293 : ℕ)^4249*500000000000^3225 ≤ 170522580297^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4419806293 10000000000 170522580297 500000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4190322809/10000000000 : ℝ), (4419806399/10000000000 : ℝ), (4419806293/10000000000 : ℝ)] ![(31790966785083/100000000000000 : ℝ), (17052258568517/50000000000000 : ℝ), (170522580297/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4190322809/10000000000 : ℝ)|^4249 ≤ (31790966785083/100000000000000 : ℝ)^3225
        have hw : |(4190322809/10000000000 : ℝ)|=(4190322809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4419806399/10000000000 : ℝ)|^4249 ≤ (17052258568517/50000000000000 : ℝ)^3225
        have hw : |(4419806399/10000000000 : ℝ)|=(4419806399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4419806293/10000000000 : ℝ)|^4249 ≤ (170522580297/500000000000 : ℝ)^3225
        have hw : |(4419806293/10000000000 : ℝ)|=(4419806293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_box_8 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-10962631/50000000 : ℝ)*x 0 + (2587694911/5000000000 : ℝ)*x 1 + (675771863/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10962631/50000000 : ℝ)^4249 ≤ (13541974471141/100000000000000 : ℝ)^3225 := by
    have hnat : (10962631 : ℕ)^4249*100000000000000^3225 ≤ 13541974471141^3225*50000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10962631 50000000 13541974471141 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2587694911/5000000000 : ℝ)^4249 ≤ (1049674039137/2500000000000 : ℝ)^3225 := by
    have hnat : (2587694911 : ℕ)^4249*2500000000000^3225 ≤ 1049674039137^3225*5000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587694911 5000000000 1049674039137 2500000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (675771863/1250000000 : ℝ)^4249 ≤ (44471063950161/100000000000000 : ℝ)^3225 := by
    have hnat : (675771863 : ℕ)^4249*100000000000000^3225 ≤ 44471063950161^3225*1250000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675771863 1250000000 44471063950161 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-10962631/50000000 : ℝ), (2587694911/5000000000 : ℝ), (675771863/1250000000 : ℝ)] ![(13541974471141/100000000000000 : ℝ), (1049674039137/2500000000000 : ℝ), (44471063950161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-10962631/50000000 : ℝ)|^4249 ≤ (13541974471141/100000000000000 : ℝ)^3225
        have hw : |(-10962631/50000000 : ℝ)|=(10962631/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2587694911/5000000000 : ℝ)|^4249 ≤ (1049674039137/2500000000000 : ℝ)^3225
        have hw : |(2587694911/5000000000 : ℝ)|=(2587694911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(675771863/1250000000 : ℝ)|^4249 ≤ (44471063950161/100000000000000 : ℝ)^3225
        have hw : |(675771863/1250000000 : ℝ)|=(675771863/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_box_9 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (527442411/1000000000 : ℝ)*x 0 + (-2060774687/10000000000 : ℝ)*x 1 + (5406175443/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527442411/1000000000 : ℝ)^4249 ≤ (21524359935229/50000000000000 : ℝ)^3225 := by
    have hnat : (527442411 : ℕ)^4249*50000000000000^3225 ≤ 21524359935229^3225*1000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527442411 1000000000 21524359935229 50000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2060774687/10000000000 : ℝ)^4249 ≤ (156002629079/1250000000000 : ℝ)^3225 := by
    have hnat : (2060774687 : ℕ)^4249*1250000000000^3225 ≤ 156002629079^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2060774687 10000000000 156002629079 1250000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406175443/10000000000 : ℝ)^4249 ≤ (2223553489589/5000000000000 : ℝ)^3225 := by
    have hnat : (5406175443 : ℕ)^4249*5000000000000^3225 ≤ 2223553489589^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406175443 10000000000 2223553489589 5000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(527442411/1000000000 : ℝ), (-2060774687/10000000000 : ℝ), (5406175443/10000000000 : ℝ)] ![(21524359935229/50000000000000 : ℝ), (156002629079/1250000000000 : ℝ), (2223553489589/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(527442411/1000000000 : ℝ)|^4249 ≤ (21524359935229/50000000000000 : ℝ)^3225
        have hw : |(527442411/1000000000 : ℝ)|=(527442411/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2060774687/10000000000 : ℝ)|^4249 ≤ (156002629079/1250000000000 : ℝ)^3225
        have hw : |(-2060774687/10000000000 : ℝ)|=(2060774687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406175443/10000000000 : ℝ)|^4249 ≤ (2223553489589/5000000000000 : ℝ)^3225
        have hw : |(5406175443/10000000000 : ℝ)|=(5406175443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_box_10 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5274423877/10000000000 : ℝ)*x 0 + (5406175451/10000000000 : ℝ)*x 1 + (-2060774989/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5274423877/10000000000 : ℝ)^4249 ≤ (43048717364937/100000000000000 : ℝ)^3225 := by
    have hnat : (5274423877 : ℕ)^4249*100000000000000^3225 ≤ 43048717364937^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274423877 10000000000 43048717364937 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406175451/10000000000 : ℝ)^4249 ≤ (44471069878483/100000000000000 : ℝ)^3225 := by
    have hnat : (5406175451 : ℕ)^4249*100000000000000^3225 ≤ 44471069878483^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406175451 10000000000 44471069878483 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2060774989/10000000000 : ℝ)^4249 ≤ (12480212735977/100000000000000 : ℝ)^3225 := by
    have hnat : (2060774989 : ℕ)^4249*100000000000000^3225 ≤ 12480212735977^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2060774989 10000000000 12480212735977 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5274423877/10000000000 : ℝ), (5406175451/10000000000 : ℝ), (-2060774989/10000000000 : ℝ)] ![(43048717364937/100000000000000 : ℝ), (44471069878483/100000000000000 : ℝ), (12480212735977/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5274423877/10000000000 : ℝ)|^4249 ≤ (43048717364937/100000000000000 : ℝ)^3225
        have hw : |(5274423877/10000000000 : ℝ)|=(5274423877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406175451/10000000000 : ℝ)|^4249 ≤ (44471069878483/100000000000000 : ℝ)^3225
        have hw : |(5406175451/10000000000 : ℝ)|=(5406175451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2060774989/10000000000 : ℝ)|^4249 ≤ (12480212735977/100000000000000 : ℝ)^3225
        have hw : |(-2060774989/10000000000 : ℝ)|=(2060774989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_box_11 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (452237207/1000000000 : ℝ)*x 0 + (2126775131/5000000000 : ℝ)*x 1 + (531693593/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (452237207/1000000000 : ℝ)^4249 ≤ (35151058586833/100000000000000 : ℝ)^3225 := by
    have hnat : (452237207 : ℕ)^4249*100000000000000^3225 ≤ 35151058586833^3225*1000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      452237207 1000000000 35151058586833 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2126775131/5000000000 : ℝ)^4249 ≤ (8106119580223/25000000000000 : ℝ)^3225 := by
    have hnat : (2126775131 : ℕ)^4249*25000000000000^3225 ≤ 8106119580223^3225*5000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126775131 5000000000 8106119580223 25000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (531693593/1250000000 : ℝ)^4249 ≤ (32424463075093/100000000000000 : ℝ)^3225 := by
    have hnat : (531693593 : ℕ)^4249*100000000000000^3225 ≤ 32424463075093^3225*1250000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531693593 1250000000 32424463075093 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(452237207/1000000000 : ℝ), (2126775131/5000000000 : ℝ), (531693593/1250000000 : ℝ)] ![(35151058586833/100000000000000 : ℝ), (8106119580223/25000000000000 : ℝ), (32424463075093/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(452237207/1000000000 : ℝ)|^4249 ≤ (35151058586833/100000000000000 : ℝ)^3225
        have hw : |(452237207/1000000000 : ℝ)|=(452237207/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2126775131/5000000000 : ℝ)|^4249 ≤ (8106119580223/25000000000000 : ℝ)^3225
        have hw : |(2126775131/5000000000 : ℝ)|=(2126775131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(531693593/1250000000 : ℝ)|^4249 ≤ (32424463075093/100000000000000 : ℝ)^3225
        have hw : |(531693593/1250000000 : ℝ)|=(531693593/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_box_12 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-398402163/2000000000 : ℝ)*x 0 + (547802713/1000000000 : ℝ)*x 1 + (5252591313/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (398402163/2000000000 : ℝ)^4249 ≤ (5967236201281/50000000000000 : ℝ)^3225 := by
    have hnat : (398402163 : ℕ)^4249*50000000000000^3225 ≤ 5967236201281^3225*2000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      398402163 2000000000 5967236201281 50000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (547802713/1000000000 : ℝ)^4249 ≤ (45251428136973/100000000000000 : ℝ)^3225 := by
    have hnat : (547802713 : ℕ)^4249*100000000000000^3225 ≤ 45251428136973^3225*1000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547802713 1000000000 45251428136973 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5252591313/10000000000 : ℝ)^4249 ≤ (42814099446117/100000000000000 : ℝ)^3225 := by
    have hnat : (5252591313 : ℕ)^4249*100000000000000^3225 ≤ 42814099446117^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252591313 10000000000 42814099446117 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-398402163/2000000000 : ℝ), (547802713/1000000000 : ℝ), (5252591313/10000000000 : ℝ)] ![(5967236201281/50000000000000 : ℝ), (45251428136973/100000000000000 : ℝ), (42814099446117/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-398402163/2000000000 : ℝ)|^4249 ≤ (5967236201281/50000000000000 : ℝ)^3225
        have hw : |(-398402163/2000000000 : ℝ)|=(398402163/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(547802713/1000000000 : ℝ)|^4249 ≤ (45251428136973/100000000000000 : ℝ)^3225
        have hw : |(547802713/1000000000 : ℝ)|=(547802713/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5252591313/10000000000 : ℝ)|^4249 ≤ (42814099446117/100000000000000 : ℝ)^3225
        have hw : |(5252591313/10000000000 : ℝ)|=(5252591313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_box_13 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5382547109/10000000000 : ℝ)*x 0 + (-2121965353/10000000000 : ℝ)*x 1 + (105051821/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5382547109/10000000000 : ℝ)^4249 ≤ (44215166541271/100000000000000 : ℝ)^3225 := by
    have hnat : (5382547109 : ℕ)^4249*100000000000000^3225 ≤ 44215166541271^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5382547109 10000000000 44215166541271 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2121965353/10000000000 : ℝ)^4249 ≤ (12970736820053/100000000000000 : ℝ)^3225 := by
    have hnat : (2121965353 : ℕ)^4249*100000000000000^3225 ≤ 12970736820053^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121965353 10000000000 12970736820053 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105051821/200000000 : ℝ)^4249 ≤ (42814096621719/100000000000000 : ℝ)^3225 := by
    have hnat : (105051821 : ℕ)^4249*100000000000000^3225 ≤ 42814096621719^3225*200000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105051821 200000000 42814096621719 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5382547109/10000000000 : ℝ), (-2121965353/10000000000 : ℝ), (105051821/200000000 : ℝ)] ![(44215166541271/100000000000000 : ℝ), (12970736820053/100000000000000 : ℝ), (42814096621719/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5382547109/10000000000 : ℝ)|^4249 ≤ (44215166541271/100000000000000 : ℝ)^3225
        have hw : |(5382547109/10000000000 : ℝ)|=(5382547109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2121965353/10000000000 : ℝ)|^4249 ≤ (12970736820053/100000000000000 : ℝ)^3225
        have hw : |(-2121965353/10000000000 : ℝ)|=(2121965353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(105051821/200000000 : ℝ)|^4249 ≤ (42814096621719/100000000000000 : ℝ)^3225
        have hw : |(105051821/200000000 : ℝ)|=(105051821/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_box_14 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (672818279/1250000000 : ℝ)*x 0 + (5252591971/10000000000 : ℝ)*x 1 + (-2121965303/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (672818279/1250000000 : ℝ)^4249 ≤ (22107578524829/50000000000000 : ℝ)^3225 := by
    have hnat : (672818279 : ℕ)^4249*50000000000000^3225 ≤ 22107578524829^3225*1250000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672818279 1250000000 22107578524829 50000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5252591971/10000000000 : ℝ)^4249 ≤ (42814106512483/100000000000000 : ℝ)^3225 := by
    have hnat : (5252591971 : ℕ)^4249*100000000000000^3225 ≤ 42814106512483^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252591971 10000000000 42814106512483 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2121965303/10000000000 : ℝ)^4249 ≤ (12970736417379/100000000000000 : ℝ)^3225 := by
    have hnat : (2121965303 : ℕ)^4249*100000000000000^3225 ≤ 12970736417379^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121965303 10000000000 12970736417379 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(672818279/1250000000 : ℝ), (5252591971/10000000000 : ℝ), (-2121965303/10000000000 : ℝ)] ![(22107578524829/50000000000000 : ℝ), (42814106512483/100000000000000 : ℝ), (12970736417379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(672818279/1250000000 : ℝ)|^4249 ≤ (22107578524829/50000000000000 : ℝ)^3225
        have hw : |(672818279/1250000000 : ℝ)|=(672818279/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5252591971/10000000000 : ℝ)|^4249 ≤ (42814106512483/100000000000000 : ℝ)^3225
        have hw : |(5252591971/10000000000 : ℝ)|=(5252591971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2121965303/10000000000 : ℝ)|^4249 ≤ (12970736417379/100000000000000 : ℝ)^3225
        have hw : |(-2121965303/10000000000 : ℝ)|=(2121965303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_box_15 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4164166383/10000000000 : ℝ)*x 0 + (1108161481/2500000000 : ℝ)*x 1 + (4432646747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4164166383/10000000000 : ℝ)^4249 ≤ (6305954886357/20000000000000 : ℝ)^3225 := by
    have hnat : (4164166383 : ℕ)^4249*20000000000000^3225 ≤ 6305954886357^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4164166383 10000000000 6305954886357 20000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1108161481/2500000000 : ℝ)^4249 ≤ (34235108587269/100000000000000 : ℝ)^3225 := by
    have hnat : (1108161481 : ℕ)^4249*100000000000000^3225 ≤ 34235108587269^3225*2500000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1108161481 2500000000 34235108587269 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4432646747/10000000000 : ℝ)^4249 ≤ (34235116961897/100000000000000 : ℝ)^3225 := by
    have hnat : (4432646747 : ℕ)^4249*100000000000000^3225 ≤ 34235116961897^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4432646747 10000000000 34235116961897 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4164166383/10000000000 : ℝ), (1108161481/2500000000 : ℝ), (4432646747/10000000000 : ℝ)] ![(6305954886357/20000000000000 : ℝ), (34235108587269/100000000000000 : ℝ), (34235116961897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4164166383/10000000000 : ℝ)|^4249 ≤ (6305954886357/20000000000000 : ℝ)^3225
        have hw : |(4164166383/10000000000 : ℝ)|=(4164166383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1108161481/2500000000 : ℝ)|^4249 ≤ (34235108587269/100000000000000 : ℝ)^3225
        have hw : |(1108161481/2500000000 : ℝ)|=(1108161481/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4432646747/10000000000 : ℝ)|^4249 ≤ (34235116961897/100000000000000 : ℝ)^3225
        have hw : |(4432646747/10000000000 : ℝ)|=(4432646747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1289_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76322037/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1467/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (551/5000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62839/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58839/100000 : ℝ) ∧ (39819/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84143/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1467/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (551/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1467/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (551/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1467/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (551/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1467/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (551/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1467/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (551/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1467/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (551/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (551/5000 : ℝ) ^ (531/128 : ℝ) ≤ (2657603684241249/25000000000000000000 : ℝ) := by
    have hpowers : (551/5000 : ℝ)^531 ≤ (2657603684241249/25000000000000000000 : ℝ)^128 := by
      have hnat : (551 : ℕ)^531*25000000000000000000^128 ≤ 2657603684241249^128*5000^531 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        551 5000 2657603684241249 25000000000000000000 531 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (551/5000 : ℝ)) (X := (2657603684241249/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 531 128 (by norm_num) hpowers
    exact h
  have hpowhi : (1467/10000 : ℝ) ^ (531/128 : ℝ) ≤ (2177045183691601/6250000000000000000 : ℝ) := by
    have hpowers : (1467/10000 : ℝ)^531 ≤ (2177045183691601/6250000000000000000 : ℝ)^128 := by
      have hnat : (1467 : ℕ)^531*6250000000000000000^128 ≤ 2177045183691601^128*10000^531 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1467 10000 2177045183691601 6250000000000000000 531 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1467/10000 : ℝ)) (X := (2177045183691601/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 531 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502657603684241249/12500000000000000000 : ℝ) ≤ (2000102492152211/2000000000000000 : ℝ) ^ (531/128 : ℝ) := by
    have hpowers : (12502657603684241249/12500000000000000000 : ℝ)^128 ≤ (2000102492152211/2000000000000000 : ℝ)^531 := by
      have hnat : (12502657603684241249 : ℕ)^128*2000000000000000^531 ≤ 2000102492152211^531*12500000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502657603684241249 12500000000000000000 2000102492152211 2000000000000000 128 531 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000102492152211/2000000000000000 : ℝ)) (X := (12502657603684241249/12500000000000000000 : ℝ)) (by norm_num) 531 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011365784419007653/25000000000000000000 : ℝ) ≤ (5000547860446937/5000000000000000 : ℝ) ^ (531/128 : ℝ) := by
    have hpowers : (25011365784419007653/25000000000000000000 : ℝ)^128 ≤ (5000547860446937/5000000000000000 : ℝ)^531 := by
      have hnat : (25011365784419007653 : ℕ)^128*5000000000000000^531 ≤ 5000547860446937^531*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011365784419007653 25000000000000000000 5000547860446937 5000000000000000 128 531 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000547860446937/5000000000000000 : ℝ)) (X := (25011365784419007653/25000000000000000000 : ℝ)) (by norm_num) 531 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (3127177045183691601/3125000000000000000 : ℝ) ≤ (10001678981026693/10000000000000000 : ℝ) ^ (531/128 : ℝ) := by
    have hpowers : (3127177045183691601/3125000000000000000 : ℝ)^128 ≤ (10001678981026693/10000000000000000 : ℝ)^531 := by
      have hnat : (3127177045183691601 : ℕ)^128*10000000000000000^531 ≤ 10001678981026693^531*3125000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3127177045183691601 3125000000000000000 10001678981026693 10000000000000000 128 531 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001678981026693/10000000000000000 : ℝ)) (X := (3127177045183691601/3125000000000000000 : ℝ)) (by norm_num) 531 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2657603684241249/25000000000000000000 : ℝ) ≤ ((3648901542845051999/3650000000000000000 : ℝ)+2*(583260132819/365000000000000 : ℝ)*(551/5000 : ℝ))^(531/128 : ℝ) := by
    rw [show (3648901542845051999/3650000000000000000 : ℝ)+2*(583260132819/365000000000000 : ℝ)*(551/5000 : ℝ)=(2000102492152211/2000000000000000 : ℝ) by norm_num, show 1+2*(2657603684241249/25000000000000000000 : ℝ)=(12502657603684241249/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2177045183691601/6250000000000000000 : ℝ)+(2657603684241249/25000000000000000000 : ℝ) ≤ ((3648901542845051999/3650000000000000000 : ℝ)+(583260132819/365000000000000 : ℝ)*((1467/10000 : ℝ)+(551/5000 : ℝ)))^(531/128 : ℝ) := by
    rw [show (3648901542845051999/3650000000000000000 : ℝ)+(583260132819/365000000000000 : ℝ)*((1467/10000 : ℝ)+(551/5000 : ℝ))=(5000547860446937/5000000000000000 : ℝ) by norm_num, show 1+(2177045183691601/6250000000000000000 : ℝ)+(2657603684241249/25000000000000000000 : ℝ)=(25011365784419007653/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2177045183691601/6250000000000000000 : ℝ) ≤ ((3648901542845051999/3650000000000000000 : ℝ)+2*(583260132819/365000000000000 : ℝ)*(1467/10000 : ℝ))^(531/128 : ℝ) := by
    rw [show (3648901542845051999/3650000000000000000 : ℝ)+2*(583260132819/365000000000000 : ℝ)*(1467/10000 : ℝ)=(10001678981026693/10000000000000000 : ℝ) by norm_num, show 1+2*(2177045183691601/6250000000000000000 : ℝ)=(3127177045183691601/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3648901542845051999/3650000000000000000 : ℝ)*(X 1 0+X 2 0)+(583260132819/365000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (531/128 : ℝ)) (lo := (551/5000 : ℝ)) (hi := (1467/10000 : ℝ)) (c := (3648901542845051999/3650000000000000000 : ℝ)) (alpha := (583260132819/365000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3648901542845051999/3650000000000000000 : ℝ)*(X 0 1+X 2 1)+(583260132819/365000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (531/128 : ℝ)) (lo := (551/5000 : ℝ)) (hi := (1467/10000 : ℝ)) (c := (3648901542845051999/3650000000000000000 : ℝ)) (alpha := (583260132819/365000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3648901542845051999/3650000000000000000 : ℝ)*(X 0 2+X 1 2)+(583260132819/365000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (531/128 : ℝ)) (lo := (551/5000 : ℝ)) (hi := (1467/10000 : ℝ)) (c := (3648901542845051999/3650000000000000000 : ℝ)) (alpha := (583260132819/365000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-383812813/2000000000 : ℝ)*X 0 0+(2696068111/5000000000 : ℝ)*X 0 1+(1348034083/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5284313109/10000000000 : ℝ)*X 1 0+(-2066501869/10000000000 : ℝ)*X 1 1+(1348034153/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2642156797/5000000000 : ℝ)*X 2 0+(539213607/1000000000 : ℝ)*X 2 1+(-2066501949/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2245089183/5000000000 : ℝ)*X 0 0+(4269933991/10000000000 : ℝ)*X 0 1+(133435441/312500000 : ℝ)*X 0 2+(2245089183/5000000000 : ℝ)*X 1 0+(4269933991/10000000000 : ℝ)*X 1 1+(133435441/312500000 : ℝ)*X 1 2+(2245089183/5000000000 : ℝ)*X 2 0+(4269933991/10000000000 : ℝ)*X 2 1+(133435441/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2265027329/10000000000 : ℝ)*X 0 0+(2631805729/5000000000 : ℝ)*X 0 1+(5263611187/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5374791183/10000000000 : ℝ)*X 1 0+(-2117683363/10000000000 : ℝ)*X 1 1+(5263612047/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((268739551/500000000 : ℝ)*X 2 0+(1052722451/2000000000 : ℝ)*X 2 1+(-264710413/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4190322809/10000000000 : ℝ)*X 0 0+(4419806399/10000000000 : ℝ)*X 0 1+(4419806293/10000000000 : ℝ)*X 0 2+(4190322809/10000000000 : ℝ)*X 1 0+(4419806399/10000000000 : ℝ)*X 1 1+(4419806293/10000000000 : ℝ)*X 1 2+(4190322809/10000000000 : ℝ)*X 2 0+(4419806399/10000000000 : ℝ)*X 2 1+(4419806293/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-10962631/50000000 : ℝ)*X 0 0+(2587694911/5000000000 : ℝ)*X 0 1+(675771863/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((527442411/1000000000 : ℝ)*X 1 0+(-2060774687/10000000000 : ℝ)*X 1 1+(5406175443/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5274423877/10000000000 : ℝ)*X 2 0+(5406175451/10000000000 : ℝ)*X 2 1+(-2060774989/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((452237207/1000000000 : ℝ)*X 0 0+(2126775131/5000000000 : ℝ)*X 0 1+(531693593/1250000000 : ℝ)*X 0 2+(452237207/1000000000 : ℝ)*X 1 0+(2126775131/5000000000 : ℝ)*X 1 1+(531693593/1250000000 : ℝ)*X 1 2+(452237207/1000000000 : ℝ)*X 2 0+(2126775131/5000000000 : ℝ)*X 2 1+(531693593/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-398402163/2000000000 : ℝ)*X 0 0+(547802713/1000000000 : ℝ)*X 0 1+(5252591313/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5382547109/10000000000 : ℝ)*X 1 0+(-2121965353/10000000000 : ℝ)*X 1 1+(105051821/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((672818279/1250000000 : ℝ)*X 2 0+(5252591971/10000000000 : ℝ)*X 2 1+(-2121965303/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4164166383/10000000000 : ℝ)*X 0 0+(1108161481/2500000000 : ℝ)*X 0 1+(4432646747/10000000000 : ℝ)*X 0 2+(4164166383/10000000000 : ℝ)*X 1 0+(1108161481/2500000000 : ℝ)*X 1 1+(4432646747/10000000000 : ℝ)*X 1 2+(4164166383/10000000000 : ℝ)*X 2 0+(1108161481/2500000000 : ℝ)*X 2 1+(4432646747/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62839/100000 : ℝ) ≤ (-114675763512965769591191423307741/182500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7084901/100000000000000 : ℝ)*(upper1) + (60945929/100000000000000 : ℝ)*(upper3) + (18083587/50000000000000 : ℝ)*(upper5) + (2860601234973247/100000000000000 : ℝ)*(major0) + (2860601234973247/100000000000000 : ℝ)*(major1) + (2860601234973247/100000000000000 : ℝ)*(major2) + (5458278231/100000000000000 : ℝ)*(sp3) + (483513755413541/12500000000000 : ℝ)*(sp4) + (3867915209884089/100000000000000 : ℝ)*(sp5) + (1933916945531119/50000000000000 : ℝ)*(sp6) + (1874028141593617/100000000000000 : ℝ)*(sp7) + (208585009/5000000000000 : ℝ)*(sp8) + (99502562209/50000000000000 : ℝ)*(sp13) + (280323946269/100000000000000 : ℝ)*(sp14) + (234254199983981/12500000000000 : ℝ)*(f.failure) + (967028553752127/25000000000000 : ℝ)*(f.sum) + (4297641330543/18250000000000000000000000000 : ℝ)*base65 + (1084403078098199247/365000000000000000000000000000000 : ℝ)*base68 + (3789746731763199247/365000000000000000000000000000000 : ℝ)*base70 + (680589072998199247/365000000000000000000000000000000 : ℝ)*base72 + (10148245741457/18250000000000000000000000000 : ℝ)*base74 + (4759308443381800753/365000000000000000000000000000000 : ℝ)*base75 + (655487470566800753/365000000000000000000000000000000 : ℝ)*base77 + (717265165423199247/365000000000000000000000000000000 : ℝ)*base80 + (1310186348797207/18250000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (3539297/625000000000000000000 : ℝ)*base89 + (3539297/625000000000000000000 : ℝ)*base91 + (3539297/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (58839/100000 : ℝ) ≤ (2684658615493935042910199741589/4562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (27679823/100000000000000 : ℝ)*(upper0) + (42391083/100000000000000 : ℝ)*(lower3) + (26177353/50000000000000 : ℝ)*(upper4) + (146376374462363/5000000000000 : ℝ)*(major0) + (146376374462363/5000000000000 : ℝ)*(major1) + (146376374462363/5000000000000 : ℝ)*(major2) + (48969528444711/1250000000000 : ℝ)*(sp0) + (1958775199323907/50000000000000 : ℝ)*(sp1) + (979384238483599/25000000000000 : ℝ)*(sp2) + (1917869880763601/100000000000000 : ℝ)*(sp3) + (1238949739/10000000000000 : ℝ)*(sp5) + (3229276351/12500000000000 : ℝ)*(sp10) + (4182681457/50000000000000 : ℝ)*(sp11) + (128142081/25000000000000 : ℝ)*(sp12) + (383575649225303/20000000000000 : ℝ)*(f.failure) + (979390697036301/25000000000000 : ℝ)*(f.sum) + (945675129839/456250000000000000000000000 : ℝ)*base66 + (29472892979633637/18250000000000000000000000000000 : ℝ)*base67 + (189932580391383637/18250000000000000000000000000000 : ℝ)*base69 + (17443378049883637/18250000000000000000000000000000 : ℝ)*base71 + (84093525391881/1825000000000000000000000000 : ℝ)*base74 + (106463469241883637/18250000000000000000000000000000 : ℝ)*base75 + (76468700721883637/18250000000000000000000000000000 : ℝ)*base77 + (989047938846366363/18250000000000000000000000000000 : ℝ)*base80 + (1608916040347/912500000000000000000000000 : ℝ)*base81 + (3097789/1000000000000000000000 : ℝ)*base90 + (3097789/1000000000000000000000 : ℝ)*base92 + (3097789/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (39819/50000 : ℝ) ≤ (145344340147056964063249547564823/182500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (38990343/100000000000000 : ℝ)*(upper1) + (6954059/2500000000000 : ℝ)*(upper3) + (6080271/10000000000000 : ℝ)*(upper4) + (114871759/50000000000000 : ℝ)*(lower5) + (3241606801904353/100000000000000 : ℝ)*(major0) + (3241606801904353/100000000000000 : ℝ)*(major1) + (3241606801904353/100000000000000 : ℝ)*(major2) + (800899659/20000000000000 : ℝ)*(sp0) + (163566147093/100000000000000 : ℝ)*(sp2) + (9491539837/50000000000000 : ℝ)*(sp3) + (4333025184649677/100000000000000 : ℝ)*(sp8) + (1083257297286993/25000000000000 : ℝ)*(sp9) + (4332865623000879/100000000000000 : ℝ)*(sp10) + (424723704027733/20000000000000 : ℝ)*(sp11) + (1061818751609169/50000000000000 : ℝ)*(f.failure) + (1083257297286993/25000000000000 : ℝ)*(f.sum) + (9724508234357/18250000000000000000000000000 : ℝ)*base65 + (735425234899478353/365000000000000000000000000000000 : ℝ)*base68 + (3695822722419478353/365000000000000000000000000000000 : ℝ)*base70 + (2610290077089478353/365000000000000000000000000000000 : ℝ)*base72 + (74950341461107/18250000000000000000000000000 : ℝ)*base73 + (3910804673939478353/365000000000000000000000000000000 : ℝ)*base76 + (4237702876914478353/365000000000000000000000000000000 : ℝ)*base78 + (3547398723474478353/365000000000000000000000000000000 : ℝ)*base80 + (138757227716107/18250000000000000000000000000 : ℝ)*base81 + (19042747/2500000000000000000000 : ℝ)*base90 + (19042747/2500000000000000000000 : ℝ)*base92 + (19042747/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-84143/100000 : ℝ) ≤ (-7677816677424271697014010716137/9125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3886309/3125000000000 : ℝ)*(lower0) + (208298507/100000000000000 : ℝ)*(lower1) + (90410019/50000000000000 : ℝ)*(lower4) + (163873986847793/5000000000000 : ℝ)*(major0) + (163873986847793/5000000000000 : ℝ)*(major1) + (163873986847793/5000000000000 : ℝ)*(major2) + (6677772257/100000000000000 : ℝ)*(sp0) + (189704622711/50000000000000 : ℝ)*(sp5) + (110972387179/100000000000000 : ℝ)*(sp6) + (8529183419/10000000000000 : ℝ)*(sp7) + (1108965269569597/25000000000000 : ℝ)*(sp12) + (4435488346805223/100000000000000 : ℝ)*(sp13) + (2217878391831733/50000000000000 : ℝ)*(sp14) + (536763311234959/25000000000000 : ℝ)*(sp15) + (1073569268387013/50000000000000 : ℝ)*(f.failure) + (887173551210129/20000000000000 : ℝ)*(f.sum) + (7022426563791/1825000000000000000000000000 : ℝ)*base66 + (84666419897941793/18250000000000000000000000000000 : ℝ)*base68 + (207485017354441793/18250000000000000000000000000000 : ℝ)*base70 + (319043279747691793/18250000000000000000000000000000 : ℝ)*base72 + (50486069338509/1825000000000000000000000000 : ℝ)*base73 + (376225762296441793/18250000000000000000000000000000 : ℝ)*base76 + (326949693649441793/18250000000000000000000000000000 : ℝ)*base78 + (359764194023191793/18250000000000000000000000000000 : ℝ)*base80 + (5396100269083/912500000000000000000000000 : ℝ)*base82 + (36505481/2500000000000000000000 : ℝ)*base89 + (36505481/2500000000000000000000 : ℝ)*base91 + (36505481/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1289_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76322037/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1467/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (551/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62839/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58839/100000 : ℝ) else (39819/50000 : ℝ) ≤ X j i ∧ X j i ≤ (84143/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1289_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1289_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76322037/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2937/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5503/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62839/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58839/100000 : ℝ) else (39819/50000 : ℝ) ≤ X j i ∧ X j i ≤ (84143/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1289_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1289_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1289_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76322037/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2937/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5503/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62839/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58839/100000 : ℝ) else (39819/50000 : ℝ) ≤ X j i ∧ X j i ≤ (84143/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1289_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
