-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1484_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:14:06.437612+00:00
-- url     : https://prove2.me/submissions/d6e08c6d-50e6-4ee1-b811-63ef5502a204

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
theorem support_rectangle_w1484_s0_0 (p : ℝ) (hpa : (4463/1024 : ℝ) ≤ p) (hpb : p ≤ (4465/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-857969179/5000000000 : ℝ)*x 0 + (2967357571/5000000000 : ℝ)*x 1 + (4843159419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (857969179/5000000000 : ℝ)^4465 ≤ (2031087500271/20000000000000 : ℝ)^3441 := by
    have hnat : (857969179 : ℕ)^4465*20000000000000^3441 ≤ 2031087500271^3441*5000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      857969179 5000000000 2031087500271 20000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2967357571/5000000000 : ℝ)^4465 ≤ (10162403091213/20000000000000 : ℝ)^3441 := by
    have hnat : (2967357571 : ℕ)^4465*20000000000000^3441 ≤ 10162403091213^3441*5000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2967357571 5000000000 10162403091213 20000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4843159419/10000000000 : ℝ)^4465 ≤ (39032547030043/100000000000000 : ℝ)^3441 := by
    have hnat : (4843159419 : ℕ)^4465*100000000000000^3441 ≤ 39032547030043^3441*10000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4843159419 10000000000 39032547030043 100000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4465/1024 : ℝ)) 4465 3441 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-857969179/5000000000 : ℝ), (2967357571/5000000000 : ℝ), (4843159419/10000000000 : ℝ)] ![(2031087500271/20000000000000 : ℝ), (10162403091213/20000000000000 : ℝ), (39032547030043/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-857969179/5000000000 : ℝ)|^4465 ≤ (2031087500271/20000000000000 : ℝ)^3441
        have hw : |(-857969179/5000000000 : ℝ)|=(857969179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2967357571/5000000000 : ℝ)|^4465 ≤ (10162403091213/20000000000000 : ℝ)^3441
        have hw : |(2967357571/5000000000 : ℝ)|=(2967357571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4843159419/10000000000 : ℝ)|^4465 ≤ (39032547030043/100000000000000 : ℝ)^3441
        have hw : |(4843159419/10000000000 : ℝ)|=(4843159419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1484_s0_1 (p : ℝ) (hpa : (4463/1024 : ℝ) ≤ p) (hpb : p ≤ (4465/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2742048967/5000000000 : ℝ)*x 0 + (-291252767/1250000000 : ℝ)*x 1 + (151348733/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2742048967/5000000000 : ℝ)^4465 ≤ (22931690318311/50000000000000 : ℝ)^3441 := by
    have hnat : (2742048967 : ℕ)^4465*50000000000000^3441 ≤ 22931690318311^3441*5000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2742048967 5000000000 22931690318311 50000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (291252767/1250000000 : ℝ)^4465 ≤ (15104071932957/100000000000000 : ℝ)^3441 := by
    have hnat : (291252767 : ℕ)^4465*100000000000000^3441 ≤ 15104071932957^3441*1250000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      291252767 1250000000 15104071932957 100000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (151348733/312500000 : ℝ)^4465 ≤ (39032547416977/100000000000000 : ℝ)^3441 := by
    have hnat : (151348733 : ℕ)^4465*100000000000000^3441 ≤ 39032547416977^3441*312500000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      151348733 312500000 39032547416977 100000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4465/1024 : ℝ)) 4465 3441 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2742048967/5000000000 : ℝ), (-291252767/1250000000 : ℝ), (151348733/312500000 : ℝ)] ![(22931690318311/50000000000000 : ℝ), (15104071932957/100000000000000 : ℝ), (39032547416977/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2742048967/5000000000 : ℝ)|^4465 ≤ (22931690318311/50000000000000 : ℝ)^3441
        have hw : |(2742048967/5000000000 : ℝ)|=(2742048967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-291252767/1250000000 : ℝ)|^4465 ≤ (15104071932957/100000000000000 : ℝ)^3441
        have hw : |(-291252767/1250000000 : ℝ)|=(291252767/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(151348733/312500000 : ℝ)|^4465 ≤ (39032547416977/100000000000000 : ℝ)^3441
        have hw : |(151348733/312500000 : ℝ)|=(151348733/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1484_s0_2 (p : ℝ) (hpa : (4463/1024 : ℝ) ≤ p) (hpb : p ≤ (4465/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5484097837/10000000000 : ℝ)*x 0 + (484315951/1000000000 : ℝ)*x 1 + (-1165011097/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5484097837/10000000000 : ℝ)^4465 ≤ (5732922448001/12500000000000 : ℝ)^3441 := by
    have hnat : (5484097837 : ℕ)^4465*12500000000000^3441 ≤ 5732922448001^3441*10000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5484097837 10000000000 5732922448001 12500000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (484315951/1000000000 : ℝ)^4465 ≤ (39032547981691/100000000000000 : ℝ)^3441 := by
    have hnat : (484315951 : ℕ)^4465*100000000000000^3441 ≤ 39032547981691^3441*1000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      484315951 1000000000 39032547981691 100000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1165011097/5000000000 : ℝ)^4465 ≤ (15104072420821/100000000000000 : ℝ)^3441 := by
    have hnat : (1165011097 : ℕ)^4465*100000000000000^3441 ≤ 15104072420821^3441*5000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1165011097 5000000000 15104072420821 100000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4465/1024 : ℝ)) 4465 3441 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5484097837/10000000000 : ℝ), (484315951/1000000000 : ℝ), (-1165011097/5000000000 : ℝ)] ![(5732922448001/12500000000000 : ℝ), (39032547981691/100000000000000 : ℝ), (15104072420821/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5484097837/10000000000 : ℝ)|^4465 ≤ (5732922448001/12500000000000 : ℝ)^3441
        have hw : |(5484097837/10000000000 : ℝ)|=(5484097837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(484315951/1000000000 : ℝ)|^4465 ≤ (39032547981691/100000000000000 : ℝ)^3441
        have hw : |(484315951/1000000000 : ℝ)|=(484315951/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1165011097/5000000000 : ℝ)|^4465 ≤ (15104072420821/100000000000000 : ℝ)^3441
        have hw : |(-1165011097/5000000000 : ℝ)|=(1165011097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1484_s0_3 (p : ℝ) (hpa : (4463/1024 : ℝ) ≤ p) (hpb : p ≤ (4465/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4152781187/10000000000 : ℝ)*x 0 + (1545700269/5000000000 : ℝ)*x 1 + (551783947/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4152781187/10000000000 : ℝ)^4465 ≤ (1278855143877/4000000000000 : ℝ)^3441 := by
    have hnat : (4152781187 : ℕ)^4465*4000000000000^3441 ≤ 1278855143877^3441*10000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4152781187 10000000000 1278855143877 4000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1545700269/5000000000 : ℝ)^4465 ≤ (21798753114101/100000000000000 : ℝ)^3441 := by
    have hnat : (1545700269 : ℕ)^4465*100000000000000^3441 ≤ 21798753114101^3441*5000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1545700269 5000000000 21798753114101 100000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (551783947/1000000000 : ℝ)^4465 ≤ (1444683383669/3125000000000 : ℝ)^3441 := by
    have hnat : (551783947 : ℕ)^4465*3125000000000^3441 ≤ 1444683383669^3441*1000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551783947 1000000000 1444683383669 3125000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4465/1024 : ℝ)) 4465 3441 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4152781187/10000000000 : ℝ), (1545700269/5000000000 : ℝ), (551783947/1000000000 : ℝ)] ![(1278855143877/4000000000000 : ℝ), (21798753114101/100000000000000 : ℝ), (1444683383669/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4152781187/10000000000 : ℝ)|^4465 ≤ (1278855143877/4000000000000 : ℝ)^3441
        have hw : |(4152781187/10000000000 : ℝ)|=(4152781187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1545700269/5000000000 : ℝ)|^4465 ≤ (21798753114101/100000000000000 : ℝ)^3441
        have hw : |(1545700269/5000000000 : ℝ)|=(1545700269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(551783947/1000000000 : ℝ)|^4465 ≤ (1444683383669/3125000000000 : ℝ)^3441
        have hw : |(551783947/1000000000 : ℝ)|=(551783947/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1484_s0_4 (p : ℝ) (hpa : (4463/1024 : ℝ) ≤ p) (hpb : p ≤ (4465/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-107481581/625000000 : ℝ)*x 0 + (4871143647/10000000000 : ℝ)*x 1 + (1181144989/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107481581/625000000 : ℝ)^4465 ≤ (5092187599709/50000000000000 : ℝ)^3441 := by
    have hnat : (107481581 : ℕ)^4465*50000000000000^3441 ≤ 5092187599709^3441*625000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107481581 625000000 5092187599709 50000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4871143647/10000000000 : ℝ)^4465 ≤ (39325448105931/100000000000000 : ℝ)^3441 := by
    have hnat : (4871143647 : ℕ)^4465*100000000000000^3441 ≤ 39325448105931^3441*10000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4871143647 10000000000 39325448105931 100000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1181144989/2000000000 : ℝ)^4465 ≤ (12622544170987/25000000000000 : ℝ)^3441 := by
    have hnat : (1181144989 : ℕ)^4465*25000000000000^3441 ≤ 12622544170987^3441*2000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1181144989 2000000000 12622544170987 25000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4465/1024 : ℝ)) 4465 3441 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-107481581/625000000 : ℝ), (4871143647/10000000000 : ℝ), (1181144989/2000000000 : ℝ)] ![(5092187599709/50000000000000 : ℝ), (39325448105931/100000000000000 : ℝ), (12622544170987/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-107481581/625000000 : ℝ)|^4465 ≤ (5092187599709/50000000000000 : ℝ)^3441
        have hw : |(-107481581/625000000 : ℝ)|=(107481581/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4871143647/10000000000 : ℝ)|^4465 ≤ (39325448105931/100000000000000 : ℝ)^3441
        have hw : |(4871143647/10000000000 : ℝ)|=(4871143647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1181144989/2000000000 : ℝ)|^4465 ≤ (12622544170987/25000000000000 : ℝ)^3441
        have hw : |(1181144989/2000000000 : ℝ)|=(1181144989/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1484_s0_5 (p : ℝ) (hpa : (4463/1024 : ℝ) ≤ p) (hpb : p ≤ (4465/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5186027181/10000000000 : ℝ)*x 0 + (-1267456517/10000000000 : ℝ)*x 1 + (1476431249/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5186027181/10000000000 : ℝ)^4465 ≤ (10663826682633/25000000000000 : ℝ)^3441 := by
    have hnat : (5186027181 : ℕ)^4465*25000000000000^3441 ≤ 10663826682633^3441*10000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5186027181 10000000000 10663826682633 25000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1267456517/10000000000 : ℝ)^4465 ≤ (6854516010367/100000000000000 : ℝ)^3441 := by
    have hnat : (1267456517 : ℕ)^4465*100000000000000^3441 ≤ 6854516010367^3441*10000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1267456517 10000000000 6854516010367 100000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1476431249/2500000000 : ℝ)^4465 ≤ (50490177249719/100000000000000 : ℝ)^3441 := by
    have hnat : (1476431249 : ℕ)^4465*100000000000000^3441 ≤ 50490177249719^3441*2500000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1476431249 2500000000 50490177249719 100000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4465/1024 : ℝ)) 4465 3441 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5186027181/10000000000 : ℝ), (-1267456517/10000000000 : ℝ), (1476431249/2500000000 : ℝ)] ![(10663826682633/25000000000000 : ℝ), (6854516010367/100000000000000 : ℝ), (50490177249719/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5186027181/10000000000 : ℝ)|^4465 ≤ (10663826682633/25000000000000 : ℝ)^3441
        have hw : |(5186027181/10000000000 : ℝ)|=(5186027181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1267456517/10000000000 : ℝ)|^4465 ≤ (6854516010367/100000000000000 : ℝ)^3441
        have hw : |(-1267456517/10000000000 : ℝ)|=(1267456517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1476431249/2500000000 : ℝ)|^4465 ≤ (50490177249719/100000000000000 : ℝ)^3441
        have hw : |(1476431249/2500000000 : ℝ)|=(1476431249/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1484_s0_6 (p : ℝ) (hpa : (4463/1024 : ℝ) ≤ p) (hpb : p ≤ (4465/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5186027239/10000000000 : ℝ)*x 0 + (5905724869/10000000000 : ℝ)*x 1 + (-316864157/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5186027239/10000000000 : ℝ)^4465 ≤ (853106146991/2000000000000 : ℝ)^3441 := by
    have hnat : (5186027239 : ℕ)^4465*2000000000000^3441 ≤ 853106146991^3441*10000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5186027239 10000000000 853106146991 2000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5905724869/10000000000 : ℝ)^4465 ≤ (50490175840839/100000000000000 : ℝ)^3441 := by
    have hnat : (5905724869 : ℕ)^4465*100000000000000^3441 ≤ 50490175840839^3441*10000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5905724869 10000000000 50490175840839 100000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (316864157/2500000000 : ℝ)^4465 ≤ (3427258394653/50000000000000 : ℝ)^3441 := by
    have hnat : (316864157 : ℕ)^4465*50000000000000^3441 ≤ 3427258394653^3441*2500000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      316864157 2500000000 3427258394653 50000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4465/1024 : ℝ)) 4465 3441 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5186027239/10000000000 : ℝ), (5905724869/10000000000 : ℝ), (-316864157/2500000000 : ℝ)] ![(853106146991/2000000000000 : ℝ), (50490175840839/100000000000000 : ℝ), (3427258394653/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5186027239/10000000000 : ℝ)|^4465 ≤ (853106146991/2000000000000 : ℝ)^3441
        have hw : |(5186027239/10000000000 : ℝ)|=(5186027239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5905724869/10000000000 : ℝ)|^4465 ≤ (50490175840839/100000000000000 : ℝ)^3441
        have hw : |(5905724869/10000000000 : ℝ)|=(5905724869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-316864157/2500000000 : ℝ)|^4465 ≤ (3427258394653/50000000000000 : ℝ)^3441
        have hw : |(-316864157/2500000000 : ℝ)|=(316864157/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1484_s0_7 (p : ℝ) (hpa : (4463/1024 : ℝ) ≤ p) (hpb : p ≤ (4465/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (208057771/500000000 : ℝ)*x 0 + (545563267/1000000000 : ℝ)*x 1 + (1577921769/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (208057771/500000000 : ℝ)^4465 ≤ (8013765261127/25000000000000 : ℝ)^3441 := by
    have hnat : (208057771 : ℕ)^4465*25000000000000^3441 ≤ 8013765261127^3441*500000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208057771 500000000 8013765261127 25000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (545563267/1000000000 : ℝ)^4465 ≤ (22777361538721/50000000000000 : ℝ)^3441 := by
    have hnat : (545563267 : ℕ)^4465*50000000000000^3441 ≤ 22777361538721^3441*1000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545563267 1000000000 22777361538721 50000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1577921769/5000000000 : ℝ)^4465 ≤ (22390215870483/100000000000000 : ℝ)^3441 := by
    have hnat : (1577921769 : ℕ)^4465*100000000000000^3441 ≤ 22390215870483^3441*5000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1577921769 5000000000 22390215870483 100000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4465/1024 : ℝ)) 4465 3441 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(208057771/500000000 : ℝ), (545563267/1000000000 : ℝ), (1577921769/5000000000 : ℝ)] ![(8013765261127/25000000000000 : ℝ), (22777361538721/50000000000000 : ℝ), (22390215870483/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(208057771/500000000 : ℝ)|^4465 ≤ (8013765261127/25000000000000 : ℝ)^3441
        have hw : |(208057771/500000000 : ℝ)|=(208057771/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(545563267/1000000000 : ℝ)|^4465 ≤ (22777361538721/50000000000000 : ℝ)^3441
        have hw : |(545563267/1000000000 : ℝ)|=(545563267/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1577921769/5000000000 : ℝ)|^4465 ≤ (22390215870483/100000000000000 : ℝ)^3441
        have hw : |(1577921769/5000000000 : ℝ)|=(1577921769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1484_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4463/1024 : ℝ) ≤ p) (hpb : p ≤ (4465/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80572949/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (123/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (6463/25000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4463/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4463 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4463*1^1024 ≤ 0^1024*1^4463 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4463 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4463 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4463/1024 : ℝ) ≤ (115212315581182757/6250000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4463 ≤ (115212315581182757/6250000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4463*6250000000000000000^1024 ≤ 115212315581182757^1024*5^4463 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 115212315581182757 6250000000000000000 4463 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (115212315581182757/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4463 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4463/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4463 := by
      have hnat : (1 : ℕ)^1024*1^4463 ≤ 1^4463*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4463 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4463 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6365212315581182757/6250000000000000000 : ℝ) ≤ (10041998121671639/10000000000000000 : ℝ) ^ (4463/1024 : ℝ) := by
    have hpowers : (6365212315581182757/6250000000000000000 : ℝ)^1024 ≤ (10041998121671639/10000000000000000 : ℝ)^4463 := by
      have hnat : (6365212315581182757 : ℕ)^1024*10000000000000000^4463 ≤ 10041998121671639^4463*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6365212315581182757 6250000000000000000 10041998121671639 10000000000000000 1024 4463 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10041998121671639/10000000000000000 : ℝ)) (X := (6365212315581182757/6250000000000000000 : ℝ)) (by norm_num) 4463 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3240212315581182757/3125000000000000000 : ℝ) ≤ (5041998121671639/5000000000000000 : ℝ) ^ (4463/1024 : ℝ) := by
    have hpowers : (3240212315581182757/3125000000000000000 : ℝ)^1024 ≤ (5041998121671639/5000000000000000 : ℝ)^4463 := by
      have hnat : (3240212315581182757 : ℕ)^1024*5000000000000000^4463 ≤ 5041998121671639^4463*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3240212315581182757 3125000000000000000 5041998121671639 5000000000000000 1024 4463 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5041998121671639/5000000000000000 : ℝ)) (X := (3240212315581182757/3125000000000000000 : ℝ)) (by norm_num) 4463 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(41998121671639/4000000000000000 : ℝ)*(0 : ℝ))^(4463/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(41998121671639/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(115212315581182757/6250000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(41998121671639/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4463/1024 : ℝ) := by
    rw [show (1 : ℝ)+(41998121671639/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10041998121671639/10000000000000000 : ℝ) by norm_num, show 1+(115212315581182757/6250000000000000000 : ℝ)+(0 : ℝ)=(6365212315581182757/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(115212315581182757/6250000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(41998121671639/4000000000000000 : ℝ)*(2/5 : ℝ))^(4463/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(41998121671639/4000000000000000 : ℝ)*(2/5 : ℝ)=(5041998121671639/5000000000000000 : ℝ) by norm_num, show 1+2*(115212315581182757/6250000000000000000 : ℝ)=(3240212315581182757/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(41998121671639/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4463/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (41998121671639/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(41998121671639/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4463/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (41998121671639/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(41998121671639/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4463/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (41998121671639/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-857969179/5000000000 : ℝ)*X 0 0+(2967357571/5000000000 : ℝ)*X 0 1+(4843159419/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1484_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2742048967/5000000000 : ℝ)*X 1 0+(-291252767/1250000000 : ℝ)*X 1 1+(151348733/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1484_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5484097837/10000000000 : ℝ)*X 2 0+(484315951/1000000000 : ℝ)*X 2 1+(-1165011097/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1484_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4152781187/10000000000 : ℝ)*X 0 0+(1545700269/5000000000 : ℝ)*X 0 1+(551783947/1000000000 : ℝ)*X 0 2+(4152781187/10000000000 : ℝ)*X 1 0+(1545700269/5000000000 : ℝ)*X 1 1+(551783947/1000000000 : ℝ)*X 1 2+(4152781187/10000000000 : ℝ)*X 2 0+(1545700269/5000000000 : ℝ)*X 2 1+(551783947/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1484_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-107481581/625000000 : ℝ)*X 0 0+(4871143647/10000000000 : ℝ)*X 0 1+(1181144989/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1484_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5186027181/10000000000 : ℝ)*X 1 0+(-1267456517/10000000000 : ℝ)*X 1 1+(1476431249/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1484_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5186027239/10000000000 : ℝ)*X 2 0+(5905724869/10000000000 : ℝ)*X 2 1+(-316864157/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1484_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((208057771/500000000 : ℝ)*X 0 0+(545563267/1000000000 : ℝ)*X 0 1+(1577921769/5000000000 : ℝ)*X 0 2+(208057771/500000000 : ℝ)*X 1 0+(545563267/1000000000 : ℝ)*X 1 1+(1577921769/5000000000 : ℝ)*X 1 2+(208057771/500000000 : ℝ)*X 2 0+(545563267/1000000000 : ℝ)*X 2 1+(1577921769/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1484_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (20037928378179466463889/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (17511749/5000000000000 : ℝ)*(base19) + (66287517/20000000000000 : ℝ)*(base23) + (7120257/12500000000000 : ℝ)*(upper3) + (284451/20000000000000 : ℝ)*(upper4) + (3384389/10000000000000 : ℝ)*(upper5) + (83015871468417/12500000000000 : ℝ)*(major0) + (83015871468417/12500000000000 : ℝ)*(major1) + (83015871468417/12500000000000 : ℝ)*(major2) + (114515617431511/12500000000000 : ℝ)*(sp0) + (57257861549817/6250000000000 : ℝ)*(sp1) + (458062901797233/50000000000000 : ℝ)*(sp2) + (412127127888271/100000000000000 : ℝ)*(sp3) + (1195579963/100000000000000 : ℝ)*(sp4) + (627139869/100000000000000 : ℝ)*(sp7) + (20606387751407/5000000000000 : ℝ)*(f.failure) + (916126135032051/100000000000000 : ℝ)*(f.sum) + (37488919499537/25000000000000000000000000000 : ℝ)*base66 + (180028053875463/50000000000000000000000000000 : ℝ)*base67 + (198626706824537/50000000000000000000000000000 : ℝ)*base70 + (328190712124537/50000000000000000000000000000 : ℝ)*base72 + (128711027225463/25000000000000000000000000000 : ℝ)*base73 + (417137653074537/50000000000000000000000000000 : ℝ)*base76 + (160756751824537/50000000000000000000000000000 : ℝ)*base78 + (224717548725463/50000000000000000000000000000 : ℝ)*base79 + (71360729074537/25000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (889243/250000000000000000000 : ℝ)*base89 + (889243/250000000000000000000 : ℝ)*base91 + (889243/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (87048625524742210695009/10000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1931782787/100000000000000 : ℝ)*(base19) + (1956607423/100000000000000 : ℝ)*(base23) + (159631583/100000000000000 : ℝ)*(base32) + (36209279/12500000000000 : ℝ)*(upper3) + (18715311/10000000000000 : ℝ)*(upper5) + (35034910139277/5000000000000 : ℝ)*(major0) + (35034910139277/5000000000000 : ℝ)*(major1) + (35034910139277/5000000000000 : ℝ)*(major2) + (2381877979/50000000000000 : ℝ)*(sp1) + (1251898383/25000000000000 : ℝ)*(sp2) + (483286937880167/50000000000000 : ℝ)*(sp4) + (966567180221589/100000000000000 : ℝ)*(sp5) + (966566911559379/100000000000000 : ℝ)*(sp6) + (217411040008537/50000000000000 : ℝ)*(sp7) + (434822239648657/100000000000000 : ℝ)*(f.failure) + (483286937880167/50000000000000 : ℝ)*(f.sum) + (6698428705003/10000000000000000000000000000 : ℝ)*base65 + (172308562694997/20000000000000000000000000000 : ℝ)*base68 + (50848437974997/20000000000000000000000000000 : ℝ)*base70 + (856701645003/20000000000000000000000000000 : ℝ)*base71 + (45172206924997/10000000000000000000000000000 : ℝ)*base74 + (124745355214997/20000000000000000000000000000 : ℝ)*base76 + (146569568034997/20000000000000000000000000000 : ℝ)*base78 + (104150314154997/20000000000000000000000000000 : ℝ)*base80 + (3383504945003/10000000000000000000000000000 : ℝ)*base81 + (18379493/5000000000000000000000 : ℝ)*base89 + (18379493/5000000000000000000000 : ℝ)*base91 + (18379493/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1484_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4463/1024 : ℝ) ≤ p) (hpb : p ≤ (4465/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80572949/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (123/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6463/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1484_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1484_s1_0 (p : ℝ) (hpa : (4463/1024 : ℝ) ≤ p) (hpb : p ≤ (4465/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1877242707/10000000000 : ℝ)*x 0 + (5589858117/10000000000 : ℝ)*x 1 + (1271116061/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1877242707/10000000000 : ℝ)^4465 ≤ (5705568077311/50000000000000 : ℝ)^3441 := by
    have hnat : (1877242707 : ℕ)^4465*50000000000000^3441 ≤ 5705568077311^3441*10000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1877242707 10000000000 5705568077311 50000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5589858117/10000000000 : ℝ)^4465 ≤ (47014336562127/100000000000000 : ℝ)^3441 := by
    have hnat : (5589858117 : ℕ)^4465*100000000000000^3441 ≤ 47014336562127^3441*10000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5589858117 10000000000 47014336562127 100000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1271116061/2500000000 : ℝ)^4465 ≤ (831490545373/2000000000000 : ℝ)^3441 := by
    have hnat : (1271116061 : ℕ)^4465*2000000000000^3441 ≤ 831490545373^3441*2500000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1271116061 2500000000 831490545373 2000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4465/1024 : ℝ)) 4465 3441 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1877242707/10000000000 : ℝ), (5589858117/10000000000 : ℝ), (1271116061/2500000000 : ℝ)] ![(5705568077311/50000000000000 : ℝ), (47014336562127/100000000000000 : ℝ), (831490545373/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1877242707/10000000000 : ℝ)|^4465 ≤ (5705568077311/50000000000000 : ℝ)^3441
        have hw : |(-1877242707/10000000000 : ℝ)|=(1877242707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5589858117/10000000000 : ℝ)|^4465 ≤ (47014336562127/100000000000000 : ℝ)^3441
        have hw : |(5589858117/10000000000 : ℝ)|=(5589858117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1271116061/2500000000 : ℝ)|^4465 ≤ (831490545373/2000000000000 : ℝ)^3441
        have hw : |(1271116061/2500000000 : ℝ)|=(1271116061/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1484_s1_1 (p : ℝ) (hpa : (4463/1024 : ℝ) ≤ p) (hpb : p ≤ (4465/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1347952481/2500000000 : ℝ)*x 0 + (-2144333671/10000000000 : ℝ)*x 1 + (5084465573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1347952481/2500000000 : ℝ)^4465 ≤ (44864416739567/100000000000000 : ℝ)^3441 := by
    have hnat : (1347952481 : ℕ)^4465*100000000000000^3441 ≤ 44864416739567^3441*2500000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347952481 2500000000 44864416739567 100000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2144333671/10000000000 : ℝ)^4465 ≤ (6780520941213/50000000000000 : ℝ)^3441 := by
    have hnat : (2144333671 : ℕ)^4465*50000000000000^3441 ≤ 6780520941213^3441*10000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2144333671 10000000000 6780520941213 50000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5084465573/10000000000 : ℝ)^4465 ≤ (8314908273891/20000000000000 : ℝ)^3441 := by
    have hnat : (5084465573 : ℕ)^4465*20000000000000^3441 ≤ 8314908273891^3441*10000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5084465573 10000000000 8314908273891 20000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4465/1024 : ℝ)) 4465 3441 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1347952481/2500000000 : ℝ), (-2144333671/10000000000 : ℝ), (5084465573/10000000000 : ℝ)] ![(44864416739567/100000000000000 : ℝ), (6780520941213/50000000000000 : ℝ), (8314908273891/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1347952481/2500000000 : ℝ)|^4465 ≤ (44864416739567/100000000000000 : ℝ)^3441
        have hw : |(1347952481/2500000000 : ℝ)|=(1347952481/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2144333671/10000000000 : ℝ)|^4465 ≤ (6780520941213/50000000000000 : ℝ)^3441
        have hw : |(-2144333671/10000000000 : ℝ)|=(2144333671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5084465573/10000000000 : ℝ)|^4465 ≤ (8314908273891/20000000000000 : ℝ)^3441
        have hw : |(5084465573/10000000000 : ℝ)|=(5084465573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1484_s1_2 (p : ℝ) (hpa : (4463/1024 : ℝ) ≤ p) (hpb : p ≤ (4465/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2695905539/5000000000 : ℝ)*x 0 + (5084464983/10000000000 : ℝ)*x 1 + (-1072166457/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2695905539/5000000000 : ℝ)^4465 ≤ (22432214599669/50000000000000 : ℝ)^3441 := by
    have hnat : (2695905539 : ℕ)^4465*50000000000000^3441 ≤ 22432214599669^3441*5000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695905539 5000000000 22432214599669 50000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5084464983/10000000000 : ℝ)^4465 ≤ (324801055543/781250000000 : ℝ)^3441 := by
    have hnat : (5084464983 : ℕ)^4465*781250000000^3441 ≤ 324801055543^3441*10000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5084464983 10000000000 324801055543 781250000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1072166457/5000000000 : ℝ)^4465 ≤ (13561035670399/100000000000000 : ℝ)^3441 := by
    have hnat : (1072166457 : ℕ)^4465*100000000000000^3441 ≤ 13561035670399^3441*5000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072166457 5000000000 13561035670399 100000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4465/1024 : ℝ)) 4465 3441 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2695905539/5000000000 : ℝ), (5084464983/10000000000 : ℝ), (-1072166457/5000000000 : ℝ)] ![(22432214599669/50000000000000 : ℝ), (324801055543/781250000000 : ℝ), (13561035670399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2695905539/5000000000 : ℝ)|^4465 ≤ (22432214599669/50000000000000 : ℝ)^3441
        have hw : |(2695905539/5000000000 : ℝ)|=(2695905539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5084464983/10000000000 : ℝ)|^4465 ≤ (324801055543/781250000000 : ℝ)^3441
        have hw : |(5084464983/10000000000 : ℝ)|=(5084464983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1072166457/5000000000 : ℝ)|^4465 ≤ (13561035670399/100000000000000 : ℝ)^3441
        have hw : |(-1072166457/5000000000 : ℝ)|=(1072166457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1484_s1_3 (p : ℝ) (hpa : (4463/1024 : ℝ) ≤ p) (hpb : p ≤ (4465/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4259810721/10000000000 : ℝ)*x 0 + (3730086321/10000000000 : ℝ)*x 1 + (2426766761/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4259810721/10000000000 : ℝ)^4465 ≤ (8261165931001/25000000000000 : ℝ)^3441 := by
    have hnat : (4259810721 : ℕ)^4465*25000000000000^3441 ≤ 8261165931001^3441*10000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4259810721 10000000000 8261165931001 25000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3730086321/10000000000 : ℝ)^4465 ≤ (13907132861803/50000000000000 : ℝ)^3441 := by
    have hnat : (3730086321 : ℕ)^4465*50000000000000^3441 ≤ 13907132861803^3441*10000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3730086321 10000000000 13907132861803 50000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2426766761/5000000000 : ℝ)^4465 ≤ (19570535265979/50000000000000 : ℝ)^3441 := by
    have hnat : (2426766761 : ℕ)^4465*50000000000000^3441 ≤ 19570535265979^3441*5000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2426766761 5000000000 19570535265979 50000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4465/1024 : ℝ)) 4465 3441 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4259810721/10000000000 : ℝ), (3730086321/10000000000 : ℝ), (2426766761/5000000000 : ℝ)] ![(8261165931001/25000000000000 : ℝ), (13907132861803/50000000000000 : ℝ), (19570535265979/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4259810721/10000000000 : ℝ)|^4465 ≤ (8261165931001/25000000000000 : ℝ)^3441
        have hw : |(4259810721/10000000000 : ℝ)|=(4259810721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3730086321/10000000000 : ℝ)|^4465 ≤ (13907132861803/50000000000000 : ℝ)^3441
        have hw : |(3730086321/10000000000 : ℝ)|=(3730086321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2426766761/5000000000 : ℝ)|^4465 ≤ (19570535265979/50000000000000 : ℝ)^3441
        have hw : |(2426766761/5000000000 : ℝ)|=(2426766761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1484_s1_4 (p : ℝ) (hpa : (4463/1024 : ℝ) ≤ p) (hpb : p ≤ (4465/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-234700333/1250000000 : ℝ)*x 0 + (5090345047/10000000000 : ℝ)*x 1 + (697984843/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (234700333/1250000000 : ℝ)^4465 ≤ (114139754349/1000000000000 : ℝ)^3441 := by
    have hnat : (234700333 : ℕ)^4465*1000000000000^3441 ≤ 114139754349^3441*1250000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      234700333 1250000000 114139754349 1000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5090345047/10000000000 : ℝ)^4465 ≤ (20818466915393/50000000000000 : ℝ)^3441 := by
    have hnat : (5090345047 : ℕ)^4465*50000000000000^3441 ≤ 20818466915393^3441*10000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5090345047 10000000000 20818466915393 50000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (697984843/1250000000 : ℝ)^4465 ≤ (46949090723469/100000000000000 : ℝ)^3441 := by
    have hnat : (697984843 : ℕ)^4465*100000000000000^3441 ≤ 46949090723469^3441*1250000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      697984843 1250000000 46949090723469 100000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4465/1024 : ℝ)) 4465 3441 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-234700333/1250000000 : ℝ), (5090345047/10000000000 : ℝ), (697984843/1250000000 : ℝ)] ![(114139754349/1000000000000 : ℝ), (20818466915393/50000000000000 : ℝ), (46949090723469/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-234700333/1250000000 : ℝ)|^4465 ≤ (114139754349/1000000000000 : ℝ)^3441
        have hw : |(-234700333/1250000000 : ℝ)|=(234700333/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5090345047/10000000000 : ℝ)|^4465 ≤ (20818466915393/50000000000000 : ℝ)^3441
        have hw : |(5090345047/10000000000 : ℝ)|=(5090345047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(697984843/1250000000 : ℝ)|^4465 ≤ (46949090723469/100000000000000 : ℝ)^3441
        have hw : |(697984843/1250000000 : ℝ)|=(697984843/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1484_s1_5 (p : ℝ) (hpa : (4463/1024 : ℝ) ≤ p) (hpb : p ≤ (4465/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5259160223/10000000000 : ℝ)*x 0 + (-102807487/625000000 : ℝ)*x 1 + (1116775759/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5259160223/10000000000 : ℝ)^4465 ≤ (10859366881199/25000000000000 : ℝ)^3441 := by
    have hnat : (5259160223 : ℕ)^4465*25000000000000^3441 ≤ 10859366881199^3441*10000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5259160223 10000000000 10859366881199 25000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (102807487/625000000 : ℝ)^4465 ≤ (961344117269/10000000000000 : ℝ)^3441 := by
    have hnat : (102807487 : ℕ)^4465*10000000000000^3441 ≤ 961344117269^3441*625000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      102807487 625000000 961344117269 10000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1116775759/2000000000 : ℝ)^4465 ≤ (46949091279883/100000000000000 : ℝ)^3441 := by
    have hnat : (1116775759 : ℕ)^4465*100000000000000^3441 ≤ 46949091279883^3441*2000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1116775759 2000000000 46949091279883 100000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4465/1024 : ℝ)) 4465 3441 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5259160223/10000000000 : ℝ), (-102807487/625000000 : ℝ), (1116775759/2000000000 : ℝ)] ![(10859366881199/25000000000000 : ℝ), (961344117269/10000000000000 : ℝ), (46949091279883/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5259160223/10000000000 : ℝ)|^4465 ≤ (10859366881199/25000000000000 : ℝ)^3441
        have hw : |(5259160223/10000000000 : ℝ)|=(5259160223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-102807487/625000000 : ℝ)|^4465 ≤ (961344117269/10000000000000 : ℝ)^3441
        have hw : |(-102807487/625000000 : ℝ)|=(102807487/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1116775759/2000000000 : ℝ)|^4465 ≤ (46949091279883/100000000000000 : ℝ)^3441
        have hw : |(1116775759/2000000000 : ℝ)|=(1116775759/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1484_s1_6 (p : ℝ) (hpa : (4463/1024 : ℝ) ≤ p) (hpb : p ≤ (4465/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (164348757/312500000 : ℝ)*x 0 + (5583878773/10000000000 : ℝ)*x 1 + (-1644919823/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (164348757/312500000 : ℝ)^4465 ≤ (43437467535513/100000000000000 : ℝ)^3441 := by
    have hnat : (164348757 : ℕ)^4465*100000000000000^3441 ≤ 43437467535513^3441*312500000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164348757 312500000 43437467535513 100000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5583878773/10000000000 : ℝ)^4465 ≤ (23474545519931/50000000000000 : ℝ)^3441 := by
    have hnat : (5583878773 : ℕ)^4465*50000000000000^3441 ≤ 23474545519931^3441*10000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5583878773 10000000000 23474545519931 50000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1644919823/10000000000 : ℝ)^4465 ≤ (9613441407779/100000000000000 : ℝ)^3441 := by
    have hnat : (1644919823 : ℕ)^4465*100000000000000^3441 ≤ 9613441407779^3441*10000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1644919823 10000000000 9613441407779 100000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4465/1024 : ℝ)) 4465 3441 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(164348757/312500000 : ℝ), (5583878773/10000000000 : ℝ), (-1644919823/10000000000 : ℝ)] ![(43437467535513/100000000000000 : ℝ), (23474545519931/50000000000000 : ℝ), (9613441407779/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(164348757/312500000 : ℝ)|^4465 ≤ (43437467535513/100000000000000 : ℝ)^3441
        have hw : |(164348757/312500000 : ℝ)|=(164348757/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5583878773/10000000000 : ℝ)|^4465 ≤ (23474545519931/50000000000000 : ℝ)^3441
        have hw : |(5583878773/10000000000 : ℝ)|=(5583878773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1644919823/10000000000 : ℝ)|^4465 ≤ (9613441407779/100000000000000 : ℝ)^3441
        have hw : |(-1644919823/10000000000 : ℝ)|=(1644919823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1484_s1_7 (p : ℝ) (hpa : (4463/1024 : ℝ) ≤ p) (hpb : p ≤ (4465/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (170424467/400000000 : ℝ)*x 0 + (2420231161/5000000000 : ℝ)*x 1 + (1871688417/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (170424467/400000000 : ℝ)^4465 ≤ (33052726183563/100000000000000 : ℝ)^3441 := by
    have hnat : (170424467 : ℕ)^4465*100000000000000^3441 ≤ 33052726183563^3441*400000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170424467 400000000 33052726183563 100000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2420231161/5000000000 : ℝ)^4465 ≤ (9751086004529/25000000000000 : ℝ)^3441 := by
    have hnat : (2420231161 : ℕ)^4465*25000000000000^3441 ≤ 9751086004529^3441*5000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2420231161 5000000000 9751086004529 25000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1871688417/5000000000 : ℝ)^4465 ≤ (6985732445479/25000000000000 : ℝ)^3441 := by
    have hnat : (1871688417 : ℕ)^4465*25000000000000^3441 ≤ 6985732445479^3441*5000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1871688417 5000000000 6985732445479 25000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4465/1024 : ℝ)) 4465 3441 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(170424467/400000000 : ℝ), (2420231161/5000000000 : ℝ), (1871688417/5000000000 : ℝ)] ![(33052726183563/100000000000000 : ℝ), (9751086004529/25000000000000 : ℝ), (6985732445479/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(170424467/400000000 : ℝ)|^4465 ≤ (33052726183563/100000000000000 : ℝ)^3441
        have hw : |(170424467/400000000 : ℝ)|=(170424467/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2420231161/5000000000 : ℝ)|^4465 ≤ (9751086004529/25000000000000 : ℝ)^3441
        have hw : |(2420231161/5000000000 : ℝ)|=(2420231161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1871688417/5000000000 : ℝ)|^4465 ≤ (6985732445479/25000000000000 : ℝ)^3441
        have hw : |(1871688417/5000000000 : ℝ)|=(1871688417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1484_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4463/1024 : ℝ) ≤ p) (hpb : p ≤ (4465/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80572949/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6463/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (123/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (1991/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (18649/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6463/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (123/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6463/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (123/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6463/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (123/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6463/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (123/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6463/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (123/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6463/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (123/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (123/5000 : ℝ) ^ (4463/1024 : ℝ) ≤ (4853154187269/50000000000000000000 : ℝ) := by
    have hpowers : (123/5000 : ℝ)^4463 ≤ (4853154187269/50000000000000000000 : ℝ)^1024 := by
      have hnat : (123 : ℕ)^4463*50000000000000000000^1024 ≤ 4853154187269^1024*5000^4463 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        123 5000 4853154187269 50000000000000000000 4463 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (123/5000 : ℝ)) (X := (4853154187269/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4463 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (6463/25000 : ℝ) ^ (4463/1024 : ℝ) ≤ (275052381360056741/100000000000000000000 : ℝ) := by
    have hpowers : (6463/25000 : ℝ)^4463 ≤ (275052381360056741/100000000000000000000 : ℝ)^1024 := by
      have hnat : (6463 : ℕ)^4463*100000000000000000000^1024 ≤ 275052381360056741^1024*25000^4463 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6463 25000 275052381360056741 100000000000000000000 4463 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6463/25000 : ℝ)) (X := (275052381360056741/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4463 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000004853154187269/25000000000000000000 : ℝ) ≤ (5000000222703541/5000000000000000 : ℝ) ^ (4463/1024 : ℝ) := by
    have hpowers : (25000004853154187269/25000000000000000000 : ℝ)^1024 ≤ (5000000222703541/5000000000000000 : ℝ)^4463 := by
      have hnat : (25000004853154187269 : ℕ)^1024*5000000000000000^4463 ≤ 5000000222703541^4463*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000004853154187269 25000000000000000000 5000000222703541 5000000000000000 1024 4463 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000222703541/5000000000000000 : ℝ)) (X := (25000004853154187269/25000000000000000000 : ℝ)) (by norm_num) 4463 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100275062087668431279/100000000000000000000 : ℝ) ≤ (5003152202180769/5000000000000000 : ℝ) ^ (4463/1024 : ℝ) := by
    have hpowers : (100275062087668431279/100000000000000000000 : ℝ)^1024 ≤ (5003152202180769/5000000000000000 : ℝ)^4463 := by
      have hnat : (100275062087668431279 : ℕ)^1024*5000000000000000^4463 ≤ 5003152202180769^4463*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100275062087668431279 100000000000000000000 5003152202180769 5000000000000000 1024 4463 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5003152202180769/5000000000000000 : ℝ)) (X := (100275062087668431279/100000000000000000000 : ℝ)) (by norm_num) 4463 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50275052381360056741/50000000000000000000 : ℝ) ≤ (5006304181657997/5000000000000000 : ℝ) ^ (4463/1024 : ℝ) := by
    have hpowers : (50275052381360056741/50000000000000000000 : ℝ)^1024 ≤ (5006304181657997/5000000000000000 : ℝ)^4463 := by
      have hnat : (50275052381360056741 : ℕ)^1024*5000000000000000^4463 ≤ 5006304181657997^4463*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50275052381360056741 50000000000000000000 5006304181657997 5000000000000000 1024 4463 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5006304181657997/5000000000000000 : ℝ)) (X := (50275052381360056741/50000000000000000000 : ℝ)) (by norm_num) 4463 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4853154187269/50000000000000000000 : ℝ) ≤ ((107485751351519549/107500000000000000 : ℝ)+2*(46352639371/17200000000000 : ℝ)*(123/5000 : ℝ))^(4463/1024 : ℝ) := by
    rw [show (107485751351519549/107500000000000000 : ℝ)+2*(46352639371/17200000000000 : ℝ)*(123/5000 : ℝ)=(5000000222703541/5000000000000000 : ℝ) by norm_num, show 1+2*(4853154187269/50000000000000000000 : ℝ)=(25000004853154187269/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(275052381360056741/100000000000000000000 : ℝ)+(4853154187269/50000000000000000000 : ℝ) ≤ ((107485751351519549/107500000000000000 : ℝ)+(46352639371/17200000000000 : ℝ)*((6463/25000 : ℝ)+(123/5000 : ℝ)))^(4463/1024 : ℝ) := by
    rw [show (107485751351519549/107500000000000000 : ℝ)+(46352639371/17200000000000 : ℝ)*((6463/25000 : ℝ)+(123/5000 : ℝ))=(5003152202180769/5000000000000000 : ℝ) by norm_num, show 1+(275052381360056741/100000000000000000000 : ℝ)+(4853154187269/50000000000000000000 : ℝ)=(100275062087668431279/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(275052381360056741/100000000000000000000 : ℝ) ≤ ((107485751351519549/107500000000000000 : ℝ)+2*(46352639371/17200000000000 : ℝ)*(6463/25000 : ℝ))^(4463/1024 : ℝ) := by
    rw [show (107485751351519549/107500000000000000 : ℝ)+2*(46352639371/17200000000000 : ℝ)*(6463/25000 : ℝ)=(5006304181657997/5000000000000000 : ℝ) by norm_num, show 1+2*(275052381360056741/100000000000000000000 : ℝ)=(50275052381360056741/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (107485751351519549/107500000000000000 : ℝ)*(X 1 0+X 2 0)+(46352639371/17200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4463/1024 : ℝ)) (lo := (123/5000 : ℝ)) (hi := (6463/25000 : ℝ)) (c := (107485751351519549/107500000000000000 : ℝ)) (alpha := (46352639371/17200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (107485751351519549/107500000000000000 : ℝ)*(X 0 1+X 2 1)+(46352639371/17200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4463/1024 : ℝ)) (lo := (123/5000 : ℝ)) (hi := (6463/25000 : ℝ)) (c := (107485751351519549/107500000000000000 : ℝ)) (alpha := (46352639371/17200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (107485751351519549/107500000000000000 : ℝ)*(X 0 2+X 1 2)+(46352639371/17200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4463/1024 : ℝ)) (lo := (123/5000 : ℝ)) (hi := (6463/25000 : ℝ)) (c := (107485751351519549/107500000000000000 : ℝ)) (alpha := (46352639371/17200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1877242707/10000000000 : ℝ)*X 0 0+(5589858117/10000000000 : ℝ)*X 0 1+(1271116061/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1484_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1347952481/2500000000 : ℝ)*X 1 0+(-2144333671/10000000000 : ℝ)*X 1 1+(5084465573/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1484_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2695905539/5000000000 : ℝ)*X 2 0+(5084464983/10000000000 : ℝ)*X 2 1+(-1072166457/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1484_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4259810721/10000000000 : ℝ)*X 0 0+(3730086321/10000000000 : ℝ)*X 0 1+(2426766761/5000000000 : ℝ)*X 0 2+(4259810721/10000000000 : ℝ)*X 1 0+(3730086321/10000000000 : ℝ)*X 1 1+(2426766761/5000000000 : ℝ)*X 1 2+(4259810721/10000000000 : ℝ)*X 2 0+(3730086321/10000000000 : ℝ)*X 2 1+(2426766761/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1484_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-234700333/1250000000 : ℝ)*X 0 0+(5090345047/10000000000 : ℝ)*X 0 1+(697984843/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1484_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5259160223/10000000000 : ℝ)*X 1 0+(-102807487/625000000 : ℝ)*X 1 1+(1116775759/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1484_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((164348757/312500000 : ℝ)*X 2 0+(5583878773/10000000000 : ℝ)*X 2 1+(-1644919823/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1484_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((170424467/400000000 : ℝ)*X 0 0+(2420231161/5000000000 : ℝ)*X 0 1+(1871688417/5000000000 : ℝ)*X 0 2+(170424467/400000000 : ℝ)*X 1 0+(2420231161/5000000000 : ℝ)*X 1 1+(1871688417/5000000000 : ℝ)*X 1 2+(170424467/400000000 : ℝ)*X 2 0+(2420231161/5000000000 : ℝ)*X 2 1+(1871688417/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1484_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1076333379382065312288957/134375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1510570531/100000000000000 : ℝ)*(base19) + (939231509/50000000000000 : ℝ)*(base23) + (1139289/50000000000000 : ℝ)*(upper3) + (29979711/100000000000000 : ℝ)*(upper4) + (203789159/50000000000000 : ℝ)*(upper5) + (143440945430087/10000000000000 : ℝ)*(major0) + (143440945430087/10000000000000 : ℝ)*(major1) + (143440945430087/10000000000000 : ℝ)*(major2) + (1978667640051203/100000000000000 : ℝ)*(sp0) + (1978686217306847/100000000000000 : ℝ)*(sp1) + (49467146235359/2500000000000 : ℝ)*(sp2) + (445062458190627/50000000000000 : ℝ)*(sp3) + (803513047/4000000000000 : ℝ)*(sp4) + (2998672839/50000000000000 : ℝ)*(sp7) + (222532728431733/25000000000000 : ℝ)*(f.failure) + (989343863938689/50000000000000 : ℝ)*(f.sum) + (17829761859/86000000000000000000000000 : ℝ)*base65 + (3127650624197987/1075000000000000000000000000000 : ℝ)*base68 + (4971586241147987/1075000000000000000000000000000 : ℝ)*base70 + (3165730979147987/1075000000000000000000000000000 : ℝ)*base72 + (116655161159/86000000000000000000000000 : ℝ)*base73 + (815495014927013/1075000000000000000000000000000 : ℝ)*base75 + (857201215047987/1075000000000000000000000000000 : ℝ)*base78 + (1175435470997987/1075000000000000000000000000000 : ℝ)*base80 + (243732094723/86000000000000000000000000 : ℝ)*base82 + (2009383/1250000000000000000000 : ℝ)*base90 + (2009383/1250000000000000000000 : ℝ)*base92 + (2009383/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (420656236224116030617137/67187500000000000000000000000 : ℝ) := by norm_num
    linear_combination (240673433/20000000000000 : ℝ)*(base19) + (1279101501/100000000000000 : ℝ)*(base23) + (42370619/25000000000000 : ℝ)*(upper3) + (30248807/100000000000000 : ℝ)*(lower4) + (120673387/100000000000000 : ℝ)*(upper5) + (146885481101691/10000000000000 : ℝ)*(major0) + (146885481101691/10000000000000 : ℝ)*(major1) + (146885481101691/10000000000000 : ℝ)*(major2) + (465887603/6250000000000 : ℝ)*(sp1) + (8161141239/100000000000000 : ℝ)*(sp2) + (506550809585943/25000000000000 : ℝ)*(sp4) + (2026194580774959/100000000000000 : ℝ)*(sp5) + (2026193798101033/100000000000000 : ℝ)*(sp6) + (227876543748093/25000000000000 : ℝ)*(sp7) + (227876543748093/25000000000000 : ℝ)*(f.failure) + (506550809585943/25000000000000 : ℝ)*(f.sum) + (145225710049/86000000000000000000000000 : ℝ)*base65 + (9539255472613609/1075000000000000000000000000000 : ℝ)*base67 + (1449893858513609/1075000000000000000000000000000 : ℝ)*base69 + (8874638183538609/1075000000000000000000000000000 : ℝ)*base71 + (283505543833/86000000000000000000000000 : ℝ)*base73 + (4193964291938609/1075000000000000000000000000000 : ℝ)*base75 + (3522270776663609/1075000000000000000000000000000 : ℝ)*base77 + (8313601876536391/1075000000000000000000000000000 : ℝ)*base80 + (28361690937/86000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (8863743/1250000000000000000000 : ℝ)*base90 + (8863743/1250000000000000000000 : ℝ)*base92 + (8863743/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1484_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4463/1024 : ℝ) ≤ p) (hpb : p ≤ (4465/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80572949/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6463/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (123/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1991/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (18649/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1484_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1484_s2_0 (p : ℝ) (hpa : (4463/1024 : ℝ) ≤ p) (hpb : p ≤ (4465/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1905170801/10000000000 : ℝ)*x 0 + (273372901/500000000 : ℝ)*x 1 + (81075437/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1905170801/10000000000 : ℝ)^4465 ≤ (5815953961557/50000000000000 : ℝ)^3441 := by
    have hnat : (1905170801 : ℕ)^4465*50000000000000^3441 ≤ 5815953961557^3441*10000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1905170801 10000000000 5815953961557 50000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (273372901/500000000 : ℝ)^4465 ≤ (45682890915309/100000000000000 : ℝ)^3441 := by
    have hnat : (273372901 : ℕ)^4465*100000000000000^3441 ≤ 45682890915309^3441*500000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273372901 500000000 45682890915309 100000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (81075437/156250000 : ℝ)^4465 ≤ (2134260057233/5000000000000 : ℝ)^3441 := by
    have hnat : (81075437 : ℕ)^4465*5000000000000^3441 ≤ 2134260057233^3441*156250000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81075437 156250000 2134260057233 5000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4465/1024 : ℝ)) 4465 3441 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1905170801/10000000000 : ℝ), (273372901/500000000 : ℝ), (81075437/156250000 : ℝ)] ![(5815953961557/50000000000000 : ℝ), (45682890915309/100000000000000 : ℝ), (2134260057233/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1905170801/10000000000 : ℝ)|^4465 ≤ (5815953961557/50000000000000 : ℝ)^3441
        have hw : |(-1905170801/10000000000 : ℝ)|=(1905170801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(273372901/500000000 : ℝ)|^4465 ≤ (45682890915309/100000000000000 : ℝ)^3441
        have hw : |(273372901/500000000 : ℝ)|=(273372901/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(81075437/156250000 : ℝ)|^4465 ≤ (2134260057233/5000000000000 : ℝ)^3441
        have hw : |(81075437/156250000 : ℝ)|=(81075437/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1484_s2_1 (p : ℝ) (hpa : (4463/1024 : ℝ) ≤ p) (hpb : p ≤ (4465/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5360992431/10000000000 : ℝ)*x 0 + (-512215439/2500000000 : ℝ)*x 1 + (5188828173/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5360992431/10000000000 : ℝ)^4465 ≤ (44531962748617/100000000000000 : ℝ)^3441 := by
    have hnat : (5360992431 : ℕ)^4465*100000000000000^3441 ≤ 44531962748617^3441*10000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5360992431 10000000000 44531962748617 100000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (512215439/2500000000 : ℝ)^4465 ≤ (12782833904499/100000000000000 : ℝ)^3441 := by
    have hnat : (512215439 : ℕ)^4465*100000000000000^3441 ≤ 12782833904499^3441*2500000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      512215439 2500000000 12782833904499 100000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5188828173/10000000000 : ℝ)^4465 ≤ (42685203332919/100000000000000 : ℝ)^3441 := by
    have hnat : (5188828173 : ℕ)^4465*100000000000000^3441 ≤ 42685203332919^3441*10000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5188828173 10000000000 42685203332919 100000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4465/1024 : ℝ)) 4465 3441 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5360992431/10000000000 : ℝ), (-512215439/2500000000 : ℝ), (5188828173/10000000000 : ℝ)] ![(44531962748617/100000000000000 : ℝ), (12782833904499/100000000000000 : ℝ), (42685203332919/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5360992431/10000000000 : ℝ)|^4465 ≤ (44531962748617/100000000000000 : ℝ)^3441
        have hw : |(5360992431/10000000000 : ℝ)|=(5360992431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-512215439/2500000000 : ℝ)|^4465 ≤ (12782833904499/100000000000000 : ℝ)^3441
        have hw : |(-512215439/2500000000 : ℝ)|=(512215439/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5188828173/10000000000 : ℝ)|^4465 ≤ (42685203332919/100000000000000 : ℝ)^3441
        have hw : |(5188828173/10000000000 : ℝ)|=(5188828173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1484_s2_2 (p : ℝ) (hpa : (4463/1024 : ℝ) ≤ p) (hpb : p ≤ (4465/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (268049631/500000000 : ℝ)*x 0 + (5188828129/10000000000 : ℝ)*x 1 + (-2048861563/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268049631/500000000 : ℝ)^4465 ≤ (44531964785777/100000000000000 : ℝ)^3441 := by
    have hnat : (268049631 : ℕ)^4465*100000000000000^3441 ≤ 44531964785777^3441*500000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268049631 500000000 44531964785777 100000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5188828129/10000000000 : ℝ)^4465 ≤ (10671300715811/25000000000000 : ℝ)^3441 := by
    have hnat : (5188828129 : ℕ)^4465*25000000000000^3441 ≤ 10671300715811^3441*10000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5188828129 10000000000 10671300715811 25000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2048861563/10000000000 : ℝ)^4465 ≤ (319570808551/2500000000000 : ℝ)^3441 := by
    have hnat : (2048861563 : ℕ)^4465*2500000000000^3441 ≤ 319570808551^3441*10000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2048861563 10000000000 319570808551 2500000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4465/1024 : ℝ)) 4465 3441 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(268049631/500000000 : ℝ), (5188828129/10000000000 : ℝ), (-2048861563/10000000000 : ℝ)] ![(44531964785777/100000000000000 : ℝ), (10671300715811/25000000000000 : ℝ), (319570808551/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(268049631/500000000 : ℝ)|^4465 ≤ (44531964785777/100000000000000 : ℝ)^3441
        have hw : |(268049631/500000000 : ℝ)|=(268049631/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5188828129/10000000000 : ℝ)|^4465 ≤ (10671300715811/25000000000000 : ℝ)^3441
        have hw : |(5188828129/10000000000 : ℝ)|=(5188828129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2048861563/10000000000 : ℝ)|^4465 ≤ (319570808551/2500000000000 : ℝ)^3441
        have hw : |(-2048861563/10000000000 : ℝ)|=(2048861563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1484_s2_3 (p : ℝ) (hpa : (4463/1024 : ℝ) ≤ p) (hpb : p ≤ (4465/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069938977/2500000000 : ℝ)*x 0 + (31838371/80000000 : ℝ)*x 1 + (183966747/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069938977/2500000000 : ℝ)^4465 ≤ (16622783742151/50000000000000 : ℝ)^3441 := by
    have hnat : (1069938977 : ℕ)^4465*50000000000000^3441 ≤ 16622783742151^3441*2500000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069938977 2500000000 16622783742151 50000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (31838371/80000000 : ℝ)^4465 ≤ (236360178631/781250000000 : ℝ)^3441 := by
    have hnat : (31838371 : ℕ)^4465*781250000000^3441 ≤ 236360178631^3441*80000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31838371 80000000 236360178631 781250000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (183966747/400000000 : ℝ)^4465 ≤ (2281270602177/6250000000000 : ℝ)^3441 := by
    have hnat : (183966747 : ℕ)^4465*6250000000000^3441 ≤ 2281270602177^3441*400000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      183966747 400000000 2281270602177 6250000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4465/1024 : ℝ)) 4465 3441 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069938977/2500000000 : ℝ), (31838371/80000000 : ℝ), (183966747/400000000 : ℝ)] ![(16622783742151/50000000000000 : ℝ), (236360178631/781250000000 : ℝ), (2281270602177/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069938977/2500000000 : ℝ)|^4465 ≤ (16622783742151/50000000000000 : ℝ)^3441
        have hw : |(1069938977/2500000000 : ℝ)|=(1069938977/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(31838371/80000000 : ℝ)|^4465 ≤ (236360178631/781250000000 : ℝ)^3441
        have hw : |(31838371/80000000 : ℝ)|=(31838371/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(183966747/400000000 : ℝ)|^4465 ≤ (2281270602177/6250000000000 : ℝ)^3441
        have hw : |(183966747/400000000 : ℝ)|=(183966747/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1484_s2_4 (p : ℝ) (hpa : (4463/1024 : ℝ) ≤ p) (hpb : p ≤ (4465/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1905231441/10000000000 : ℝ)*x 0 + (324414021/625000000 : ℝ)*x 1 + (1093128981/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1905231441/10000000000 : ℝ)^4465 ≤ (11632388336477/100000000000000 : ℝ)^3441 := by
    have hnat : (1905231441 : ℕ)^4465*100000000000000^3441 ≤ 11632388336477^3441*10000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1905231441 10000000000 11632388336477 100000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (324414021/625000000 : ℝ)^4465 ≤ (42704377343747/100000000000000 : ℝ)^3441 := by
    have hnat : (324414021 : ℕ)^4465*100000000000000^3441 ≤ 42704377343747^3441*625000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324414021 625000000 42704377343747 100000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1093128981/2000000000 : ℝ)^4465 ≤ (22831617147881/50000000000000 : ℝ)^3441 := by
    have hnat : (1093128981 : ℕ)^4465*50000000000000^3441 ≤ 22831617147881^3441*2000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093128981 2000000000 22831617147881 50000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4465/1024 : ℝ)) 4465 3441 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1905231441/10000000000 : ℝ), (324414021/625000000 : ℝ), (1093128981/2000000000 : ℝ)] ![(11632388336477/100000000000000 : ℝ), (42704377343747/100000000000000 : ℝ), (22831617147881/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1905231441/10000000000 : ℝ)|^4465 ≤ (11632388336477/100000000000000 : ℝ)^3441
        have hw : |(-1905231441/10000000000 : ℝ)|=(1905231441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(324414021/625000000 : ℝ)|^4465 ≤ (42704377343747/100000000000000 : ℝ)^3441
        have hw : |(324414021/625000000 : ℝ)|=(324414021/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1093128981/2000000000 : ℝ)|^4465 ≤ (22831617147881/50000000000000 : ℝ)^3441
        have hw : |(1093128981/2000000000 : ℝ)|=(1093128981/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1484_s2_5 (p : ℝ) (hpa : (4463/1024 : ℝ) ≤ p) (hpb : p ≤ (4465/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5288146447/10000000000 : ℝ)*x 0 + (-1772045053/10000000000 : ℝ)*x 1 + (5465644899/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288146447/10000000000 : ℝ)^4465 ≤ (10937093914923/25000000000000 : ℝ)^3441 := by
    have hnat : (5288146447 : ℕ)^4465*25000000000000^3441 ≤ 10937093914923^3441*10000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288146447 10000000000 10937093914923 25000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1772045053/10000000000 : ℝ)^4465 ≤ (10588390099119/100000000000000 : ℝ)^3441 := by
    have hnat : (1772045053 : ℕ)^4465*100000000000000^3441 ≤ 10588390099119^3441*10000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1772045053 10000000000 10588390099119 100000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5465644899/10000000000 : ℝ)^4465 ≤ (45663234230717/100000000000000 : ℝ)^3441 := by
    have hnat : (5465644899 : ℕ)^4465*100000000000000^3441 ≤ 45663234230717^3441*10000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5465644899 10000000000 45663234230717 100000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4465/1024 : ℝ)) 4465 3441 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288146447/10000000000 : ℝ), (-1772045053/10000000000 : ℝ), (5465644899/10000000000 : ℝ)] ![(10937093914923/25000000000000 : ℝ), (10588390099119/100000000000000 : ℝ), (45663234230717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288146447/10000000000 : ℝ)|^4465 ≤ (10937093914923/25000000000000 : ℝ)^3441
        have hw : |(5288146447/10000000000 : ℝ)|=(5288146447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1772045053/10000000000 : ℝ)|^4465 ≤ (10588390099119/100000000000000 : ℝ)^3441
        have hw : |(-1772045053/10000000000 : ℝ)|=(1772045053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5465644899/10000000000 : ℝ)|^4465 ≤ (45663234230717/100000000000000 : ℝ)^3441
        have hw : |(5465644899/10000000000 : ℝ)|=(5465644899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1484_s2_6 (p : ℝ) (hpa : (4463/1024 : ℝ) ≤ p) (hpb : p ≤ (4465/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644073349/5000000000 : ℝ)*x 0 + (5465644937/10000000000 : ℝ)*x 1 + (-1772044651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644073349/5000000000 : ℝ)^4465 ≤ (8749675670827/20000000000000 : ℝ)^3441 := by
    have hnat : (2644073349 : ℕ)^4465*20000000000000^3441 ≤ 8749675670827^3441*5000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644073349 5000000000 8749675670827 20000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5465644937/10000000000 : ℝ)^4465 ≤ (11415808660667/25000000000000 : ℝ)^3441 := by
    have hnat : (5465644937 : ℕ)^4465*25000000000000^3441 ≤ 11415808660667^3441*10000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5465644937 10000000000 11415808660667 25000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1772044651/10000000000 : ℝ)^4465 ≤ (5294193491127/50000000000000 : ℝ)^3441 := by
    have hnat : (1772044651 : ℕ)^4465*50000000000000^3441 ≤ 5294193491127^3441*10000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1772044651 10000000000 5294193491127 50000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4465/1024 : ℝ)) 4465 3441 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644073349/5000000000 : ℝ), (5465644937/10000000000 : ℝ), (-1772044651/10000000000 : ℝ)] ![(8749675670827/20000000000000 : ℝ), (11415808660667/25000000000000 : ℝ), (5294193491127/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644073349/5000000000 : ℝ)|^4465 ≤ (8749675670827/20000000000000 : ℝ)^3441
        have hw : |(2644073349/5000000000 : ℝ)|=(2644073349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5465644937/10000000000 : ℝ)|^4465 ≤ (11415808660667/25000000000000 : ℝ)^3441
        have hw : |(5465644937/10000000000 : ℝ)|=(5465644937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1772044651/10000000000 : ℝ)|^4465 ≤ (5294193491127/50000000000000 : ℝ)^3441
        have hw : |(-1772044651/10000000000 : ℝ)|=(1772044651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1484_s2_7 (p : ℝ) (hpa : (4463/1024 : ℝ) ≤ p) (hpb : p ≤ (4465/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4279890299/10000000000 : ℝ)*x 0 + (2297587441/5000000000 : ℝ)*x 1 + (3983827357/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4279890299/10000000000 : ℝ)^4465 ≤ (16623461061933/50000000000000 : ℝ)^3441 := by
    have hnat : (4279890299 : ℕ)^4465*50000000000000^3441 ≤ 16623461061933^3441*10000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4279890299 10000000000 16623461061933 50000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2297587441/5000000000 : ℝ)^4465 ≤ (36459206741679/100000000000000 : ℝ)^3441 := by
    have hnat : (2297587441 : ℕ)^4465*100000000000000^3441 ≤ 36459206741679^3441*5000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2297587441 5000000000 36459206741679 100000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3983827357/10000000000 : ℝ)^4465 ≤ (30293871117267/100000000000000 : ℝ)^3441 := by
    have hnat : (3983827357 : ℕ)^4465*100000000000000^3441 ≤ 30293871117267^3441*10000000000^4465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3983827357 10000000000 30293871117267 100000000000000 4465 3441 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4465/1024 : ℝ)) 4465 3441 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4279890299/10000000000 : ℝ), (2297587441/5000000000 : ℝ), (3983827357/10000000000 : ℝ)] ![(16623461061933/50000000000000 : ℝ), (36459206741679/100000000000000 : ℝ), (30293871117267/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4279890299/10000000000 : ℝ)|^4465 ≤ (16623461061933/50000000000000 : ℝ)^3441
        have hw : |(4279890299/10000000000 : ℝ)|=(4279890299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2297587441/5000000000 : ℝ)|^4465 ≤ (36459206741679/100000000000000 : ℝ)^3441
        have hw : |(2297587441/5000000000 : ℝ)|=(2297587441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3983827357/10000000000 : ℝ)|^4465 ≤ (30293871117267/100000000000000 : ℝ)^3441
        have hw : |(3983827357/10000000000 : ℝ)|=(3983827357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1484_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4463/1024 : ℝ) ≤ p) (hpb : p ≤ (4465/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80572949/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18649/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1991/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (10219/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16113/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (18649/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1991/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (18649/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1991/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (18649/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1991/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (18649/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1991/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (18649/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1991/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (18649/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1991/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1991/25000 : ℝ) ^ (4463/1024 : ℝ) ≤ (1624396940689837/100000000000000000000 : ℝ) := by
    have hpowers : (1991/25000 : ℝ)^4463 ≤ (1624396940689837/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1991 : ℕ)^4463*100000000000000000000^1024 ≤ 1624396940689837^1024*25000^4463 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1991 25000 1624396940689837 100000000000000000000 4463 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1991/25000 : ℝ)) (X := (1624396940689837/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4463 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (18649/100000 : ℝ) ^ (4463/1024 : ℝ) ≤ (66256163391906397/100000000000000000000 : ℝ) := by
    have hpowers : (18649/100000 : ℝ)^4463 ≤ (66256163391906397/100000000000000000000 : ℝ)^1024 := by
      have hnat : (18649 : ℕ)^4463*100000000000000000000^1024 ≤ 66256163391906397^1024*100000^4463 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18649 100000 66256163391906397 100000000000000000000 4463 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18649/100000 : ℝ)) (X := (66256163391906397/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4463 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001624396940689837/50000000000000000000 : ℝ) ≤ (10000074540069337/10000000000000000 : ℝ) ^ (4463/1024 : ℝ) := by
    have hpowers : (50001624396940689837/50000000000000000000 : ℝ)^1024 ≤ (10000074540069337/10000000000000000 : ℝ)^4463 := by
      have hnat : (50001624396940689837 : ℕ)^1024*10000000000000000^4463 ≤ 10000074540069337^4463*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001624396940689837 50000000000000000000 10000074540069337 10000000000000000 1024 4463 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000074540069337/10000000000000000 : ℝ)) (X := (50001624396940689837/50000000000000000000 : ℝ)) (by norm_num) 4463 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50033940280166298117/50000000000000000000 : ℝ) ≤ (500077852926533/500000000000000 : ℝ) ^ (4463/1024 : ℝ) := by
    have hpowers : (50033940280166298117/50000000000000000000 : ℝ)^1024 ≤ (500077852926533/500000000000000 : ℝ)^4463 := by
      have hnat : (50033940280166298117 : ℕ)^1024*500000000000000^4463 ≤ 500077852926533^4463*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033940280166298117 50000000000000000000 500077852926533 500000000000000 1024 4463 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500077852926533/500000000000000 : ℝ)) (X := (50033940280166298117/50000000000000000000 : ℝ)) (by norm_num) 4463 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50066256163391906397/50000000000000000000 : ℝ) ≤ (10003039576991983/10000000000000000 : ℝ) ^ (4463/1024 : ℝ) := by
    have hpowers : (50066256163391906397/50000000000000000000 : ℝ)^1024 ≤ (10003039576991983/10000000000000000 : ℝ)^4463 := by
      have hnat : (50066256163391906397 : ℕ)^1024*10000000000000000^4463 ≤ 10003039576991983^4463*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50066256163391906397 50000000000000000000 10003039576991983 10000000000000000 1024 4463 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003039576991983/10000000000000000 : ℝ)) (X := (50066256163391906397/50000000000000000000 : ℝ)) (by norm_num) 4463 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1624396940689837/100000000000000000000 : ℝ) ≤ ((106827182906588913101/106850000000000000000 : ℝ)+2*(1482518461323/1068500000000000 : ℝ)*(1991/25000 : ℝ))^(4463/1024 : ℝ) := by
    rw [show (106827182906588913101/106850000000000000000 : ℝ)+2*(1482518461323/1068500000000000 : ℝ)*(1991/25000 : ℝ)=(10000074540069337/10000000000000000 : ℝ) by norm_num, show 1+2*(1624396940689837/100000000000000000000 : ℝ)=(50001624396940689837/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(66256163391906397/100000000000000000000 : ℝ)+(1624396940689837/100000000000000000000 : ℝ) ≤ ((106827182906588913101/106850000000000000000 : ℝ)+(1482518461323/1068500000000000 : ℝ)*((18649/100000 : ℝ)+(1991/25000 : ℝ)))^(4463/1024 : ℝ) := by
    rw [show (106827182906588913101/106850000000000000000 : ℝ)+(1482518461323/1068500000000000 : ℝ)*((18649/100000 : ℝ)+(1991/25000 : ℝ))=(500077852926533/500000000000000 : ℝ) by norm_num, show 1+(66256163391906397/100000000000000000000 : ℝ)+(1624396940689837/100000000000000000000 : ℝ)=(50033940280166298117/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(66256163391906397/100000000000000000000 : ℝ) ≤ ((106827182906588913101/106850000000000000000 : ℝ)+2*(1482518461323/1068500000000000 : ℝ)*(18649/100000 : ℝ))^(4463/1024 : ℝ) := by
    rw [show (106827182906588913101/106850000000000000000 : ℝ)+2*(1482518461323/1068500000000000 : ℝ)*(18649/100000 : ℝ)=(10003039576991983/10000000000000000 : ℝ) by norm_num, show 1+2*(66256163391906397/100000000000000000000 : ℝ)=(50066256163391906397/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (106827182906588913101/106850000000000000000 : ℝ)*(X 1 0+X 2 0)+(1482518461323/1068500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4463/1024 : ℝ)) (lo := (1991/25000 : ℝ)) (hi := (18649/100000 : ℝ)) (c := (106827182906588913101/106850000000000000000 : ℝ)) (alpha := (1482518461323/1068500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (106827182906588913101/106850000000000000000 : ℝ)*(X 0 1+X 2 1)+(1482518461323/1068500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4463/1024 : ℝ)) (lo := (1991/25000 : ℝ)) (hi := (18649/100000 : ℝ)) (c := (106827182906588913101/106850000000000000000 : ℝ)) (alpha := (1482518461323/1068500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (106827182906588913101/106850000000000000000 : ℝ)*(X 0 2+X 1 2)+(1482518461323/1068500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4463/1024 : ℝ)) (lo := (1991/25000 : ℝ)) (hi := (18649/100000 : ℝ)) (c := (106827182906588913101/106850000000000000000 : ℝ)) (alpha := (1482518461323/1068500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1905170801/10000000000 : ℝ)*X 0 0+(273372901/500000000 : ℝ)*X 0 1+(81075437/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1484_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5360992431/10000000000 : ℝ)*X 1 0+(-512215439/2500000000 : ℝ)*X 1 1+(5188828173/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1484_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((268049631/500000000 : ℝ)*X 2 0+(5188828129/10000000000 : ℝ)*X 2 1+(-2048861563/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1484_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1069938977/2500000000 : ℝ)*X 0 0+(31838371/80000000 : ℝ)*X 0 1+(183966747/400000000 : ℝ)*X 0 2+(1069938977/2500000000 : ℝ)*X 1 0+(31838371/80000000 : ℝ)*X 1 1+(183966747/400000000 : ℝ)*X 1 2+(1069938977/2500000000 : ℝ)*X 2 0+(31838371/80000000 : ℝ)*X 2 1+(183966747/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1484_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1905231441/10000000000 : ℝ)*X 0 0+(324414021/625000000 : ℝ)*X 0 1+(1093128981/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1484_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5288146447/10000000000 : ℝ)*X 1 0+(-1772045053/10000000000 : ℝ)*X 1 1+(5465644899/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1484_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2644073349/5000000000 : ℝ)*X 2 0+(5465644937/10000000000 : ℝ)*X 2 1+(-1772044651/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1484_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4279890299/10000000000 : ℝ)*X 0 0+(2297587441/5000000000 : ℝ)*X 0 1+(3983827357/10000000000 : ℝ)*X 0 2+(4279890299/10000000000 : ℝ)*X 1 0+(2297587441/5000000000 : ℝ)*X 1 1+(3983827357/10000000000 : ℝ)*X 1 2+(4279890299/10000000000 : ℝ)*X 2 0+(2297587441/5000000000 : ℝ)*X 2 1+(3983827357/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1484_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (703410201632323819119519/166953125000000000000000000000 : ℝ) := by norm_num
    linear_combination (171214113/50000000000000 : ℝ)*(base19) + (33060019/10000000000000 : ℝ)*(base23) + (74173071/100000000000000 : ℝ)*(lower2) + (51025049/100000000000000 : ℝ)*(upper3) + (28511799/25000000000000 : ℝ)*(upper5) + (650442858547/25000000000 : ℝ)*(major0) + (650442858547/25000000000 : ℝ)*(major1) + (650442858547/25000000000 : ℝ)*(major2) + (3588991957610999/100000000000000 : ℝ)*(sp0) + (1794499190648973/50000000000000 : ℝ)*(sp1) + (1794499196562991/50000000000000 : ℝ)*(sp2) + (322908171688167/20000000000000 : ℝ)*(sp3) + (3383057587/50000000000000 : ℝ)*(sp4) + (3145768319/100000000000000 : ℝ)*(sp7) + (807272002104577/50000000000000 : ℝ)*(f.failure) + (3588998723726173/100000000000000 : ℝ)*(f.sum) + (1804062632769/534250000000000000000000000 : ℝ)*base66 + (32207272929975497/2671250000000000000000000000000 : ℝ)*base67 + (23432264540761747/2671250000000000000000000000000 : ℝ)*base69 + (29440620945825497/2671250000000000000000000000000 : ℝ)*base71 + (11080169301901/2137000000000000000000000000 : ℝ)*base73 + (26050292139046747/2671250000000000000000000000000 : ℝ)*base75 + (35396423613802997/2671250000000000000000000000000 : ℝ)*base77 + (40818551546152997/2671250000000000000000000000000 : ℝ)*base79 + (2589205817497/1068500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (24712427/2500000000000000000000 : ℝ)*base90 + (24712427/2500000000000000000000 : ℝ)*base92 + (24712427/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (28210297143505473511428932589/2671250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (169659/12207031250 : ℝ)*(base19) + (345932717/20000000000000 : ℝ)*(base23) + (36931649/20000000000000 : ℝ)*(upper3) + (48573801/100000000000000 : ℝ)*(lower4) + (10704207/4000000000000 : ℝ)*(upper5) + (1317956205264437/50000000000000 : ℝ)*(major0) + (1317956205264437/50000000000000 : ℝ)*(major1) + (1317956205264437/50000000000000 : ℝ)*(major2) + (16016585219/100000000000000 : ℝ)*(sp1) + (10744246419/50000000000000 : ℝ)*(sp2) + (1818047044262897/50000000000000 : ℝ)*(sp4) + (113627396315439/3125000000000 : ℝ)*(sp5) + (3636070870369371/100000000000000 : ℝ)*(sp6) + (1635730380508273/100000000000000 : ℝ)*(sp7) + (1635730380508273/100000000000000 : ℝ)*(f.failure) + (1818047044262897/50000000000000 : ℝ)*(f.sum) + (156345846479723/53425000000000000000000000000 : ℝ)*base66 + (31580958343408789137/5342500000000000000000000000000000 : ℝ)*base67 + (6706906295516289137/5342500000000000000000000000000000 : ℝ)*base69 + (33576422230526210863/5342500000000000000000000000000000 : ℝ)*base72 + (2660840487393/834765625000000000000000000 : ℝ)*base73 + (8010914390116210863/5342500000000000000000000000000000 : ℝ)*base76 + (37167265601471289137/5342500000000000000000000000000000 : ℝ)*base77 + (37696294002246289137/5342500000000000000000000000000000 : ℝ)*base79 + (45160879752437/13356250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (25492923/5000000000000000000000 : ℝ)*base90 + (25492923/5000000000000000000000 : ℝ)*base92 + (25492923/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1484_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4463/1024 : ℝ) ≤ p) (hpb : p ≤ (4465/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80572949/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18649/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1991/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10219/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16113/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1484_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1484_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4463/1024 : ℝ) ≤ p) (hpb : p ≤ (4465/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80572949/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10219/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16113/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1484_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1484_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1484_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4463/1024 : ℝ) ≤ p) (hpb : p ≤ (4465/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80572949/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10219/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16113/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1484_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
