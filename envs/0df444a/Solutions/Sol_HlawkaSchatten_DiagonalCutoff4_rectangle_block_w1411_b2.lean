-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1411_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:48:48.629866+00:00
-- url     : https://prove2.me/submissions/7d5ddfc0-da4f-42e2-8396-54751663ae19

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
theorem support_rectangle_w1411_s6_0 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1985827919/10000000000 : ℝ)*x 0 + (2704576621/5000000000 : ℝ)*x 1 + (5246484491/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1985827919/10000000000 : ℝ)^4371 ≤ (12110161123843/100000000000000 : ℝ)^3347 := by
    have hnat : (1985827919 : ℕ)^4371*100000000000000^3347 ≤ 12110161123843^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1985827919 10000000000 12110161123843 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2704576621/5000000000 : ℝ)^4371 ≤ (22410490521777/50000000000000 : ℝ)^3347 := by
    have hnat : (2704576621 : ℕ)^4371*50000000000000^3347 ≤ 22410490521777^3347*5000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704576621 5000000000 22410490521777 50000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246484491/10000000000 : ℝ)^4371 ≤ (5383607227701/12500000000000 : ℝ)^3347 := by
    have hnat : (5246484491 : ℕ)^4371*12500000000000^3347 ≤ 5383607227701^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246484491 10000000000 5383607227701 12500000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1985827919/10000000000 : ℝ), (2704576621/5000000000 : ℝ), (5246484491/10000000000 : ℝ)] ![(12110161123843/100000000000000 : ℝ), (22410490521777/50000000000000 : ℝ), (5383607227701/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1985827919/10000000000 : ℝ)|^4371 ≤ (12110161123843/100000000000000 : ℝ)^3347
        have hw : |(-1985827919/10000000000 : ℝ)|=(1985827919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2704576621/5000000000 : ℝ)|^4371 ≤ (22410490521777/50000000000000 : ℝ)^3347
        have hw : |(2704576621/5000000000 : ℝ)|=(2704576621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246484491/10000000000 : ℝ)|^4371 ≤ (5383607227701/12500000000000 : ℝ)^3347
        have hw : |(5246484491/10000000000 : ℝ)|=(5246484491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_s6_1 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347701373/10000000000 : ℝ)*x 0 + (-1034329239/5000000000 : ℝ)*x 1 + (655810467/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347701373/10000000000 : ℝ)^4371 ≤ (44157154127683/100000000000000 : ℝ)^3347 := by
    have hnat : (5347701373 : ℕ)^4371*100000000000000^3347 ≤ 44157154127683^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347701373 10000000000 44157154127683 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1034329239/5000000000 : ℝ)^4371 ≤ (12773996129581/100000000000000 : ℝ)^3347 := by
    have hnat : (1034329239 : ℕ)^4371*100000000000000^3347 ≤ 12773996129581^3347*5000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034329239 5000000000 12773996129581 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655810467/1250000000 : ℝ)^4371 ≤ (43068849727537/100000000000000 : ℝ)^3347 := by
    have hnat : (655810467 : ℕ)^4371*100000000000000^3347 ≤ 43068849727537^3347*1250000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655810467 1250000000 43068849727537 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347701373/10000000000 : ℝ), (-1034329239/5000000000 : ℝ), (655810467/1250000000 : ℝ)] ![(44157154127683/100000000000000 : ℝ), (12773996129581/100000000000000 : ℝ), (43068849727537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347701373/10000000000 : ℝ)|^4371 ≤ (44157154127683/100000000000000 : ℝ)^3347
        have hw : |(5347701373/10000000000 : ℝ)|=(5347701373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1034329239/5000000000 : ℝ)|^4371 ≤ (12773996129581/100000000000000 : ℝ)^3347
        have hw : |(-1034329239/5000000000 : ℝ)|=(1034329239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(655810467/1250000000 : ℝ)|^4371 ≤ (43068849727537/100000000000000 : ℝ)^3347
        have hw : |(655810467/1250000000 : ℝ)|=(655810467/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_s6_2 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347700797/10000000000 : ℝ)*x 0 + (5246484499/10000000000 : ℝ)*x 1 + (-1034329117/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347700797/10000000000 : ℝ)^4371 ≤ (22078573958199/50000000000000 : ℝ)^3347 := by
    have hnat : (5347700797 : ℕ)^4371*50000000000000^3347 ≤ 22078573958199^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347700797 10000000000 22078573958199 50000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246484499/10000000000 : ℝ)^4371 ≤ (43068857907373/100000000000000 : ℝ)^3347 := by
    have hnat : (5246484499 : ℕ)^4371*100000000000000^3347 ≤ 43068857907373^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246484499 10000000000 43068857907373 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1034329117/5000000000 : ℝ)^4371 ≤ (3193498540477/25000000000000 : ℝ)^3347 := by
    have hnat : (1034329117 : ℕ)^4371*25000000000000^3347 ≤ 3193498540477^3347*5000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034329117 5000000000 3193498540477 25000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347700797/10000000000 : ℝ), (5246484499/10000000000 : ℝ), (-1034329117/5000000000 : ℝ)] ![(22078573958199/50000000000000 : ℝ), (43068857907373/100000000000000 : ℝ), (3193498540477/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347700797/10000000000 : ℝ)|^4371 ≤ (22078573958199/50000000000000 : ℝ)^3347
        have hw : |(5347700797/10000000000 : ℝ)|=(5347700797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246484499/10000000000 : ℝ)|^4371 ≤ (43068857907373/100000000000000 : ℝ)^3347
        have hw : |(5246484499/10000000000 : ℝ)|=(5246484499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1034329117/5000000000 : ℝ)|^4371 ≤ (3193498540477/25000000000000 : ℝ)^3347
        have hw : |(-1034329117/5000000000 : ℝ)|=(1034329117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_s6_3 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2154447013/5000000000 : ℝ)*x 0 + (2068657413/5000000000 : ℝ)*x 1 + (4486902667/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2154447013/5000000000 : ℝ)^4371 ≤ (1332176061391/4000000000000 : ℝ)^3347 := by
    have hnat : (2154447013 : ℕ)^4371*4000000000000^3347 ≤ 1332176061391^3347*5000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2154447013 5000000000 1332176061391 4000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2068657413/5000000000 : ℝ)^4371 ≤ (31583139128869/100000000000000 : ℝ)^3347 := by
    have hnat : (2068657413 : ℕ)^4371*100000000000000^3347 ≤ 31583139128869^3347*5000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2068657413 5000000000 31583139128869 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4486902667/10000000000 : ℝ)^4371 ≤ (3511245933289/10000000000000 : ℝ)^3347 := by
    have hnat : (4486902667 : ℕ)^4371*10000000000000^3347 ≤ 3511245933289^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4486902667 10000000000 3511245933289 10000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2154447013/5000000000 : ℝ), (2068657413/5000000000 : ℝ), (4486902667/10000000000 : ℝ)] ![(1332176061391/4000000000000 : ℝ), (31583139128869/100000000000000 : ℝ), (3511245933289/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2154447013/5000000000 : ℝ)|^4371 ≤ (1332176061391/4000000000000 : ℝ)^3347
        have hw : |(2154447013/5000000000 : ℝ)|=(2154447013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2068657413/5000000000 : ℝ)|^4371 ≤ (31583139128869/100000000000000 : ℝ)^3347
        have hw : |(2068657413/5000000000 : ℝ)|=(2068657413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4486902667/10000000000 : ℝ)|^4371 ≤ (3511245933289/10000000000000 : ℝ)^3347
        have hw : |(4486902667/10000000000 : ℝ)|=(4486902667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_s6_4 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-397167983/2000000000 : ℝ)*x 0 + (5247069983/10000000000 : ℝ)*x 1 + (1081712869/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (397167983/2000000000 : ℝ)^4371 ≤ (3027564165137/25000000000000 : ℝ)^3347 := by
    have hnat : (397167983 : ℕ)^4371*25000000000000^3347 ≤ 3027564165137^3347*2000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      397167983 2000000000 3027564165137 25000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247069983/10000000000 : ℝ)^4371 ≤ (43075134768213/100000000000000 : ℝ)^3347 := by
    have hnat : (5247069983 : ℕ)^4371*100000000000000^3347 ≤ 43075134768213^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247069983 10000000000 43075134768213 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081712869/2000000000 : ℝ)^4371 ≤ (11203652137973/25000000000000 : ℝ)^3347 := by
    have hnat : (1081712869 : ℕ)^4371*25000000000000^3347 ≤ 11203652137973^3347*2000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081712869 2000000000 11203652137973 25000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-397167983/2000000000 : ℝ), (5247069983/10000000000 : ℝ), (1081712869/2000000000 : ℝ)] ![(3027564165137/25000000000000 : ℝ), (43075134768213/100000000000000 : ℝ), (11203652137973/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-397167983/2000000000 : ℝ)|^4371 ≤ (3027564165137/25000000000000 : ℝ)^3347
        have hw : |(-397167983/2000000000 : ℝ)|=(397167983/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247069983/10000000000 : ℝ)|^4371 ≤ (43075134768213/100000000000000 : ℝ)^3347
        have hw : |(5247069983/10000000000 : ℝ)|=(5247069983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081712869/2000000000 : ℝ)|^4371 ≤ (11203652137973/25000000000000 : ℝ)^3347
        have hw : |(1081712869/2000000000 : ℝ)|=(1081712869/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_s6_5 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652743587/5000000000 : ℝ)*x 0 + (-953289137/5000000000 : ℝ)*x 1 + (5408564311/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652743587/5000000000 : ℝ)^4371 ≤ (136570277411/312500000000 : ℝ)^3347 := by
    have hnat : (2652743587 : ℕ)^4371*312500000000^3347 ≤ 136570277411^3347*5000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652743587 5000000000 136570277411 312500000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (953289137/5000000000 : ℝ)^4371 ≤ (11482903026753/100000000000000 : ℝ)^3347 := by
    have hnat : (953289137 : ℕ)^4371*100000000000000^3347 ≤ 11482903026753^3347*5000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      953289137 5000000000 11482903026753 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5408564311/10000000000 : ℝ)^4371 ≤ (22407304091991/50000000000000 : ℝ)^3347 := by
    have hnat : (5408564311 : ℕ)^4371*50000000000000^3347 ≤ 22407304091991^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408564311 10000000000 22407304091991 50000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652743587/5000000000 : ℝ), (-953289137/5000000000 : ℝ), (5408564311/10000000000 : ℝ)] ![(136570277411/312500000000 : ℝ), (11482903026753/100000000000000 : ℝ), (22407304091991/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652743587/5000000000 : ℝ)|^4371 ≤ (136570277411/312500000000 : ℝ)^3347
        have hw : |(2652743587/5000000000 : ℝ)|=(2652743587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-953289137/5000000000 : ℝ)|^4371 ≤ (11482903026753/100000000000000 : ℝ)^3347
        have hw : |(-953289137/5000000000 : ℝ)|=(953289137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5408564311/10000000000 : ℝ)|^4371 ≤ (22407304091991/50000000000000 : ℝ)^3347
        have hw : |(5408564311/10000000000 : ℝ)|=(5408564311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_s6_6 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652743593/5000000000 : ℝ)*x 0 + (540856429/1000000000 : ℝ)*x 1 + (-953289143/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652743593/5000000000 : ℝ)^4371 ≤ (43702488900609/100000000000000 : ℝ)^3347 := by
    have hnat : (2652743593 : ℕ)^4371*100000000000000^3347 ≤ 43702488900609^3347*5000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652743593 5000000000 43702488900609 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (540856429/1000000000 : ℝ)^4371 ≤ (44814607956743/100000000000000 : ℝ)^3347 := by
    have hnat : (540856429 : ℕ)^4371*100000000000000^3347 ≤ 44814607956743^3347*1000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540856429 1000000000 44814607956743 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (953289143/5000000000 : ℝ)^4371 ≤ (5741451560569/50000000000000 : ℝ)^3347 := by
    have hnat : (953289143 : ℕ)^4371*50000000000000^3347 ≤ 5741451560569^3347*5000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      953289143 5000000000 5741451560569 50000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652743593/5000000000 : ℝ), (540856429/1000000000 : ℝ), (-953289143/5000000000 : ℝ)] ![(43702488900609/100000000000000 : ℝ), (44814607956743/100000000000000 : ℝ), (5741451560569/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652743593/5000000000 : ℝ)|^4371 ≤ (43702488900609/100000000000000 : ℝ)^3347
        have hw : |(2652743593/5000000000 : ℝ)|=(2652743593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(540856429/1000000000 : ℝ)|^4371 ≤ (44814607956743/100000000000000 : ℝ)^3347
        have hw : |(540856429/1000000000 : ℝ)|=(540856429/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-953289143/5000000000 : ℝ)|^4371 ≤ (5741451560569/50000000000000 : ℝ)^3347
        have hw : |(-953289143/5000000000 : ℝ)|=(953289143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_s6_7 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4308919203/10000000000 : ℝ)*x 0 + (448564349/1000000000 : ℝ)*x 1 + (827716007/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4308919203/10000000000 : ℝ)^4371 ≤ (8326163917561/25000000000000 : ℝ)^3347 := by
    have hnat : (4308919203 : ℕ)^4371*25000000000000^3347 ≤ 8326163917561^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4308919203 10000000000 8326163917561 25000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (448564349/1000000000 : ℝ)^4371 ≤ (35099591428321/100000000000000 : ℝ)^3347 := by
    have hnat : (448564349 : ℕ)^4371*100000000000000^3347 ≤ 35099591428321^3347*1000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448564349 1000000000 35099591428321 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (827716007/2000000000 : ℝ)^4371 ≤ (6319150576853/20000000000000 : ℝ)^3347 := by
    have hnat : (827716007 : ℕ)^4371*20000000000000^3347 ≤ 6319150576853^3347*2000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      827716007 2000000000 6319150576853 20000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4308919203/10000000000 : ℝ), (448564349/1000000000 : ℝ), (827716007/2000000000 : ℝ)] ![(8326163917561/25000000000000 : ℝ), (35099591428321/100000000000000 : ℝ), (6319150576853/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4308919203/10000000000 : ℝ)|^4371 ≤ (8326163917561/25000000000000 : ℝ)^3347
        have hw : |(4308919203/10000000000 : ℝ)|=(4308919203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(448564349/1000000000 : ℝ)|^4371 ≤ (35099591428321/100000000000000 : ℝ)^3347
        have hw : |(448564349/1000000000 : ℝ)|=(448564349/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(827716007/2000000000 : ℝ)|^4371 ≤ (6319150576853/20000000000000 : ℝ)^3347
        have hw : |(827716007/2000000000 : ℝ)|=(827716007/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1411_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7872689/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (461/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5649/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5651/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3687/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (461/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5649/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (461/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5649/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (461/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5649/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (461/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5649/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (461/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5649/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (461/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5649/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5649/50000 : ℝ) ^ (2185/512 : ℝ) ≤ (9090969849827489/100000000000000000000 : ℝ) := by
    have hpowers : (5649/50000 : ℝ)^2185 ≤ (9090969849827489/100000000000000000000 : ℝ)^512 := by
      have hnat : (5649 : ℕ)^2185*100000000000000000000^512 ≤ 9090969849827489^512*50000^2185 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5649 50000 9090969849827489 100000000000000000000 2185 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5649/50000 : ℝ)) (X := (9090969849827489/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2185 512 (by norm_num) hpowers
    exact h
  have hpowhi : (461/3125 : ℝ) ^ (2185/512 : ℝ) ≤ (14189800918555501/50000000000000000000 : ℝ) := by
    have hpowers : (461/3125 : ℝ)^2185 ≤ (14189800918555501/50000000000000000000 : ℝ)^512 := by
      have hnat : (461 : ℕ)^2185*50000000000000000000^512 ≤ 14189800918555501^512*3125^2185 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        461 3125 14189800918555501 50000000000000000000 2185 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (461/3125 : ℝ)) (X := (14189800918555501/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2185 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009090969849827489/50000000000000000000 : ℝ) ≤ (1000042601854511/1000000000000000 : ℝ) ^ (2185/512 : ℝ) := by
    have hpowers : (50009090969849827489/50000000000000000000 : ℝ)^512 ≤ (1000042601854511/1000000000000000 : ℝ)^2185 := by
      have hnat : (50009090969849827489 : ℕ)^512*1000000000000000^2185 ≤ 1000042601854511^2185*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009090969849827489 50000000000000000000 1000042601854511 1000000000000000 512 2185 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000042601854511/1000000000000000 : ℝ)) (X := (50009090969849827489/50000000000000000000 : ℝ)) (by norm_num) 2185 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100037470571686938491/100000000000000000000 : ℝ) ≤ (1000087790302997/1000000000000000 : ℝ) ^ (2185/512 : ℝ) := by
    have hpowers : (100037470571686938491/100000000000000000000 : ℝ)^512 ≤ (1000087790302997/1000000000000000 : ℝ)^2185 := by
      have hnat : (100037470571686938491 : ℕ)^512*1000000000000000^2185 ≤ 1000087790302997^2185*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100037470571686938491 100000000000000000000 1000087790302997 1000000000000000 512 2185 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000087790302997/1000000000000000 : ℝ)) (X := (100037470571686938491/100000000000000000000 : ℝ)) (by norm_num) 2185 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25014189800918555501/25000000000000000000 : ℝ) ≤ (1000132978751483/1000000000000000 : ℝ) ^ (2185/512 : ℝ) := by
    have hpowers : (25014189800918555501/25000000000000000000 : ℝ)^512 ≤ (1000132978751483/1000000000000000 : ℝ)^2185 := by
      have hnat : (25014189800918555501 : ℕ)^512*1000000000000000^2185 ≤ 1000132978751483^2185*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014189800918555501 25000000000000000000 1000132978751483 1000000000000000 512 2185 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000132978751483/1000000000000000 : ℝ)) (X := (25014189800918555501/25000000000000000000 : ℝ)) (by norm_num) 2185 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9090969849827489/100000000000000000000 : ℝ) ≤ ((1726563034311745669/1727000000000000000 : ℝ)+2*(22594224243/17270000000000 : ℝ)*(5649/50000 : ℝ))^(2185/512 : ℝ) := by
    rw [show (1726563034311745669/1727000000000000000 : ℝ)+2*(22594224243/17270000000000 : ℝ)*(5649/50000 : ℝ)=(1000042601854511/1000000000000000 : ℝ) by norm_num, show 1+2*(9090969849827489/100000000000000000000 : ℝ)=(50009090969849827489/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14189800918555501/50000000000000000000 : ℝ)+(9090969849827489/100000000000000000000 : ℝ) ≤ ((1726563034311745669/1727000000000000000 : ℝ)+(22594224243/17270000000000 : ℝ)*((461/3125 : ℝ)+(5649/50000 : ℝ)))^(2185/512 : ℝ) := by
    rw [show (1726563034311745669/1727000000000000000 : ℝ)+(22594224243/17270000000000 : ℝ)*((461/3125 : ℝ)+(5649/50000 : ℝ))=(1000087790302997/1000000000000000 : ℝ) by norm_num, show 1+(14189800918555501/50000000000000000000 : ℝ)+(9090969849827489/100000000000000000000 : ℝ)=(100037470571686938491/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14189800918555501/50000000000000000000 : ℝ) ≤ ((1726563034311745669/1727000000000000000 : ℝ)+2*(22594224243/17270000000000 : ℝ)*(461/3125 : ℝ))^(2185/512 : ℝ) := by
    rw [show (1726563034311745669/1727000000000000000 : ℝ)+2*(22594224243/17270000000000 : ℝ)*(461/3125 : ℝ)=(1000132978751483/1000000000000000 : ℝ) by norm_num, show 1+2*(14189800918555501/50000000000000000000 : ℝ)=(25014189800918555501/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1726563034311745669/1727000000000000000 : ℝ)*(X 1 0+X 2 0)+(22594224243/17270000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2185/512 : ℝ)) (lo := (5649/50000 : ℝ)) (hi := (461/3125 : ℝ)) (c := (1726563034311745669/1727000000000000000 : ℝ)) (alpha := (22594224243/17270000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1726563034311745669/1727000000000000000 : ℝ)*(X 0 1+X 2 1)+(22594224243/17270000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2185/512 : ℝ)) (lo := (5649/50000 : ℝ)) (hi := (461/3125 : ℝ)) (c := (1726563034311745669/1727000000000000000 : ℝ)) (alpha := (22594224243/17270000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1726563034311745669/1727000000000000000 : ℝ)*(X 0 2+X 1 2)+(22594224243/17270000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2185/512 : ℝ)) (lo := (5649/50000 : ℝ)) (hi := (461/3125 : ℝ)) (c := (1726563034311745669/1727000000000000000 : ℝ)) (alpha := (22594224243/17270000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1985827919/10000000000 : ℝ)*X 0 0+(2704576621/5000000000 : ℝ)*X 0 1+(5246484491/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347701373/10000000000 : ℝ)*X 1 0+(-1034329239/5000000000 : ℝ)*X 1 1+(655810467/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347700797/10000000000 : ℝ)*X 2 0+(5246484499/10000000000 : ℝ)*X 2 1+(-1034329117/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2154447013/5000000000 : ℝ)*X 0 0+(2068657413/5000000000 : ℝ)*X 0 1+(4486902667/10000000000 : ℝ)*X 0 2+(2154447013/5000000000 : ℝ)*X 1 0+(2068657413/5000000000 : ℝ)*X 1 1+(4486902667/10000000000 : ℝ)*X 1 2+(2154447013/5000000000 : ℝ)*X 2 0+(2068657413/5000000000 : ℝ)*X 2 1+(4486902667/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-397167983/2000000000 : ℝ)*X 0 0+(5247069983/10000000000 : ℝ)*X 0 1+(1081712869/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652743587/5000000000 : ℝ)*X 1 0+(-953289137/5000000000 : ℝ)*X 1 1+(5408564311/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652743593/5000000000 : ℝ)*X 2 0+(540856429/1000000000 : ℝ)*X 2 1+(-953289143/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4308919203/10000000000 : ℝ)*X 0 0+(448564349/1000000000 : ℝ)*X 0 1+(827716007/2000000000 : ℝ)*X 0 2+(4308919203/10000000000 : ℝ)*X 1 0+(448564349/1000000000 : ℝ)*X 1 1+(827716007/2000000000 : ℝ)*X 1 2+(4308919203/10000000000 : ℝ)*X 2 0+(448564349/1000000000 : ℝ)*X 2 1+(827716007/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1093475710880913861826436229/86350000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2181102479/100000000000000 : ℝ)*(base19) + (140223649/12500000000000 : ℝ)*(base23) + (227677419/100000000000000 : ℝ)*(lower2) + (93410267/100000000000000 : ℝ)*(upper3) + (15285669/100000000000000 : ℝ)*(lower4) + (4504034559197751/100000000000000 : ℝ)*(major0) + (4504034559197751/100000000000000 : ℝ)*(major1) + (4504034559197751/100000000000000 : ℝ)*(major2) + (6147495189844597/100000000000000 : ℝ)*(sp0) + (6147522577020583/100000000000000 : ℝ)*(sp1) + (614752363633387/10000000000000 : ℝ)*(sp2) + (57210545105107/2000000000000 : ℝ)*(sp3) + (14784139233/50000000000000 : ℝ)*(sp4) + (1668290717/10000000000000 : ℝ)*(sp7) + (71513598454063/2500000000000 : ℝ)*(f.failure) + (6147524758123063/100000000000000 : ℝ)*(f.sum) + (12275968808507/1727000000000000000000000000 : ℝ)*base65 + (1325902385627690419/172700000000000000000000000000000 : ℝ)*base67 + (220441509146190419/172700000000000000000000000000000 : ℝ)*base69 + (1909417153321790419/172700000000000000000000000000000 : ℝ)*base71 + (746210137727/215875000000000000000000000 : ℝ)*base74 + (3165460381560490419/172700000000000000000000000000000 : ℝ)*base75 + (1080675803438090419/172700000000000000000000000000000 : ℝ)*base77 + (3593270051107090419/172700000000000000000000000000000 : ℝ)*base79 + (481203551077/863500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (89593/12500000000000000000 : ℝ)*base90 + (89593/12500000000000000000 : ℝ)*base92 + (89593/12500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (407427104299957422355614729/43175000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (894991609/50000000000000 : ℝ)*(base19) + (1900053203/100000000000000 : ℝ)*(base23) + (152542287/25000000000000 : ℝ)*(lower1) + (95318437/50000000000000 : ℝ)*(upper3) + (24460521/50000000000000 : ℝ)*(lower4) + (56413689/25000000000000 : ℝ)*(upper5) + (2268357138082247/50000000000000 : ℝ)*(major0) + (2268357138082247/50000000000000 : ℝ)*(major1) + (2268357138082247/50000000000000 : ℝ)*(major2) + (242326349/50000000000000 : ℝ)*(sp2) + (387008073885171/6250000000000 : ℝ)*(sp4) + (3096063696089759/50000000000000 : ℝ)*(sp5) + (1238425359491367/20000000000000 : ℝ)*(sp6) + (2881299055611427/100000000000000 : ℝ)*(sp7) + (2881299055611427/100000000000000 : ℝ)*(f.failure) + (387008073885171/6250000000000 : ℝ)*(f.sum) + (1989199035123/1727000000000000000000000000 : ℝ)*base66 + (254096585320838243/86350000000000000000000000000000 : ℝ)*base67 + (399019769272611757/86350000000000000000000000000000 : ℝ)*base70 + (325944091232411757/86350000000000000000000000000000 : ℝ)*base72 + (3959377597281/863500000000000000000000000 : ℝ)*base74 + (19192469865542911757/86350000000000000000000000000000 : ℝ)*base76 + (175843143074188243/86350000000000000000000000000000 : ℝ)*base77 + (347434522520561757/86350000000000000000000000000000 : ℝ)*base80 + (6668883076303/1727000000000000000000000000 : ℝ)*base81 + (382797/500000000000000000000 : ℝ)*base90 + (382797/500000000000000000000 : ℝ)*base92 + (382797/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1411_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7872689/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (461/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5649/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5651/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3687/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1411_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1411_s7_0 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1985831223/10000000000 : ℝ)*x 0 + (2704561767/5000000000 : ℝ)*x 1 + (5246512023/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1985831223/10000000000 : ℝ)^4371 ≤ (3027546859259/25000000000000 : ℝ)^3347 := by
    have hnat : (1985831223 : ℕ)^4371*25000000000000^3347 ≤ 3027546859259^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1985831223 10000000000 3027546859259 25000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2704561767/5000000000 : ℝ)^4371 ≤ (11205164891581/25000000000000 : ℝ)^3347 := by
    have hnat : (2704561767 : ℕ)^4371*25000000000000^3347 ≤ 11205164891581^3347*5000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704561767 5000000000 11205164891581 25000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246512023/10000000000 : ℝ)^4371 ≤ (21534576491029/50000000000000 : ℝ)^3347 := by
    have hnat : (5246512023 : ℕ)^4371*50000000000000^3347 ≤ 21534576491029^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246512023 10000000000 21534576491029 50000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1985831223/10000000000 : ℝ), (2704561767/5000000000 : ℝ), (5246512023/10000000000 : ℝ)] ![(3027546859259/25000000000000 : ℝ), (11205164891581/25000000000000 : ℝ), (21534576491029/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1985831223/10000000000 : ℝ)|^4371 ≤ (3027546859259/25000000000000 : ℝ)^3347
        have hw : |(-1985831223/10000000000 : ℝ)|=(1985831223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2704561767/5000000000 : ℝ)|^4371 ≤ (11205164891581/25000000000000 : ℝ)^3347
        have hw : |(2704561767/5000000000 : ℝ)|=(2704561767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246512023/10000000000 : ℝ)|^4371 ≤ (21534576491029/50000000000000 : ℝ)^3347
        have hw : |(5246512023/10000000000 : ℝ)|=(5246512023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_s7_1 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673846733/5000000000 : ℝ)*x 0 + (-129289467/625000000 : ℝ)*x 1 + (1311628001/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673846733/5000000000 : ℝ)^4371 ≤ (44157068862709/100000000000000 : ℝ)^3347 := by
    have hnat : (2673846733 : ℕ)^4371*100000000000000^3347 ≤ 44157068862709^3347*5000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673846733 5000000000 44157068862709 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (129289467/625000000 : ℝ)^4371 ≤ (2554755669467/20000000000000 : ℝ)^3347 := by
    have hnat : (129289467 : ℕ)^4371*20000000000000^3347 ≤ 2554755669467^3347*625000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129289467 625000000 2554755669467 20000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311628001/2500000000 : ℝ)^4371 ≤ (21534576389183/50000000000000 : ℝ)^3347 := by
    have hnat : (1311628001 : ℕ)^4371*50000000000000^3347 ≤ 21534576389183^3347*2500000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311628001 2500000000 21534576389183 50000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673846733/5000000000 : ℝ), (-129289467/625000000 : ℝ), (1311628001/2500000000 : ℝ)] ![(44157068862709/100000000000000 : ℝ), (2554755669467/20000000000000 : ℝ), (21534576389183/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673846733/5000000000 : ℝ)|^4371 ≤ (44157068862709/100000000000000 : ℝ)^3347
        have hw : |(2673846733/5000000000 : ℝ)|=(2673846733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-129289467/625000000 : ℝ)|^4371 ≤ (2554755669467/20000000000000 : ℝ)^3347
        have hw : |(-129289467/625000000 : ℝ)|=(129289467/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311628001/2500000000 : ℝ)|^4371 ≤ (21534576389183/50000000000000 : ℝ)^3347
        have hw : |(1311628001/2500000000 : ℝ)|=(1311628001/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_s7_2 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673846679/5000000000 : ℝ)*x 0 + (2623256071/5000000000 : ℝ)*x 1 + (-2068631433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673846679/5000000000 : ℝ)^4371 ≤ (22078533849047/50000000000000 : ℝ)^3347 := by
    have hnat : (2673846679 : ℕ)^4371*50000000000000^3347 ≤ 22078533849047^3347*5000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673846679 5000000000 22078533849047 50000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623256071/5000000000 : ℝ)^4371 ≤ (8613830851563/20000000000000 : ℝ)^3347 := by
    have hnat : (2623256071 : ℕ)^4371*20000000000000^3347 ≤ 8613830851563^3347*5000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623256071 5000000000 8613830851563 20000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2068631433/10000000000 : ℝ)^4371 ≤ (12773778032831/100000000000000 : ℝ)^3347 := by
    have hnat : (2068631433 : ℕ)^4371*100000000000000^3347 ≤ 12773778032831^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2068631433 10000000000 12773778032831 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673846679/5000000000 : ℝ), (2623256071/5000000000 : ℝ), (-2068631433/10000000000 : ℝ)] ![(22078533849047/50000000000000 : ℝ), (8613830851563/20000000000000 : ℝ), (12773778032831/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673846679/5000000000 : ℝ)|^4371 ≤ (22078533849047/50000000000000 : ℝ)^3347
        have hw : |(2673846679/5000000000 : ℝ)|=(2673846679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623256071/5000000000 : ℝ)|^4371 ≤ (8613830851563/20000000000000 : ℝ)^3347
        have hw : |(2623256071/5000000000 : ℝ)|=(2623256071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2068631433/10000000000 : ℝ)|^4371 ≤ (12773778032831/100000000000000 : ℝ)^3347
        have hw : |(-2068631433/10000000000 : ℝ)|=(2068631433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_s7_3 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (172355863/400000000 : ℝ)*x 0 + (4137376001/10000000000 : ℝ)*x 1 + (4486840473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (172355863/400000000 : ℝ)^4371 ≤ (16652213632121/50000000000000 : ℝ)^3347 := by
    have hnat : (172355863 : ℕ)^4371*50000000000000^3347 ≤ 16652213632121^3347*400000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172355863 400000000 16652213632121 50000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4137376001/10000000000 : ℝ)^4371 ≤ (31583748998177/100000000000000 : ℝ)^3347 := by
    have hnat : (4137376001 : ℕ)^4371*100000000000000^3347 ≤ 31583748998177^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4137376001 10000000000 31583748998177 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4486840473/10000000000 : ℝ)^4371 ≤ (35111823727951/100000000000000 : ℝ)^3347 := by
    have hnat : (4486840473 : ℕ)^4371*100000000000000^3347 ≤ 35111823727951^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4486840473 10000000000 35111823727951 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(172355863/400000000 : ℝ), (4137376001/10000000000 : ℝ), (4486840473/10000000000 : ℝ)] ![(16652213632121/50000000000000 : ℝ), (31583748998177/100000000000000 : ℝ), (35111823727951/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(172355863/400000000 : ℝ)|^4371 ≤ (16652213632121/50000000000000 : ℝ)^3347
        have hw : |(172355863/400000000 : ℝ)|=(172355863/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4137376001/10000000000 : ℝ)|^4371 ≤ (31583748998177/100000000000000 : ℝ)^3347
        have hw : |(4137376001/10000000000 : ℝ)|=(4137376001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4486840473/10000000000 : ℝ)|^4371 ≤ (35111823727951/100000000000000 : ℝ)^3347
        have hw : |(4486840473/10000000000 : ℝ)|=(4486840473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_s7_4 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1985842701/10000000000 : ℝ)*x 0 + (5247097413/10000000000 : ℝ)*x 1 + (5408535117/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1985842701/10000000000 : ℝ)^4371 ≤ (1513784856051/12500000000000 : ℝ)^3347 := by
    have hnat : (1985842701 : ℕ)^4371*12500000000000^3347 ≤ 1513784856051^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1985842701 10000000000 1513784856051 12500000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247097413/10000000000 : ℝ)^4371 ≤ (21537714422599/50000000000000 : ℝ)^3347 := by
    have hnat : (5247097413 : ℕ)^4371*50000000000000^3347 ≤ 21537714422599^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247097413 10000000000 21537714422599 50000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5408535117/10000000000 : ℝ)^4371 ≤ (8962858455877/20000000000000 : ℝ)^3347 := by
    have hnat : (5408535117 : ℕ)^4371*20000000000000^3347 ≤ 8962858455877^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408535117 10000000000 8962858455877 20000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1985842701/10000000000 : ℝ), (5247097413/10000000000 : ℝ), (5408535117/10000000000 : ℝ)] ![(1513784856051/12500000000000 : ℝ), (21537714422599/50000000000000 : ℝ), (8962858455877/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1985842701/10000000000 : ℝ)|^4371 ≤ (1513784856051/12500000000000 : ℝ)^3347
        have hw : |(-1985842701/10000000000 : ℝ)|=(1985842701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247097413/10000000000 : ℝ)|^4371 ≤ (21537714422599/50000000000000 : ℝ)^3347
        have hw : |(5247097413/10000000000 : ℝ)|=(5247097413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5408535117/10000000000 : ℝ)|^4371 ≤ (8962858455877/20000000000000 : ℝ)^3347
        have hw : |(5408535117/10000000000 : ℝ)|=(5408535117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_s7_5 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305494527/10000000000 : ℝ)*x 0 + (-1906608371/10000000000 : ℝ)*x 1 + (43268281/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305494527/10000000000 : ℝ)^4371 ≤ (21851283935229/50000000000000 : ℝ)^3347 := by
    have hnat : (5305494527 : ℕ)^4371*50000000000000^3347 ≤ 21851283935229^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305494527 10000000000 21851283935229 50000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1906608371/10000000000 : ℝ)^4371 ≤ (5741569876499/50000000000000 : ℝ)^3347 := by
    have hnat : (1906608371 : ℕ)^4371*50000000000000^3347 ≤ 5741569876499^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1906608371 10000000000 5741569876499 50000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (43268281/80000000 : ℝ)^4371 ≤ (350111659109/781250000000 : ℝ)^3347 := by
    have hnat : (43268281 : ℕ)^4371*781250000000^3347 ≤ 350111659109^3347*80000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43268281 80000000 350111659109 781250000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305494527/10000000000 : ℝ), (-1906608371/10000000000 : ℝ), (43268281/80000000 : ℝ)] ![(21851283935229/50000000000000 : ℝ), (5741569876499/50000000000000 : ℝ), (350111659109/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305494527/10000000000 : ℝ)|^4371 ≤ (21851283935229/50000000000000 : ℝ)^3347
        have hw : |(5305494527/10000000000 : ℝ)|=(5305494527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1906608371/10000000000 : ℝ)|^4371 ≤ (5741569876499/50000000000000 : ℝ)^3347
        have hw : |(-1906608371/10000000000 : ℝ)|=(1906608371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(43268281/80000000 : ℝ)|^4371 ≤ (350111659109/781250000000 : ℝ)^3347
        have hw : |(43268281/80000000 : ℝ)|=(43268281/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_s7_6 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305494533/10000000000 : ℝ)*x 0 + (5408535123/10000000000 : ℝ)*x 1 + (-381321673/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305494533/10000000000 : ℝ)^4371 ≤ (21851283967501/50000000000000 : ℝ)^3347 := by
    have hnat : (5305494533 : ℕ)^4371*50000000000000^3347 ≤ 21851283967501^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305494533 10000000000 21851283967501 50000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5408535123/10000000000 : ℝ)^4371 ≤ (44814292344311/100000000000000 : ℝ)^3347 := by
    have hnat : (5408535123 : ℕ)^4371*100000000000000^3347 ≤ 44814292344311^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408535123 10000000000 44814292344311 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (381321673/2000000000 : ℝ)^4371 ≤ (2296627941161/20000000000000 : ℝ)^3347 := by
    have hnat : (381321673 : ℕ)^4371*20000000000000^3347 ≤ 2296627941161^3347*2000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      381321673 2000000000 2296627941161 20000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305494533/10000000000 : ℝ), (5408535123/10000000000 : ℝ), (-381321673/2000000000 : ℝ)] ![(21851283967501/50000000000000 : ℝ), (44814292344311/100000000000000 : ℝ), (2296627941161/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305494533/10000000000 : ℝ)|^4371 ≤ (21851283967501/50000000000000 : ℝ)^3347
        have hw : |(5305494533/10000000000 : ℝ)|=(5305494533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5408535123/10000000000 : ℝ)|^4371 ≤ (44814292344311/100000000000000 : ℝ)^3347
        have hw : |(5408535123/10000000000 : ℝ)|=(5408535123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-381321673/2000000000 : ℝ)|^4371 ≤ (2296627941161/20000000000000 : ℝ)^3347
        have hw : |(-381321673/2000000000 : ℝ)|=(381321673/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_s7_7 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (134653787/312500000 : ℝ)*x 0 + (4485582439/10000000000 : ℝ)*x 1 + (1034660151/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134653787/312500000 : ℝ)^4371 ≤ (16652337833193/50000000000000 : ℝ)^3347 := by
    have hnat : (134653787 : ℕ)^4371*50000000000000^3347 ≤ 16652337833193^3347*312500000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134653787 312500000 16652337833193 50000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4485582439/10000000000 : ℝ)^4371 ≤ (17549483779033/50000000000000 : ℝ)^3347 := by
    have hnat : (4485582439 : ℕ)^4371*50000000000000^3347 ≤ 17549483779033^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4485582439 10000000000 17549483779033 50000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1034660151/2500000000 : ℝ)^4371 ≤ (15798178384339/50000000000000 : ℝ)^3347 := by
    have hnat : (1034660151 : ℕ)^4371*50000000000000^3347 ≤ 15798178384339^3347*2500000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034660151 2500000000 15798178384339 50000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(134653787/312500000 : ℝ), (4485582439/10000000000 : ℝ), (1034660151/2500000000 : ℝ)] ![(16652337833193/50000000000000 : ℝ), (17549483779033/50000000000000 : ℝ), (15798178384339/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(134653787/312500000 : ℝ)|^4371 ≤ (16652337833193/50000000000000 : ℝ)^3347
        have hw : |(134653787/312500000 : ℝ)|=(134653787/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4485582439/10000000000 : ℝ)|^4371 ≤ (17549483779033/50000000000000 : ℝ)^3347
        have hw : |(4485582439/10000000000 : ℝ)|=(4485582439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1034660151/2500000000 : ℝ)|^4371 ≤ (15798178384339/50000000000000 : ℝ)^3347
        have hw : |(1034660151/2500000000 : ℝ)|=(1034660151/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1411_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7872689/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3687/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5651/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11303/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14747/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3687/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5651/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3687/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5651/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3687/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5651/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3687/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5651/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3687/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5651/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3687/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5651/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5651/50000 : ℝ) ^ (2185/512 : ℝ) ≤ (2276178368924713/25000000000000000000 : ℝ) := by
    have hpowers : (5651/50000 : ℝ)^2185 ≤ (2276178368924713/25000000000000000000 : ℝ)^512 := by
      have hnat : (5651 : ℕ)^2185*25000000000000000000^512 ≤ 2276178368924713^512*50000^2185 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5651 50000 2276178368924713 25000000000000000000 2185 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5651/50000 : ℝ)) (X := (2276178368924713/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2185 512 (by norm_num) hpowers
    exact h
  have hpowhi : (3687/25000 : ℝ) ^ (2185/512 : ℝ) ≤ (3543347107142439/12500000000000000000 : ℝ) := by
    have hpowers : (3687/25000 : ℝ)^2185 ≤ (3543347107142439/12500000000000000000 : ℝ)^512 := by
      have hnat : (3687 : ℕ)^2185*12500000000000000000^512 ≤ 3543347107142439^512*25000^2185 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3687 25000 3543347107142439 12500000000000000000 2185 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3687/25000 : ℝ)) (X := (3543347107142439/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2185 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502276178368924713/12500000000000000000 : ℝ) ≤ (10000426662550259/10000000000000000 : ℝ) ^ (2185/512 : ℝ) := by
    have hpowers : (12502276178368924713/12500000000000000000 : ℝ)^512 ≤ (10000426662550259/10000000000000000 : ℝ)^2185 := by
      have hnat : (12502276178368924713 : ℕ)^512*10000000000000000^2185 ≤ 10000426662550259^2185*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502276178368924713 12500000000000000000 10000426662550259 10000000000000000 512 2185 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000426662550259/10000000000000000 : ℝ)) (X := (12502276178368924713/12500000000000000000 : ℝ)) (by norm_num) 2185 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (25009362872583209591/25000000000000000000 : ℝ) ≤ (2000175491206891/2000000000000000 : ℝ) ^ (2185/512 : ℝ) := by
    have hpowers : (25009362872583209591/25000000000000000000 : ℝ)^512 ≤ (2000175491206891/2000000000000000 : ℝ)^2185 := by
      have hnat : (25009362872583209591 : ℕ)^512*2000000000000000^2185 ≤ 2000175491206891^2185*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25009362872583209591 25000000000000000000 2000175491206891 2000000000000000 512 2185 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000175491206891/2000000000000000 : ℝ)) (X := (25009362872583209591/25000000000000000000 : ℝ)) (by norm_num) 2185 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (6253543347107142439/6250000000000000000 : ℝ) ≤ (10001328249518651/10000000000000000 : ℝ) ^ (2185/512 : ℝ) := by
    have hpowers : (6253543347107142439/6250000000000000000 : ℝ)^512 ≤ (10001328249518651/10000000000000000 : ℝ)^2185 := by
      have hnat : (6253543347107142439 : ℕ)^512*10000000000000000^2185 ≤ 10001328249518651^2185*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253543347107142439 6250000000000000000 10001328249518651 10000000000000000 512 2185 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001328249518651/10000000000000000 : ℝ)) (X := (6253543347107142439/6250000000000000000 : ℝ)) (by norm_num) 2185 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2276178368924713/25000000000000000000 : ℝ) ≤ ((3445128054323142613/3446000000000000000 : ℝ)+2*(112698371049/86150000000000 : ℝ)*(5651/50000 : ℝ))^(2185/512 : ℝ) := by
    rw [show (3445128054323142613/3446000000000000000 : ℝ)+2*(112698371049/86150000000000 : ℝ)*(5651/50000 : ℝ)=(10000426662550259/10000000000000000 : ℝ) by norm_num, show 1+2*(2276178368924713/25000000000000000000 : ℝ)=(12502276178368924713/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3543347107142439/12500000000000000000 : ℝ)+(2276178368924713/25000000000000000000 : ℝ) ≤ ((3445128054323142613/3446000000000000000 : ℝ)+(112698371049/86150000000000 : ℝ)*((3687/25000 : ℝ)+(5651/50000 : ℝ)))^(2185/512 : ℝ) := by
    rw [show (3445128054323142613/3446000000000000000 : ℝ)+(112698371049/86150000000000 : ℝ)*((3687/25000 : ℝ)+(5651/50000 : ℝ))=(2000175491206891/2000000000000000 : ℝ) by norm_num, show 1+(3543347107142439/12500000000000000000 : ℝ)+(2276178368924713/25000000000000000000 : ℝ)=(25009362872583209591/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3543347107142439/12500000000000000000 : ℝ) ≤ ((3445128054323142613/3446000000000000000 : ℝ)+2*(112698371049/86150000000000 : ℝ)*(3687/25000 : ℝ))^(2185/512 : ℝ) := by
    rw [show (3445128054323142613/3446000000000000000 : ℝ)+2*(112698371049/86150000000000 : ℝ)*(3687/25000 : ℝ)=(10001328249518651/10000000000000000 : ℝ) by norm_num, show 1+2*(3543347107142439/12500000000000000000 : ℝ)=(6253543347107142439/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3445128054323142613/3446000000000000000 : ℝ)*(X 1 0+X 2 0)+(112698371049/86150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2185/512 : ℝ)) (lo := (5651/50000 : ℝ)) (hi := (3687/25000 : ℝ)) (c := (3445128054323142613/3446000000000000000 : ℝ)) (alpha := (112698371049/86150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3445128054323142613/3446000000000000000 : ℝ)*(X 0 1+X 2 1)+(112698371049/86150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2185/512 : ℝ)) (lo := (5651/50000 : ℝ)) (hi := (3687/25000 : ℝ)) (c := (3445128054323142613/3446000000000000000 : ℝ)) (alpha := (112698371049/86150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3445128054323142613/3446000000000000000 : ℝ)*(X 0 2+X 1 2)+(112698371049/86150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2185/512 : ℝ)) (lo := (5651/50000 : ℝ)) (hi := (3687/25000 : ℝ)) (c := (3445128054323142613/3446000000000000000 : ℝ)) (alpha := (112698371049/86150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1985831223/10000000000 : ℝ)*X 0 0+(2704561767/5000000000 : ℝ)*X 0 1+(5246512023/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673846733/5000000000 : ℝ)*X 1 0+(-129289467/625000000 : ℝ)*X 1 1+(1311628001/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673846679/5000000000 : ℝ)*X 2 0+(2623256071/5000000000 : ℝ)*X 2 1+(-2068631433/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((172355863/400000000 : ℝ)*X 0 0+(4137376001/10000000000 : ℝ)*X 0 1+(4486840473/10000000000 : ℝ)*X 0 2+(172355863/400000000 : ℝ)*X 1 0+(4137376001/10000000000 : ℝ)*X 1 1+(4486840473/10000000000 : ℝ)*X 1 2+(172355863/400000000 : ℝ)*X 2 0+(4137376001/10000000000 : ℝ)*X 2 1+(4486840473/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1985842701/10000000000 : ℝ)*X 0 0+(5247097413/10000000000 : ℝ)*X 0 1+(5408535117/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305494527/10000000000 : ℝ)*X 1 0+(-1906608371/10000000000 : ℝ)*X 1 1+(43268281/80000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305494533/10000000000 : ℝ)*X 2 0+(5408535123/10000000000 : ℝ)*X 2 1+(-381321673/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((134653787/312500000 : ℝ)*X 0 0+(4485582439/10000000000 : ℝ)*X 0 1+(1034660151/2500000000 : ℝ)*X 0 2+(134653787/312500000 : ℝ)*X 1 0+(4485582439/10000000000 : ℝ)*X 1 1+(1034660151/2500000000 : ℝ)*X 1 2+(134653787/312500000 : ℝ)*X 2 0+(4485582439/10000000000 : ℝ)*X 2 1+(1034660151/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1262158540718952000732595359/172300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1390749733/100000000000000 : ℝ)*(base19) + (286064527/25000000000000 : ℝ)*(base23) + (65399591/100000000000000 : ℝ)*(lower2) + (194078573/100000000000000 : ℝ)*(upper3) + (1664729/1250000000000 : ℝ)*(upper5) + (4505616348363681/100000000000000 : ℝ)*(major0) + (4505616348363681/100000000000000 : ℝ)*(major1) + (2252808174181841/50000000000000 : ℝ)*(major2) + (384353487894839/6250000000000 : ℝ)*(sp0) + (3074841259121633/50000000000000 : ℝ)*(sp1) + (1537420691183723/25000000000000 : ℝ)*(sp2) + (1430767171170257/50000000000000 : ℝ)*(sp3) + (1124107023/4000000000000 : ℝ)*(sp4) + (14201215367/100000000000000 : ℝ)*(sp7) + (2861548543555881/100000000000000 : ℝ)*(f.failure) + (6149683908992999/100000000000000 : ℝ)*(f.sum) + (13222653955789/4307500000000000000000000000 : ℝ)*base66 + (2530298437453441547/344600000000000000000000000000000 : ℝ)*base68 + (80839010103829467/172300000000000000000000000000000 : ℝ)*base70 + (1603560666267041547/344600000000000000000000000000000 : ℝ)*base72 + (4641944343669/4307500000000000000000000000 : ℝ)*base74 + (1531008702821070533/172300000000000000000000000000000 : ℝ)*base75 + (4775820428257001547/344600000000000000000000000000000 : ℝ)*base78 + (1498524776928798453/344600000000000000000000000000000 : ℝ)*base79 + (214021272493/2153750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (234009/500000000000000000000 : ℝ)*base89 + (234009/500000000000000000000 : ℝ)*base91 + (4765991/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (102651265698280683535463937/17230000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1016900423/100000000000000 : ℝ)*(base19) + (278431319/25000000000000 : ℝ)*(base23) + (345691107/100000000000000 : ℝ)*(lower1) + (25234121/20000000000000 : ℝ)*(upper3) + (3972347/10000000000000 : ℝ)*(lower4) + (63090279/50000000000000 : ℝ)*(upper5) + (453831757294783/10000000000000 : ℝ)*(major0) + (453831757294783/10000000000000 : ℝ)*(major1) + (453831757294783/10000000000000 : ℝ)*(major2) + (234909491/12500000000000 : ℝ)*(sp2) + (6194317626662009/100000000000000 : ℝ)*(sp4) + (3097158304880793/50000000000000 : ℝ)*(sp5) + (1238862926732161/20000000000000 : ℝ)*(sp6) + (360289665080431/12500000000000 : ℝ)*(sp7) + (360289665080431/12500000000000 : ℝ)*(f.failure) + (6194317626662009/100000000000000 : ℝ)*(f.sum) + (10273997149539/1723000000000000000000000000 : ℝ)*base65 + (925596870240372021/34460000000000000000000000000000 : ℝ)*base68 + (229392539462132021/34460000000000000000000000000000 : ℝ)*base70 + (3536878369411727979/34460000000000000000000000000000 : ℝ)*base71 + (125669992243/34460000000000000000000000 : ℝ)*base73 + (42979039730752021/34460000000000000000000000000000 : ℝ)*base76 + (164846722181092021/34460000000000000000000000000000 : ℝ)*base78 + (139837786269587979/34460000000000000000000000000000 : ℝ)*base79 + (3483089315679/1723000000000000000000000000 : ℝ)*base81 + (501041/62500000000000000000 : ℝ)*base90 + (501041/62500000000000000000 : ℝ)*base92 + (501041/62500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1411_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7872689/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3687/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5651/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11303/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14747/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1411_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1411_box_0 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1823855739/10000000000 : ℝ)*x 0 + (1077405317/2000000000 : ℝ)*x 1 + (5387026217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1823855739/10000000000 : ℝ)^4371 ≤ (677288614061/6250000000000 : ℝ)^3347 := by
    have hnat : (1823855739 : ℕ)^4371*6250000000000^3347 ≤ 677288614061^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1823855739 10000000000 677288614061 6250000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1077405317/2000000000 : ℝ)^4371 ≤ (44581693072049/100000000000000 : ℝ)^3347 := by
    have hnat : (1077405317 : ℕ)^4371*100000000000000^3347 ≤ 44581693072049^3347*2000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077405317 2000000000 44581693072049 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5387026217/10000000000 : ℝ)^4371 ≤ (22290844547411/50000000000000 : ℝ)^3347 := by
    have hnat : (5387026217 : ℕ)^4371*50000000000000^3347 ≤ 22290844547411^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387026217 10000000000 22290844547411 50000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1823855739/10000000000 : ℝ), (1077405317/2000000000 : ℝ), (5387026217/10000000000 : ℝ)] ![(677288614061/6250000000000 : ℝ), (44581693072049/100000000000000 : ℝ), (22290844547411/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1823855739/10000000000 : ℝ)|^4371 ≤ (677288614061/6250000000000 : ℝ)^3347
        have hw : |(-1823855739/10000000000 : ℝ)|=(1823855739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1077405317/2000000000 : ℝ)|^4371 ≤ (44581693072049/100000000000000 : ℝ)^3347
        have hw : |(1077405317/2000000000 : ℝ)|=(1077405317/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5387026217/10000000000 : ℝ)|^4371 ≤ (22290844547411/50000000000000 : ℝ)^3347
        have hw : |(5387026217/10000000000 : ℝ)|=(5387026217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_box_1 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5285924561/10000000000 : ℝ)*x 0 + (-245335083/1250000000 : ℝ)*x 1 + (269351313/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285924561/10000000000 : ℝ)^4371 ≤ (869843307203/2000000000000 : ℝ)^3347 := by
    have hnat : (5285924561 : ℕ)^4371*2000000000000^3347 ≤ 869843307203^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285924561 10000000000 869843307203 2000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (245335083/1250000000 : ℝ)^4371 ≤ (11926145066419/100000000000000 : ℝ)^3347 := by
    have hnat : (245335083 : ℕ)^4371*100000000000000^3347 ≤ 11926145066419^3347*1250000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      245335083 1250000000 11926145066419 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269351313/500000000 : ℝ)^4371 ≤ (87073612421/195312500000 : ℝ)^3347 := by
    have hnat : (269351313 : ℕ)^4371*195312500000^3347 ≤ 87073612421^3347*500000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269351313 500000000 87073612421 195312500000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285924561/10000000000 : ℝ), (-245335083/1250000000 : ℝ), (269351313/500000000 : ℝ)] ![(869843307203/2000000000000 : ℝ), (11926145066419/100000000000000 : ℝ), (87073612421/195312500000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285924561/10000000000 : ℝ)|^4371 ≤ (869843307203/2000000000000 : ℝ)^3347
        have hw : |(5285924561/10000000000 : ℝ)|=(5285924561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-245335083/1250000000 : ℝ)|^4371 ≤ (11926145066419/100000000000000 : ℝ)^3347
        have hw : |(-245335083/1250000000 : ℝ)|=(245335083/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269351313/500000000 : ℝ)|^4371 ≤ (87073612421/195312500000 : ℝ)^3347
        have hw : |(269351313/500000000 : ℝ)|=(269351313/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_box_2 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5285923979/10000000000 : ℝ)*x 0 + (10774053/20000000 : ℝ)*x 1 + (-15701449/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285923979/10000000000 : ℝ)^4371 ≤ (21746079553217/50000000000000 : ℝ)^3347 := by
    have hnat : (5285923979 : ℕ)^4371*50000000000000^3347 ≤ 21746079553217^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285923979 10000000000 21746079553217 50000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (10774053/20000000 : ℝ)^4371 ≤ (11145423038349/25000000000000 : ℝ)^3347 := by
    have hnat : (10774053 : ℕ)^4371*25000000000000^3347 ≤ 11145423038349^3347*20000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10774053 20000000 11145423038349 25000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (15701449/80000000 : ℝ)^4371 ≤ (2385229744939/20000000000000 : ℝ)^3347 := by
    have hnat : (15701449 : ℕ)^4371*20000000000000^3347 ≤ 2385229744939^3347*80000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15701449 80000000 2385229744939 20000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285923979/10000000000 : ℝ), (10774053/20000000 : ℝ), (-15701449/80000000 : ℝ)] ![(21746079553217/50000000000000 : ℝ), (11145423038349/25000000000000 : ℝ), (2385229744939/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285923979/10000000000 : ℝ)|^4371 ≤ (21746079553217/50000000000000 : ℝ)^3347
        have hw : |(5285923979/10000000000 : ℝ)|=(5285923979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(10774053/20000000 : ℝ)|^4371 ≤ (11145423038349/25000000000000 : ℝ)^3347
        have hw : |(10774053/20000000 : ℝ)|=(10774053/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-15701449/80000000 : ℝ)|^4371 ≤ (2385229744939/20000000000000 : ℝ)^3347
        have hw : |(-15701449/80000000 : ℝ)|=(15701449/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_box_3 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4455562407/10000000000 : ℝ)*x 0 + (847861531/2000000000 : ℝ)*x 1 + (529913487/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4455562407/10000000000 : ℝ)^4371 ≤ (17396256458383/50000000000000 : ℝ)^3347 := by
    have hnat : (4455562407 : ℕ)^4371*50000000000000^3347 ≤ 17396256458383^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4455562407 10000000000 17396256458383 50000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (847861531/2000000000 : ℝ)^4371 ≤ (32603742324467/100000000000000 : ℝ)^3347 := by
    have hnat : (847861531 : ℕ)^4371*100000000000000^3347 ≤ 32603742324467^3347*2000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      847861531 2000000000 32603742324467 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (529913487/1250000000 : ℝ)^4371 ≤ (32603744745021/100000000000000 : ℝ)^3347 := by
    have hnat : (529913487 : ℕ)^4371*100000000000000^3347 ≤ 32603744745021^3347*1250000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529913487 1250000000 32603744745021 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4455562407/10000000000 : ℝ), (847861531/2000000000 : ℝ), (529913487/1250000000 : ℝ)] ![(17396256458383/50000000000000 : ℝ), (32603742324467/100000000000000 : ℝ), (32603744745021/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4455562407/10000000000 : ℝ)|^4371 ≤ (17396256458383/50000000000000 : ℝ)^3347
        have hw : |(4455562407/10000000000 : ℝ)|=(4455562407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(847861531/2000000000 : ℝ)|^4371 ≤ (32603742324467/100000000000000 : ℝ)^3347
        have hw : |(847861531/2000000000 : ℝ)|=(847861531/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(529913487/1250000000 : ℝ)|^4371 ≤ (32603744745021/100000000000000 : ℝ)^3347
        have hw : |(529913487/1250000000 : ℝ)|=(529913487/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_box_4 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-33602271/156250000 : ℝ)*x 0 + (2633123463/5000000000 : ℝ)*x 1 + (5266246513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33602271/156250000 : ℝ)^4371 ≤ (6719156788081/50000000000000 : ℝ)^3347 := by
    have hnat : (33602271 : ℕ)^4371*50000000000000^3347 ≤ 6719156788081^3347*156250000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33602271 156250000 6719156788081 50000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633123463/5000000000 : ℝ)^4371 ≤ (43280845426503/100000000000000 : ℝ)^3347 := by
    have hnat : (2633123463 : ℕ)^4371*100000000000000^3347 ≤ 43280845426503^3347*5000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633123463 5000000000 43280845426503 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266246513/10000000000 : ℝ)^4371 ≤ (4328084099379/10000000000000 : ℝ)^3347 := by
    have hnat : (5266246513 : ℕ)^4371*10000000000000^3347 ≤ 4328084099379^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266246513 10000000000 4328084099379 10000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-33602271/156250000 : ℝ), (2633123463/5000000000 : ℝ), (5266246513/10000000000 : ℝ)] ![(6719156788081/50000000000000 : ℝ), (43280845426503/100000000000000 : ℝ), (4328084099379/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-33602271/156250000 : ℝ)|^4371 ≤ (6719156788081/50000000000000 : ℝ)^3347
        have hw : |(-33602271/156250000 : ℝ)|=(33602271/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633123463/5000000000 : ℝ)|^4371 ≤ (43280845426503/100000000000000 : ℝ)^3347
        have hw : |(2633123463/5000000000 : ℝ)|=(2633123463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266246513/10000000000 : ℝ)|^4371 ≤ (4328084099379/10000000000000 : ℝ)^3347
        have hw : |(5266246513/10000000000 : ℝ)|=(5266246513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_box_5 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5370513841/10000000000 : ℝ)*x 0 + (-402320483/2000000000 : ℝ)*x 1 + (5266247453/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5370513841/10000000000 : ℝ)^4371 ≤ (8880662467671/20000000000000 : ℝ)^3347 := by
    have hnat : (5370513841 : ℕ)^4371*20000000000000^3347 ≤ 8880662467671^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370513841 10000000000 8880662467671 20000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (402320483/2000000000 : ℝ)^4371 ≤ (12315836565171/100000000000000 : ℝ)^3347 := by
    have hnat : (402320483 : ℕ)^4371*100000000000000^3347 ≤ 12315836565171^3347*2000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      402320483 2000000000 12315836565171 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266247453/10000000000 : ℝ)^4371 ≤ (1731234043311/4000000000000 : ℝ)^3347 := by
    have hnat : (5266247453 : ℕ)^4371*4000000000000^3347 ≤ 1731234043311^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266247453 10000000000 1731234043311 4000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5370513841/10000000000 : ℝ), (-402320483/2000000000 : ℝ), (5266247453/10000000000 : ℝ)] ![(8880662467671/20000000000000 : ℝ), (12315836565171/100000000000000 : ℝ), (1731234043311/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5370513841/10000000000 : ℝ)|^4371 ≤ (8880662467671/20000000000000 : ℝ)^3347
        have hw : |(5370513841/10000000000 : ℝ)|=(5370513841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-402320483/2000000000 : ℝ)|^4371 ≤ (12315836565171/100000000000000 : ℝ)^3347
        have hw : |(-402320483/2000000000 : ℝ)|=(402320483/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266247453/10000000000 : ℝ)|^4371 ≤ (1731234043311/4000000000000 : ℝ)^3347
        have hw : |(5266247453/10000000000 : ℝ)|=(5266247453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_box_6 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5370513897/10000000000 : ℝ)*x 0 + (2633123431/5000000000 : ℝ)*x 1 + (-502900783/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5370513897/10000000000 : ℝ)^4371 ≤ (44403312943017/100000000000000 : ℝ)^3347 := by
    have hnat : (5370513897 : ℕ)^4371*100000000000000^3347 ≤ 44403312943017^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370513897 10000000000 44403312943017 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633123431/5000000000 : ℝ)^4371 ≤ (21640422369797/50000000000000 : ℝ)^3347 := by
    have hnat : (2633123431 : ℕ)^4371*50000000000000^3347 ≤ 21640422369797^3347*5000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633123431 5000000000 21640422369797 50000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (502900783/2500000000 : ℝ)^4371 ≤ (6157921148981/50000000000000 : ℝ)^3347 := by
    have hnat : (502900783 : ℕ)^4371*50000000000000^3347 ≤ 6157921148981^3347*2500000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      502900783 2500000000 6157921148981 50000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5370513897/10000000000 : ℝ), (2633123431/5000000000 : ℝ), (-502900783/2500000000 : ℝ)] ![(44403312943017/100000000000000 : ℝ), (21640422369797/50000000000000 : ℝ), (6157921148981/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5370513897/10000000000 : ℝ)|^4371 ≤ (44403312943017/100000000000000 : ℝ)^3347
        have hw : |(5370513897/10000000000 : ℝ)|=(5370513897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633123431/5000000000 : ℝ)|^4371 ≤ (21640422369797/50000000000000 : ℝ)^3347
        have hw : |(2633123431/5000000000 : ℝ)|=(2633123431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-502900783/2500000000 : ℝ)|^4371 ≤ (6157921148981/50000000000000 : ℝ)^3347
        have hw : |(-502900783/2500000000 : ℝ)|=(502900783/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_box_7 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4161206087/10000000000 : ℝ)*x 0 + (4386434423/10000000000 : ℝ)*x 1 + (4386434597/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4161206087/10000000000 : ℝ)^4371 ≤ (397769085381/1250000000000 : ℝ)^3347 := by
    have hnat : (4161206087 : ℕ)^4371*1250000000000^3347 ≤ 397769085381^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4161206087 10000000000 397769085381 1250000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4386434423/10000000000 : ℝ)^4371 ≤ (34089235694461/100000000000000 : ℝ)^3347 := by
    have hnat : (4386434423 : ℕ)^4371*100000000000000^3347 ≤ 34089235694461^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4386434423 10000000000 34089235694461 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4386434597/10000000000 : ℝ)^4371 ≤ (34089237460417/100000000000000 : ℝ)^3347 := by
    have hnat : (4386434597 : ℕ)^4371*100000000000000^3347 ≤ 34089237460417^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4386434597 10000000000 34089237460417 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4161206087/10000000000 : ℝ), (4386434423/10000000000 : ℝ), (4386434597/10000000000 : ℝ)] ![(397769085381/1250000000000 : ℝ), (34089235694461/100000000000000 : ℝ), (34089237460417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4161206087/10000000000 : ℝ)|^4371 ≤ (397769085381/1250000000000 : ℝ)^3347
        have hw : |(4161206087/10000000000 : ℝ)|=(4161206087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4386434423/10000000000 : ℝ)|^4371 ≤ (34089235694461/100000000000000 : ℝ)^3347
        have hw : |(4386434423/10000000000 : ℝ)|=(4386434423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4386434597/10000000000 : ℝ)|^4371 ≤ (34089237460417/100000000000000 : ℝ)^3347
        have hw : |(4386434597/10000000000 : ℝ)|=(4386434597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_box_8 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2081774573/10000000000 : ℝ)*x 0 + (2591392449/5000000000 : ℝ)*x 1 + (1080202341/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2081774573/10000000000 : ℝ)^4371 ≤ (402495931757/3125000000000 : ℝ)^3347 := by
    have hnat : (2081774573 : ℕ)^4371*3125000000000^3347 ≤ 402495931757^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2081774573 10000000000 402495931757 3125000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2591392449/5000000000 : ℝ)^4371 ≤ (42387230382051/100000000000000 : ℝ)^3347 := by
    have hnat : (2591392449 : ℕ)^4371*100000000000000^3347 ≤ 42387230382051^3347*5000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591392449 5000000000 42387230382051 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1080202341/2000000000 : ℝ)^4371 ≤ (11183224945451/25000000000000 : ℝ)^3347 := by
    have hnat : (1080202341 : ℕ)^4371*25000000000000^3347 ≤ 11183224945451^3347*2000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080202341 2000000000 11183224945451 25000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2081774573/10000000000 : ℝ), (2591392449/5000000000 : ℝ), (1080202341/2000000000 : ℝ)] ![(402495931757/3125000000000 : ℝ), (42387230382051/100000000000000 : ℝ), (11183224945451/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2081774573/10000000000 : ℝ)|^4371 ≤ (402495931757/3125000000000 : ℝ)^3347
        have hw : |(-2081774573/10000000000 : ℝ)|=(2081774573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2591392449/5000000000 : ℝ)|^4371 ≤ (42387230382051/100000000000000 : ℝ)^3347
        have hw : |(2591392449/5000000000 : ℝ)|=(2591392449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1080202341/2000000000 : ℝ)|^4371 ≤ (11183224945451/25000000000000 : ℝ)^3347
        have hw : |(1080202341/2000000000 : ℝ)|=(1080202341/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_box_9 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2638062749/5000000000 : ℝ)*x 0 + (-1956888461/10000000000 : ℝ)*x 1 + (675126421/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638062749/5000000000 : ℝ)^4371 ≤ (21693451090111/50000000000000 : ℝ)^3347 := by
    have hnat : (2638062749 : ℕ)^4371*50000000000000^3347 ≤ 21693451090111^3347*5000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638062749 5000000000 21693451090111 50000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1956888461/10000000000 : ℝ)^4371 ≤ (5940100836357/50000000000000 : ℝ)^3347 := by
    have hnat : (1956888461 : ℕ)^4371*50000000000000^3347 ≤ 5940100836357^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1956888461 10000000000 5940100836357 50000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (675126421/1250000000 : ℝ)^4371 ≤ (22366448068363/50000000000000 : ℝ)^3347 := by
    have hnat : (675126421 : ℕ)^4371*50000000000000^3347 ≤ 22366448068363^3347*1250000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675126421 1250000000 22366448068363 50000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638062749/5000000000 : ℝ), (-1956888461/10000000000 : ℝ), (675126421/1250000000 : ℝ)] ![(21693451090111/50000000000000 : ℝ), (5940100836357/50000000000000 : ℝ), (22366448068363/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638062749/5000000000 : ℝ)|^4371 ≤ (21693451090111/50000000000000 : ℝ)^3347
        have hw : |(2638062749/5000000000 : ℝ)|=(2638062749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1956888461/10000000000 : ℝ)|^4371 ≤ (5940100836357/50000000000000 : ℝ)^3347
        have hw : |(-1956888461/10000000000 : ℝ)|=(1956888461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(675126421/1250000000 : ℝ)|^4371 ≤ (22366448068363/50000000000000 : ℝ)^3347
        have hw : |(675126421/1250000000 : ℝ)|=(675126421/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_box_10 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276125383/10000000000 : ℝ)*x 0 + (5401011403/10000000000 : ℝ)*x 1 + (-244611071/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276125383/10000000000 : ℝ)^4371 ≤ (5423362618153/12500000000000 : ℝ)^3347 := by
    have hnat : (5276125383 : ℕ)^4371*12500000000000^3347 ≤ 5423362618153^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276125383 10000000000 5423362618153 12500000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5401011403/10000000000 : ℝ)^4371 ≤ (8946579303059/20000000000000 : ℝ)^3347 := by
    have hnat : (5401011403 : ℕ)^4371*20000000000000^3347 ≤ 8946579303059^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401011403 10000000000 8946579303059 20000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (244611071/1250000000 : ℝ)^4371 ≤ (11880202521047/100000000000000 : ℝ)^3347 := by
    have hnat : (244611071 : ℕ)^4371*100000000000000^3347 ≤ 11880202521047^3347*1250000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      244611071 1250000000 11880202521047 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276125383/10000000000 : ℝ), (5401011403/10000000000 : ℝ), (-244611071/1250000000 : ℝ)] ![(5423362618153/12500000000000 : ℝ), (8946579303059/20000000000000 : ℝ), (11880202521047/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276125383/10000000000 : ℝ)|^4371 ≤ (5423362618153/12500000000000 : ℝ)^3347
        have hw : |(5276125383/10000000000 : ℝ)|=(5276125383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5401011403/10000000000 : ℝ)|^4371 ≤ (8946579303059/20000000000000 : ℝ)^3347
        have hw : |(5401011403/10000000000 : ℝ)|=(5401011403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-244611071/1250000000 : ℝ)|^4371 ≤ (11880202521047/100000000000000 : ℝ)^3347
        have hw : |(-244611071/1250000000 : ℝ)|=(244611071/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_box_11 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4489088033/10000000000 : ℝ)*x 0 + (844451657/2000000000 : ℝ)*x 1 + (4222257303/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4489088033/10000000000 : ℝ)^4371 ≤ (17567397430601/50000000000000 : ℝ)^3347 := by
    have hnat : (4489088033 : ℕ)^4371*50000000000000^3347 ≤ 17567397430601^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4489088033 10000000000 17567397430601 50000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (844451657/2000000000 : ℝ)^4371 ≤ (32432607485549/100000000000000 : ℝ)^3347 := by
    have hnat : (844451657 : ℕ)^4371*100000000000000^3347 ≤ 32432607485549^3347*2000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      844451657 2000000000 32432607485549 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4222257303/10000000000 : ℝ)^4371 ≤ (32432597634701/100000000000000 : ℝ)^3347 := by
    have hnat : (4222257303 : ℕ)^4371*100000000000000^3347 ≤ 32432597634701^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4222257303 10000000000 32432597634701 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4489088033/10000000000 : ℝ), (844451657/2000000000 : ℝ), (4222257303/10000000000 : ℝ)] ![(17567397430601/50000000000000 : ℝ), (32432607485549/100000000000000 : ℝ), (32432597634701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4489088033/10000000000 : ℝ)|^4371 ≤ (17567397430601/50000000000000 : ℝ)^3347
        have hw : |(4489088033/10000000000 : ℝ)|=(4489088033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(844451657/2000000000 : ℝ)|^4371 ≤ (32432607485549/100000000000000 : ℝ)^3347
        have hw : |(844451657/2000000000 : ℝ)|=(844451657/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4222257303/10000000000 : ℝ)|^4371 ≤ (32432597634701/100000000000000 : ℝ)^3347
        have hw : |(4222257303/10000000000 : ℝ)|=(4222257303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_box_12 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-473209331/2500000000 : ℝ)*x 0 + (5468428597/10000000000 : ℝ)*x 1 + (2627565137/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (473209331/2500000000 : ℝ)^4371 ≤ (11374943980837/100000000000000 : ℝ)^3347 := by
    have hnat : (473209331 : ℕ)^4371*100000000000000^3347 ≤ 11374943980837^3347*2500000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      473209331 2500000000 11374943980837 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5468428597/10000000000 : ℝ)^4371 ≤ (1818539465151/4000000000000 : ℝ)^3347 := by
    have hnat : (5468428597 : ℕ)^4371*4000000000000^3347 ≤ 1818539465151^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5468428597 10000000000 1818539465151 4000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2627565137/5000000000 : ℝ)^4371 ≤ (21580784682471/50000000000000 : ℝ)^3347 := by
    have hnat : (2627565137 : ℕ)^4371*50000000000000^3347 ≤ 21580784682471^3347*5000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627565137 5000000000 21580784682471 50000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-473209331/2500000000 : ℝ), (5468428597/10000000000 : ℝ), (2627565137/5000000000 : ℝ)] ![(11374943980837/100000000000000 : ℝ), (1818539465151/4000000000000 : ℝ), (21580784682471/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-473209331/2500000000 : ℝ)|^4371 ≤ (11374943980837/100000000000000 : ℝ)^3347
        have hw : |(-473209331/2500000000 : ℝ)|=(473209331/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5468428597/10000000000 : ℝ)|^4371 ≤ (1818539465151/4000000000000 : ℝ)^3347
        have hw : |(5468428597/10000000000 : ℝ)|=(5468428597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2627565137/5000000000 : ℝ)|^4371 ≤ (21580784682471/50000000000000 : ℝ)^3347
        have hw : |(2627565137/5000000000 : ℝ)|=(2627565137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_box_13 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2689149277/5000000000 : ℝ)*x 0 + (-252000673/1250000000 : ℝ)*x 1 + (2627564743/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2689149277/5000000000 : ℝ)^4371 ≤ (22243693340951/50000000000000 : ℝ)^3347 := by
    have hnat : (2689149277 : ℕ)^4371*50000000000000^3347 ≤ 22243693340951^3347*5000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2689149277 5000000000 22243693340951 50000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (252000673/1250000000 : ℝ)^4371 ≤ (3087763096291/25000000000000 : ℝ)^3347 := by
    have hnat : (252000673 : ℕ)^4371*25000000000000^3347 ≤ 3087763096291^3347*1250000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      252000673 1250000000 3087763096291 25000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2627564743/5000000000 : ℝ)^4371 ≤ (21580780456417/50000000000000 : ℝ)^3347 := by
    have hnat : (2627564743 : ℕ)^4371*50000000000000^3347 ≤ 21580780456417^3347*5000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627564743 5000000000 21580780456417 50000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2689149277/5000000000 : ℝ), (-252000673/1250000000 : ℝ), (2627564743/5000000000 : ℝ)] ![(22243693340951/50000000000000 : ℝ), (3087763096291/25000000000000 : ℝ), (21580780456417/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2689149277/5000000000 : ℝ)|^4371 ≤ (22243693340951/50000000000000 : ℝ)^3347
        have hw : |(2689149277/5000000000 : ℝ)|=(2689149277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-252000673/1250000000 : ℝ)|^4371 ≤ (3087763096291/25000000000000 : ℝ)^3347
        have hw : |(-252000673/1250000000 : ℝ)|=(252000673/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2627564743/5000000000 : ℝ)|^4371 ≤ (21580780456417/50000000000000 : ℝ)^3347
        have hw : |(2627564743/5000000000 : ℝ)|=(2627564743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_box_14 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5378298421/10000000000 : ℝ)*x 0 + (525512949/1000000000 : ℝ)*x 1 + (-1008002779/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5378298421/10000000000 : ℝ)^4371 ≤ (22243692622597/50000000000000 : ℝ)^3347 := by
    have hnat : (5378298421 : ℕ)^4371*50000000000000^3347 ≤ 22243692622597^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378298421 10000000000 22243692622597 50000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (525512949/1000000000 : ℝ)^4371 ≤ (21580780477869/50000000000000 : ℝ)^3347 := by
    have hnat : (525512949 : ℕ)^4371*50000000000000^3347 ≤ 21580780477869^3347*1000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525512949 1000000000 21580780477869 50000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1008002779/5000000000 : ℝ)^4371 ≤ (3087763444329/25000000000000 : ℝ)^3347 := by
    have hnat : (1008002779 : ℕ)^4371*25000000000000^3347 ≤ 3087763444329^3347*5000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1008002779 5000000000 3087763444329 25000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5378298421/10000000000 : ℝ), (525512949/1000000000 : ℝ), (-1008002779/5000000000 : ℝ)] ![(22243692622597/50000000000000 : ℝ), (21580780477869/50000000000000 : ℝ), (3087763444329/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5378298421/10000000000 : ℝ)|^4371 ≤ (22243692622597/50000000000000 : ℝ)^3347
        have hw : |(5378298421/10000000000 : ℝ)|=(5378298421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(525512949/1000000000 : ℝ)|^4371 ≤ (21580780477869/50000000000000 : ℝ)^3347
        have hw : |(525512949/1000000000 : ℝ)|=(525512949/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1008002779/5000000000 : ℝ)|^4371 ≤ (3087763444329/25000000000000 : ℝ)^3347
        have hw : |(-1008002779/5000000000 : ℝ)|=(1008002779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_box_15 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4133664979/10000000000 : ℝ)*x 0 + (175998601/400000000 : ℝ)*x 1 + (274997767/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4133664979/10000000000 : ℝ)^4371 ≤ (31546757858993/100000000000000 : ℝ)^3347 := by
    have hnat : (4133664979 : ℕ)^4371*100000000000000^3347 ≤ 31546757858993^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4133664979 10000000000 31546757858993 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (175998601/400000000 : ℝ)^4371 ≤ (17113312443597/50000000000000 : ℝ)^3347 := by
    have hnat : (175998601 : ℕ)^4371*50000000000000^3347 ≤ 17113312443597^3347*400000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      175998601 400000000 17113312443597 50000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (274997767/625000000 : ℝ)^4371 ≤ (34226617237661/100000000000000 : ℝ)^3347 := by
    have hnat : (274997767 : ℕ)^4371*100000000000000^3347 ≤ 34226617237661^3347*625000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274997767 625000000 34226617237661 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4133664979/10000000000 : ℝ), (175998601/400000000 : ℝ), (274997767/625000000 : ℝ)] ![(31546757858993/100000000000000 : ℝ), (17113312443597/50000000000000 : ℝ), (34226617237661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4133664979/10000000000 : ℝ)|^4371 ≤ (31546757858993/100000000000000 : ℝ)^3347
        have hw : |(4133664979/10000000000 : ℝ)|=(4133664979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(175998601/400000000 : ℝ)|^4371 ≤ (17113312443597/50000000000000 : ℝ)^3347
        have hw : |(175998601/400000000 : ℝ)|=(175998601/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(274997767/625000000 : ℝ)|^4371 ≤ (34226617237661/100000000000000 : ℝ)^3347
        have hw : |(274997767/625000000 : ℝ)|=(274997767/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1411_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7872689/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14747/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11303/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62889/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59077/100000 : ℝ) ∧ (80349/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84617/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14747/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11303/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14747/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11303/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14747/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11303/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14747/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11303/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14747/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11303/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14747/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11303/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11303/100000 : ℝ) ^ (2185/512 : ℝ) ≤ (9108151866535189/100000000000000000000 : ℝ) := by
    have hpowers : (11303/100000 : ℝ)^2185 ≤ (9108151866535189/100000000000000000000 : ℝ)^512 := by
      have hnat : (11303 : ℕ)^2185*100000000000000000000^512 ≤ 9108151866535189^512*100000^2185 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11303 100000 9108151866535189 100000000000000000000 2185 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11303/100000 : ℝ)) (X := (9108151866535189/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2185 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14747/100000 : ℝ) ^ (2185/512 : ℝ) ≤ (7084643789071579/25000000000000000000 : ℝ) := by
    have hpowers : (14747/100000 : ℝ)^2185 ≤ (7084643789071579/25000000000000000000 : ℝ)^512 := by
      have hnat : (14747 : ℕ)^2185*25000000000000000000^512 ≤ 7084643789071579^512*100000^2185 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14747 100000 7084643789071579 25000000000000000000 2185 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14747/100000 : ℝ)) (X := (7084643789071579/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2185 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009108151866535189/50000000000000000000 : ℝ) ≤ (5000213411833969/5000000000000000 : ℝ) ^ (2185/512 : ℝ) := by
    have hpowers : (50009108151866535189/50000000000000000000 : ℝ)^512 ≤ (5000213411833969/5000000000000000 : ℝ)^2185 := by
      have hnat : (50009108151866535189 : ℕ)^512*5000000000000000^2185 ≤ 5000213411833969^2185*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009108151866535189 50000000000000000000 5000213411833969 5000000000000000 512 2185 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000213411833969/5000000000000000 : ℝ)) (X := (50009108151866535189/50000000000000000000 : ℝ)) (by norm_num) 2185 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (20007489345404564301/20000000000000000000 : ℝ) ≤ (2000175468890043/2000000000000000 : ℝ) ^ (2185/512 : ℝ) := by
    have hpowers : (20007489345404564301/20000000000000000000 : ℝ)^512 ≤ (2000175468890043/2000000000000000 : ℝ)^2185 := by
      have hnat : (20007489345404564301 : ℕ)^512*2000000000000000^2185 ≤ 2000175468890043^2185*20000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20007489345404564301 20000000000000000000 2000175468890043 2000000000000000 512 2185 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000175468890043/2000000000000000 : ℝ)) (X := (20007489345404564301/20000000000000000000 : ℝ)) (by norm_num) 2185 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507084643789071579/12500000000000000000 : ℝ) ≤ (2500331966308123/2500000000000000 : ℝ) ^ (2185/512 : ℝ) := by
    have hpowers : (12507084643789071579/12500000000000000000 : ℝ)^512 ≤ (2500331966308123/2500000000000000 : ℝ)^2185 := by
      have hnat : (12507084643789071579 : ℕ)^512*2500000000000000^2185 ≤ 2500331966308123^2185*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507084643789071579 12500000000000000000 2500331966308123 2500000000000000 512 2185 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500331966308123/2500000000000000 : ℝ)) (X := (12507084643789071579/12500000000000000000 : ℝ)) (by norm_num) 2185 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9108151866535189/100000000000000000000 : ℝ) ≤ ((3443128550790822461/3444000000000000000 : ℝ)+2*(450520782277/344400000000000 : ℝ)*(11303/100000 : ℝ))^(2185/512 : ℝ) := by
    rw [show (3443128550790822461/3444000000000000000 : ℝ)+2*(450520782277/344400000000000 : ℝ)*(11303/100000 : ℝ)=(5000213411833969/5000000000000000 : ℝ) by norm_num, show 1+2*(9108151866535189/100000000000000000000 : ℝ)=(50009108151866535189/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7084643789071579/25000000000000000000 : ℝ)+(9108151866535189/100000000000000000000 : ℝ) ≤ ((3443128550790822461/3444000000000000000 : ℝ)+(450520782277/344400000000000 : ℝ)*((14747/100000 : ℝ)+(11303/100000 : ℝ)))^(2185/512 : ℝ) := by
    rw [show (3443128550790822461/3444000000000000000 : ℝ)+(450520782277/344400000000000 : ℝ)*((14747/100000 : ℝ)+(11303/100000 : ℝ))=(2000175468890043/2000000000000000 : ℝ) by norm_num, show 1+(7084643789071579/25000000000000000000 : ℝ)+(9108151866535189/100000000000000000000 : ℝ)=(20007489345404564301/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7084643789071579/25000000000000000000 : ℝ) ≤ ((3443128550790822461/3444000000000000000 : ℝ)+2*(450520782277/344400000000000 : ℝ)*(14747/100000 : ℝ))^(2185/512 : ℝ) := by
    rw [show (3443128550790822461/3444000000000000000 : ℝ)+2*(450520782277/344400000000000 : ℝ)*(14747/100000 : ℝ)=(2500331966308123/2500000000000000 : ℝ) by norm_num, show 1+2*(7084643789071579/25000000000000000000 : ℝ)=(12507084643789071579/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3443128550790822461/3444000000000000000 : ℝ)*(X 1 0+X 2 0)+(450520782277/344400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2185/512 : ℝ)) (lo := (11303/100000 : ℝ)) (hi := (14747/100000 : ℝ)) (c := (3443128550790822461/3444000000000000000 : ℝ)) (alpha := (450520782277/344400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3443128550790822461/3444000000000000000 : ℝ)*(X 0 1+X 2 1)+(450520782277/344400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2185/512 : ℝ)) (lo := (11303/100000 : ℝ)) (hi := (14747/100000 : ℝ)) (c := (3443128550790822461/3444000000000000000 : ℝ)) (alpha := (450520782277/344400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3443128550790822461/3444000000000000000 : ℝ)*(X 0 2+X 1 2)+(450520782277/344400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2185/512 : ℝ)) (lo := (11303/100000 : ℝ)) (hi := (14747/100000 : ℝ)) (c := (3443128550790822461/3444000000000000000 : ℝ)) (alpha := (450520782277/344400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1823855739/10000000000 : ℝ)*X 0 0+(1077405317/2000000000 : ℝ)*X 0 1+(5387026217/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5285924561/10000000000 : ℝ)*X 1 0+(-245335083/1250000000 : ℝ)*X 1 1+(269351313/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5285923979/10000000000 : ℝ)*X 2 0+(10774053/20000000 : ℝ)*X 2 1+(-15701449/80000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4455562407/10000000000 : ℝ)*X 0 0+(847861531/2000000000 : ℝ)*X 0 1+(529913487/1250000000 : ℝ)*X 0 2+(4455562407/10000000000 : ℝ)*X 1 0+(847861531/2000000000 : ℝ)*X 1 1+(529913487/1250000000 : ℝ)*X 1 2+(4455562407/10000000000 : ℝ)*X 2 0+(847861531/2000000000 : ℝ)*X 2 1+(529913487/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-33602271/156250000 : ℝ)*X 0 0+(2633123463/5000000000 : ℝ)*X 0 1+(5266246513/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5370513841/10000000000 : ℝ)*X 1 0+(-402320483/2000000000 : ℝ)*X 1 1+(5266247453/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5370513897/10000000000 : ℝ)*X 2 0+(2633123431/5000000000 : ℝ)*X 2 1+(-502900783/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4161206087/10000000000 : ℝ)*X 0 0+(4386434423/10000000000 : ℝ)*X 0 1+(4386434597/10000000000 : ℝ)*X 0 2+(4161206087/10000000000 : ℝ)*X 1 0+(4386434423/10000000000 : ℝ)*X 1 1+(4386434597/10000000000 : ℝ)*X 1 2+(4161206087/10000000000 : ℝ)*X 2 0+(4386434423/10000000000 : ℝ)*X 2 1+(4386434597/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2081774573/10000000000 : ℝ)*X 0 0+(2591392449/5000000000 : ℝ)*X 0 1+(1080202341/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2638062749/5000000000 : ℝ)*X 1 0+(-1956888461/10000000000 : ℝ)*X 1 1+(675126421/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5276125383/10000000000 : ℝ)*X 2 0+(5401011403/10000000000 : ℝ)*X 2 1+(-244611071/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4489088033/10000000000 : ℝ)*X 0 0+(844451657/2000000000 : ℝ)*X 0 1+(4222257303/10000000000 : ℝ)*X 0 2+(4489088033/10000000000 : ℝ)*X 1 0+(844451657/2000000000 : ℝ)*X 1 1+(4222257303/10000000000 : ℝ)*X 1 2+(4489088033/10000000000 : ℝ)*X 2 0+(844451657/2000000000 : ℝ)*X 2 1+(4222257303/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-473209331/2500000000 : ℝ)*X 0 0+(5468428597/10000000000 : ℝ)*X 0 1+(2627565137/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2689149277/5000000000 : ℝ)*X 1 0+(-252000673/1250000000 : ℝ)*X 1 1+(2627564743/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5378298421/10000000000 : ℝ)*X 2 0+(525512949/1000000000 : ℝ)*X 2 1+(-1008002779/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4133664979/10000000000 : ℝ)*X 0 0+(175998601/400000000 : ℝ)*X 0 1+(274997767/625000000 : ℝ)*X 0 2+(4133664979/10000000000 : ℝ)*X 1 0+(175998601/400000000 : ℝ)*X 1 1+(274997767/625000000 : ℝ)*X 1 2+(4133664979/10000000000 : ℝ)*X 2 0+(175998601/400000000 : ℝ)*X 2 1+(274997767/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62889/100000 : ℝ) ≤ (-902417784025062832191232444393/1435000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6761523/25000000000000 : ℝ)*(upper1) + (1176031/4000000000000 : ℝ)*(upper3) + (107442221/50000000000000 : ℝ)*(lower4) + (17669473/25000000000000 : ℝ)*(lower5) + (149854560533413/5000000000000 : ℝ)*(major0) + (149854560533413/5000000000000 : ℝ)*(major1) + (149854560533413/5000000000000 : ℝ)*(major2) + (1683138639/20000000000000 : ℝ)*(sp3) + (1027917714634583/25000000000000 : ℝ)*(sp4) + (2055662671795821/50000000000000 : ℝ)*(sp5) + (2055815477072639/50000000000000 : ℝ)*(sp6) + (11896657704253/625000000000 : ℝ)*(sp7) + (345514946689/100000000000000 : ℝ)*(sp13) + (19952196527/50000000000000 : ℝ)*(sp14) + (76138945934947/4000000000000 : ℝ)*(f.failure) + (1027917714634583/25000000000000 : ℝ)*(f.sum) + (29602285049/13453125000000000000000000 : ℝ)*base66 + (64010357534353131/5740000000000000000000000000000 : ℝ)*base67 + (11211380435906869/5740000000000000000000000000000 : ℝ)*base70 + (43441822022913131/5740000000000000000000000000000 : ℝ)*base71 + (883468663451/430500000000000000000000000 : ℝ)*base73 + (9081107454733131/5740000000000000000000000000000 : ℝ)*base75 + (33690758973633131/5740000000000000000000000000000 : ℝ)*base77 + (46572164842993131/5740000000000000000000000000000 : ℝ)*base79 + (17948281736771/861000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (37517/20000000000000000000 : ℝ)*base90 + (37517/20000000000000000000 : ℝ)*base92 + (37517/20000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (59077/100000 : ℝ) ≤ (206778546074456310093666417731/350000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (20585107/50000000000000 : ℝ)*(lower0) + (52883683/20000000000000 : ℝ)*(upper2) + (4514953/100000000000000 : ℝ)*(lower4) + (22191361/25000000000000 : ℝ)*(lower5) + (767023130081363/25000000000000 : ℝ)*(major0) + (767023130081363/25000000000000 : ℝ)*(major1) + (767023130081363/25000000000000 : ℝ)*(major2) + (208396163644293/5000000000000 : ℝ)*(sp0) + (4167921651421643/100000000000000 : ℝ)*(sp1) + (2083962383836517/50000000000000 : ℝ)*(sp2) + (487140251213407/25000000000000 : ℝ)*(sp3) + (3116251391/100000000000000 : ℝ)*(sp5) + (3036629997/50000000000000 : ℝ)*(sp7) + (59791487/4000000000000 : ℝ)*(sp12) + (974283539056811/50000000000000 : ℝ)*(f.failure) + (2083962383836517/50000000000000 : ℝ)*(f.sum) + (49090475938181/4305000000000000000000000000 : ℝ)*base65 + (181381907831234781/28700000000000000000000000000000 : ℝ)*base67 + (4728835949934781/28700000000000000000000000000000 : ℝ)*base69 + (523704164127534781/28700000000000000000000000000000 : ℝ)*base71 + (7406686744937/2152500000000000000000000000 : ℝ)*base74 + (52463401112834781/28700000000000000000000000000000 : ℝ)*base75 + (416061779619134781/28700000000000000000000000000000 : ℝ)*base77 + (14807985333734781/28700000000000000000000000000000 : ℝ)*base79 + (4027027343471/4305000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (3665221/250000000000000000000 : ℝ)*base90 + (3665221/250000000000000000000 : ℝ)*base92 + (3665221/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (80349/100000 : ℝ) ≤ (230607811574637210966652171909/287000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (58583663/100000000000000 : ℝ)*(upper1) + (2400257/20000000000000 : ℝ)*(lower3) + (49461071/100000000000000 : ℝ)*(upper4) + (136724219/50000000000000 : ℝ)*(lower5) + (16884748790723/500000000000 : ℝ)*(major0) + (16884748790723/500000000000 : ℝ)*(major1) + (16884748790723/500000000000 : ℝ)*(major2) + (104258376829/100000000000000 : ℝ)*(sp2) + (4066883661/10000000000000 : ℝ)*(sp3) + (6221312601/100000000000000 : ℝ)*(sp4) + (1145596275240453/25000000000000 : ℝ)*(sp8) + (4582391322274413/100000000000000 : ℝ)*(sp9) + (286392941493599/6250000000000 : ℝ)*(sp10) + (1072341903612627/50000000000000 : ℝ)*(sp11) + (268090559507733/12500000000000 : ℝ)*(f.failure) + (4582391322274413/100000000000000 : ℝ)*(f.sum) + (1199015070221/430500000000000000000000000 : ℝ)*base66 + (1526712193994899/574000000000000000000000000000 : ℝ)*base68 + (5881198830816899/574000000000000000000000000000 : ℝ)*base70 + (1893601332610899/574000000000000000000000000000 : ℝ)*base72 + (2499931161743/861000000000000000000000000 : ℝ)*base73 + (1036241169930899/574000000000000000000000000000 : ℝ)*base76 + (3099905146696899/574000000000000000000000000000 : ℝ)*base78 + (1760610966094899/574000000000000000000000000000 : ℝ)*base80 + (82722154937/34440000000000000000000000 : ℝ)*base81 + (4037/62500000000000000000 : ℝ)*base89 + (4037/62500000000000000000 : ℝ)*base91 + (4037/62500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-84617/100000 : ℝ) ≤ (-12142185106486185691158623274243/14350000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9135063/6250000000000 : ℝ)*(lower0) + (11967601/20000000000000 : ℝ)*(upper1) + (17176089/100000000000000 : ℝ)*(upper3) + (25176627/25000000000000 : ℝ)*(lower4) + (68284596700219/2000000000000 : ℝ)*(major0) + (68284596700219/2000000000000 : ℝ)*(major1) + (426778729376369/12500000000000 : ℝ)*(major2) + (293914548327/100000000000000 : ℝ)*(sp5) + (343189446959/100000000000000 : ℝ)*(sp6) + (23450487233/50000000000000 : ℝ)*(sp7) + (4688263199126603/100000000000000 : ℝ)*(sp12) + (1171992321144569/25000000000000 : ℝ)*(sp13) + (937584001935929/20000000000000 : ℝ)*(sp14) + (2168354413373751/100000000000000 : ℝ)*(sp15) + (1084200657174109/50000000000000 : ℝ)*(f.failure) + (4688263199126603/100000000000000 : ℝ)*(f.sum) + (1816576881549/5740000000000000000000000000 : ℝ)*base65 + (22697639816632241/6888000000000000000000000000000 : ℝ)*base68 + (612097685181461609/43050000000000000000000000000000 : ℝ)*base69 + (75142043865256241/6888000000000000000000000000000 : ℝ)*base72 + (23576665440849/5740000000000000000000000000 : ℝ)*base73 + (258754992844211609/43050000000000000000000000000000 : ℝ)*base75 + (22227597072394347/2296000000000000000000000000000 : ℝ)*base78 + (21339401094746347/2296000000000000000000000000000 : ℝ)*base80 + (6955084669357/1722000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (4009101/250000000000000000000 : ℝ)*base89 + (4009101/250000000000000000000 : ℝ)*base91 + (990899/250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1411_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7872689/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14747/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11303/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62889/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59077/100000 : ℝ) else (80349/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84617/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1411_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1411_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7872689/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (461/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5649/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62889/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59077/100000 : ℝ) else (80349/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84617/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1411_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1411_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1411_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7872689/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (461/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5649/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62889/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59077/100000 : ℝ) else (80349/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84617/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1411_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
