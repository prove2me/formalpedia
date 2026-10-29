-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1643_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:11:19.847768+00:00
-- url     : https://prove2.me/submissions/a67ec9d0-6d76-41a4-b5e2-f03867d34b39

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
theorem support_rectangle_w1643_s0_0 (p : ℝ) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1505019667/10000000000 : ℝ)*x 0 + (1448509127/2500000000 : ℝ)*x 1 + (2458382207/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1505019667/10000000000 : ℝ)^4891 ≤ (4557444977161/50000000000000 : ℝ)^3867 := by
    have hnat : (1505019667 : ℕ)^4891*50000000000000^3867 ≤ 4557444977161^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1505019667 10000000000 4557444977161 50000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1448509127/2500000000 : ℝ)^4891 ≤ (2005753320729/4000000000000 : ℝ)^3867 := by
    have hnat : (1448509127 : ℕ)^4891*4000000000000^3867 ≤ 2005753320729^3867*2500000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1448509127 2500000000 2005753320729 4000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2458382207/5000000000 : ℝ)^4891 ≤ (20370638506767/50000000000000 : ℝ)^3867 := by
    have hnat : (2458382207 : ℕ)^4891*50000000000000^3867 ≤ 20370638506767^3867*5000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2458382207 5000000000 20370638506767 50000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4891/1024 : ℝ)) 4891 3867 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1505019667/10000000000 : ℝ), (1448509127/2500000000 : ℝ), (2458382207/5000000000 : ℝ)] ![(4557444977161/50000000000000 : ℝ), (2005753320729/4000000000000 : ℝ), (20370638506767/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1505019667/10000000000 : ℝ)|^4891 ≤ (4557444977161/50000000000000 : ℝ)^3867
        have hw : |(-1505019667/10000000000 : ℝ)|=(1505019667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1448509127/2500000000 : ℝ)|^4891 ≤ (2005753320729/4000000000000 : ℝ)^3867
        have hw : |(1448509127/2500000000 : ℝ)|=(1448509127/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2458382207/5000000000 : ℝ)|^4891 ≤ (20370638506767/50000000000000 : ℝ)^3867
        have hw : |(2458382207/5000000000 : ℝ)|=(2458382207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1643_s0_1 (p : ℝ) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (136008031/250000000 : ℝ)*x 0 + (-496819597/2500000000 : ℝ)*x 1 + (614595709/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (136008031/250000000 : ℝ)^4891 ≤ (23151901735119/50000000000000 : ℝ)^3867 := by
    have hnat : (136008031 : ℕ)^4891*50000000000000^3867 ≤ 23151901735119^3867*250000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136008031 250000000 23151901735119 50000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (496819597/2500000000 : ℝ)^4891 ≤ (3238726579577/25000000000000 : ℝ)^3867 := by
    have hnat : (496819597 : ℕ)^4891*25000000000000^3867 ≤ 3238726579577^3867*2500000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      496819597 2500000000 3238726579577 25000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (614595709/1250000000 : ℝ)^4891 ≤ (2546330637369/6250000000000 : ℝ)^3867 := by
    have hnat : (614595709 : ℕ)^4891*6250000000000^3867 ≤ 2546330637369^3867*1250000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      614595709 1250000000 2546330637369 6250000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4891/1024 : ℝ)) 4891 3867 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(136008031/250000000 : ℝ), (-496819597/2500000000 : ℝ), (614595709/1250000000 : ℝ)] ![(23151901735119/50000000000000 : ℝ), (3238726579577/25000000000000 : ℝ), (2546330637369/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(136008031/250000000 : ℝ)|^4891 ≤ (23151901735119/50000000000000 : ℝ)^3867
        have hw : |(136008031/250000000 : ℝ)|=(136008031/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-496819597/2500000000 : ℝ)|^4891 ≤ (3238726579577/25000000000000 : ℝ)^3867
        have hw : |(-496819597/2500000000 : ℝ)|=(496819597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(614595709/1250000000 : ℝ)|^4891 ≤ (2546330637369/6250000000000 : ℝ)^3867
        have hw : |(614595709/1250000000 : ℝ)|=(614595709/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1643_s0_2 (p : ℝ) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2720161693/5000000000 : ℝ)*x 0 + (2458382083/5000000000 : ℝ)*x 1 + (-794911/4000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2720161693/5000000000 : ℝ)^4891 ≤ (46303826572013/100000000000000 : ℝ)^3867 := by
    have hnat : (2720161693 : ℕ)^4891*100000000000000^3867 ≤ 46303826572013^3867*5000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2720161693 5000000000 46303826572013 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2458382083/5000000000 : ℝ)^4891 ≤ (40741274414389/100000000000000 : ℝ)^3867 := by
    have hnat : (2458382083 : ℕ)^4891*100000000000000^3867 ≤ 40741274414389^3867*5000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2458382083 5000000000 40741274414389 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (794911/4000000 : ℝ)^4891 ≤ (12954898996607/100000000000000 : ℝ)^3867 := by
    have hnat : (794911 : ℕ)^4891*100000000000000^3867 ≤ 12954898996607^3867*4000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      794911 4000000 12954898996607 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4891/1024 : ℝ)) 4891 3867 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2720161693/5000000000 : ℝ), (2458382083/5000000000 : ℝ), (-794911/4000000 : ℝ)] ![(46303826572013/100000000000000 : ℝ), (40741274414389/100000000000000 : ℝ), (12954898996607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2720161693/5000000000 : ℝ)|^4891 ≤ (46303826572013/100000000000000 : ℝ)^3867
        have hw : |(2720161693/5000000000 : ℝ)|=(2720161693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2458382083/5000000000 : ℝ)|^4891 ≤ (40741274414389/100000000000000 : ℝ)^3867
        have hw : |(2458382083/5000000000 : ℝ)|=(2458382083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-794911/4000000 : ℝ)|^4891 ≤ (12954898996607/100000000000000 : ℝ)^3867
        have hw : |(-794911/4000000 : ℝ)|=(794911/4000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1643_s0_3 (p : ℝ) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2046951521/5000000000 : ℝ)*x 0 + (3080917157/10000000000 : ℝ)*x 1 + (1332658033/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2046951521/5000000000 : ℝ)^4891 ≤ (258535221969/800000000000 : ℝ)^3867 := by
    have hnat : (2046951521 : ℕ)^4891*800000000000^3867 ≤ 258535221969^3867*5000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2046951521 5000000000 258535221969 800000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3080917157/10000000000 : ℝ)^4891 ≤ (22556933396449/100000000000000 : ℝ)^3867 := by
    have hnat : (3080917157 : ℕ)^4891*100000000000000^3867 ≤ 22556933396449^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3080917157 10000000000 22556933396449 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1332658033/2500000000 : ℝ)^4891 ≤ (45126163845721/100000000000000 : ℝ)^3867 := by
    have hnat : (1332658033 : ℕ)^4891*100000000000000^3867 ≤ 45126163845721^3867*2500000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1332658033 2500000000 45126163845721 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4891/1024 : ℝ)) 4891 3867 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2046951521/5000000000 : ℝ), (3080917157/10000000000 : ℝ), (1332658033/2500000000 : ℝ)] ![(258535221969/800000000000 : ℝ), (22556933396449/100000000000000 : ℝ), (45126163845721/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2046951521/5000000000 : ℝ)|^4891 ≤ (258535221969/800000000000 : ℝ)^3867
        have hw : |(2046951521/5000000000 : ℝ)|=(2046951521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3080917157/10000000000 : ℝ)|^4891 ≤ (22556933396449/100000000000000 : ℝ)^3867
        have hw : |(3080917157/10000000000 : ℝ)|=(3080917157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1332658033/2500000000 : ℝ)|^4891 ≤ (45126163845721/100000000000000 : ℝ)^3867
        have hw : |(1332658033/2500000000 : ℝ)|=(1332658033/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1643_s0_4 (p : ℝ) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1507396941/10000000000 : ℝ)*x 0 + (2469303971/5000000000 : ℝ)*x 1 + (5771434351/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1507396941/10000000000 : ℝ)^4891 ≤ (1141637980851/12500000000000 : ℝ)^3867 := by
    have hnat : (1507396941 : ℕ)^4891*12500000000000^3867 ≤ 1141637980851^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1507396941 10000000000 1141637980851 12500000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2469303971/5000000000 : ℝ)^4891 ≤ (40970340897439/100000000000000 : ℝ)^3867 := by
    have hnat : (2469303971 : ℕ)^4891*100000000000000^3867 ≤ 40970340897439^3867*5000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2469303971 5000000000 40970340897439 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5771434351/10000000000 : ℝ)^4891 ≤ (49896555236363/100000000000000 : ℝ)^3867 := by
    have hnat : (5771434351 : ℕ)^4891*100000000000000^3867 ≤ 49896555236363^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5771434351 10000000000 49896555236363 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4891/1024 : ℝ)) 4891 3867 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1507396941/10000000000 : ℝ), (2469303971/5000000000 : ℝ), (5771434351/10000000000 : ℝ)] ![(1141637980851/12500000000000 : ℝ), (40970340897439/100000000000000 : ℝ), (49896555236363/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1507396941/10000000000 : ℝ)|^4891 ≤ (1141637980851/12500000000000 : ℝ)^3867
        have hw : |(-1507396941/10000000000 : ℝ)|=(1507396941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2469303971/5000000000 : ℝ)|^4891 ≤ (40970340897439/100000000000000 : ℝ)^3867
        have hw : |(2469303971/5000000000 : ℝ)|=(2469303971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5771434351/10000000000 : ℝ)|^4891 ≤ (49896555236363/100000000000000 : ℝ)^3867
        have hw : |(5771434351/10000000000 : ℝ)|=(5771434351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1643_s0_5 (p : ℝ) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1040176241/2000000000 : ℝ)*x 0 + (-283152169/2500000000 : ℝ)*x 1 + (5771434967/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1040176241/2000000000 : ℝ)^4891 ≤ (43741407666003/100000000000000 : ℝ)^3867 := by
    have hnat : (1040176241 : ℕ)^4891*100000000000000^3867 ≤ 43741407666003^3867*2000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040176241 2000000000 43741407666003 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (283152169/2500000000 : ℝ)^4891 ≤ (49703362101/781250000000 : ℝ)^3867 := by
    have hnat : (283152169 : ℕ)^4891*781250000000^3867 ≤ 49703362101^3867*2500000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283152169 2500000000 49703362101 781250000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5771434967/10000000000 : ℝ)^4891 ≤ (49896561972191/100000000000000 : ℝ)^3867 := by
    have hnat : (5771434967 : ℕ)^4891*100000000000000^3867 ≤ 49896561972191^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5771434967 10000000000 49896561972191 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4891/1024 : ℝ)) 4891 3867 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1040176241/2000000000 : ℝ), (-283152169/2500000000 : ℝ), (5771434967/10000000000 : ℝ)] ![(43741407666003/100000000000000 : ℝ), (49703362101/781250000000 : ℝ), (49896561972191/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1040176241/2000000000 : ℝ)|^4891 ≤ (43741407666003/100000000000000 : ℝ)^3867
        have hw : |(1040176241/2000000000 : ℝ)|=(1040176241/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-283152169/2500000000 : ℝ)|^4891 ≤ (49703362101/781250000000 : ℝ)^3867
        have hw : |(-283152169/2500000000 : ℝ)|=(283152169/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5771434967/10000000000 : ℝ)|^4891 ≤ (49896561972191/100000000000000 : ℝ)^3867
        have hw : |(5771434967/10000000000 : ℝ)|=(5771434967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1643_s0_6 (p : ℝ) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1040176209/2000000000 : ℝ)*x 0 + (5771435251/10000000000 : ℝ)*x 1 + (-566304239/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1040176209/2000000000 : ℝ)^4891 ≤ (10935351491001/25000000000000 : ℝ)^3867 := by
    have hnat : (1040176209 : ℕ)^4891*25000000000000^3867 ≤ 10935351491001^3867*2000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040176209 2000000000 10935351491001 25000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5771435251/10000000000 : ℝ)^4891 ≤ (49896565077671/100000000000000 : ℝ)^3867 := by
    have hnat : (5771435251 : ℕ)^4891*100000000000000^3867 ≤ 49896565077671^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5771435251 10000000000 49896565077671 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (566304239/5000000000 : ℝ)^4891 ≤ (3181014471109/50000000000000 : ℝ)^3867 := by
    have hnat : (566304239 : ℕ)^4891*50000000000000^3867 ≤ 3181014471109^3867*5000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      566304239 5000000000 3181014471109 50000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4891/1024 : ℝ)) 4891 3867 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1040176209/2000000000 : ℝ), (5771435251/10000000000 : ℝ), (-566304239/5000000000 : ℝ)] ![(10935351491001/25000000000000 : ℝ), (49896565077671/100000000000000 : ℝ), (3181014471109/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1040176209/2000000000 : ℝ)|^4891 ≤ (10935351491001/25000000000000 : ℝ)^3867
        have hw : |(1040176209/2000000000 : ℝ)|=(1040176209/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5771435251/10000000000 : ℝ)|^4891 ≤ (49896565077671/100000000000000 : ℝ)^3867
        have hw : |(5771435251/10000000000 : ℝ)|=(5771435251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-566304239/5000000000 : ℝ)|^4891 ≤ (3181014471109/50000000000000 : ℝ)^3867
        have hw : |(-566304239/5000000000 : ℝ)|=(566304239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1643_s0_7 (p : ℝ) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (820000211/2000000000 : ℝ)*x 0 + (5274617453/10000000000 : ℝ)*x 1 + (3138873721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (820000211/2000000000 : ℝ)^4891 ≤ (32377798866641/100000000000000 : ℝ)^3867 := by
    have hnat : (820000211 : ℕ)^4891*100000000000000^3867 ≤ 32377798866641^3867*2000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      820000211 2000000000 32377798866641 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5274617453/10000000000 : ℝ)^4891 ≤ (5565905478627/12500000000000 : ℝ)^3867 := by
    have hnat : (5274617453 : ℕ)^4891*12500000000000^3867 ≤ 5565905478627^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274617453 10000000000 5565905478627 12500000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3138873721/10000000000 : ℝ)^4891 ≤ (2309495729633/10000000000000 : ℝ)^3867 := by
    have hnat : (3138873721 : ℕ)^4891*10000000000000^3867 ≤ 2309495729633^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3138873721 10000000000 2309495729633 10000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4891/1024 : ℝ)) 4891 3867 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(820000211/2000000000 : ℝ), (5274617453/10000000000 : ℝ), (3138873721/10000000000 : ℝ)] ![(32377798866641/100000000000000 : ℝ), (5565905478627/12500000000000 : ℝ), (2309495729633/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(820000211/2000000000 : ℝ)|^4891 ≤ (32377798866641/100000000000000 : ℝ)^3867
        have hw : |(820000211/2000000000 : ℝ)|=(820000211/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5274617453/10000000000 : ℝ)|^4891 ≤ (5565905478627/12500000000000 : ℝ)^3867
        have hw : |(5274617453/10000000000 : ℝ)|=(5274617453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3138873721/10000000000 : ℝ)|^4891 ≤ (2309495729633/10000000000000 : ℝ)^3867
        have hw : |(3138873721/10000000000 : ℝ)|=(3138873721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1643_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (178222457/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (4707/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (23507/100000 : ℝ)*pair X 0 0 := by
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
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (4887/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4887 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4887*1^1024 ≤ 0^1024*1^4887 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4887 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4887 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4887/1024 : ℝ) ≤ (315345662541312903/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4887 ≤ (315345662541312903/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4887*25000000000000000000^1024 ≤ 315345662541312903^1024*5^4887 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 315345662541312903 25000000000000000000 4887 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (315345662541312903/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4887 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4887/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4887 := by
      have hnat : (1 : ℕ)^1024*1^4887 ≤ 1^4887*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4887 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4887 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25315345662541312903/25000000000000000000 : ℝ) ≤ (10026299661940251/10000000000000000 : ℝ) ^ (4887/1024 : ℝ) := by
    have hpowers : (25315345662541312903/25000000000000000000 : ℝ)^1024 ≤ (10026299661940251/10000000000000000 : ℝ)^4887 := by
      have hnat : (25315345662541312903 : ℕ)^1024*10000000000000000^4887 ≤ 10026299661940251^4887*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25315345662541312903 25000000000000000000 10026299661940251 10000000000000000 1024 4887 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10026299661940251/10000000000000000 : ℝ)) (X := (25315345662541312903/25000000000000000000 : ℝ)) (by norm_num) 4887 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12815345662541312903/12500000000000000000 : ℝ) ≤ (5026299661940251/5000000000000000 : ℝ) ^ (4887/1024 : ℝ) := by
    have hpowers : (12815345662541312903/12500000000000000000 : ℝ)^1024 ≤ (5026299661940251/5000000000000000 : ℝ)^4887 := by
      have hnat : (12815345662541312903 : ℕ)^1024*5000000000000000^4887 ≤ 5026299661940251^4887*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12815345662541312903 12500000000000000000 5026299661940251 5000000000000000 1024 4887 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5026299661940251/5000000000000000 : ℝ)) (X := (12815345662541312903/12500000000000000000 : ℝ)) (by norm_num) 4887 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(26299661940251/4000000000000000 : ℝ)*(0 : ℝ))^(4887/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(26299661940251/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(315345662541312903/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(26299661940251/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4887/1024 : ℝ) := by
    rw [show (1 : ℝ)+(26299661940251/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10026299661940251/10000000000000000 : ℝ) by norm_num, show 1+(315345662541312903/25000000000000000000 : ℝ)+(0 : ℝ)=(25315345662541312903/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(315345662541312903/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(26299661940251/4000000000000000 : ℝ)*(2/5 : ℝ))^(4887/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(26299661940251/4000000000000000 : ℝ)*(2/5 : ℝ)=(5026299661940251/5000000000000000 : ℝ) by norm_num, show 1+2*(315345662541312903/25000000000000000000 : ℝ)=(12815345662541312903/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(26299661940251/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4887/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (26299661940251/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(26299661940251/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4887/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (26299661940251/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(26299661940251/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4887/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (26299661940251/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1505019667/10000000000 : ℝ)*X 0 0+(1448509127/2500000000 : ℝ)*X 0 1+(2458382207/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1643_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((136008031/250000000 : ℝ)*X 1 0+(-496819597/2500000000 : ℝ)*X 1 1+(614595709/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1643_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2720161693/5000000000 : ℝ)*X 2 0+(2458382083/5000000000 : ℝ)*X 2 1+(-794911/4000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1643_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2046951521/5000000000 : ℝ)*X 0 0+(3080917157/10000000000 : ℝ)*X 0 1+(1332658033/2500000000 : ℝ)*X 0 2+(2046951521/5000000000 : ℝ)*X 1 0+(3080917157/10000000000 : ℝ)*X 1 1+(1332658033/2500000000 : ℝ)*X 1 2+(2046951521/5000000000 : ℝ)*X 2 0+(3080917157/10000000000 : ℝ)*X 2 1+(1332658033/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1643_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1507396941/10000000000 : ℝ)*X 0 0+(2469303971/5000000000 : ℝ)*X 0 1+(5771434351/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1643_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1040176241/2000000000 : ℝ)*X 1 0+(-283152169/2500000000 : ℝ)*X 1 1+(5771434967/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1643_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1040176209/2000000000 : ℝ)*X 2 0+(5771435251/10000000000 : ℝ)*X 2 1+(-566304239/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1643_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((820000211/2000000000 : ℝ)*X 0 0+(5274617453/10000000000 : ℝ)*X 0 1+(3138873721/10000000000 : ℝ)*X 0 2+(820000211/2000000000 : ℝ)*X 1 0+(5274617453/10000000000 : ℝ)*X 1 1+(3138873721/10000000000 : ℝ)*X 1 2+(820000211/2000000000 : ℝ)*X 2 0+(5274617453/10000000000 : ℝ)*X 2 1+(3138873721/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1643_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (656502873268410567/100000000000000000000000 : ℝ) := by norm_num
    linear_combination (443364707/50000000000000 : ℝ)*(base19) + (72453139/6250000000000 : ℝ)*(base23) + (1880361/100000000000000 : ℝ)*(base24) + (47670409/50000000000000 : ℝ)*(upper4) + (263241833/100000000000000 : ℝ)*(upper5) + (198051431364769/25000000000000 : ℝ)*(major0) + (198051431364769/25000000000000 : ℝ)*(major1) + (198051431364769/25000000000000 : ℝ)*(major2) + (284975101616181/25000000000000 : ℝ)*(sp0) + (1139906471491301/100000000000000 : ℝ)*(sp1) + (113990619709013/10000000000000 : ℝ)*(sp2) + (111125630542087/25000000000000 : ℝ)*(sp3) + (6951755991/100000000000000 : ℝ)*(sp4) + (337923699/25000000000000 : ℝ)*(sp7) + (55562984232893/12500000000000 : ℝ)*(f.failure) + (227981471644143/20000000000000 : ℝ)*(f.sum) + (99546766567019/50000000000000000000000000000 : ℝ)*base65 + (389089089382981/100000000000000000000000000000 : ℝ)*base68 + (239163778482981/100000000000000000000000000000 : ℝ)*base70 + (122749700817019/100000000000000000000000000000 : ℝ)*base71 + (136520457382981/50000000000000000000000000000 : ℝ)*base74 + (105807847982981/100000000000000000000000000000 : ℝ)*base76 + (114425006817019/100000000000000000000000000000 : ℝ)*base77 + (47834815982981/100000000000000000000000000000 : ℝ)*base80 + (182538521817019/50000000000000000000000000000 : ℝ)*base81 + (678101/1250000000000000000000 : ℝ)*base89 + (678101/1250000000000000000000 : ℝ)*base91 + (678101/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (37479508395151810428531/4000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (819337733/50000000000000 : ℝ)*(base19) + (339584591/20000000000000 : ℝ)*(base23) + (36747711/50000000000000 : ℝ)*(base39) + (176604949/50000000000000 : ℝ)*(upper3) + (144990231/50000000000000 : ℝ)*(upper5) + (834475258016693/100000000000000 : ℝ)*(major0) + (834475258016693/100000000000000 : ℝ)*(major1) + (834475184521271/100000000000000 : ℝ)*(major2) + (242011493/5000000000000 : ℝ)*(sp1) + (1070647433/20000000000000 : ℝ)*(sp2) + (1200728968822367/100000000000000 : ℝ)*(sp4) + (600361244958521/50000000000000 : ℝ)*(sp5) + (120072199115767/10000000000000 : ℝ)*(sp6) + (468221161386353/100000000000000 : ℝ)*(sp7) + (468221161386353/100000000000000 : ℝ)*(f.failure) + (1200729042317789/100000000000000 : ℝ)*(f.sum) + (28598065002759/100000000000000000000000000000 : ℝ)*base66 + (903992608620979/400000000000000000000000000000 : ℝ)*base68 + (2158196805390057/400000000000000000000000000000 : ℝ)*base70 + (2858619329420979/400000000000000000000000000000 : ℝ)*base72 + (269834558097241/100000000000000000000000000000 : ℝ)*base73 + (3935974692190057/400000000000000000000000000000 : ℝ)*base76 + (3496256775390057/400000000000000000000000000000 : ℝ)*base78 + (4093242860990057/400000000000000000000000000000 : ℝ)*base80 + (268876623990057/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (57929321/10000000000000000000000 : ℝ)*base89 + (57929321/10000000000000000000000 : ℝ)*base91 + (57929321/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1643_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (178222457/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4707/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (23507/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1643_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1643_s1_0 (p : ℝ) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1613817631/10000000000 : ℝ)*x 0 + (1375408471/2500000000 : ℝ)*x 1 + (2569257859/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1613817631/10000000000 : ℝ)^4891 ≤ (311129053807/3125000000000 : ℝ)^3867 := by
    have hnat : (1613817631 : ℕ)^4891*3125000000000^3867 ≤ 311129053807^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1613817631 10000000000 311129053807 3125000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1375408471/2500000000 : ℝ)^4891 ≤ (46964818662493/100000000000000 : ℝ)^3867 := by
    have hnat : (1375408471 : ℕ)^4891*100000000000000^3867 ≤ 46964818662493^3867*2500000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1375408471 2500000000 46964818662493 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2569257859/5000000000 : ℝ)^4891 ≤ (43079051595657/100000000000000 : ℝ)^3867 := by
    have hnat : (2569257859 : ℕ)^4891*100000000000000^3867 ≤ 43079051595657^3867*5000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2569257859 5000000000 43079051595657 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4891/1024 : ℝ)) 4891 3867 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1613817631/10000000000 : ℝ), (1375408471/2500000000 : ℝ), (2569257859/5000000000 : ℝ)] ![(311129053807/3125000000000 : ℝ), (46964818662493/100000000000000 : ℝ), (43079051595657/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1613817631/10000000000 : ℝ)|^4891 ≤ (311129053807/3125000000000 : ℝ)^3867
        have hw : |(-1613817631/10000000000 : ℝ)|=(1613817631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1375408471/2500000000 : ℝ)|^4891 ≤ (46964818662493/100000000000000 : ℝ)^3867
        have hw : |(1375408471/2500000000 : ℝ)|=(1375408471/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2569257859/5000000000 : ℝ)|^4891 ≤ (43079051595657/100000000000000 : ℝ)^3867
        have hw : |(2569257859/5000000000 : ℝ)|=(2569257859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1643_s1_1 (p : ℝ) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (335159331/625000000 : ℝ)*x 0 + (-901386539/5000000000 : ℝ)*x 1 + (513851553/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (335159331/625000000 : ℝ)^4891 ≤ (45468175685027/100000000000000 : ℝ)^3867 := by
    have hnat : (335159331 : ℕ)^4891*100000000000000^3867 ≤ 45468175685027^3867*625000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335159331 625000000 45468175685027 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (901386539/5000000000 : ℝ)^4891 ≤ (18324439513/160000000000 : ℝ)^3867 := by
    have hnat : (901386539 : ℕ)^4891*160000000000^3867 ≤ 18324439513^3867*5000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901386539 5000000000 18324439513 160000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (513851553/1000000000 : ℝ)^4891 ≤ (21539524801093/50000000000000 : ℝ)^3867 := by
    have hnat : (513851553 : ℕ)^4891*50000000000000^3867 ≤ 21539524801093^3867*1000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513851553 1000000000 21539524801093 50000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4891/1024 : ℝ)) 4891 3867 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(335159331/625000000 : ℝ), (-901386539/5000000000 : ℝ), (513851553/1000000000 : ℝ)] ![(45468175685027/100000000000000 : ℝ), (18324439513/160000000000 : ℝ), (21539524801093/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(335159331/625000000 : ℝ)|^4891 ≤ (45468175685027/100000000000000 : ℝ)^3867
        have hw : |(335159331/625000000 : ℝ)|=(335159331/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-901386539/5000000000 : ℝ)|^4891 ≤ (18324439513/160000000000 : ℝ)^3867
        have hw : |(-901386539/5000000000 : ℝ)|=(901386539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(513851553/1000000000 : ℝ)|^4891 ≤ (21539524801093/50000000000000 : ℝ)^3867
        have hw : |(513851553/1000000000 : ℝ)|=(513851553/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1643_s1_2 (p : ℝ) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (335159401/625000000 : ℝ)*x 0 + (1027702849/2000000000 : ℝ)*x 1 + (-1802773279/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (335159401/625000000 : ℝ)^4891 ≤ (11367046923997/25000000000000 : ℝ)^3867 := by
    have hnat : (335159401 : ℕ)^4891*25000000000000^3867 ≤ 11367046923997^3867*625000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335159401 625000000 11367046923997 25000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1027702849/2000000000 : ℝ)^4891 ≤ (8615807195321/20000000000000 : ℝ)^3867 := by
    have hnat : (1027702849 : ℕ)^4891*20000000000000^3867 ≤ 8615807195321^3867*2000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1027702849 2000000000 8615807195321 20000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1802773279/10000000000 : ℝ)^4891 ≤ (11452776310687/100000000000000 : ℝ)^3867 := by
    have hnat : (1802773279 : ℕ)^4891*100000000000000^3867 ≤ 11452776310687^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1802773279 10000000000 11452776310687 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4891/1024 : ℝ)) 4891 3867 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(335159401/625000000 : ℝ), (1027702849/2000000000 : ℝ), (-1802773279/10000000000 : ℝ)] ![(11367046923997/25000000000000 : ℝ), (8615807195321/20000000000000 : ℝ), (11452776310687/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(335159401/625000000 : ℝ)|^4891 ≤ (11367046923997/25000000000000 : ℝ)^3867
        have hw : |(335159401/625000000 : ℝ)|=(335159401/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1027702849/2000000000 : ℝ)|^4891 ≤ (8615807195321/20000000000000 : ℝ)^3867
        have hw : |(1027702849/2000000000 : ℝ)|=(1027702849/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1802773279/10000000000 : ℝ)|^4891 ≤ (11452776310687/100000000000000 : ℝ)^3867
        have hw : |(-1802773279/10000000000 : ℝ)|=(1802773279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1643_s1_3 (p : ℝ) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (208908209/500000000 : ℝ)*x 0 + (3731527867/10000000000 : ℝ)*x 1 + (932545559/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (208908209/500000000 : ℝ)^4891 ≤ (8290117145849/25000000000000 : ℝ)^3867 := by
    have hnat : (208908209 : ℕ)^4891*25000000000000^3867 ≤ 8290117145849^3867*500000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208908209 500000000 8290117145849 25000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3731527867/10000000000 : ℝ)^4891 ≤ (28742215915439/100000000000000 : ℝ)^3867 := by
    have hnat : (3731527867 : ℕ)^4891*100000000000000^3867 ≤ 28742215915439^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3731527867 10000000000 28742215915439 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (932545559/2000000000 : ℝ)^4891 ≤ (1523892619761/4000000000000 : ℝ)^3867 := by
    have hnat : (932545559 : ℕ)^4891*4000000000000^3867 ≤ 1523892619761^3867*2000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      932545559 2000000000 1523892619761 4000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4891/1024 : ℝ)) 4891 3867 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(208908209/500000000 : ℝ), (3731527867/10000000000 : ℝ), (932545559/2000000000 : ℝ)] ![(8290117145849/25000000000000 : ℝ), (28742215915439/100000000000000 : ℝ), (1523892619761/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(208908209/500000000 : ℝ)|^4891 ≤ (8290117145849/25000000000000 : ℝ)^3867
        have hw : |(208908209/500000000 : ℝ)|=(208908209/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3731527867/10000000000 : ℝ)|^4891 ≤ (28742215915439/100000000000000 : ℝ)^3867
        have hw : |(3731527867/10000000000 : ℝ)|=(3731527867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(932545559/2000000000 : ℝ)|^4891 ≤ (1523892619761/4000000000000 : ℝ)^3867
        have hw : |(932545559/2000000000 : ℝ)|=(932545559/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1643_s1_4 (p : ℝ) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-806992037/5000000000 : ℝ)*x 0 + (5142241469/10000000000 : ℝ)*x 1 + (5497853909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (806992037/5000000000 : ℝ)^4891 ≤ (9957428488231/100000000000000 : ℝ)^3867 := by
    have hnat : (806992037 : ℕ)^4891*100000000000000^3867 ≤ 9957428488231^3867*5000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      806992037 5000000000 9957428488231 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5142241469/10000000000 : ℝ)^4891 ≤ (10779640408351/25000000000000 : ℝ)^3867 := by
    have hnat : (5142241469 : ℕ)^4891*25000000000000^3867 ≤ 10779640408351^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5142241469 10000000000 10779640408351 25000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5497853909/10000000000 : ℝ)^4891 ≤ (46924009858561/100000000000000 : ℝ)^3867 := by
    have hnat : (5497853909 : ℕ)^4891*100000000000000^3867 ≤ 46924009858561^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5497853909 10000000000 46924009858561 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4891/1024 : ℝ)) 4891 3867 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-806992037/5000000000 : ℝ), (5142241469/10000000000 : ℝ), (5497853909/10000000000 : ℝ)] ![(9957428488231/100000000000000 : ℝ), (10779640408351/25000000000000 : ℝ), (46924009858561/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-806992037/5000000000 : ℝ)|^4891 ≤ (9957428488231/100000000000000 : ℝ)^3867
        have hw : |(-806992037/5000000000 : ℝ)|=(806992037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5142241469/10000000000 : ℝ)|^4891 ≤ (10779640408351/25000000000000 : ℝ)^3867
        have hw : |(5142241469/10000000000 : ℝ)|=(5142241469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5497853909/10000000000 : ℝ)|^4891 ≤ (46924009858561/100000000000000 : ℝ)^3867
        have hw : |(5497853909/10000000000 : ℝ)|=(5497853909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1643_s1_5 (p : ℝ) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2632766393/5000000000 : ℝ)*x 0 + (-144343423/1000000000 : ℝ)*x 1 + (549785391/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2632766393/5000000000 : ℝ)^4891 ≤ (8886053387483/20000000000000 : ℝ)^3867 := by
    have hnat : (2632766393 : ℕ)^4891*20000000000000^3867 ≤ 8886053387483^3867*5000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632766393 5000000000 8886053387483 20000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (144343423/1000000000 : ℝ)^4891 ≤ (8645723175963/100000000000000 : ℝ)^3867 := by
    have hnat : (144343423 : ℕ)^4891*100000000000000^3867 ≤ 8645723175963^3867*1000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      144343423 1000000000 8645723175963 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (549785391/1000000000 : ℝ)^4891 ≤ (11731002467339/25000000000000 : ℝ)^3867 := by
    have hnat : (549785391 : ℕ)^4891*25000000000000^3867 ≤ 11731002467339^3867*1000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549785391 1000000000 11731002467339 25000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4891/1024 : ℝ)) 4891 3867 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2632766393/5000000000 : ℝ), (-144343423/1000000000 : ℝ), (549785391/1000000000 : ℝ)] ![(8886053387483/20000000000000 : ℝ), (8645723175963/100000000000000 : ℝ), (11731002467339/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2632766393/5000000000 : ℝ)|^4891 ≤ (8886053387483/20000000000000 : ℝ)^3867
        have hw : |(2632766393/5000000000 : ℝ)|=(2632766393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-144343423/1000000000 : ℝ)|^4891 ≤ (8645723175963/100000000000000 : ℝ)^3867
        have hw : |(-144343423/1000000000 : ℝ)|=(144343423/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(549785391/1000000000 : ℝ)|^4891 ≤ (11731002467339/25000000000000 : ℝ)^3867
        have hw : |(549785391/1000000000 : ℝ)|=(549785391/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1643_s1_6 (p : ℝ) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (658191579/1250000000 : ℝ)*x 0 + (5497854139/10000000000 : ℝ)*x 1 + (-36085853/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (658191579/1250000000 : ℝ)^4891 ≤ (44430265293873/100000000000000 : ℝ)^3867 := by
    have hnat : (658191579 : ℕ)^4891*100000000000000^3867 ≤ 44430265293873^3867*1250000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658191579 1250000000 44430265293873 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5497854139/10000000000 : ℝ)^4891 ≤ (46924012341427/100000000000000 : ℝ)^3867 := by
    have hnat : (5497854139 : ℕ)^4891*100000000000000^3867 ≤ 46924012341427^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5497854139 10000000000 46924012341427 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (36085853/250000000 : ℝ)^4891 ≤ (4322861171313/50000000000000 : ℝ)^3867 := by
    have hnat : (36085853 : ℕ)^4891*50000000000000^3867 ≤ 4322861171313^3867*250000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36085853 250000000 4322861171313 50000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4891/1024 : ℝ)) 4891 3867 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(658191579/1250000000 : ℝ), (5497854139/10000000000 : ℝ), (-36085853/250000000 : ℝ)] ![(44430265293873/100000000000000 : ℝ), (46924012341427/100000000000000 : ℝ), (4322861171313/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(658191579/1250000000 : ℝ)|^4891 ≤ (44430265293873/100000000000000 : ℝ)^3867
        have hw : |(658191579/1250000000 : ℝ)|=(658191579/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5497854139/10000000000 : ℝ)|^4891 ≤ (46924012341427/100000000000000 : ℝ)^3867
        have hw : |(5497854139/10000000000 : ℝ)|=(5497854139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-36085853/250000000 : ℝ)|^4891 ≤ (4322861171313/50000000000000 : ℝ)^3867
        have hw : |(-36085853/250000000 : ℝ)|=(36085853/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1643_s1_7 (p : ℝ) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2089293771/5000000000 : ℝ)*x 0 + (581646499/1250000000 : ℝ)*x 1 + (1870611023/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2089293771/5000000000 : ℝ)^4891 ≤ (8291179615069/25000000000000 : ℝ)^3867 := by
    have hnat : (2089293771 : ℕ)^4891*25000000000000^3867 ≤ 8291179615069^3867*5000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2089293771 5000000000 8291179615069 25000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (581646499/1250000000 : ℝ)^4891 ≤ (7599718102037/20000000000000 : ℝ)^3867 := by
    have hnat : (581646499 : ℕ)^4891*20000000000000^3867 ≤ 7599718102037^3867*1250000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      581646499 1250000000 7599718102037 20000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1870611023/5000000000 : ℝ)^4891 ≤ (28836691012563/100000000000000 : ℝ)^3867 := by
    have hnat : (1870611023 : ℕ)^4891*100000000000000^3867 ≤ 28836691012563^3867*5000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1870611023 5000000000 28836691012563 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4891/1024 : ℝ)) 4891 3867 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2089293771/5000000000 : ℝ), (581646499/1250000000 : ℝ), (1870611023/5000000000 : ℝ)] ![(8291179615069/25000000000000 : ℝ), (7599718102037/20000000000000 : ℝ), (28836691012563/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2089293771/5000000000 : ℝ)|^4891 ≤ (8291179615069/25000000000000 : ℝ)^3867
        have hw : |(2089293771/5000000000 : ℝ)|=(2089293771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(581646499/1250000000 : ℝ)|^4891 ≤ (7599718102037/20000000000000 : ℝ)^3867
        have hw : |(581646499/1250000000 : ℝ)|=(581646499/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1870611023/5000000000 : ℝ)|^4891 ≤ (28836691012563/100000000000000 : ℝ)^3867
        have hw : |(1870611023/5000000000 : ℝ)|=(1870611023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1643_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (178222457/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (23507/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4707/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (483/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17371/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (23507/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4707/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (23507/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4707/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (23507/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4707/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (23507/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4707/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (23507/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4707/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (23507/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4707/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4707/100000 : ℝ) ^ (4887/1024 : ℝ) ≤ (46315198781067/100000000000000000000 : ℝ) := by
    have hpowers : (4707/100000 : ℝ)^4887 ≤ (46315198781067/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4707 : ℕ)^4887*100000000000000000000^1024 ≤ 46315198781067^1024*100000^4887 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4707 100000 46315198781067 100000000000000000000 4887 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4707/100000 : ℝ)) (X := (46315198781067/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4887 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (23507/100000 : ℝ) ^ (4887/1024 : ℝ) ≤ (99784534246442389/100000000000000000000 : ℝ) := by
    have hpowers : (23507/100000 : ℝ)^4887 ≤ (99784534246442389/100000000000000000000 : ℝ)^1024 := by
      have hnat : (23507 : ℕ)^4887*100000000000000000000^1024 ≤ 99784534246442389^1024*100000^4887 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        23507 100000 99784534246442389 100000000000000000000 4887 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (23507/100000 : ℝ)) (X := (99784534246442389/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4887 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000046315198781067/50000000000000000000 : ℝ) ≤ (10000001940934979/10000000000000000 : ℝ) ^ (4887/1024 : ℝ) := by
    have hpowers : (50000046315198781067/50000000000000000000 : ℝ)^1024 ≤ (10000001940934979/10000000000000000 : ℝ)^4887 := by
      have hnat : (50000046315198781067 : ℕ)^1024*10000000000000000^4887 ≤ 10000001940934979^4887*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000046315198781067 50000000000000000000 10000001940934979 10000000000000000 1024 4887 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000001940934979/10000000000000000 : ℝ)) (X := (50000046315198781067/50000000000000000000 : ℝ)) (by norm_num) 4887 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (3128119714045163233/3125000000000000000 : ℝ) ≤ (5001045492928849/5000000000000000 : ℝ) ^ (4887/1024 : ℝ) := by
    have hpowers : (3128119714045163233/3125000000000000000 : ℝ)^1024 ≤ (5001045492928849/5000000000000000 : ℝ)^4887 := by
      have hnat : (3128119714045163233 : ℕ)^1024*5000000000000000^4887 ≤ 5001045492928849^4887*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3128119714045163233 3125000000000000000 5001045492928849 5000000000000000 1024 4887 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001045492928849/5000000000000000 : ℝ)) (X := (3128119714045163233/3125000000000000000 : ℝ)) (by norm_num) 4887 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50099784534246442389/50000000000000000000 : ℝ) ≤ (10004180030780417/10000000000000000 : ℝ) ^ (4887/1024 : ℝ) := by
    have hpowers : (50099784534246442389/50000000000000000000 : ℝ)^1024 ≤ (10004180030780417/10000000000000000 : ℝ)^4887 := by
      have hnat : (50099784534246442389 : ℕ)^1024*10000000000000000^4887 ≤ 10004180030780417^4887*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50099784534246442389 50000000000000000000 10004180030780417 10000000000000000 1024 4887 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004180030780417/10000000000000000 : ℝ)) (X := (50099784534246442389/50000000000000000000 : ℝ)) (by norm_num) 4887 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(46315198781067/100000000000000000000 : ℝ) ≤ ((93990185110337564267/94000000000000000000 : ℝ)+2*(2089044922719/1880000000000000 : ℝ)*(4707/100000 : ℝ))^(4887/1024 : ℝ) := by
    rw [show (93990185110337564267/94000000000000000000 : ℝ)+2*(2089044922719/1880000000000000 : ℝ)*(4707/100000 : ℝ)=(10000001940934979/10000000000000000 : ℝ) by norm_num, show 1+2*(46315198781067/100000000000000000000 : ℝ)=(50000046315198781067/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(99784534246442389/100000000000000000000 : ℝ)+(46315198781067/100000000000000000000 : ℝ) ≤ ((93990185110337564267/94000000000000000000 : ℝ)+(2089044922719/1880000000000000 : ℝ)*((23507/100000 : ℝ)+(4707/100000 : ℝ)))^(4887/1024 : ℝ) := by
    rw [show (93990185110337564267/94000000000000000000 : ℝ)+(2089044922719/1880000000000000 : ℝ)*((23507/100000 : ℝ)+(4707/100000 : ℝ))=(5001045492928849/5000000000000000 : ℝ) by norm_num, show 1+(99784534246442389/100000000000000000000 : ℝ)+(46315198781067/100000000000000000000 : ℝ)=(3128119714045163233/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(99784534246442389/100000000000000000000 : ℝ) ≤ ((93990185110337564267/94000000000000000000 : ℝ)+2*(2089044922719/1880000000000000 : ℝ)*(23507/100000 : ℝ))^(4887/1024 : ℝ) := by
    rw [show (93990185110337564267/94000000000000000000 : ℝ)+2*(2089044922719/1880000000000000 : ℝ)*(23507/100000 : ℝ)=(10004180030780417/10000000000000000 : ℝ) by norm_num, show 1+2*(99784534246442389/100000000000000000000 : ℝ)=(50099784534246442389/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (93990185110337564267/94000000000000000000 : ℝ)*(X 1 0+X 2 0)+(2089044922719/1880000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4887/1024 : ℝ)) (lo := (4707/100000 : ℝ)) (hi := (23507/100000 : ℝ)) (c := (93990185110337564267/94000000000000000000 : ℝ)) (alpha := (2089044922719/1880000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (93990185110337564267/94000000000000000000 : ℝ)*(X 0 1+X 2 1)+(2089044922719/1880000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4887/1024 : ℝ)) (lo := (4707/100000 : ℝ)) (hi := (23507/100000 : ℝ)) (c := (93990185110337564267/94000000000000000000 : ℝ)) (alpha := (2089044922719/1880000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (93990185110337564267/94000000000000000000 : ℝ)*(X 0 2+X 1 2)+(2089044922719/1880000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4887/1024 : ℝ)) (lo := (4707/100000 : ℝ)) (hi := (23507/100000 : ℝ)) (c := (93990185110337564267/94000000000000000000 : ℝ)) (alpha := (2089044922719/1880000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1613817631/10000000000 : ℝ)*X 0 0+(1375408471/2500000000 : ℝ)*X 0 1+(2569257859/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1643_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((335159331/625000000 : ℝ)*X 1 0+(-901386539/5000000000 : ℝ)*X 1 1+(513851553/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1643_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((335159401/625000000 : ℝ)*X 2 0+(1027702849/2000000000 : ℝ)*X 2 1+(-1802773279/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1643_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((208908209/500000000 : ℝ)*X 0 0+(3731527867/10000000000 : ℝ)*X 0 1+(932545559/2000000000 : ℝ)*X 0 2+(208908209/500000000 : ℝ)*X 1 0+(3731527867/10000000000 : ℝ)*X 1 1+(932545559/2000000000 : ℝ)*X 1 2+(208908209/500000000 : ℝ)*X 2 0+(3731527867/10000000000 : ℝ)*X 2 1+(932545559/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1643_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-806992037/5000000000 : ℝ)*X 0 0+(5142241469/10000000000 : ℝ)*X 0 1+(5497853909/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1643_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2632766393/5000000000 : ℝ)*X 1 0+(-144343423/1000000000 : ℝ)*X 1 1+(549785391/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1643_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((658191579/1250000000 : ℝ)*X 2 0+(5497854139/10000000000 : ℝ)*X 2 1+(-36085853/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1643_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2089293771/5000000000 : ℝ)*X 0 0+(581646499/1250000000 : ℝ)*X 0 1+(1870611023/5000000000 : ℝ)*X 0 2+(2089293771/5000000000 : ℝ)*X 1 0+(581646499/1250000000 : ℝ)*X 1 1+(1870611023/5000000000 : ℝ)*X 1 2+(2089293771/5000000000 : ℝ)*X 2 0+(581646499/1250000000 : ℝ)*X 2 1+(1870611023/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1643_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15929319555557678655782953401/2350000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (213987091/50000000000000 : ℝ)*(base1) + (111772003/20000000000000 : ℝ)*(base19) + (20213909/1562500000000 : ℝ)*(base23) + (6156747/50000000000000 : ℝ)*(lower2) + (97930741/100000000000000 : ℝ)*(lower4) + (99940147/100000000000000 : ℝ)*(upper5) + (1913902936655601/100000000000000 : ℝ)*(major0) + (1913902936655601/100000000000000 : ℝ)*(major1) + (1913902936655601/100000000000000 : ℝ)*(major2) + (21515014080857/781250000000 : ℝ)*(sp0) + (1376960407757749/50000000000000 : ℝ)*(sp1) + (1376960040342669/50000000000000 : ℝ)*(sp2) + (536941832728547/50000000000000 : ℝ)*(sp3) + (44889153/25000000000000 : ℝ)*(sp7) + (67117767061743/6250000000000 : ℝ)*(f.failure) + (1376960687187757/50000000000000 : ℝ)*(f.sum) + (696904301387119/94000000000000000000000000000 : ℝ)*base65 + (33104191239938959467/9400000000000000000000000000000000 : ℝ)*base67 + (41253274953661040533/9400000000000000000000000000000000 : ℝ)*base70 + (20423743720461040533/9400000000000000000000000000000000 : ℝ)*base72 + (116721608247119/94000000000000000000000000000 : ℝ)*base73 + (33734799746461040533/9400000000000000000000000000000000 : ℝ)*base76 + (50315849000461040533/9400000000000000000000000000000000 : ℝ)*base78 + (64138249892461040533/9400000000000000000000000000000000 : ℝ)*base80 + (121589619020881/94000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1912551/625000000000000000000 : ℝ)*base89 + (1912551/625000000000000000000 : ℝ)*base91 + (1912551/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5596434370131217407249935649/1175000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (968601293/100000000000000 : ℝ)*(base19) + (478411029/50000000000000 : ℝ)*(base23) + (26721053/100000000000000 : ℝ)*(upper2) + (117991091/100000000000000 : ℝ)*(upper3) + (12471443/10000000000000 : ℝ)*(upper5) + (488575138831551/25000000000000 : ℝ)*(major0) + (488575138831551/25000000000000 : ℝ)*(major1) + (488575138831551/25000000000000 : ℝ)*(major2) + (2214963551/25000000000000 : ℝ)*(sp1) + (9929861679/100000000000000 : ℝ)*(sp2) + (2812049715740661/100000000000000 : ℝ)*(sp4) + (703009971821291/25000000000000 : ℝ)*(sp5) + (703009707264231/25000000000000 : ℝ)*(sp6) + (274137809036911/25000000000000 : ℝ)*(sp7) + (274137809036911/25000000000000 : ℝ)*(f.failure) + (2812049715740661/100000000000000 : ℝ)*(f.sum) + (68931472241831/23500000000000000000000000000 : ℝ)*base66 + (16340681437158238117/2350000000000000000000000000000000 : ℝ)*base67 + (11707901739558238117/2350000000000000000000000000000000 : ℝ)*base69 + (21024653311508238117/2350000000000000000000000000000000 : ℝ)*base71 + (113200928331169/23500000000000000000000000000 : ℝ)*base73 + (4890349211291761883/2350000000000000000000000000000000 : ℝ)*base76 + (4250125776891761883/2350000000000000000000000000000000 : ℝ)*base78 + (10565662699458238117/2350000000000000000000000000000000 : ℝ)*base79 + (26717777286669/23500000000000000000000000000 : ℝ)*base81 + (17889673/2500000000000000000000 : ℝ)*base90 + (17889673/2500000000000000000000 : ℝ)*base92 + (17889673/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1643_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (178222457/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (23507/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4707/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (483/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17371/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1643_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1643_s2_0 (p : ℝ) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1623807643/10000000000 : ℝ)*x 0 + (5453621719/10000000000 : ℝ)*x 1 + (1035989133/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1623807643/10000000000 : ℝ)^4891 ≤ (2508536303813/25000000000000 : ℝ)^3867 := by
    have hnat : (1623807643 : ℕ)^4891*25000000000000^3867 ≤ 2508536303813^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1623807643 10000000000 2508536303813 25000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5453621719/10000000000 : ℝ)^4891 ≤ (23223514983087/50000000000000 : ℝ)^3867 := by
    have hnat : (5453621719 : ℕ)^4891*50000000000000^3867 ≤ 23223514983087^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5453621719 10000000000 23223514983087 50000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1035989133/2000000000 : ℝ)^4891 ≤ (21759412401929/50000000000000 : ℝ)^3867 := by
    have hnat : (1035989133 : ℕ)^4891*50000000000000^3867 ≤ 21759412401929^3867*2000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035989133 2000000000 21759412401929 50000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4891/1024 : ℝ)) 4891 3867 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1623807643/10000000000 : ℝ), (5453621719/10000000000 : ℝ), (1035989133/2000000000 : ℝ)] ![(2508536303813/25000000000000 : ℝ), (23223514983087/50000000000000 : ℝ), (21759412401929/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1623807643/10000000000 : ℝ)|^4891 ≤ (2508536303813/25000000000000 : ℝ)^3867
        have hw : |(-1623807643/10000000000 : ℝ)|=(1623807643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5453621719/10000000000 : ℝ)|^4891 ≤ (23223514983087/50000000000000 : ℝ)^3867
        have hw : |(5453621719/10000000000 : ℝ)|=(5453621719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1035989133/2000000000 : ℝ)|^4891 ≤ (21759412401929/50000000000000 : ℝ)^3867
        have hw : |(1035989133/2000000000 : ℝ)|=(1035989133/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1643_s2_1 (p : ℝ) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337468057/2500000000 : ℝ)*x 0 + (-1764848563/10000000000 : ℝ)*x 1 + (2589973181/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337468057/2500000000 : ℝ)^4891 ≤ (9066453694287/20000000000000 : ℝ)^3867 := by
    have hnat : (1337468057 : ℕ)^4891*20000000000000^3867 ≤ 9066453694287^3867*2500000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337468057 2500000000 9066453694287 20000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1764848563/10000000000 : ℝ)^4891 ≤ (2787224825881/25000000000000 : ℝ)^3867 := by
    have hnat : (1764848563 : ℕ)^4891*25000000000000^3867 ≤ 2787224825881^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1764848563 10000000000 2787224825881 25000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2589973181/5000000000 : ℝ)^4891 ≤ (10879708052569/25000000000000 : ℝ)^3867 := by
    have hnat : (2589973181 : ℕ)^4891*25000000000000^3867 ≤ 10879708052569^3867*5000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2589973181 5000000000 10879708052569 25000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4891/1024 : ℝ)) 4891 3867 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337468057/2500000000 : ℝ), (-1764848563/10000000000 : ℝ), (2589973181/5000000000 : ℝ)] ![(9066453694287/20000000000000 : ℝ), (2787224825881/25000000000000 : ℝ), (10879708052569/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337468057/2500000000 : ℝ)|^4891 ≤ (9066453694287/20000000000000 : ℝ)^3867
        have hw : |(1337468057/2500000000 : ℝ)|=(1337468057/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1764848563/10000000000 : ℝ)|^4891 ≤ (2787224825881/25000000000000 : ℝ)^3867
        have hw : |(-1764848563/10000000000 : ℝ)|=(1764848563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2589973181/5000000000 : ℝ)|^4891 ≤ (10879708052569/25000000000000 : ℝ)^3867
        have hw : |(2589973181/5000000000 : ℝ)|=(2589973181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1643_s2_2 (p : ℝ) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674937187/5000000000 : ℝ)*x 0 + (5179944943/10000000000 : ℝ)*x 1 + (-441211893/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674937187/5000000000 : ℝ)^4891 ≤ (362658331767/800000000000 : ℝ)^3867 := by
    have hnat : (2674937187 : ℕ)^4891*800000000000^3867 ≤ 362658331767^3867*5000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674937187 5000000000 362658331767 800000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5179944943/10000000000 : ℝ)^4891 ≤ (43518817131787/100000000000000 : ℝ)^3867 := by
    have hnat : (5179944943 : ℕ)^4891*100000000000000^3867 ≤ 43518817131787^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179944943 10000000000 43518817131787 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (441211893/2500000000 : ℝ)^4891 ≤ (2787222846353/25000000000000 : ℝ)^3867 := by
    have hnat : (441211893 : ℕ)^4891*25000000000000^3867 ≤ 2787222846353^3867*2500000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441211893 2500000000 2787222846353 25000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4891/1024 : ℝ)) 4891 3867 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674937187/5000000000 : ℝ), (5179944943/10000000000 : ℝ), (-441211893/2500000000 : ℝ)] ![(362658331767/800000000000 : ℝ), (43518817131787/100000000000000 : ℝ), (2787222846353/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674937187/5000000000 : ℝ)|^4891 ≤ (362658331767/800000000000 : ℝ)^3867
        have hw : |(2674937187/5000000000 : ℝ)|=(2674937187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5179944943/10000000000 : ℝ)|^4891 ≤ (43518817131787/100000000000000 : ℝ)^3867
        have hw : |(5179944943/10000000000 : ℝ)|=(5179944943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-441211893/2500000000 : ℝ)|^4891 ≤ (2787222846353/25000000000000 : ℝ)^3867
        have hw : |(-441211893/2500000000 : ℝ)|=(441211893/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1643_s2_3 (p : ℝ) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (523199687/1250000000 : ℝ)*x 0 + (384545987/1000000000 : ℝ)*x 1 + (2273644413/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (523199687/1250000000 : ℝ)^4891 ≤ (8308775936679/25000000000000 : ℝ)^3867 := by
    have hnat : (523199687 : ℕ)^4891*25000000000000^3867 ≤ 8308775936679^3867*1250000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523199687 1250000000 8308775936679 25000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (384545987/1000000000 : ℝ)^4891 ≤ (7464154543779/25000000000000 : ℝ)^3867 := by
    have hnat : (384545987 : ℕ)^4891*25000000000000^3867 ≤ 7464154543779^3867*1000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      384545987 1000000000 7464154543779 25000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2273644413/5000000000 : ℝ)^4891 ≤ (36908278057361/100000000000000 : ℝ)^3867 := by
    have hnat : (2273644413 : ℕ)^4891*100000000000000^3867 ≤ 36908278057361^3867*5000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2273644413 5000000000 36908278057361 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4891/1024 : ℝ)) 4891 3867 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(523199687/1250000000 : ℝ), (384545987/1000000000 : ℝ), (2273644413/5000000000 : ℝ)] ![(8308775936679/25000000000000 : ℝ), (7464154543779/25000000000000 : ℝ), (36908278057361/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(523199687/1250000000 : ℝ)|^4891 ≤ (8308775936679/25000000000000 : ℝ)^3867
        have hw : |(523199687/1250000000 : ℝ)|=(523199687/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(384545987/1000000000 : ℝ)|^4891 ≤ (7464154543779/25000000000000 : ℝ)^3867
        have hw : |(384545987/1000000000 : ℝ)|=(384545987/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2273644413/5000000000 : ℝ)|^4891 ≤ (36908278057361/100000000000000 : ℝ)^3867
        have hw : |(2273644413/5000000000 : ℝ)|=(2273644413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1643_s2_4 (p : ℝ) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-101492343/625000000 : ℝ)*x 0 + (2591034151/5000000000 : ℝ)*x 1 + (2725738461/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (101492343/625000000 : ℝ)^4891 ≤ (10034691107701/100000000000000 : ℝ)^3867 := by
    have hnat : (101492343 : ℕ)^4891*100000000000000^3867 ≤ 10034691107701^3867*625000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      101492343 625000000 10034691107701 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2591034151/5000000000 : ℝ)^4891 ≤ (43541381460863/100000000000000 : ℝ)^3867 := by
    have hnat : (2591034151 : ℕ)^4891*100000000000000^3867 ≤ 43541381460863^3867*5000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591034151 5000000000 43541381460863 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2725738461/5000000000 : ℝ)^4891 ≤ (23211963705791/50000000000000 : ℝ)^3867 := by
    have hnat : (2725738461 : ℕ)^4891*50000000000000^3867 ≤ 23211963705791^3867*5000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2725738461 5000000000 23211963705791 50000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4891/1024 : ℝ)) 4891 3867 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-101492343/625000000 : ℝ), (2591034151/5000000000 : ℝ), (2725738461/5000000000 : ℝ)] ![(10034691107701/100000000000000 : ℝ), (43541381460863/100000000000000 : ℝ), (23211963705791/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-101492343/625000000 : ℝ)|^4891 ≤ (10034691107701/100000000000000 : ℝ)^3867
        have hw : |(-101492343/625000000 : ℝ)|=(101492343/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2591034151/5000000000 : ℝ)|^4891 ≤ (43541381460863/100000000000000 : ℝ)^3867
        have hw : |(2591034151/5000000000 : ℝ)|=(2591034151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2725738461/5000000000 : ℝ)|^4891 ≤ (23211963705791/50000000000000 : ℝ)^3867
        have hw : |(2725738461/5000000000 : ℝ)|=(2725738461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1643_s2_5 (p : ℝ) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276817789/10000000000 : ℝ)*x 0 + (-1493317231/10000000000 : ℝ)*x 1 + (218059051/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276817789/10000000000 : ℝ)^4891 ≤ (11137684651479/25000000000000 : ℝ)^3867 := by
    have hnat : (5276817789 : ℕ)^4891*25000000000000^3867 ≤ 11137684651479^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276817789 10000000000 11137684651479 25000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1493317231/10000000000 : ℝ)^4891 ≤ (1805068187413/20000000000000 : ℝ)^3867 := by
    have hnat : (1493317231 : ℕ)^4891*20000000000000^3867 ≤ 1805068187413^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1493317231 10000000000 1805068187413 20000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (218059051/400000000 : ℝ)^4891 ≤ (23211960221411/50000000000000 : ℝ)^3867 := by
    have hnat : (218059051 : ℕ)^4891*50000000000000^3867 ≤ 23211960221411^3867*400000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218059051 400000000 23211960221411 50000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4891/1024 : ℝ)) 4891 3867 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276817789/10000000000 : ℝ), (-1493317231/10000000000 : ℝ), (218059051/400000000 : ℝ)] ![(11137684651479/25000000000000 : ℝ), (1805068187413/20000000000000 : ℝ), (23211960221411/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276817789/10000000000 : ℝ)|^4891 ≤ (11137684651479/25000000000000 : ℝ)^3867
        have hw : |(5276817789/10000000000 : ℝ)|=(5276817789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1493317231/10000000000 : ℝ)|^4891 ≤ (1805068187413/20000000000000 : ℝ)^3867
        have hw : |(-1493317231/10000000000 : ℝ)|=(1493317231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(218059051/400000000 : ℝ)|^4891 ≤ (23211960221411/50000000000000 : ℝ)^3867
        have hw : |(218059051/400000000 : ℝ)|=(218059051/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1643_s2_6 (p : ℝ) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276818629/10000000000 : ℝ)*x 0 + (5451475833/10000000000 : ℝ)*x 1 + (-37332917/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276818629/10000000000 : ℝ)^4891 ≤ (1782029903031/4000000000000 : ℝ)^3867 := by
    have hnat : (5276818629 : ℕ)^4891*4000000000000^3867 ≤ 1782029903031^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276818629 10000000000 1782029903031 4000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5451475833/10000000000 : ℝ)^4891 ≤ (23211957841047/50000000000000 : ℝ)^3867 := by
    have hnat : (5451475833 : ℕ)^4891*50000000000000^3867 ≤ 23211957841047^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5451475833 10000000000 23211957841047 50000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (37332917/250000000 : ℝ)^4891 ≤ (4512668362541/50000000000000 : ℝ)^3867 := by
    have hnat : (37332917 : ℕ)^4891*50000000000000^3867 ≤ 4512668362541^3867*250000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37332917 250000000 4512668362541 50000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4891/1024 : ℝ)) 4891 3867 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276818629/10000000000 : ℝ), (5451475833/10000000000 : ℝ), (-37332917/250000000 : ℝ)] ![(1782029903031/4000000000000 : ℝ), (23211957841047/50000000000000 : ℝ), (4512668362541/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276818629/10000000000 : ℝ)|^4891 ≤ (1782029903031/4000000000000 : ℝ)^3867
        have hw : |(5276818629/10000000000 : ℝ)|=(5276818629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5451475833/10000000000 : ℝ)|^4891 ≤ (23211957841047/50000000000000 : ℝ)^3867
        have hw : |(5451475833/10000000000 : ℝ)|=(5451475833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-37332917/250000000 : ℝ)|^4891 ≤ (4512668362541/50000000000000 : ℝ)^3867
        have hw : |(-37332917/250000000 : ℝ)|=(37332917/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1643_s2_7 (p : ℝ) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2092890049/5000000000 : ℝ)*x 0 + (283865317/625000000 : ℝ)*x 1 + (240685127/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2092890049/5000000000 : ℝ)^4891 ≤ (8309234406881/25000000000000 : ℝ)^3867 := by
    have hnat : (2092890049 : ℕ)^4891*25000000000000^3867 ≤ 8309234406881^3867*5000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2092890049 5000000000 8309234406881 25000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (283865317/625000000 : ℝ)^4891 ≤ (36852402179039/100000000000000 : ℝ)^3867 := by
    have hnat : (283865317 : ℕ)^4891*100000000000000^3867 ≤ 36852402179039^3867*625000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283865317 625000000 36852402179039 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (240685127/625000000 : ℝ)^4891 ≤ (29910660177509/100000000000000 : ℝ)^3867 := by
    have hnat : (240685127 : ℕ)^4891*100000000000000^3867 ≤ 29910660177509^3867*625000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      240685127 625000000 29910660177509 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4891/1024 : ℝ)) 4891 3867 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2092890049/5000000000 : ℝ), (283865317/625000000 : ℝ), (240685127/625000000 : ℝ)] ![(8309234406881/25000000000000 : ℝ), (36852402179039/100000000000000 : ℝ), (29910660177509/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2092890049/5000000000 : ℝ)|^4891 ≤ (8309234406881/25000000000000 : ℝ)^3867
        have hw : |(2092890049/5000000000 : ℝ)|=(2092890049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(283865317/625000000 : ℝ)|^4891 ≤ (36852402179039/100000000000000 : ℝ)^3867
        have hw : |(283865317/625000000 : ℝ)|=(283865317/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(240685127/625000000 : ℝ)|^4891 ≤ (29910660177509/100000000000000 : ℝ)^3867
        have hw : |(240685127/625000000 : ℝ)|=(240685127/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1643_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (178222457/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17371/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (483/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (2111/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16369/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17371/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (483/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17371/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (483/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17371/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (483/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17371/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (483/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17371/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (483/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17371/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (483/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (483/5000 : ℝ) ^ (4887/1024 : ℝ) ≤ (178958774946411/12500000000000000000 : ℝ) := by
    have hpowers : (483/5000 : ℝ)^4887 ≤ (178958774946411/12500000000000000000 : ℝ)^1024 := by
      have hnat : (483 : ℕ)^4887*12500000000000000000^1024 ≤ 178958774946411^1024*5000^4887 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        483 5000 178958774946411 12500000000000000000 4887 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (483/5000 : ℝ)) (X := (178958774946411/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4887 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17371/100000 : ℝ) ^ (4887/1024 : ℝ) ≤ (23555571701290047/100000000000000000000 : ℝ) := by
    have hpowers : (17371/100000 : ℝ)^4887 ≤ (23555571701290047/100000000000000000000 : ℝ)^1024 := by
      have hnat : (17371 : ℕ)^4887*100000000000000000000^1024 ≤ 23555571701290047^1024*100000^4887 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17371 100000 23555571701290047 100000000000000000000 4887 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17371/100000 : ℝ)) (X := (23555571701290047/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4887 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250178958774946411/6250000000000000000 : ℝ) ≤ (1250007499558491/1250000000000000 : ℝ) ^ (4887/1024 : ℝ) := by
    have hpowers : (6250178958774946411/6250000000000000000 : ℝ)^1024 ≤ (1250007499558491/1250000000000000 : ℝ)^4887 := by
      have hnat : (6250178958774946411 : ℕ)^1024*1250000000000000^4887 ≤ 1250007499558491^4887*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250178958774946411 6250000000000000000 1250007499558491 1250000000000000 1024 4887 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250007499558491/1250000000000000 : ℝ)) (X := (6250178958774946411/6250000000000000000 : ℝ)) (by norm_num) 4887 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20004997448380172267/20000000000000000000 : ℝ) ≤ (2500130879932361/2500000000000000 : ℝ) ^ (4887/1024 : ℝ) := by
    have hpowers : (20004997448380172267/20000000000000000000 : ℝ)^1024 ≤ (2500130879932361/2500000000000000 : ℝ)^4887 := by
      have hnat : (20004997448380172267 : ℕ)^1024*2500000000000000^4887 ≤ 2500130879932361^4887*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20004997448380172267 20000000000000000000 2500130879932361 2500000000000000 1024 4887 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500130879932361/2500000000000000 : ℝ)) (X := (20004997448380172267/20000000000000000000 : ℝ)) (by norm_num) 4887 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50023555571701290047/50000000000000000000 : ℝ) ≤ (125012338037387/125000000000000 : ℝ) ^ (4887/1024 : ℝ) := by
    have hpowers : (50023555571701290047/50000000000000000000 : ℝ)^1024 ≤ (125012338037387/125000000000000 : ℝ)^4887 := by
      have hnat : (50023555571701290047 : ℕ)^1024*125000000000000^4887 ≤ 125012338037387^4887*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023555571701290047 50000000000000000000 125012338037387 125000000000000 1024 4887 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125012338037387/125000000000000 : ℝ)) (X := (50023555571701290047/50000000000000000000 : ℝ)) (by norm_num) 4887 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(178958774946411/12500000000000000000 : ℝ) ≤ ((9637688420418962961/9638750000000000000 : ℝ)+2*(115880815379/192775000000000 : ℝ)*(483/5000 : ℝ))^(4887/1024 : ℝ) := by
    rw [show (9637688420418962961/9638750000000000000 : ℝ)+2*(115880815379/192775000000000 : ℝ)*(483/5000 : ℝ)=(1250007499558491/1250000000000000 : ℝ) by norm_num, show 1+2*(178958774946411/12500000000000000000 : ℝ)=(6250178958774946411/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(23555571701290047/100000000000000000000 : ℝ)+(178958774946411/12500000000000000000 : ℝ) ≤ ((9637688420418962961/9638750000000000000 : ℝ)+(115880815379/192775000000000 : ℝ)*((17371/100000 : ℝ)+(483/5000 : ℝ)))^(4887/1024 : ℝ) := by
    rw [show (9637688420418962961/9638750000000000000 : ℝ)+(115880815379/192775000000000 : ℝ)*((17371/100000 : ℝ)+(483/5000 : ℝ))=(2500130879932361/2500000000000000 : ℝ) by norm_num, show 1+(23555571701290047/100000000000000000000 : ℝ)+(178958774946411/12500000000000000000 : ℝ)=(20004997448380172267/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(23555571701290047/100000000000000000000 : ℝ) ≤ ((9637688420418962961/9638750000000000000 : ℝ)+2*(115880815379/192775000000000 : ℝ)*(17371/100000 : ℝ))^(4887/1024 : ℝ) := by
    rw [show (9637688420418962961/9638750000000000000 : ℝ)+2*(115880815379/192775000000000 : ℝ)*(17371/100000 : ℝ)=(125012338037387/125000000000000 : ℝ) by norm_num, show 1+2*(23555571701290047/100000000000000000000 : ℝ)=(50023555571701290047/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9637688420418962961/9638750000000000000 : ℝ)*(X 1 0+X 2 0)+(115880815379/192775000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4887/1024 : ℝ)) (lo := (483/5000 : ℝ)) (hi := (17371/100000 : ℝ)) (c := (9637688420418962961/9638750000000000000 : ℝ)) (alpha := (115880815379/192775000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9637688420418962961/9638750000000000000 : ℝ)*(X 0 1+X 2 1)+(115880815379/192775000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4887/1024 : ℝ)) (lo := (483/5000 : ℝ)) (hi := (17371/100000 : ℝ)) (c := (9637688420418962961/9638750000000000000 : ℝ)) (alpha := (115880815379/192775000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9637688420418962961/9638750000000000000 : ℝ)*(X 0 2+X 1 2)+(115880815379/192775000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4887/1024 : ℝ)) (lo := (483/5000 : ℝ)) (hi := (17371/100000 : ℝ)) (c := (9637688420418962961/9638750000000000000 : ℝ)) (alpha := (115880815379/192775000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1623807643/10000000000 : ℝ)*X 0 0+(5453621719/10000000000 : ℝ)*X 0 1+(1035989133/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1643_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337468057/2500000000 : ℝ)*X 1 0+(-1764848563/10000000000 : ℝ)*X 1 1+(2589973181/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1643_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674937187/5000000000 : ℝ)*X 2 0+(5179944943/10000000000 : ℝ)*X 2 1+(-441211893/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1643_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((523199687/1250000000 : ℝ)*X 0 0+(384545987/1000000000 : ℝ)*X 0 1+(2273644413/5000000000 : ℝ)*X 0 2+(523199687/1250000000 : ℝ)*X 1 0+(384545987/1000000000 : ℝ)*X 1 1+(2273644413/5000000000 : ℝ)*X 1 2+(523199687/1250000000 : ℝ)*X 2 0+(384545987/1000000000 : ℝ)*X 2 1+(2273644413/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1643_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-101492343/625000000 : ℝ)*X 0 0+(2591034151/5000000000 : ℝ)*X 0 1+(2725738461/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1643_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5276817789/10000000000 : ℝ)*X 1 0+(-1493317231/10000000000 : ℝ)*X 1 1+(218059051/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1643_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5276818629/10000000000 : ℝ)*X 2 0+(5451475833/10000000000 : ℝ)*X 2 1+(-37332917/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1643_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2092890049/5000000000 : ℝ)*X 0 0+(283865317/625000000 : ℝ)*X 0 1+(240685127/625000000 : ℝ)*X 0 2+(2092890049/5000000000 : ℝ)*X 1 0+(283865317/625000000 : ℝ)*X 1 1+(240685127/625000000 : ℝ)*X 1 2+(2092890049/5000000000 : ℝ)*X 2 0+(283865317/625000000 : ℝ)*X 2 1+(240685127/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1643_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (77424590201774258299373853/30121093750000000000000000000000 : ℝ) := by norm_num
    linear_combination (90620949/10000000000000 : ℝ)*(base23) + (43391399/50000000000000 : ℝ)*(lower2) + (123167427/50000000000000 : ℝ)*(upper4) + (290878183/100000000000000 : ℝ)*(upper5) + (317426148634693/12500000000000 : ℝ)*(major0) + (317426148634693/12500000000000 : ℝ)*(major1) + (317426148634693/12500000000000 : ℝ)*(major2) + (3653950635041919/100000000000000 : ℝ)*(sp0) + (913490003616801/25000000000000 : ℝ)*(sp1) + (3653963733237921/100000000000000 : ℝ)*(sp2) + (356212586174589/25000000000000 : ℝ)*(sp3) + (3501101373/25000000000000 : ℝ)*(sp4) + (289061263/6250000000000 : ℝ)*(sp5) + (3308327841/100000000000000 : ℝ)*(sp7) + (712426826513099/50000000000000 : ℝ)*(f.failure) + (3653964639447411/100000000000000 : ℝ)*(f.sum) + (99103732659249/38555000000000000000000000000 : ℝ)*base65 + (419195382340048299/60242187500000000000000000000000 : ℝ)*base67 + (125782340813735087/30121093750000000000000000000000 : ℝ)*base69 + (221965592768512777/120484375000000000000000000000000 : ℝ)*base72 + (50388430362311/9638750000000000000000000000 : ℝ)*base73 + (171497627658794027/120484375000000000000000000000000 : ℝ)*base76 + (96208842307580973/120484375000000000000000000000000 : ℝ)*base77 + (224115149965578837/30121093750000000000000000000000 : ℝ)*base79 + (26533547901781/9638750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (46464243/5000000000000000000000 : ℝ)*base89 + (46464243/5000000000000000000000 : ℝ)*base91 + (46464243/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1911483795680561585708371383/240968750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (606778401/100000000000000 : ℝ)*(base19) + (209898277/10000000000000 : ℝ)*(base23) + (371641569/100000000000000 : ℝ)*(lower4) + (161249787/100000000000000 : ℝ)*(upper5) + (1289814861665417/50000000000000 : ℝ)*(major0) + (1289814861665417/50000000000000 : ℝ)*(major1) + (1289814861665417/50000000000000 : ℝ)*(major2) + (147947849/10000000000000 : ℝ)*(sp0) + (349920687/12500000000000 : ℝ)*(sp1) + (17031362121/100000000000000 : ℝ)*(sp2) + (927959112007639/25000000000000 : ℝ)*(sp4) + (74236690427303/2000000000000 : ℝ)*(sp5) + (927954699291039/25000000000000 : ℝ)*(sp6) + (72371062736803/5000000000000 : ℝ)*(sp7) + (72371062736803/5000000000000 : ℝ)*(f.failure) + (1855918963754523/50000000000000 : ℝ)*(f.sum) + (164778995402083/19277500000000000000000000000 : ℝ)*base66 + (2169481408810355263/481937500000000000000000000000000 : ℝ)*base68 + (152376273339105263/481937500000000000000000000000000 : ℝ)*base70 + (4166329571856355263/481937500000000000000000000000000 : ℝ)*base72 + (69473019827933/19277500000000000000000000000 : ℝ)*base74 + (1901456292371605263/481937500000000000000000000000000 : ℝ)*base76 + (3707308653002605263/481937500000000000000000000000000 : ℝ)*base78 + (5066497279274042763/481937500000000000000000000000000 : ℝ)*base80 + (11433069883299/9638750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (4984971/500000000000000000000 : ℝ)*base89 + (4984971/500000000000000000000 : ℝ)*base91 + (4984971/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1643_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (178222457/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17371/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (483/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2111/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16369/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1643_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1643_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (178222457/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2111/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16369/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1643_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1643_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1643_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (178222457/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2111/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16369/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1643_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
