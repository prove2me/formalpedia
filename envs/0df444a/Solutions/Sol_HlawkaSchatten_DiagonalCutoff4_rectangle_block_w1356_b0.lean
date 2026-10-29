-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1356_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:09:17.552993+00:00
-- url     : https://prove2.me/submissions/28e32142-aabb-4b85-87d2-f6d3fddb58ce

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
theorem support_rectangle_w1356_s0_0 (p : ℝ) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-450224683/2500000000 : ℝ)*x 0 + (5990892069/10000000000 : ℝ)*x 1 + (4814238303/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (450224683/2500000000 : ℝ)^1079 ≤ (10565837926073/100000000000000 : ℝ)^823 := by
    have hnat : (450224683 : ℕ)^1079*100000000000000^823 ≤ 10565837926073^823*2500000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450224683 2500000000 10565837926073 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5990892069/10000000000 : ℝ)^1079 ≤ (51083264529763/100000000000000 : ℝ)^823 := by
    have hnat : (5990892069 : ℕ)^1079*100000000000000^823 ≤ 51083264529763^823*10000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5990892069 10000000000 51083264529763 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4814238303/10000000000 : ℝ)^1079 ≤ (1917544876379/5000000000000 : ℝ)^823 := by
    have hnat : (4814238303 : ℕ)^1079*5000000000000^823 ≤ 1917544876379^823*10000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4814238303 10000000000 1917544876379 5000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1079/256 : ℝ)) 1079 823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-450224683/2500000000 : ℝ), (5990892069/10000000000 : ℝ), (4814238303/10000000000 : ℝ)] ![(10565837926073/100000000000000 : ℝ), (51083264529763/100000000000000 : ℝ), (1917544876379/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-450224683/2500000000 : ℝ)|^1079 ≤ (10565837926073/100000000000000 : ℝ)^823
        have hw : |(-450224683/2500000000 : ℝ)|=(450224683/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5990892069/10000000000 : ℝ)|^1079 ≤ (51083264529763/100000000000000 : ℝ)^823
        have hw : |(5990892069/10000000000 : ℝ)|=(5990892069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4814238303/10000000000 : ℝ)|^1079 ≤ (1917544876379/5000000000000 : ℝ)^823
        have hw : |(4814238303/10000000000 : ℝ)|=(4814238303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1356_s0_1 (p : ℝ) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2750122699/5000000000 : ℝ)*x 0 + (-2469025731/10000000000 : ℝ)*x 1 + (4814238779/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2750122699/5000000000 : ℝ)^1079 ≤ (22834739788519/50000000000000 : ℝ)^823 := by
    have hnat : (2750122699 : ℕ)^1079*50000000000000^823 ≤ 22834739788519^823*5000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2750122699 5000000000 22834739788519 50000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2469025731/10000000000 : ℝ)^1079 ≤ (998726119711/6250000000000 : ℝ)^823 := by
    have hnat : (2469025731 : ℕ)^1079*6250000000000^823 ≤ 998726119711^823*10000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2469025731 10000000000 998726119711 6250000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4814238779/10000000000 : ℝ)^1079 ≤ (7670180499791/20000000000000 : ℝ)^823 := by
    have hnat : (4814238779 : ℕ)^1079*20000000000000^823 ≤ 7670180499791^823*10000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4814238779 10000000000 7670180499791 20000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1079/256 : ℝ)) 1079 823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2750122699/5000000000 : ℝ), (-2469025731/10000000000 : ℝ), (4814238779/10000000000 : ℝ)] ![(22834739788519/50000000000000 : ℝ), (998726119711/6250000000000 : ℝ), (7670180499791/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2750122699/5000000000 : ℝ)|^1079 ≤ (22834739788519/50000000000000 : ℝ)^823
        have hw : |(2750122699/5000000000 : ℝ)|=(2750122699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2469025731/10000000000 : ℝ)|^1079 ≤ (998726119711/6250000000000 : ℝ)^823
        have hw : |(-2469025731/10000000000 : ℝ)|=(2469025731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4814238779/10000000000 : ℝ)|^1079 ≤ (7670180499791/20000000000000 : ℝ)^823
        have hw : |(4814238779/10000000000 : ℝ)|=(4814238779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1356_s0_2 (p : ℝ) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2750122619/5000000000 : ℝ)*x 0 + (601779793/1250000000 : ℝ)*x 1 + (-2469026471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2750122619/5000000000 : ℝ)^1079 ≤ (45669477835289/100000000000000 : ℝ)^823 := by
    have hnat : (2750122619 : ℕ)^1079*100000000000000^823 ≤ 45669477835289^823*5000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2750122619 5000000000 45669477835289 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (601779793/1250000000 : ℝ)^1079 ≤ (38350897955787/100000000000000 : ℝ)^823 := by
    have hnat : (601779793 : ℕ)^1079*100000000000000^823 ≤ 38350897955787^823*1250000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      601779793 1250000000 38350897955787 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2469026471/10000000000 : ℝ)^1079 ≤ (15979624194429/100000000000000 : ℝ)^823 := by
    have hnat : (2469026471 : ℕ)^1079*100000000000000^823 ≤ 15979624194429^823*10000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2469026471 10000000000 15979624194429 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1079/256 : ℝ)) 1079 823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2750122619/5000000000 : ℝ), (601779793/1250000000 : ℝ), (-2469026471/10000000000 : ℝ)] ![(45669477835289/100000000000000 : ℝ), (38350897955787/100000000000000 : ℝ), (15979624194429/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2750122619/5000000000 : ℝ)|^1079 ≤ (45669477835289/100000000000000 : ℝ)^823
        have hw : |(2750122619/5000000000 : ℝ)|=(2750122619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(601779793/1250000000 : ℝ)|^1079 ≤ (38350897955787/100000000000000 : ℝ)^823
        have hw : |(601779793/1250000000 : ℝ)|=(601779793/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2469026471/10000000000 : ℝ)|^1079 ≤ (15979624194429/100000000000000 : ℝ)^823
        have hw : |(-2469026471/10000000000 : ℝ)|=(2469026471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1356_s0_3 (p : ℝ) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2088329247/5000000000 : ℝ)*x 0 + (388237553/1250000000 : ℝ)*x 1 + (1116694871/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2088329247/5000000000 : ℝ)^1079 ≤ (15916776777699/50000000000000 : ℝ)^823 := by
    have hnat : (2088329247 : ℕ)^1079*50000000000000^823 ≤ 15916776777699^823*5000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2088329247 5000000000 15916776777699 50000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (388237553/1250000000 : ℝ)^1079 ≤ (21588817199129/100000000000000 : ℝ)^823 := by
    have hnat : (388237553 : ℕ)^1079*100000000000000^823 ≤ 21588817199129^823*1250000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      388237553 1250000000 21588817199129 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1116694871/2000000000 : ℝ)^1079 ≤ (23288814614471/50000000000000 : ℝ)^823 := by
    have hnat : (1116694871 : ℕ)^1079*50000000000000^823 ≤ 23288814614471^823*2000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1116694871 2000000000 23288814614471 50000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1079/256 : ℝ)) 1079 823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2088329247/5000000000 : ℝ), (388237553/1250000000 : ℝ), (1116694871/2000000000 : ℝ)] ![(15916776777699/50000000000000 : ℝ), (21588817199129/100000000000000 : ℝ), (23288814614471/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2088329247/5000000000 : ℝ)|^1079 ≤ (15916776777699/50000000000000 : ℝ)^823
        have hw : |(2088329247/5000000000 : ℝ)|=(2088329247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(388237553/1250000000 : ℝ)|^1079 ≤ (21588817199129/100000000000000 : ℝ)^823
        have hw : |(388237553/1250000000 : ℝ)|=(388237553/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1116694871/2000000000 : ℝ)|^1079 ≤ (23288814614471/50000000000000 : ℝ)^823
        have hw : |(1116694871/2000000000 : ℝ)|=(1116694871/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1356_s0_4 (p : ℝ) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-361056487/2000000000 : ℝ)*x 0 + (2422248411/5000000000 : ℝ)*x 1 + (238382107/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (361056487/2000000000 : ℝ)^1079 ≤ (10599569893967/100000000000000 : ℝ)^823 := by
    have hnat : (361056487 : ℕ)^1079*100000000000000^823 ≤ 10599569893967^823*2000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      361056487 2000000000 10599569893967 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2422248411/5000000000 : ℝ)^1079 ≤ (19333613968557/50000000000000 : ℝ)^823 := by
    have hnat : (2422248411 : ℕ)^1079*50000000000000^823 ≤ 19333613968557^823*5000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2422248411 5000000000 19333613968557 50000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (238382107/400000000 : ℝ)^1079 ≤ (12683300537321/25000000000000 : ℝ)^823 := by
    have hnat : (238382107 : ℕ)^1079*25000000000000^823 ≤ 12683300537321^823*400000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      238382107 400000000 12683300537321 25000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1079/256 : ℝ)) 1079 823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-361056487/2000000000 : ℝ), (2422248411/5000000000 : ℝ), (238382107/400000000 : ℝ)] ![(10599569893967/100000000000000 : ℝ), (19333613968557/50000000000000 : ℝ), (12683300537321/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-361056487/2000000000 : ℝ)|^1079 ≤ (10599569893967/100000000000000 : ℝ)^823
        have hw : |(-361056487/2000000000 : ℝ)|=(361056487/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2422248411/5000000000 : ℝ)|^1079 ≤ (19333613968557/50000000000000 : ℝ)^823
        have hw : |(2422248411/5000000000 : ℝ)|=(2422248411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(238382107/400000000 : ℝ)|^1079 ≤ (12683300537321/25000000000000 : ℝ)^823
        have hw : |(238382107/400000000 : ℝ)|=(238382107/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1356_s0_5 (p : ℝ) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1035896411/2000000000 : ℝ)*x 0 + (-33092833/250000000 : ℝ)*x 1 + (5959552167/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1035896411/2000000000 : ℝ)^1079 ≤ (42209777769603/100000000000000 : ℝ)^823 := by
    have hnat : (1035896411 : ℕ)^1079*100000000000000^823 ≤ 42209777769603^823*2000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035896411 2000000000 42209777769603 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (33092833/250000000 : ℝ)^1079 ≤ (3528512868669/50000000000000 : ℝ)^823 := by
    have hnat : (33092833 : ℕ)^1079*50000000000000^823 ≤ 3528512868669^823*250000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33092833 250000000 3528512868669 50000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5959552167/10000000000 : ℝ)^1079 ≤ (25366598239767/50000000000000 : ℝ)^823 := by
    have hnat : (5959552167 : ℕ)^1079*50000000000000^823 ≤ 25366598239767^823*10000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5959552167 10000000000 25366598239767 50000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1079/256 : ℝ)) 1079 823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1035896411/2000000000 : ℝ), (-33092833/250000000 : ℝ), (5959552167/10000000000 : ℝ)] ![(42209777769603/100000000000000 : ℝ), (3528512868669/50000000000000 : ℝ), (25366598239767/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1035896411/2000000000 : ℝ)|^1079 ≤ (42209777769603/100000000000000 : ℝ)^823
        have hw : |(1035896411/2000000000 : ℝ)|=(1035896411/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-33092833/250000000 : ℝ)|^1079 ≤ (3528512868669/50000000000000 : ℝ)^823
        have hw : |(-33092833/250000000 : ℝ)|=(33092833/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5959552167/10000000000 : ℝ)|^1079 ≤ (25366598239767/50000000000000 : ℝ)^823
        have hw : |(5959552167/10000000000 : ℝ)|=(5959552167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1356_s0_6 (p : ℝ) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1294870481/2500000000 : ℝ)*x 0 + (2979776399/5000000000 : ℝ)*x 1 + (-1292688/9765625 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1294870481/2500000000 : ℝ)^1079 ≤ (42209776369953/100000000000000 : ℝ)^823 := by
    have hnat : (1294870481 : ℕ)^1079*100000000000000^823 ≤ 42209776369953^823*2500000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294870481 2500000000 42209776369953 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2979776399/5000000000 : ℝ)^1079 ≤ (25366601761039/50000000000000 : ℝ)^823 := by
    have hnat : (2979776399 : ℕ)^1079*50000000000000^823 ≤ 25366601761039^823*5000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2979776399 5000000000 25366601761039 50000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1292688/9765625 : ℝ)^1079 ≤ (352851004489/5000000000000 : ℝ)^823 := by
    have hnat : (1292688 : ℕ)^1079*5000000000000^823 ≤ 352851004489^823*9765625^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1292688 9765625 352851004489 5000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1079/256 : ℝ)) 1079 823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1294870481/2500000000 : ℝ), (2979776399/5000000000 : ℝ), (-1292688/9765625 : ℝ)] ![(42209776369953/100000000000000 : ℝ), (25366601761039/50000000000000 : ℝ), (352851004489/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1294870481/2500000000 : ℝ)|^1079 ≤ (42209776369953/100000000000000 : ℝ)^823
        have hw : |(1294870481/2500000000 : ℝ)|=(1294870481/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2979776399/5000000000 : ℝ)|^1079 ≤ (25366601761039/50000000000000 : ℝ)^823
        have hw : |(2979776399/5000000000 : ℝ)|=(2979776399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1292688/9765625 : ℝ)|^1079 ≤ (352851004489/5000000000000 : ℝ)^823
        have hw : |(-1292688/9765625 : ℝ)|=(1292688/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1356_s0_7 (p : ℝ) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4185885437/10000000000 : ℝ)*x 0 + (551976309/1000000000 : ℝ)*x 1 + (3171888783/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4185885437/10000000000 : ℝ)^1079 ≤ (31925786212339/100000000000000 : ℝ)^823 := by
    have hnat : (4185885437 : ℕ)^1079*100000000000000^823 ≤ 31925786212339^823*10000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4185885437 10000000000 31925786212339 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (551976309/1000000000 : ℝ)^1079 ≤ (5735258125523/12500000000000 : ℝ)^823 := by
    have hnat : (551976309 : ℕ)^1079*12500000000000^823 ≤ 5735258125523^823*1000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551976309 1000000000 5735258125523 12500000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3171888783/10000000000 : ℝ)^1079 ≤ (22192148767863/100000000000000 : ℝ)^823 := by
    have hnat : (3171888783 : ℕ)^1079*100000000000000^823 ≤ 22192148767863^823*10000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3171888783 10000000000 22192148767863 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1079/256 : ℝ)) 1079 823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4185885437/10000000000 : ℝ), (551976309/1000000000 : ℝ), (3171888783/10000000000 : ℝ)] ![(31925786212339/100000000000000 : ℝ), (5735258125523/12500000000000 : ℝ), (22192148767863/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4185885437/10000000000 : ℝ)|^1079 ≤ (31925786212339/100000000000000 : ℝ)^823
        have hw : |(4185885437/10000000000 : ℝ)|=(4185885437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(551976309/1000000000 : ℝ)|^1079 ≤ (5735258125523/12500000000000 : ℝ)^823
        have hw : |(551976309/1000000000 : ℝ)|=(551976309/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3171888783/10000000000 : ℝ)|^1079 ≤ (22192148767863/100000000000000 : ℝ)^823
        have hw : |(3171888783/10000000000 : ℝ)|=(3171888783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1356_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77640267/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1519/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (26771/100000 : ℝ)*pair X 0 0 := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
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
  have hpowlo : (0 : ℝ) ^ (4315/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4315 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4315*1^1024 ≤ 0^1024*1^4315 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4315 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4315 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4315/1024 : ℝ) ≤ (42088519615709093/2000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4315 ≤ (42088519615709093/2000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4315*2000000000000000000^1024 ≤ 42088519615709093^1024*5^4315 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 42088519615709093 2000000000000000000 4315 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (42088519615709093/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4315 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4315/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4315 := by
      have hnat : (1 : ℕ)^1024*1^4315 ≤ 1^4315*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4315 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4315 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (2042088519615709093/2000000000000000000 : ℝ) ≤ (502477229917293/500000000000000 : ℝ) ^ (4315/1024 : ℝ) := by
    have hpowers : (2042088519615709093/2000000000000000000 : ℝ)^1024 ≤ (502477229917293/500000000000000 : ℝ)^4315 := by
      have hnat : (2042088519615709093 : ℕ)^1024*500000000000000^4315 ≤ 502477229917293^4315*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2042088519615709093 2000000000000000000 502477229917293 500000000000000 1024 4315 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (502477229917293/500000000000000 : ℝ)) (X := (2042088519615709093/2000000000000000000 : ℝ)) (by norm_num) 4315 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1042088519615709093/1000000000000000000 : ℝ) ≤ (252477229917293/250000000000000 : ℝ) ^ (4315/1024 : ℝ) := by
    have hpowers : (1042088519615709093/1000000000000000000 : ℝ)^1024 ≤ (252477229917293/250000000000000 : ℝ)^4315 := by
      have hnat : (1042088519615709093 : ℕ)^1024*250000000000000^4315 ≤ 252477229917293^4315*1000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1042088519615709093 1000000000000000000 252477229917293 250000000000000 1024 4315 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (252477229917293/250000000000000 : ℝ)) (X := (1042088519615709093/1000000000000000000 : ℝ)) (by norm_num) 4315 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(2477229917293/200000000000000 : ℝ)*(0 : ℝ))^(4315/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(2477229917293/200000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(42088519615709093/2000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(2477229917293/200000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4315/1024 : ℝ) := by
    rw [show (1 : ℝ)+(2477229917293/200000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(502477229917293/500000000000000 : ℝ) by norm_num, show 1+(42088519615709093/2000000000000000000 : ℝ)+(0 : ℝ)=(2042088519615709093/2000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(42088519615709093/2000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(2477229917293/200000000000000 : ℝ)*(2/5 : ℝ))^(4315/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(2477229917293/200000000000000 : ℝ)*(2/5 : ℝ)=(252477229917293/250000000000000 : ℝ) by norm_num, show 1+2*(42088519615709093/2000000000000000000 : ℝ)=(1042088519615709093/1000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(2477229917293/200000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4315/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2477229917293/200000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(2477229917293/200000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4315/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2477229917293/200000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(2477229917293/200000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4315/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2477229917293/200000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-450224683/2500000000 : ℝ)*X 0 0+(5990892069/10000000000 : ℝ)*X 0 1+(4814238303/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1356_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2750122699/5000000000 : ℝ)*X 1 0+(-2469025731/10000000000 : ℝ)*X 1 1+(4814238779/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1356_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2750122619/5000000000 : ℝ)*X 2 0+(601779793/1250000000 : ℝ)*X 2 1+(-2469026471/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1356_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2088329247/5000000000 : ℝ)*X 0 0+(388237553/1250000000 : ℝ)*X 0 1+(1116694871/2000000000 : ℝ)*X 0 2+(2088329247/5000000000 : ℝ)*X 1 0+(388237553/1250000000 : ℝ)*X 1 1+(1116694871/2000000000 : ℝ)*X 1 2+(2088329247/5000000000 : ℝ)*X 2 0+(388237553/1250000000 : ℝ)*X 2 1+(1116694871/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1356_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-361056487/2000000000 : ℝ)*X 0 0+(2422248411/5000000000 : ℝ)*X 0 1+(238382107/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1356_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1035896411/2000000000 : ℝ)*X 1 0+(-33092833/250000000 : ℝ)*X 1 1+(5959552167/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1356_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1294870481/2500000000 : ℝ)*X 2 0+(2979776399/5000000000 : ℝ)*X 2 1+(-1292688/9765625 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1356_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4185885437/10000000000 : ℝ)*X 0 0+(551976309/1000000000 : ℝ)*X 0 1+(3171888783/10000000000 : ℝ)*X 0 2+(4185885437/10000000000 : ℝ)*X 1 0+(551976309/1000000000 : ℝ)*X 1 1+(3171888783/10000000000 : ℝ)*X 1 2+(4185885437/10000000000 : ℝ)*X 2 0+(551976309/1000000000 : ℝ)*X 2 1+(3171888783/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1356_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4275412885188095644761/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (24591041/20000000000000 : ℝ)*(base1) + (8492281/50000000000000 : ℝ)*(base16) + (776559899/100000000000000 : ℝ)*(base19) + (768822023/100000000000000 : ℝ)*(base23) + (141358831/100000000000000 : ℝ)*(upper3) + (313373855170409/50000000000000 : ℝ)*(major0) + (313373855170409/50000000000000 : ℝ)*(major1) + (313373855170409/50000000000000 : ℝ)*(major2) + (26558454279347/3125000000000 : ℝ)*(sp0) + (849871667302601/100000000000000 : ℝ)*(sp1) + (849871692025039/100000000000000 : ℝ)*(sp2) + (40362147332093/10000000000000 : ℝ)*(sp3) + (2046863163/100000000000000 : ℝ)*(sp4) + (39048357/3125000000000 : ℝ)*(sp7) + (403622845823559/100000000000000 : ℝ)*(f.failure) + (424936230423531/50000000000000 : ℝ)*(f.sum) + (5509062607837/5000000000000000000000000000 : ℝ)*base65 + (72020395437163/10000000000000000000000000000 : ℝ)*base68 + (85380575807163/10000000000000000000000000000 : ℝ)*base70 + (17738748077163/10000000000000000000000000000 : ℝ)*base72 + (9865649762163/5000000000000000000000000000 : ℝ)*base74 + (73289102227163/10000000000000000000000000000 : ℝ)*base76 + (68867088917163/10000000000000000000000000000 : ℝ)*base78 + (10520007977163/10000000000000000000000000000 : ℝ)*base80 + (1482947882163/5000000000000000000000000000 : ℝ)*base82 + (55650253/5000000000000000000000 : ℝ)*base89 + (55650253/5000000000000000000000 : ℝ)*base91 + (55650253/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (84256366759389530121999/10000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1519643713/100000000000000 : ℝ)*(base19) + (1717623627/100000000000000 : ℝ)*(base23) + (205883449/100000000000000 : ℝ)*(base39) + (85127189/50000000000000 : ℝ)*(upper3) + (15785369/6250000000000 : ℝ)*(upper5) + (165341534764823/25000000000000 : ℝ)*(major0) + (165341534764823/25000000000000 : ℝ)*(major1) + (661365933175843/100000000000000 : ℝ)*(major2) + (3476703817/100000000000000 : ℝ)*(sp1) + (3794843261/100000000000000 : ℝ)*(sp2) + (89681482547209/10000000000000 : ℝ)*(sp4) + (11210122864057/1250000000000 : ℝ)*(sp5) + (896809518888651/100000000000000 : ℝ)*(sp6) + (106479241477121/25000000000000 : ℝ)*(sp7) + (106479241477121/25000000000000 : ℝ)*(f.failure) + (896815031355539/100000000000000 : ℝ)*(f.sum) + (7566893694089/4000000000000000000000000000 : ℝ)*base66 + (182204644752999/20000000000000000000000000000 : ℝ)*base67 + (60657117174139/5000000000000000000000000000 : ℝ)*base69 + (137451666072999/20000000000000000000000000000 : ℝ)*base71 + (4191535205911/4000000000000000000000000000 : ℝ)*base73 + (20345616109139/5000000000000000000000000000 : ℝ)*base75 + (18438330034139/5000000000000000000000000000 : ℝ)*base77 + (26190741574139/5000000000000000000000000000 : ℝ)*base79 + (6575316461639/2500000000000000000000000000 : ℝ)*base81 + (1168693/1250000000000000000000 : ℝ)*base90 + (1168693/1250000000000000000000 : ℝ)*base92 + (1168693/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1356_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77640267/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1519/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (26771/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1356_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1356_s1_0 (p : ℝ) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1983693049/10000000000 : ℝ)*x 0 + (563591401/1000000000 : ℝ)*x 1 + (2526069197/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1983693049/10000000000 : ℝ)^1079 ≤ (749598881043/6250000000000 : ℝ)^823 := by
    have hnat : (1983693049 : ℕ)^1079*6250000000000^823 ≤ 749598881043^823*10000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1983693049 10000000000 749598881043 6250000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (563591401/1000000000 : ℝ)^1079 ≤ (47151992745229/100000000000000 : ℝ)^823 := by
    have hnat : (563591401 : ℕ)^1079*100000000000000^823 ≤ 47151992745229^823*1000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563591401 1000000000 47151992745229 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2526069197/5000000000 : ℝ)^1079 ≤ (40854425146037/100000000000000 : ℝ)^823 := by
    have hnat : (2526069197 : ℕ)^1079*100000000000000^823 ≤ 40854425146037^823*5000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2526069197 5000000000 40854425146037 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1079/256 : ℝ)) 1079 823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1983693049/10000000000 : ℝ), (563591401/1000000000 : ℝ), (2526069197/5000000000 : ℝ)] ![(749598881043/6250000000000 : ℝ), (47151992745229/100000000000000 : ℝ), (40854425146037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1983693049/10000000000 : ℝ)|^1079 ≤ (749598881043/6250000000000 : ℝ)^823
        have hw : |(-1983693049/10000000000 : ℝ)|=(1983693049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(563591401/1000000000 : ℝ)|^1079 ≤ (47151992745229/100000000000000 : ℝ)^823
        have hw : |(563591401/1000000000 : ℝ)|=(563591401/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2526069197/5000000000 : ℝ)|^1079 ≤ (40854425146037/100000000000000 : ℝ)^823
        have hw : |(2526069197/5000000000 : ℝ)|=(2526069197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1356_s1_1 (p : ℝ) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2702131359/5000000000 : ℝ)*x 0 + (-1147419841/5000000000 : ℝ)*x 1 + (2526069549/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2702131359/5000000000 : ℝ)^1079 ≤ (44627465950649/100000000000000 : ℝ)^823 := by
    have hnat : (2702131359 : ℕ)^1079*100000000000000^823 ≤ 44627465950649^823*5000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702131359 5000000000 44627465950649 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1147419841/5000000000 : ℝ)^1079 ≤ (14518101419813/100000000000000 : ℝ)^823 := by
    have hnat : (1147419841 : ℕ)^1079*100000000000000^823 ≤ 14518101419813^823*5000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1147419841 5000000000 14518101419813 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2526069549/5000000000 : ℝ)^1079 ≤ (20427216304903/50000000000000 : ℝ)^823 := by
    have hnat : (2526069549 : ℕ)^1079*50000000000000^823 ≤ 20427216304903^823*5000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2526069549 5000000000 20427216304903 50000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1079/256 : ℝ)) 1079 823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2702131359/5000000000 : ℝ), (-1147419841/5000000000 : ℝ), (2526069549/5000000000 : ℝ)] ![(44627465950649/100000000000000 : ℝ), (14518101419813/100000000000000 : ℝ), (20427216304903/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2702131359/5000000000 : ℝ)|^1079 ≤ (44627465950649/100000000000000 : ℝ)^823
        have hw : |(2702131359/5000000000 : ℝ)|=(2702131359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1147419841/5000000000 : ℝ)|^1079 ≤ (14518101419813/100000000000000 : ℝ)^823
        have hw : |(-1147419841/5000000000 : ℝ)|=(1147419841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2526069549/5000000000 : ℝ)|^1079 ≤ (20427216304903/50000000000000 : ℝ)^823
        have hw : |(2526069549/5000000000 : ℝ)|=(2526069549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1356_s1_2 (p : ℝ) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5404262781/10000000000 : ℝ)*x 0 + (5052138531/10000000000 : ℝ)*x 1 + (-573710081/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5404262781/10000000000 : ℝ)^1079 ≤ (22313733316359/50000000000000 : ℝ)^823 := by
    have hnat : (5404262781 : ℕ)^1079*50000000000000^823 ≤ 22313733316359^823*10000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404262781 10000000000 22313733316359 50000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5052138531/10000000000 : ℝ)^1079 ≤ (5106803324813/12500000000000 : ℝ)^823 := by
    have hnat : (5052138531 : ℕ)^1079*12500000000000^823 ≤ 5106803324813^823*10000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5052138531 10000000000 5106803324813 12500000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (573710081/2500000000 : ℝ)^1079 ≤ (7259053372373/50000000000000 : ℝ)^823 := by
    have hnat : (573710081 : ℕ)^1079*50000000000000^823 ≤ 7259053372373^823*2500000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      573710081 2500000000 7259053372373 50000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1079/256 : ℝ)) 1079 823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5404262781/10000000000 : ℝ), (5052138531/10000000000 : ℝ), (-573710081/2500000000 : ℝ)] ![(22313733316359/50000000000000 : ℝ), (5106803324813/12500000000000 : ℝ), (7259053372373/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5404262781/10000000000 : ℝ)|^1079 ≤ (22313733316359/50000000000000 : ℝ)^823
        have hw : |(5404262781/10000000000 : ℝ)|=(5404262781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5052138531/10000000000 : ℝ)|^1079 ≤ (5106803324813/12500000000000 : ℝ)^823
        have hw : |(5052138531/10000000000 : ℝ)|=(5052138531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-573710081/2500000000 : ℝ)|^1079 ≤ (7259053372373/50000000000000 : ℝ)^823
        have hw : |(-573710081/2500000000 : ℝ)|=(573710081/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1356_s1_3 (p : ℝ) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2144903789/5000000000 : ℝ)*x 0 + (464470159/1250000000 : ℝ)*x 1 + (2472480991/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2144903789/5000000000 : ℝ)^1079 ≤ (206055873421/625000000000 : ℝ)^823 := by
    have hnat : (2144903789 : ℕ)^1079*625000000000^823 ≤ 206055873421^823*5000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2144903789 5000000000 206055873421 625000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (464470159/1250000000 : ℝ)^1079 ≤ (13654572933897/50000000000000 : ℝ)^823 := by
    have hnat : (464470159 : ℕ)^1079*50000000000000^823 ≤ 13654572933897^823*1250000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      464470159 1250000000 13654572933897 50000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2472480991/5000000000 : ℝ)^1079 ≤ (7944382873669/20000000000000 : ℝ)^823 := by
    have hnat : (2472480991 : ℕ)^1079*20000000000000^823 ≤ 7944382873669^823*5000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2472480991 5000000000 7944382873669 20000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1079/256 : ℝ)) 1079 823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2144903789/5000000000 : ℝ), (464470159/1250000000 : ℝ), (2472480991/5000000000 : ℝ)] ![(206055873421/625000000000 : ℝ), (13654572933897/50000000000000 : ℝ), (7944382873669/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2144903789/5000000000 : ℝ)|^1079 ≤ (206055873421/625000000000 : ℝ)^823
        have hw : |(2144903789/5000000000 : ℝ)|=(2144903789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(464470159/1250000000 : ℝ)|^1079 ≤ (13654572933897/50000000000000 : ℝ)^823
        have hw : |(464470159/1250000000 : ℝ)|=(464470159/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2472480991/5000000000 : ℝ)|^1079 ≤ (7944382873669/20000000000000 : ℝ)^823
        have hw : |(2472480991/5000000000 : ℝ)|=(2472480991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1356_s1_4 (p : ℝ) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-496051147/2500000000 : ℝ)*x 0 + (1011877047/2000000000 : ℝ)*x 1 + (2814268381/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (496051147/2500000000 : ℝ)^1079 ≤ (11997637109371/100000000000000 : ℝ)^823 := by
    have hnat : (496051147 : ℕ)^1079*100000000000000^823 ≤ 11997637109371^823*2500000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      496051147 2500000000 11997637109371 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1011877047/2000000000 : ℝ)^1079 ≤ (40931272877613/100000000000000 : ℝ)^823 := by
    have hnat : (1011877047 : ℕ)^1079*100000000000000^823 ≤ 40931272877613^823*2000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1011877047 2000000000 40931272877613 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2814268381/5000000000 : ℝ)^1079 ≤ (47071090004209/100000000000000 : ℝ)^823 := by
    have hnat : (2814268381 : ℕ)^1079*100000000000000^823 ≤ 47071090004209^823*5000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2814268381 5000000000 47071090004209 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1079/256 : ℝ)) 1079 823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-496051147/2500000000 : ℝ), (1011877047/2000000000 : ℝ), (2814268381/5000000000 : ℝ)] ![(11997637109371/100000000000000 : ℝ), (40931272877613/100000000000000 : ℝ), (47071090004209/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-496051147/2500000000 : ℝ)|^1079 ≤ (11997637109371/100000000000000 : ℝ)^823
        have hw : |(-496051147/2500000000 : ℝ)|=(496051147/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1011877047/2000000000 : ℝ)|^1079 ≤ (40931272877613/100000000000000 : ℝ)^823
        have hw : |(1011877047/2000000000 : ℝ)|=(1011877047/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2814268381/5000000000 : ℝ)|^1079 ≤ (47071090004209/100000000000000 : ℝ)^823
        have hw : |(2814268381/5000000000 : ℝ)|=(2814268381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1356_s1_5 (p : ℝ) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1050521023/2000000000 : ℝ)*x 0 + (-429610457/2500000000 : ℝ)*x 1 + (5628536821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050521023/2000000000 : ℝ)^1079 ≤ (42992760492627/100000000000000 : ℝ)^823 := by
    have hnat : (1050521023 : ℕ)^1079*100000000000000^823 ≤ 42992760492627^823*2000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050521023 2000000000 42992760492627 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (429610457/2500000000 : ℝ)^1079 ≤ (155252325771/1562500000000 : ℝ)^823 := by
    have hnat : (429610457 : ℕ)^1079*1562500000000^823 ≤ 155252325771^823*2500000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429610457 2500000000 155252325771 1562500000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5628536821/10000000000 : ℝ)^1079 ≤ (23535545325551/50000000000000 : ℝ)^823 := by
    have hnat : (5628536821 : ℕ)^1079*50000000000000^823 ≤ 23535545325551^823*10000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5628536821 10000000000 23535545325551 50000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1079/256 : ℝ)) 1079 823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050521023/2000000000 : ℝ), (-429610457/2500000000 : ℝ), (5628536821/10000000000 : ℝ)] ![(42992760492627/100000000000000 : ℝ), (155252325771/1562500000000 : ℝ), (23535545325551/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050521023/2000000000 : ℝ)|^1079 ≤ (42992760492627/100000000000000 : ℝ)^823
        have hw : |(1050521023/2000000000 : ℝ)|=(1050521023/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-429610457/2500000000 : ℝ)|^1079 ≤ (155252325771/1562500000000 : ℝ)^823
        have hw : |(-429610457/2500000000 : ℝ)|=(429610457/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5628536821/10000000000 : ℝ)|^1079 ≤ (23535545325551/50000000000000 : ℝ)^823
        have hw : |(5628536821/10000000000 : ℝ)|=(5628536821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1356_s1_6 (p : ℝ) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5252605009/10000000000 : ℝ)*x 0 + (5628536901/10000000000 : ℝ)*x 1 + (-1718441861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5252605009/10000000000 : ℝ)^1079 ≤ (167940466231/390625000000 : ℝ)^823 := by
    have hnat : (5252605009 : ℕ)^1079*390625000000^823 ≤ 167940466231^823*10000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252605009 10000000000 167940466231 390625000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5628536901/10000000000 : ℝ)^1079 ≤ (11767772882061/25000000000000 : ℝ)^823 := by
    have hnat : (5628536901 : ℕ)^1079*25000000000000^823 ≤ 11767772882061^823*10000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5628536901 10000000000 11767772882061 25000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1718441861/10000000000 : ℝ)^1079 ≤ (1987229819901/20000000000000 : ℝ)^823 := by
    have hnat : (1718441861 : ℕ)^1079*20000000000000^823 ≤ 1987229819901^823*10000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1718441861 10000000000 1987229819901 20000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1079/256 : ℝ)) 1079 823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5252605009/10000000000 : ℝ), (5628536901/10000000000 : ℝ), (-1718441861/10000000000 : ℝ)] ![(167940466231/390625000000 : ℝ), (11767772882061/25000000000000 : ℝ), (1987229819901/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5252605009/10000000000 : ℝ)|^1079 ≤ (167940466231/390625000000 : ℝ)^823
        have hw : |(5252605009/10000000000 : ℝ)|=(5252605009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5628536901/10000000000 : ℝ)|^1079 ≤ (11767772882061/25000000000000 : ℝ)^823
        have hw : |(5628536901/10000000000 : ℝ)|=(5628536901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1718441861/10000000000 : ℝ)|^1079 ≤ (1987229819901/20000000000000 : ℝ)^823
        have hw : |(-1718441861/10000000000 : ℝ)|=(1718441861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1356_s1_7 (p : ℝ) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4290885227/10000000000 : ℝ)*x 0 + (4929704181/10000000000 : ℝ)*x 1 + (3731292503/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4290885227/10000000000 : ℝ)^1079 ≤ (3297979857839/10000000000000 : ℝ)^823 := by
    have hnat : (4290885227 : ℕ)^1079*10000000000000^823 ≤ 3297979857839^823*10000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4290885227 10000000000 3297979857839 10000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4929704181/10000000000 : ℝ)^1079 ≤ (395613045247/1000000000000 : ℝ)^823 := by
    have hnat : (4929704181 : ℕ)^1079*1000000000000^823 ≤ 395613045247^823*10000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4929704181 10000000000 395613045247 1000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3731292503/10000000000 : ℝ)^1079 ≤ (3432362110011/12500000000000 : ℝ)^823 := by
    have hnat : (3731292503 : ℕ)^1079*12500000000000^823 ≤ 3432362110011^823*10000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3731292503 10000000000 3432362110011 12500000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1079/256 : ℝ)) 1079 823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4290885227/10000000000 : ℝ), (4929704181/10000000000 : ℝ), (3731292503/10000000000 : ℝ)] ![(3297979857839/10000000000000 : ℝ), (395613045247/1000000000000 : ℝ), (3432362110011/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4290885227/10000000000 : ℝ)|^1079 ≤ (3297979857839/10000000000000 : ℝ)^823
        have hw : |(4290885227/10000000000 : ℝ)|=(4290885227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4929704181/10000000000 : ℝ)|^1079 ≤ (395613045247/1000000000000 : ℝ)^823
        have hw : |(4929704181/10000000000 : ℝ)|=(4929704181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3731292503/10000000000 : ℝ)|^1079 ≤ (3432362110011/12500000000000 : ℝ)^823
        have hw : |(3731292503/10000000000 : ℝ)|=(3731292503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1356_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77640267/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26771/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1519/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (7019/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (19357/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (26771/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1519/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (26771/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1519/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (26771/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1519/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (26771/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1519/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (26771/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1519/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (26771/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1519/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
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
  have hpowlo : (1519/100000 : ℝ) ^ (4315/1024 : ℝ) ≤ (543583141973/25000000000000000000 : ℝ) := by
    have hpowers : (1519/100000 : ℝ)^4315 ≤ (543583141973/25000000000000000000 : ℝ)^1024 := by
      have hnat : (1519 : ℕ)^4315*25000000000000000000^1024 ≤ 543583141973^1024*100000^4315 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1519 100000 543583141973 25000000000000000000 4315 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1519/100000 : ℝ)) (X := (543583141973/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4315 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (26771/100000 : ℝ) ^ (4315/1024 : ℝ) ≤ (19374237399957369/5000000000000000000 : ℝ) := by
    have hpowers : (26771/100000 : ℝ)^4315 ≤ (19374237399957369/5000000000000000000 : ℝ)^1024 := by
      have hnat : (26771 : ℕ)^4315*5000000000000000000^1024 ≤ 19374237399957369^1024*100000^4315 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26771 100000 19374237399957369 5000000000000000000 4315 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26771/100000 : ℝ)) (X := (19374237399957369/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4315 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500000543583141973/12500000000000000000 : ℝ) ≤ (156250001612483/156250000000000 : ℝ) ^ (4315/1024 : ℝ) := by
    have hpowers : (12500000543583141973/12500000000000000000 : ℝ)^1024 ≤ (156250001612483/156250000000000 : ℝ)^4315 := by
      have hnat : (12500000543583141973 : ℕ)^1024*156250000000000^4315 ≤ 156250001612483^4315*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500000543583141973 12500000000000000000 156250001612483 156250000000000 1024 4315 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156250001612483/156250000000000 : ℝ)) (X := (12500000543583141973/12500000000000000000 : ℝ)) (by norm_num) 4315 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12548435865291464409/12500000000000000000 : ℝ) ≤ (10009181961172671/10000000000000000 : ℝ) ^ (4315/1024 : ℝ) := by
    have hpowers : (12548435865291464409/12500000000000000000 : ℝ)^1024 ≤ (10009181961172671/10000000000000000 : ℝ)^4315 := by
      have hnat : (12548435865291464409 : ℕ)^1024*10000000000000000^4315 ≤ 10009181961172671^4315*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12548435865291464409 12500000000000000000 10009181961172671 10000000000000000 1024 4315 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10009181961172671/10000000000000000 : ℝ)) (X := (12548435865291464409/12500000000000000000 : ℝ)) (by norm_num) 4315 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2519374237399957369/2500000000000000000 : ℝ) ≤ (1001836381914643/1000000000000000 : ℝ) ^ (4315/1024 : ℝ) := by
    have hpowers : (2519374237399957369/2500000000000000000 : ℝ)^1024 ≤ (1001836381914643/1000000000000000 : ℝ)^4315 := by
      have hnat : (2519374237399957369 : ℕ)^1024*1000000000000000^4315 ≤ 1001836381914643^4315*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2519374237399957369 2500000000000000000 1001836381914643 1000000000000000 1024 4315 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1001836381914643/1000000000000000 : ℝ)) (X := (2519374237399957369/2500000000000000000 : ℝ)) (by norm_num) 4315 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(543583141973/25000000000000000000 : ℝ) ≤ ((126246054060727322991/126260000000000000000 : ℝ)+2*(9181857973759/2525200000000000 : ℝ)*(1519/100000 : ℝ))^(4315/1024 : ℝ) := by
    rw [show (126246054060727322991/126260000000000000000 : ℝ)+2*(9181857973759/2525200000000000 : ℝ)*(1519/100000 : ℝ)=(156250001612483/156250000000000 : ℝ) by norm_num, show 1+2*(543583141973/25000000000000000000 : ℝ)=(12500000543583141973/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(19374237399957369/5000000000000000000 : ℝ)+(543583141973/25000000000000000000 : ℝ) ≤ ((126246054060727322991/126260000000000000000 : ℝ)+(9181857973759/2525200000000000 : ℝ)*((26771/100000 : ℝ)+(1519/100000 : ℝ)))^(4315/1024 : ℝ) := by
    rw [show (126246054060727322991/126260000000000000000 : ℝ)+(9181857973759/2525200000000000 : ℝ)*((26771/100000 : ℝ)+(1519/100000 : ℝ))=(10009181961172671/10000000000000000 : ℝ) by norm_num, show 1+(19374237399957369/5000000000000000000 : ℝ)+(543583141973/25000000000000000000 : ℝ)=(12548435865291464409/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(19374237399957369/5000000000000000000 : ℝ) ≤ ((126246054060727322991/126260000000000000000 : ℝ)+2*(9181857973759/2525200000000000 : ℝ)*(26771/100000 : ℝ))^(4315/1024 : ℝ) := by
    rw [show (126246054060727322991/126260000000000000000 : ℝ)+2*(9181857973759/2525200000000000 : ℝ)*(26771/100000 : ℝ)=(1001836381914643/1000000000000000 : ℝ) by norm_num, show 1+2*(19374237399957369/5000000000000000000 : ℝ)=(2519374237399957369/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (126246054060727322991/126260000000000000000 : ℝ)*(X 1 0+X 2 0)+(9181857973759/2525200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4315/1024 : ℝ)) (lo := (1519/100000 : ℝ)) (hi := (26771/100000 : ℝ)) (c := (126246054060727322991/126260000000000000000 : ℝ)) (alpha := (9181857973759/2525200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (126246054060727322991/126260000000000000000 : ℝ)*(X 0 1+X 2 1)+(9181857973759/2525200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4315/1024 : ℝ)) (lo := (1519/100000 : ℝ)) (hi := (26771/100000 : ℝ)) (c := (126246054060727322991/126260000000000000000 : ℝ)) (alpha := (9181857973759/2525200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (126246054060727322991/126260000000000000000 : ℝ)*(X 0 2+X 1 2)+(9181857973759/2525200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4315/1024 : ℝ)) (lo := (1519/100000 : ℝ)) (hi := (26771/100000 : ℝ)) (c := (126246054060727322991/126260000000000000000 : ℝ)) (alpha := (9181857973759/2525200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1983693049/10000000000 : ℝ)*X 0 0+(563591401/1000000000 : ℝ)*X 0 1+(2526069197/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1356_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2702131359/5000000000 : ℝ)*X 1 0+(-1147419841/5000000000 : ℝ)*X 1 1+(2526069549/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1356_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5404262781/10000000000 : ℝ)*X 2 0+(5052138531/10000000000 : ℝ)*X 2 1+(-573710081/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1356_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2144903789/5000000000 : ℝ)*X 0 0+(464470159/1250000000 : ℝ)*X 0 1+(2472480991/5000000000 : ℝ)*X 0 2+(2144903789/5000000000 : ℝ)*X 1 0+(464470159/1250000000 : ℝ)*X 1 1+(2472480991/5000000000 : ℝ)*X 1 2+(2144903789/5000000000 : ℝ)*X 2 0+(464470159/1250000000 : ℝ)*X 2 1+(2472480991/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1356_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-496051147/2500000000 : ℝ)*X 0 0+(1011877047/2000000000 : ℝ)*X 0 1+(2814268381/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1356_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1050521023/2000000000 : ℝ)*X 1 0+(-429610457/2500000000 : ℝ)*X 1 1+(5628536821/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1356_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5252605009/10000000000 : ℝ)*X 2 0+(5628536901/10000000000 : ℝ)*X 2 1+(-1718441861/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1356_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4290885227/10000000000 : ℝ)*X 0 0+(4929704181/10000000000 : ℝ)*X 0 1+(3731292503/10000000000 : ℝ)*X 0 2+(4290885227/10000000000 : ℝ)*X 1 0+(4929704181/10000000000 : ℝ)*X 1 1+(3731292503/10000000000 : ℝ)*X 1 2+(4290885227/10000000000 : ℝ)*X 2 0+(4929704181/10000000000 : ℝ)*X 2 1+(3731292503/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1356_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1239237576770212229144022339/315650000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (62472517/100000000000000 : ℝ)*(base16) + (18676281/5000000000000 : ℝ)*(base19) + (12212889/2500000000000 : ℝ)*(base23) + (1758993/10000000000000 : ℝ)*(upper2) + (33339393/50000000000000 : ℝ)*(upper3) + (126326677834457/10000000000000 : ℝ)*(major0) + (126326677834457/10000000000000 : ℝ)*(major1) + (126326677834457/10000000000000 : ℝ)*(major2) + (1712991427413451/100000000000000 : ℝ)*(sp0) + (171299458561981/10000000000000 : ℝ)*(sp1) + (1712994533102387/100000000000000 : ℝ)*(sp2) + (81353745827529/10000000000000 : ℝ)*(sp3) + (224637781/6250000000000 : ℝ)*(sp4) + (945929689/100000000000000 : ℝ)*(sp7) + (813538404204979/100000000000000 : ℝ)*(f.failure) + (1712995021617947/100000000000000 : ℝ)*(f.sum) + (27116633442913/12626000000000000000000000000 : ℝ)*base66 + (4644363335507850887/1262600000000000000000000000000000 : ℝ)*base67 + (3167345811400549113/1262600000000000000000000000000000 : ℝ)*base70 + (7935289903013450887/1262600000000000000000000000000000 : ℝ)*base71 + (34021488467931/12626000000000000000000000000 : ℝ)*base74 + (3305358273251050887/1262600000000000000000000000000000 : ℝ)*base75 + (2353190524459250887/1262600000000000000000000000000000 : ℝ)*base77 + (5724633255577650887/1262600000000000000000000000000000 : ℝ)*base79 + (59576446686471/12626000000000000000000000000 : ℝ)*base82 + (7710607/5000000000000000000000 : ℝ)*base90 + (7710607/5000000000000000000000 : ℝ)*base92 + (7710607/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16145533730788724496887345799/6313000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5729367/20000000000000 : ℝ)*(base1) + (265753853/50000000000000 : ℝ)*(base19) + (7720747/1562500000000 : ℝ)*(base23) + (30860931/50000000000000 : ℝ)*(upper3) + (10479279/20000000000000 : ℝ)*(upper5) + (1295719523139521/100000000000000 : ℝ)*(major0) + (1295719523139521/100000000000000 : ℝ)*(major1) + (1295719523139521/100000000000000 : ℝ)*(major2) + (2860301119/100000000000000 : ℝ)*(sp1) + (2793702111/100000000000000 : ℝ)*(sp2) + (219625144571653/12500000000000 : ℝ)*(sp4) + (439249434029391/25000000000000 : ℝ)*(sp5) + (1756997840096469/100000000000000 : ℝ)*(sp6) + (834437804455621/100000000000000 : ℝ)*(sp7) + (166887566620491/20000000000000 : ℝ)*(f.failure) + (1757001127926389/100000000000000 : ℝ)*(f.sum) + (120703239706861/126260000000000000000000000000 : ℝ)*base66 + (133325264410070022689/12626000000000000000000000000000000 : ℝ)*base68 + (102940429382330022689/12626000000000000000000000000000000 : ℝ)*base70 + (61164306146798022689/12626000000000000000000000000000000 : ℝ)*base72 + (766159636661821/126260000000000000000000000000 : ℝ)*base74 + (61060164373598022689/12626000000000000000000000000000000 : ℝ)*base76 + (26037797020658022689/12626000000000000000000000000000000 : ℝ)*base78 + (1806458012690022689/12626000000000000000000000000000000 : ℝ)*base80 + (493376969623961/126260000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (1088903/1000000000000000000000 : ℝ)*base90 + (1088903/1000000000000000000000 : ℝ)*base92 + (1088903/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1356_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77640267/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26771/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1519/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (7019/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (19357/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1356_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1356_s2_0 (p : ℝ) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-31603861/156250000 : ℝ)*x 0 + (5475972339/10000000000 : ℝ)*x 1 + (648388481/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (31603861/156250000 : ℝ)^1079 ≤ (12303300621309/100000000000000 : ℝ)^823 := by
    have hnat : (31603861 : ℕ)^1079*100000000000000^823 ≤ 12303300621309^823*156250000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31603861 156250000 12303300621309 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5475972339/10000000000 : ℝ)^1079 ≤ (2837839141179/6250000000000 : ℝ)^823 := by
    have hnat : (5475972339 : ℕ)^1079*6250000000000^823 ≤ 2837839141179^823*10000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5475972339 10000000000 2837839141179 6250000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (648388481/1250000000 : ℝ)^1079 ≤ (21145636553023/50000000000000 : ℝ)^823 := by
    have hnat : (648388481 : ℕ)^1079*50000000000000^823 ≤ 21145636553023^823*1250000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      648388481 1250000000 21145636553023 50000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1079/256 : ℝ)) 1079 823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-31603861/156250000 : ℝ), (5475972339/10000000000 : ℝ), (648388481/1250000000 : ℝ)] ![(12303300621309/100000000000000 : ℝ), (2837839141179/6250000000000 : ℝ), (21145636553023/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-31603861/156250000 : ℝ)|^1079 ≤ (12303300621309/100000000000000 : ℝ)^823
        have hw : |(-31603861/156250000 : ℝ)|=(31603861/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5475972339/10000000000 : ℝ)|^1079 ≤ (2837839141179/6250000000000 : ℝ)^823
        have hw : |(5475972339/10000000000 : ℝ)|=(5475972339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(648388481/1250000000 : ℝ)|^1079 ≤ (21145636553023/50000000000000 : ℝ)^823
        have hw : |(648388481/1250000000 : ℝ)|=(648388481/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1356_s2_1 (p : ℝ) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5364974341/10000000000 : ℝ)*x 0 + (-1085896201/5000000000 : ℝ)*x 1 + (2593554109/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5364974341/10000000000 : ℝ)^1079 ≤ (44202592763007/100000000000000 : ℝ)^823 := by
    have hnat : (5364974341 : ℕ)^1079*100000000000000^823 ≤ 44202592763007^823*10000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5364974341 10000000000 44202592763007 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1085896201/5000000000 : ℝ)^1079 ≤ (1688266269331/12500000000000 : ℝ)^823 := by
    have hnat : (1085896201 : ℕ)^1079*12500000000000^823 ≤ 1688266269331^823*5000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085896201 5000000000 1688266269331 12500000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2593554109/5000000000 : ℝ)^1079 ≤ (42291277061067/100000000000000 : ℝ)^823 := by
    have hnat : (2593554109 : ℕ)^1079*100000000000000^823 ≤ 42291277061067^823*5000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2593554109 5000000000 42291277061067 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1079/256 : ℝ)) 1079 823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5364974341/10000000000 : ℝ), (-1085896201/5000000000 : ℝ), (2593554109/5000000000 : ℝ)] ![(44202592763007/100000000000000 : ℝ), (1688266269331/12500000000000 : ℝ), (42291277061067/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5364974341/10000000000 : ℝ)|^1079 ≤ (44202592763007/100000000000000 : ℝ)^823
        have hw : |(5364974341/10000000000 : ℝ)|=(5364974341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1085896201/5000000000 : ℝ)|^1079 ≤ (1688266269331/12500000000000 : ℝ)^823
        have hw : |(-1085896201/5000000000 : ℝ)|=(1085896201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2593554109/5000000000 : ℝ)|^1079 ≤ (42291277061067/100000000000000 : ℝ)^823
        have hw : |(2593554109/5000000000 : ℝ)|=(2593554109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1356_s2_2 (p : ℝ) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1072994881/2000000000 : ℝ)*x 0 + (2593554071/5000000000 : ℝ)*x 1 + (-2171792417/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072994881/2000000000 : ℝ)^1079 ≤ (44202593454331/100000000000000 : ℝ)^823 := by
    have hnat : (1072994881 : ℕ)^1079*100000000000000^823 ≤ 44202593454331^823*2000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072994881 2000000000 44202593454331 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2593554071/5000000000 : ℝ)^1079 ≤ (8458255249737/20000000000000 : ℝ)^823 := by
    have hnat : (2593554071 : ℕ)^1079*20000000000000^823 ≤ 8458255249737^823*5000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2593554071 5000000000 8458255249737 20000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2171792417/10000000000 : ℝ)^1079 ≤ (3376532569237/25000000000000 : ℝ)^823 := by
    have hnat : (2171792417 : ℕ)^1079*25000000000000^823 ≤ 3376532569237^823*10000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2171792417 10000000000 3376532569237 25000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1079/256 : ℝ)) 1079 823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1072994881/2000000000 : ℝ), (2593554071/5000000000 : ℝ), (-2171792417/10000000000 : ℝ)] ![(44202593454331/100000000000000 : ℝ), (8458255249737/20000000000000 : ℝ), (3376532569237/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1072994881/2000000000 : ℝ)|^1079 ≤ (44202593454331/100000000000000 : ℝ)^823
        have hw : |(1072994881/2000000000 : ℝ)|=(1072994881/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2593554071/5000000000 : ℝ)|^1079 ≤ (8458255249737/20000000000000 : ℝ)^823
        have hw : |(2593554071/5000000000 : ℝ)|=(2593554071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2171792417/10000000000 : ℝ)|^1079 ≤ (3376532569237/25000000000000 : ℝ)^823
        have hw : |(-2171792417/10000000000 : ℝ)|=(2171792417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1356_s2_3 (p : ℝ) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ)) (x : Fin 3 → ℝ) :
    (539636251/1250000000 : ℝ)*x 0 + (2011448459/5000000000 : ℝ)*x 1 + (463113229/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (539636251/1250000000 : ℝ)^1079 ≤ (6648821883861/20000000000000 : ℝ)^823 := by
    have hnat : (539636251 : ℕ)^1079*20000000000000^823 ≤ 6648821883861^823*1250000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539636251 1250000000 6648821883861 20000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2011448459/5000000000 : ℝ)^1079 ≤ (30305951205721/100000000000000 : ℝ)^823 := by
    have hnat : (2011448459 : ℕ)^1079*100000000000000^823 ≤ 30305951205721^823*5000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2011448459 5000000000 30305951205721 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (463113229/1000000000 : ℝ)^1079 ≤ (36449939357667/100000000000000 : ℝ)^823 := by
    have hnat : (463113229 : ℕ)^1079*100000000000000^823 ≤ 36449939357667^823*1000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      463113229 1000000000 36449939357667 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1079/256 : ℝ)) 1079 823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(539636251/1250000000 : ℝ), (2011448459/5000000000 : ℝ), (463113229/1000000000 : ℝ)] ![(6648821883861/20000000000000 : ℝ), (30305951205721/100000000000000 : ℝ), (36449939357667/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(539636251/1250000000 : ℝ)|^1079 ≤ (6648821883861/20000000000000 : ℝ)^823
        have hw : |(539636251/1250000000 : ℝ)|=(539636251/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2011448459/5000000000 : ℝ)|^1079 ≤ (30305951205721/100000000000000 : ℝ)^823
        have hw : |(2011448459/5000000000 : ℝ)|=(2011448459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(463113229/1000000000 : ℝ)|^1079 ≤ (36449939357667/100000000000000 : ℝ)^823
        have hw : |(463113229/1000000000 : ℝ)|=(463113229/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1356_s2_4 (p : ℝ) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2022709103/10000000000 : ℝ)*x 0 + (1297223037/2500000000 : ℝ)*x 1 + (2737086099/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2022709103/10000000000 : ℝ)^1079 ≤ (307594876427/2500000000000 : ℝ)^823 := by
    have hnat : (2022709103 : ℕ)^1079*2500000000000^823 ≤ 307594876427^823*10000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2022709103 10000000000 307594876427 2500000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1297223037/2500000000 : ℝ)^1079 ≤ (42310346948823/100000000000000 : ℝ)^823 := by
    have hnat : (1297223037 : ℕ)^1079*100000000000000^823 ≤ 42310346948823^823*2500000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1297223037 2500000000 42310346948823 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2737086099/5000000000 : ℝ)^1079 ≤ (45385857988609/100000000000000 : ℝ)^823 := by
    have hnat : (2737086099 : ℕ)^1079*100000000000000^823 ≤ 45385857988609^823*5000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2737086099 5000000000 45385857988609 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1079/256 : ℝ)) 1079 823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2022709103/10000000000 : ℝ), (1297223037/2500000000 : ℝ), (2737086099/5000000000 : ℝ)] ![(307594876427/2500000000000 : ℝ), (42310346948823/100000000000000 : ℝ), (45385857988609/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2022709103/10000000000 : ℝ)|^1079 ≤ (307594876427/2500000000000 : ℝ)^823
        have hw : |(-2022709103/10000000000 : ℝ)|=(2022709103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1297223037/2500000000 : ℝ)|^1079 ≤ (42310346948823/100000000000000 : ℝ)^823
        have hw : |(1297223037/2500000000 : ℝ)|=(1297223037/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2737086099/5000000000 : ℝ)|^1079 ≤ (45385857988609/100000000000000 : ℝ)^823
        have hw : |(2737086099/5000000000 : ℝ)|=(2737086099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1356_s2_5 (p : ℝ) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5290407583/10000000000 : ℝ)*x 0 + (-1884728131/10000000000 : ℝ)*x 1 + (5474172161/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5290407583/10000000000 : ℝ)^1079 ≤ (43398873955619/100000000000000 : ℝ)^823 := by
    have hnat : (5290407583 : ℕ)^1079*100000000000000^823 ≤ 43398873955619^823*10000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5290407583 10000000000 43398873955619 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1884728131/10000000000 : ℝ)^1079 ≤ (1401908555887/12500000000000 : ℝ)^823 := by
    have hnat : (1884728131 : ℕ)^1079*12500000000000^823 ≤ 1401908555887^823*10000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1884728131 10000000000 1401908555887 12500000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5474172161/10000000000 : ℝ)^1079 ≤ (5673232198303/12500000000000 : ℝ)^823 := by
    have hnat : (5474172161 : ℕ)^1079*12500000000000^823 ≤ 5673232198303^823*10000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5474172161 10000000000 5673232198303 12500000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1079/256 : ℝ)) 1079 823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5290407583/10000000000 : ℝ), (-1884728131/10000000000 : ℝ), (5474172161/10000000000 : ℝ)] ![(43398873955619/100000000000000 : ℝ), (1401908555887/12500000000000 : ℝ), (5673232198303/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5290407583/10000000000 : ℝ)|^1079 ≤ (43398873955619/100000000000000 : ℝ)^823
        have hw : |(5290407583/10000000000 : ℝ)|=(5290407583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1884728131/10000000000 : ℝ)|^1079 ≤ (1401908555887/12500000000000 : ℝ)^823
        have hw : |(-1884728131/10000000000 : ℝ)|=(1884728131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5474172161/10000000000 : ℝ)|^1079 ≤ (5673232198303/12500000000000 : ℝ)^823
        have hw : |(5474172161/10000000000 : ℝ)|=(5474172161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1356_s2_6 (p : ℝ) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ)) (x : Fin 3 → ℝ) :
    (132260189/250000000 : ℝ)*x 0 + (5474172203/10000000000 : ℝ)*x 1 + (-235591013/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132260189/250000000 : ℝ)^1079 ≤ (21699436854127/50000000000000 : ℝ)^823 := by
    have hnat : (132260189 : ℕ)^1079*50000000000000^823 ≤ 21699436854127^823*250000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132260189 250000000 21699436854127 50000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5474172203/10000000000 : ℝ)^1079 ≤ (22692929021479/50000000000000 : ℝ)^823 := by
    have hnat : (5474172203 : ℕ)^1079*50000000000000^823 ≤ 22692929021479^823*10000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5474172203 10000000000 22692929021479 50000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (235591013/1250000000 : ℝ)^1079 ≤ (11215268236453/100000000000000 : ℝ)^823 := by
    have hnat : (235591013 : ℕ)^1079*100000000000000^823 ≤ 11215268236453^823*1250000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      235591013 1250000000 11215268236453 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1079/256 : ℝ)) 1079 823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132260189/250000000 : ℝ), (5474172203/10000000000 : ℝ), (-235591013/1250000000 : ℝ)] ![(21699436854127/50000000000000 : ℝ), (22692929021479/50000000000000 : ℝ), (11215268236453/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132260189/250000000 : ℝ)|^1079 ≤ (21699436854127/50000000000000 : ℝ)^823
        have hw : |(132260189/250000000 : ℝ)|=(132260189/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5474172203/10000000000 : ℝ)|^1079 ≤ (22692929021479/50000000000000 : ℝ)^823
        have hw : |(5474172203/10000000000 : ℝ)|=(5474172203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-235591013/1250000000 : ℝ)|^1079 ≤ (11215268236453/100000000000000 : ℝ)^823
        have hw : |(-235591013/1250000000 : ℝ)|=(235591013/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1356_s2_7 (p : ℝ) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ)) (x : Fin 3 → ℝ) :
    (863444173/2000000000 : ℝ)*x 0 + (4627375841/10000000000 : ℝ)*x 1 + (402668673/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (863444173/2000000000 : ℝ)^1079 ≤ (33245430545233/100000000000000 : ℝ)^823 := by
    have hnat : (863444173 : ℕ)^1079*100000000000000^823 ≤ 33245430545233^823*2000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      863444173 2000000000 33245430545233 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4627375841/10000000000 : ℝ)^1079 ≤ (1456447280831/4000000000000 : ℝ)^823 := by
    have hnat : (4627375841 : ℕ)^1079*4000000000000^823 ≤ 1456447280831^823*10000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4627375841 10000000000 1456447280831 4000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (402668673/1000000000 : ℝ)^1079 ≤ (30343387418283/100000000000000 : ℝ)^823 := by
    have hnat : (402668673 : ℕ)^1079*100000000000000^823 ≤ 30343387418283^823*1000000000^1079 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      402668673 1000000000 30343387418283 100000000000000 1079 823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1079/256 : ℝ)) 1079 823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(863444173/2000000000 : ℝ), (4627375841/10000000000 : ℝ), (402668673/1000000000 : ℝ)] ![(33245430545233/100000000000000 : ℝ), (1456447280831/4000000000000 : ℝ), (30343387418283/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(863444173/2000000000 : ℝ)|^1079 ≤ (33245430545233/100000000000000 : ℝ)^823
        have hw : |(863444173/2000000000 : ℝ)|=(863444173/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4627375841/10000000000 : ℝ)|^1079 ≤ (1456447280831/4000000000000 : ℝ)^823
        have hw : |(4627375841/10000000000 : ℝ)|=(4627375841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(402668673/1000000000 : ℝ)|^1079 ≤ (30343387418283/100000000000000 : ℝ)^823
        have hw : |(402668673/1000000000 : ℝ)|=(402668673/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1356_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77640267/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19357/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7019/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (4971/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16049/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (19357/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (7019/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (19357/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (7019/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (19357/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (7019/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (19357/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (7019/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (19357/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (7019/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (19357/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (7019/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (7019/100000 : ℝ) ^ (4315/1024 : ℝ) ≤ (1375172251841061/100000000000000000000 : ℝ) := by
    have hpowers : (7019/100000 : ℝ)^4315 ≤ (1375172251841061/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7019 : ℕ)^4315*100000000000000000000^1024 ≤ 1375172251841061^1024*100000^4315 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7019 100000 1375172251841061 100000000000000000000 4315 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7019/100000 : ℝ)) (X := (1375172251841061/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4315 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (19357/100000 : ℝ) ^ (4315/1024 : ℝ) ≤ (49408340137599273/50000000000000000000 : ℝ) := by
    have hpowers : (19357/100000 : ℝ)^4315 ≤ (49408340137599273/50000000000000000000 : ℝ)^1024 := by
      have hnat : (19357 : ℕ)^4315*50000000000000000000^1024 ≤ 49408340137599273^1024*100000^4315 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19357 100000 49408340137599273 50000000000000000000 4315 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19357/100000 : ℝ)) (X := (49408340137599273/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4315 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001375172251841061/50000000000000000000 : ℝ) ≤ (10000065268209353/10000000000000000 : ℝ) ^ (4315/1024 : ℝ) := by
    have hpowers : (50001375172251841061/50000000000000000000 : ℝ)^1024 ≤ (10000065268209353/10000000000000000 : ℝ)^4315 := by
      have hnat : (50001375172251841061 : ℕ)^1024*10000000000000000^4315 ≤ 10000065268209353^4315*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001375172251841061 50000000000000000000 10000065268209353 10000000000000000 1024 4315 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000065268209353/10000000000000000 : ℝ)) (X := (50001375172251841061/50000000000000000000 : ℝ)) (by norm_num) 4315 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100100191852527039607/100000000000000000000 : ℝ) ≤ (10002376762002971/10000000000000000 : ℝ) ^ (4315/1024 : ℝ) := by
    have hpowers : (100100191852527039607/100000000000000000000 : ℝ)^1024 ≤ (10002376762002971/10000000000000000 : ℝ)^4315 := by
      have hnat : (100100191852527039607 : ℕ)^1024*10000000000000000^4315 ≤ 10002376762002971^4315*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100100191852527039607 100000000000000000000 10002376762002971 10000000000000000 1024 4315 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002376762002971/10000000000000000 : ℝ)) (X := (100100191852527039607/100000000000000000000 : ℝ)) (by norm_num) 4315 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25049408340137599273/25000000000000000000 : ℝ) ≤ (10004688255796589/10000000000000000 : ℝ) ^ (4315/1024 : ℝ) := by
    have hpowers : (25049408340137599273/25000000000000000000 : ℝ)^1024 ≤ (10004688255796589/10000000000000000 : ℝ)^4315 := by
      have hnat : (25049408340137599273 : ℕ)^1024*10000000000000000^4315 ≤ 10004688255796589^4315*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25049408340137599273 25000000000000000000 10004688255796589 10000000000000000 1024 4315 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004688255796589/10000000000000000 : ℝ)) (X := (25049408340137599273/25000000000000000000 : ℝ)) (by norm_num) 4315 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1375172251841061/100000000000000000000 : ℝ) ≤ ((12334835652929218783/12338000000000000000 : ℝ)+2*(1155746896809/616900000000000 : ℝ)*(7019/100000 : ℝ))^(4315/1024 : ℝ) := by
    rw [show (12334835652929218783/12338000000000000000 : ℝ)+2*(1155746896809/616900000000000 : ℝ)*(7019/100000 : ℝ)=(10000065268209353/10000000000000000 : ℝ) by norm_num, show 1+2*(1375172251841061/100000000000000000000 : ℝ)=(50001375172251841061/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(49408340137599273/50000000000000000000 : ℝ)+(1375172251841061/100000000000000000000 : ℝ) ≤ ((12334835652929218783/12338000000000000000 : ℝ)+(1155746896809/616900000000000 : ℝ)*((19357/100000 : ℝ)+(7019/100000 : ℝ)))^(4315/1024 : ℝ) := by
    rw [show (12334835652929218783/12338000000000000000 : ℝ)+(1155746896809/616900000000000 : ℝ)*((19357/100000 : ℝ)+(7019/100000 : ℝ))=(10002376762002971/10000000000000000 : ℝ) by norm_num, show 1+(49408340137599273/50000000000000000000 : ℝ)+(1375172251841061/100000000000000000000 : ℝ)=(100100191852527039607/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(49408340137599273/50000000000000000000 : ℝ) ≤ ((12334835652929218783/12338000000000000000 : ℝ)+2*(1155746896809/616900000000000 : ℝ)*(19357/100000 : ℝ))^(4315/1024 : ℝ) := by
    rw [show (12334835652929218783/12338000000000000000 : ℝ)+2*(1155746896809/616900000000000 : ℝ)*(19357/100000 : ℝ)=(10004688255796589/10000000000000000 : ℝ) by norm_num, show 1+2*(49408340137599273/50000000000000000000 : ℝ)=(25049408340137599273/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (12334835652929218783/12338000000000000000 : ℝ)*(X 1 0+X 2 0)+(1155746896809/616900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4315/1024 : ℝ)) (lo := (7019/100000 : ℝ)) (hi := (19357/100000 : ℝ)) (c := (12334835652929218783/12338000000000000000 : ℝ)) (alpha := (1155746896809/616900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (12334835652929218783/12338000000000000000 : ℝ)*(X 0 1+X 2 1)+(1155746896809/616900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4315/1024 : ℝ)) (lo := (7019/100000 : ℝ)) (hi := (19357/100000 : ℝ)) (c := (12334835652929218783/12338000000000000000 : ℝ)) (alpha := (1155746896809/616900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (12334835652929218783/12338000000000000000 : ℝ)*(X 0 2+X 1 2)+(1155746896809/616900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4315/1024 : ℝ)) (lo := (7019/100000 : ℝ)) (hi := (19357/100000 : ℝ)) (c := (12334835652929218783/12338000000000000000 : ℝ)) (alpha := (1155746896809/616900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-31603861/156250000 : ℝ)*X 0 0+(5475972339/10000000000 : ℝ)*X 0 1+(648388481/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1356_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5364974341/10000000000 : ℝ)*X 1 0+(-1085896201/5000000000 : ℝ)*X 1 1+(2593554109/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1356_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1072994881/2000000000 : ℝ)*X 2 0+(2593554071/5000000000 : ℝ)*X 2 1+(-2171792417/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1356_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((539636251/1250000000 : ℝ)*X 0 0+(2011448459/5000000000 : ℝ)*X 0 1+(463113229/1000000000 : ℝ)*X 0 2+(539636251/1250000000 : ℝ)*X 1 0+(2011448459/5000000000 : ℝ)*X 1 1+(463113229/1000000000 : ℝ)*X 1 2+(539636251/1250000000 : ℝ)*X 2 0+(2011448459/5000000000 : ℝ)*X 2 1+(463113229/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1356_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2022709103/10000000000 : ℝ)*X 0 0+(1297223037/2500000000 : ℝ)*X 0 1+(2737086099/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1356_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5290407583/10000000000 : ℝ)*X 1 0+(-1884728131/10000000000 : ℝ)*X 1 1+(5474172161/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1356_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((132260189/250000000 : ℝ)*X 2 0+(5474172203/10000000000 : ℝ)*X 2 1+(-235591013/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1356_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((863444173/2000000000 : ℝ)*X 0 0+(4627375841/10000000000 : ℝ)*X 0 1+(402668673/1000000000 : ℝ)*X 0 2+(863444173/2000000000 : ℝ)*X 1 0+(4627375841/10000000000 : ℝ)*X 1 1+(402668673/1000000000 : ℝ)*X 1 2+(863444173/2000000000 : ℝ)*X 2 0+(4627375841/10000000000 : ℝ)*X 2 1+(402668673/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1356_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2253594620627131546255596129/308450000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1226966731/100000000000000 : ℝ)*(base19) + (616466161/50000000000000 : ℝ)*(base23) + (2369429/12500000000000 : ℝ)*(lower2) + (166748113/100000000000000 : ℝ)*(upper3) + (134500129/100000000000000 : ℝ)*(upper5) + (1276496560292407/50000000000000 : ℝ)*(major0) + (1276496560292407/50000000000000 : ℝ)*(major1) + (1276496560292407/50000000000000 : ℝ)*(major2) + (86546252967447/2500000000000 : ℝ)*(sp0) + (346186811623127/10000000000000 : ℝ)*(sp1) + (1730934055132839/50000000000000 : ℝ)*(sp2) + (822054113376397/50000000000000 : ℝ)*(sp3) + (19224500121/100000000000000 : ℝ)*(sp4) + (8427679123/100000000000000 : ℝ)*(sp7) + (1644116654431917/100000000000000 : ℝ)*(f.failure) + (1730934671599/50000000000 : ℝ)*(f.sum) + (35036137548527/15422500000000000000000000000 : ℝ)*base66 + (3154497846472759319/616900000000000000000000000000000 : ℝ)*base68 + (11658715230449259319/616900000000000000000000000000000 : ℝ)*base70 + (8168956698265359319/616900000000000000000000000000000 : ℝ)*base72 + (98335162411751/30845000000000000000000000000 : ℝ)*base73 + (6779516587037059319/616900000000000000000000000000000 : ℝ)*base76 + (2646547182253359319/616900000000000000000000000000000 : ℝ)*base78 + (1598095573183959319/616900000000000000000000000000000 : ℝ)*base80 + (128924455137627/15422500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (69201839/5000000000000000000000 : ℝ)*base89 + (69201839/5000000000000000000000 : ℝ)*base91 + (69201839/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11900447286962772727119/6169000000000000000000000000 : ℝ) := by norm_num
    linear_combination (530242909/100000000000000 : ℝ)*(base19) + (303901527/50000000000000 : ℝ)*(base23) + (57541919/100000000000000 : ℝ)*(upper3) + (17072739/50000000000000 : ℝ)*(lower4) + (3487393/100000000000000 : ℝ)*(upper5) + (517008093280227/20000000000000 : ℝ)*(major0) + (517008093280227/20000000000000 : ℝ)*(major1) + (517008093280227/20000000000000 : ℝ)*(major2) + (2951732367/50000000000000 : ℝ)*(sp1) + (3954134791/50000000000000 : ℝ)*(sp2) + (350532586037943/10000000000000 : ℝ)*(sp4) + (876329856667947/25000000000000 : ℝ)*(sp5) + (1752658672153397/50000000000000 : ℝ)*(sp6) + (832377504060211/50000000000000 : ℝ)*(sp7) + (832377504060211/50000000000000 : ℝ)*(f.failure) + (350532586037943/10000000000000 : ℝ)*(f.sum) + (5421433573583/6169000000000000000000000000 : ℝ)*base65 + (1338621700779843741/246760000000000000000000000000000 : ℝ)*base67 + (1406814651451763741/246760000000000000000000000000000 : ℝ)*base69 + (34291971402483741/246760000000000000000000000000000 : ℝ)*base71 + (42055103212229/6169000000000000000000000000 : ℝ)*base73 + (1979026375550636259/246760000000000000000000000000000 : ℝ)*base76 + (116540733005036259/246760000000000000000000000000000 : ℝ)*base78 + (1453287116797516259/246760000000000000000000000000000 : ℝ)*base80 + (27111341153133/6169000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (8883663/2500000000000000000000 : ℝ)*base90 + (8883663/2500000000000000000000 : ℝ)*base92 + (8883663/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1356_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77640267/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19357/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7019/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4971/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16049/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1356_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1356_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77640267/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4971/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16049/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1356_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1356_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1356_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4315/1024 : ℝ) ≤ p) (hpb : p ≤ (1079/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77640267/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4971/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16049/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1356_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
