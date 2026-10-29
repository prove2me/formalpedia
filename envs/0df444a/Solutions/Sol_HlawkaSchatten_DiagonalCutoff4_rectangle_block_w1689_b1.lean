-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1689_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:38:51.743+00:00
-- url     : https://prove2.me/submissions/0eac17dc-8569-4c0e-8139-1b94e07deddd

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
theorem support_rectangle_w1689_s3_0 (p : ℝ) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-745858621/5000000000 : ℝ)*x 0 + (5483888073/10000000000 : ℝ)*x 1 + (5135115927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (745858621/5000000000 : ℝ)^5135 ≤ (1857342022843/20000000000000 : ℝ)^4111 := by
    have hnat : (745858621 : ℕ)^5135*20000000000000^4111 ≤ 1857342022843^4111*5000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      745858621 5000000000 1857342022843 20000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5483888073/10000000000 : ℝ)^5135 ≤ (4721703670417/10000000000000 : ℝ)^4111 := by
    have hnat : (5483888073 : ℕ)^5135*10000000000000^4111 ≤ 4721703670417^4111*10000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5483888073 10000000000 4721703670417 10000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5135115927/10000000000 : ℝ)^5135 ≤ (43496253161909/100000000000000 : ℝ)^4111 := by
    have hnat : (5135115927 : ℕ)^5135*100000000000000^4111 ≤ 43496253161909^4111*10000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5135115927 10000000000 43496253161909 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5135/1024 : ℝ)) 5135 4111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-745858621/5000000000 : ℝ), (5483888073/10000000000 : ℝ), (5135115927/10000000000 : ℝ)] ![(1857342022843/20000000000000 : ℝ), (4721703670417/10000000000000 : ℝ), (43496253161909/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-745858621/5000000000 : ℝ)|^5135 ≤ (1857342022843/20000000000000 : ℝ)^4111
        have hw : |(-745858621/5000000000 : ℝ)|=(745858621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5483888073/10000000000 : ℝ)|^5135 ≤ (4721703670417/10000000000000 : ℝ)^4111
        have hw : |(5483888073/10000000000 : ℝ)|=(5483888073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5135115927/10000000000 : ℝ)|^5135 ≤ (43496253161909/100000000000000 : ℝ)^4111
        have hw : |(5135115927/10000000000 : ℝ)|=(5135115927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1689_s3_1 (p : ℝ) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350553299/10000000000 : ℝ)*x 0 + (-167290109/1000000000 : ℝ)*x 1 + (2567557973/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350553299/10000000000 : ℝ)^5135 ≤ (45787414359919/100000000000000 : ℝ)^4111 := by
    have hnat : (5350553299 : ℕ)^5135*100000000000000^4111 ≤ 45787414359919^4111*10000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350553299 10000000000 45787414359919 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (167290109/1000000000 : ℝ)^5135 ≤ (10716332257587/100000000000000 : ℝ)^4111 := by
    have hnat : (167290109 : ℕ)^5135*100000000000000^4111 ≤ 10716332257587^4111*1000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167290109 1000000000 10716332257587 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2567557973/5000000000 : ℝ)^5135 ≤ (43496253362933/100000000000000 : ℝ)^4111 := by
    have hnat : (2567557973 : ℕ)^5135*100000000000000^4111 ≤ 43496253362933^4111*5000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2567557973 5000000000 43496253362933 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5135/1024 : ℝ)) 5135 4111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350553299/10000000000 : ℝ), (-167290109/1000000000 : ℝ), (2567557973/5000000000 : ℝ)] ![(45787414359919/100000000000000 : ℝ), (10716332257587/100000000000000 : ℝ), (43496253362933/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350553299/10000000000 : ℝ)|^5135 ≤ (45787414359919/100000000000000 : ℝ)^4111
        have hw : |(5350553299/10000000000 : ℝ)|=(5350553299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-167290109/1000000000 : ℝ)|^5135 ≤ (10716332257587/100000000000000 : ℝ)^4111
        have hw : |(-167290109/1000000000 : ℝ)|=(167290109/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2567557973/5000000000 : ℝ)|^5135 ≤ (43496253362933/100000000000000 : ℝ)^4111
        have hw : |(2567557973/5000000000 : ℝ)|=(2567557973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1689_s3_2 (p : ℝ) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675276607/5000000000 : ℝ)*x 0 + (5135115903/10000000000 : ℝ)*x 1 + (-836450631/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675276607/5000000000 : ℝ)^5135 ≤ (45787413451347/100000000000000 : ℝ)^4111 := by
    have hnat : (2675276607 : ℕ)^5135*100000000000000^4111 ≤ 45787413451347^4111*5000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675276607 5000000000 45787413451347 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5135115903/10000000000 : ℝ)^5135 ≤ (2718515806749/6250000000000 : ℝ)^4111 := by
    have hnat : (5135115903 : ℕ)^5135*6250000000000^4111 ≤ 2718515806749^4111*10000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5135115903 10000000000 2718515806749 6250000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (836450631/5000000000 : ℝ)^5135 ≤ (10716333633837/100000000000000 : ℝ)^4111 := by
    have hnat : (836450631 : ℕ)^5135*100000000000000^4111 ≤ 10716333633837^4111*5000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      836450631 5000000000 10716333633837 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5135/1024 : ℝ)) 5135 4111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675276607/5000000000 : ℝ), (5135115903/10000000000 : ℝ), (-836450631/5000000000 : ℝ)] ![(45787413451347/100000000000000 : ℝ), (2718515806749/6250000000000 : ℝ), (10716333633837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675276607/5000000000 : ℝ)|^5135 ≤ (45787413451347/100000000000000 : ℝ)^4111
        have hw : |(2675276607/5000000000 : ℝ)|=(2675276607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5135115903/10000000000 : ℝ)|^5135 ≤ (2718515806749/6250000000000 : ℝ)^4111
        have hw : |(5135115903/10000000000 : ℝ)|=(5135115903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-836450631/5000000000 : ℝ)|^5135 ≤ (10716333633837/100000000000000 : ℝ)^4111
        have hw : |(-836450631/5000000000 : ℝ)|=(836450631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1689_s3_3 (p : ℝ) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1033153737/2500000000 : ℝ)*x 0 + (3669945419/10000000000 : ℝ)*x 1 + (4632817961/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1033153737/2500000000 : ℝ)^5135 ≤ (6632255491657/20000000000000 : ℝ)^4111 := by
    have hnat : (1033153737 : ℕ)^5135*20000000000000^4111 ≤ 6632255491657^4111*2500000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033153737 2500000000 6632255491657 20000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3669945419/10000000000 : ℝ)^5135 ≤ (28590491301519/100000000000000 : ℝ)^4111 := by
    have hnat : (3669945419 : ℕ)^5135*100000000000000^4111 ≤ 28590491301519^4111*10000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3669945419 10000000000 28590491301519 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4632817961/10000000000 : ℝ)^5135 ≤ (38248231221483/100000000000000 : ℝ)^4111 := by
    have hnat : (4632817961 : ℕ)^5135*100000000000000^4111 ≤ 38248231221483^4111*10000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4632817961 10000000000 38248231221483 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5135/1024 : ℝ)) 5135 4111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1033153737/2500000000 : ℝ), (3669945419/10000000000 : ℝ), (4632817961/10000000000 : ℝ)] ![(6632255491657/20000000000000 : ℝ), (28590491301519/100000000000000 : ℝ), (38248231221483/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1033153737/2500000000 : ℝ)|^5135 ≤ (6632255491657/20000000000000 : ℝ)^4111
        have hw : |(1033153737/2500000000 : ℝ)|=(1033153737/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3669945419/10000000000 : ℝ)|^5135 ≤ (28590491301519/100000000000000 : ℝ)^4111
        have hw : |(3669945419/10000000000 : ℝ)|=(3669945419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4632817961/10000000000 : ℝ)|^5135 ≤ (38248231221483/100000000000000 : ℝ)^4111
        have hw : |(4632817961/10000000000 : ℝ)|=(4632817961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1689_s3_4 (p : ℝ) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-74593989/500000000 : ℝ)*x 0 + (5138908323/10000000000 : ℝ)*x 1 + (5480039043/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (74593989/500000000 : ℝ)^5135 ≤ (4643987031033/50000000000000 : ℝ)^4111 := by
    have hnat : (74593989 : ℕ)^5135*50000000000000^4111 ≤ 4643987031033^4111*500000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      74593989 500000000 4643987031033 50000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5138908323/10000000000 : ℝ)^5135 ≤ (43536381223633/100000000000000 : ℝ)^4111 := by
    have hnat : (5138908323 : ℕ)^5135*100000000000000^4111 ≤ 43536381223633^4111*10000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5138908323 10000000000 43536381223633 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5480039043/10000000000 : ℝ)^5135 ≤ (47175644701383/100000000000000 : ℝ)^4111 := by
    have hnat : (5480039043 : ℕ)^5135*100000000000000^4111 ≤ 47175644701383^4111*10000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5480039043 10000000000 47175644701383 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5135/1024 : ℝ)) 5135 4111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-74593989/500000000 : ℝ), (5138908323/10000000000 : ℝ), (5480039043/10000000000 : ℝ)] ![(4643987031033/50000000000000 : ℝ), (43536381223633/100000000000000 : ℝ), (47175644701383/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-74593989/500000000 : ℝ)|^5135 ≤ (4643987031033/50000000000000 : ℝ)^4111
        have hw : |(-74593989/500000000 : ℝ)|=(74593989/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5138908323/10000000000 : ℝ)|^5135 ≤ (43536381223633/100000000000000 : ℝ)^4111
        have hw : |(5138908323/10000000000 : ℝ)|=(5138908323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5480039043/10000000000 : ℝ)|^5135 ≤ (47175644701383/100000000000000 : ℝ)^4111
        have hw : |(5480039043/10000000000 : ℝ)|=(5480039043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1689_s3_5 (p : ℝ) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2628659989/5000000000 : ℝ)*x 0 + (-1327977977/10000000000 : ℝ)*x 1 + (5480039041/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628659989/5000000000 : ℝ)^5135 ≤ (44793008032409/100000000000000 : ℝ)^4111 := by
    have hnat : (2628659989 : ℕ)^5135*100000000000000^4111 ≤ 44793008032409^4111*5000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628659989 5000000000 44793008032409 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1327977977/10000000000 : ℝ)^5135 ≤ (25097960209/312500000000 : ℝ)^4111 := by
    have hnat : (1327977977 : ℕ)^5135*312500000000^4111 ≤ 25097960209^4111*10000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327977977 10000000000 25097960209 312500000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5480039041/10000000000 : ℝ)^5135 ≤ (23587822339939/50000000000000 : ℝ)^4111 := by
    have hnat : (5480039041 : ℕ)^5135*50000000000000^4111 ≤ 23587822339939^4111*10000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5480039041 10000000000 23587822339939 50000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5135/1024 : ℝ)) 5135 4111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628659989/5000000000 : ℝ), (-1327977977/10000000000 : ℝ), (5480039041/10000000000 : ℝ)] ![(44793008032409/100000000000000 : ℝ), (25097960209/312500000000 : ℝ), (23587822339939/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628659989/5000000000 : ℝ)|^5135 ≤ (44793008032409/100000000000000 : ℝ)^4111
        have hw : |(2628659989/5000000000 : ℝ)|=(2628659989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1327977977/10000000000 : ℝ)|^5135 ≤ (25097960209/312500000000 : ℝ)^4111
        have hw : |(-1327977977/10000000000 : ℝ)|=(1327977977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5480039041/10000000000 : ℝ)|^5135 ≤ (23587822339939/50000000000000 : ℝ)^4111
        have hw : |(5480039041/10000000000 : ℝ)|=(5480039041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1689_s3_6 (p : ℝ) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (262865999/500000000 : ℝ)*x 0 + (5480039041/10000000000 : ℝ)*x 1 + (-53119119/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (262865999/500000000 : ℝ)^5135 ≤ (22396504026847/50000000000000 : ℝ)^4111 := by
    have hnat : (262865999 : ℕ)^5135*50000000000000^4111 ≤ 22396504026847^4111*500000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262865999 500000000 22396504026847 50000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5480039041/10000000000 : ℝ)^5135 ≤ (23587822339939/50000000000000 : ℝ)^4111 := by
    have hnat : (5480039041 : ℕ)^5135*50000000000000^4111 ≤ 23587822339939^4111*10000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5480039041 10000000000 23587822339939 50000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (53119119/400000000 : ℝ)^5135 ≤ (2007836812943/25000000000000 : ℝ)^4111 := by
    have hnat : (53119119 : ℕ)^5135*25000000000000^4111 ≤ 2007836812943^4111*400000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53119119 400000000 2007836812943 25000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5135/1024 : ℝ)) 5135 4111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(262865999/500000000 : ℝ), (5480039041/10000000000 : ℝ), (-53119119/400000000 : ℝ)] ![(22396504026847/50000000000000 : ℝ), (23587822339939/50000000000000 : ℝ), (2007836812943/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(262865999/500000000 : ℝ)|^5135 ≤ (22396504026847/50000000000000 : ℝ)^4111
        have hw : |(262865999/500000000 : ℝ)|=(262865999/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5480039041/10000000000 : ℝ)|^5135 ≤ (23587822339939/50000000000000 : ℝ)^4111
        have hw : |(5480039041/10000000000 : ℝ)|=(5480039041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-53119119/400000000 : ℝ)|^5135 ≤ (2007836812943/25000000000000 : ℝ)^4111
        have hw : |(-53119119/400000000 : ℝ)|=(53119119/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1689_s3_7 (p : ℝ) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4133063577/10000000000 : ℝ)*x 0 + (577793501/1250000000 : ℝ)*x 1 + (1840285957/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4133063577/10000000000 : ℝ)^5135 ≤ (8291443535901/25000000000000 : ℝ)^4111 := by
    have hnat : (4133063577 : ℕ)^5135*25000000000000^4111 ≤ 8291443535901^4111*10000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4133063577 10000000000 8291443535901 25000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (577793501/1250000000 : ℝ)^5135 ≤ (9535072862189/25000000000000 : ℝ)^4111 := by
    have hnat : (577793501 : ℕ)^5135*25000000000000^4111 ≤ 9535072862189^4111*1250000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      577793501 1250000000 9535072862189 25000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1840285957/5000000000 : ℝ)^5135 ≤ (14346967197689/50000000000000 : ℝ)^4111 := by
    have hnat : (1840285957 : ℕ)^5135*50000000000000^4111 ≤ 14346967197689^4111*5000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1840285957 5000000000 14346967197689 50000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5135/1024 : ℝ)) 5135 4111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4133063577/10000000000 : ℝ), (577793501/1250000000 : ℝ), (1840285957/5000000000 : ℝ)] ![(8291443535901/25000000000000 : ℝ), (9535072862189/25000000000000 : ℝ), (14346967197689/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4133063577/10000000000 : ℝ)|^5135 ≤ (8291443535901/25000000000000 : ℝ)^4111
        have hw : |(4133063577/10000000000 : ℝ)|=(4133063577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(577793501/1250000000 : ℝ)|^5135 ≤ (9535072862189/25000000000000 : ℝ)^4111
        have hw : |(577793501/1250000000 : ℝ)|=(577793501/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1840285957/5000000000 : ℝ)|^5135 ≤ (14346967197689/50000000000000 : ℝ)^4111
        have hw : |(1840285957/5000000000 : ℝ)|=(1840285957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1689_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (94018711/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8633/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9801/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (491/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17243/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8633/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9801/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8633/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9801/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8633/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9801/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8633/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9801/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8633/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9801/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8633/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9801/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9801/100000 : ℝ) ^ (5127/1024 : ℝ) ≤ (890135933851007/100000000000000000000 : ℝ) := by
    have hpowers : (9801/100000 : ℝ)^5127 ≤ (890135933851007/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9801 : ℕ)^5127*100000000000000000000^1024 ≤ 890135933851007^1024*100000^5127 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9801 100000 890135933851007 100000000000000000000 5127 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9801/100000 : ℝ)) (X := (890135933851007/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5127 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8633/50000 : ℝ) ^ (5127/1024 : ℝ) ≤ (15161569926259289/100000000000000000000 : ℝ) := by
    have hpowers : (8633/50000 : ℝ)^5127 ≤ (15161569926259289/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8633 : ℕ)^5127*100000000000000000000^1024 ≤ 15161569926259289^1024*50000^5127 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8633 50000 15161569926259289 100000000000000000000 5127 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8633/50000 : ℝ)) (X := (15161569926259289/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5127 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000890135933851007/50000000000000000000 : ℝ) ≤ (5000017778285611/5000000000000000 : ℝ) ^ (5127/1024 : ℝ) := by
    have hpowers : (50000890135933851007/50000000000000000000 : ℝ)^1024 ≤ (5000017778285611/5000000000000000 : ℝ)^5127 := by
      have hnat : (50000890135933851007 : ℕ)^1024*5000000000000000^5127 ≤ 5000017778285611^5127*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000890135933851007 50000000000000000000 5000017778285611 5000000000000000 1024 5127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000017778285611/5000000000000000 : ℝ)) (X := (50000890135933851007/50000000000000000000 : ℝ)) (by norm_num) 5127 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12502006463232513787/12500000000000000000 : ℝ) ≤ (2500080143803287/2500000000000000 : ℝ) ^ (5127/1024 : ℝ) := by
    have hpowers : (12502006463232513787/12500000000000000000 : ℝ)^1024 ≤ (2500080143803287/2500000000000000 : ℝ)^5127 := by
      have hnat : (12502006463232513787 : ℕ)^1024*2500000000000000^5127 ≤ 2500080143803287^5127*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502006463232513787 12500000000000000000 2500080143803287 2500000000000000 1024 5127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500080143803287/2500000000000000 : ℝ)) (X := (12502006463232513787/12500000000000000000 : ℝ)) (by norm_num) 5127 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50015161569926259289/50000000000000000000 : ℝ) ≤ (5000302796927537/5000000000000000 : ℝ) ^ (5127/1024 : ℝ) := by
    have hpowers : (50015161569926259289/50000000000000000000 : ℝ)^1024 ≤ (5000302796927537/5000000000000000 : ℝ)^5127 := by
      have hnat : (50015161569926259289 : ℕ)^1024*5000000000000000^5127 ≤ 5000302796927537^5127*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015161569926259289 50000000000000000000 5000302796927537 5000000000000000 1024 5127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000302796927537/5000000000000000 : ℝ)) (X := (50015161569926259289/50000000000000000000 : ℝ)) (by norm_num) 5127 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(890135933851007/100000000000000000000 : ℝ) ≤ ((37322339247192569389/37325000000000000000 : ℝ)+2*(142509320963/373250000000000 : ℝ)*(9801/100000 : ℝ))^(5127/1024 : ℝ) := by
    rw [show (37322339247192569389/37325000000000000000 : ℝ)+2*(142509320963/373250000000000 : ℝ)*(9801/100000 : ℝ)=(5000017778285611/5000000000000000 : ℝ) by norm_num, show 1+2*(890135933851007/100000000000000000000 : ℝ)=(50000890135933851007/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15161569926259289/100000000000000000000 : ℝ)+(890135933851007/100000000000000000000 : ℝ) ≤ ((37322339247192569389/37325000000000000000 : ℝ)+(142509320963/373250000000000 : ℝ)*((8633/50000 : ℝ)+(9801/100000 : ℝ)))^(5127/1024 : ℝ) := by
    rw [show (37322339247192569389/37325000000000000000 : ℝ)+(142509320963/373250000000000 : ℝ)*((8633/50000 : ℝ)+(9801/100000 : ℝ))=(2500080143803287/2500000000000000 : ℝ) by norm_num, show 1+(15161569926259289/100000000000000000000 : ℝ)+(890135933851007/100000000000000000000 : ℝ)=(12502006463232513787/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15161569926259289/100000000000000000000 : ℝ) ≤ ((37322339247192569389/37325000000000000000 : ℝ)+2*(142509320963/373250000000000 : ℝ)*(8633/50000 : ℝ))^(5127/1024 : ℝ) := by
    rw [show (37322339247192569389/37325000000000000000 : ℝ)+2*(142509320963/373250000000000 : ℝ)*(8633/50000 : ℝ)=(5000302796927537/5000000000000000 : ℝ) by norm_num, show 1+2*(15161569926259289/100000000000000000000 : ℝ)=(50015161569926259289/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (37322339247192569389/37325000000000000000 : ℝ)*(X 1 0+X 2 0)+(142509320963/373250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5127/1024 : ℝ)) (lo := (9801/100000 : ℝ)) (hi := (8633/50000 : ℝ)) (c := (37322339247192569389/37325000000000000000 : ℝ)) (alpha := (142509320963/373250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (37322339247192569389/37325000000000000000 : ℝ)*(X 0 1+X 2 1)+(142509320963/373250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5127/1024 : ℝ)) (lo := (9801/100000 : ℝ)) (hi := (8633/50000 : ℝ)) (c := (37322339247192569389/37325000000000000000 : ℝ)) (alpha := (142509320963/373250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (37322339247192569389/37325000000000000000 : ℝ)*(X 0 2+X 1 2)+(142509320963/373250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5127/1024 : ℝ)) (lo := (9801/100000 : ℝ)) (hi := (8633/50000 : ℝ)) (c := (37322339247192569389/37325000000000000000 : ℝ)) (alpha := (142509320963/373250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-745858621/5000000000 : ℝ)*X 0 0+(5483888073/10000000000 : ℝ)*X 0 1+(5135115927/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1689_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350553299/10000000000 : ℝ)*X 1 0+(-167290109/1000000000 : ℝ)*X 1 1+(2567557973/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1689_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675276607/5000000000 : ℝ)*X 2 0+(5135115903/10000000000 : ℝ)*X 2 1+(-836450631/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1689_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1033153737/2500000000 : ℝ)*X 0 0+(3669945419/10000000000 : ℝ)*X 0 1+(4632817961/10000000000 : ℝ)*X 0 2+(1033153737/2500000000 : ℝ)*X 1 0+(3669945419/10000000000 : ℝ)*X 1 1+(4632817961/10000000000 : ℝ)*X 1 2+(1033153737/2500000000 : ℝ)*X 2 0+(3669945419/10000000000 : ℝ)*X 2 1+(4632817961/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1689_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-74593989/500000000 : ℝ)*X 0 0+(5138908323/10000000000 : ℝ)*X 0 1+(5480039043/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1689_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2628659989/5000000000 : ℝ)*X 1 0+(-1327977977/10000000000 : ℝ)*X 1 1+(5480039041/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1689_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((262865999/500000000 : ℝ)*X 2 0+(5480039041/10000000000 : ℝ)*X 2 1+(-53119119/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1689_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4133063577/10000000000 : ℝ)*X 0 0+(577793501/1250000000 : ℝ)*X 0 1+(1840285957/5000000000 : ℝ)*X 0 2+(4133063577/10000000000 : ℝ)*X 1 0+(577793501/1250000000 : ℝ)*X 1 1+(1840285957/5000000000 : ℝ)*X 1 2+(4133063577/10000000000 : ℝ)*X 2 0+(577793501/1250000000 : ℝ)*X 2 1+(1840285957/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1689_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4939463954915153762829760251/373250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2016730561/100000000000000 : ℝ)*(base19) + (1826186273/100000000000000 : ℝ)*(base23) + (77580227/100000000000000 : ℝ)*(lower2) + (398299937/100000000000000 : ℝ)*(upper3) + (36481679/20000000000000 : ℝ)*(upper5) + (390581180132253/20000000000000 : ℝ)*(major0) + (390581180132253/20000000000000 : ℝ)*(major1) + (390581180132253/20000000000000 : ℝ)*(major2) + (716805325537561/25000000000000 : ℝ)*(sp0) + (1433618170173253/50000000000000 : ℝ)*(sp1) + (1433618265445397/50000000000000 : ℝ)*(sp2) + (1038565246018657/100000000000000 : ℝ)*(sp3) + (2131865853/12500000000000 : ℝ)*(sp4) + (7757104767/100000000000000 : ℝ)*(sp7) + (32455406347607/3125000000000 : ℝ)*(f.failure) + (716809589269267/25000000000000 : ℝ)*(f.sum) + (19147952491277/7465000000000000000000000000 : ℝ)*base66 + (3829044334046196583/746500000000000000000000000000000 : ℝ)*base68 + (3358454953264196583/746500000000000000000000000000000 : ℝ)*base70 + (2274941297975196583/746500000000000000000000000000000 : ℝ)*base72 + (10630493882457/7465000000000000000000000000 : ℝ)*base74 + (1706195938568196583/746500000000000000000000000000000 : ℝ)*base76 + (2474076245701803417/746500000000000000000000000000000 : ℝ)*base77 + (3120496656016803417/746500000000000000000000000000000 : ℝ)*base79 + (18314110199677/7465000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (1512077/156250000000000000000 : ℝ)*base89 + (1512077/156250000000000000000 : ℝ)*base91 + (1512077/156250000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (500922892521780046517073/37325000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1907120681/100000000000000 : ℝ)*(base19) + (2061222503/100000000000000 : ℝ)*(base23) + (575184803/100000000000000 : ℝ)*(lower1) + (143120007/50000000000000 : ℝ)*(upper3) + (34176103/50000000000000 : ℝ)*(lower4) + (279761023/100000000000000 : ℝ)*(upper5) + (124788358255549/6250000000000 : ℝ)*(major0) + (124788358255549/6250000000000 : ℝ)*(major1) + (124788358255549/6250000000000 : ℝ)*(major2) + (1295436393/100000000000000 : ℝ)*(sp2) + (732852448508451/25000000000000 : ℝ)*(sp4) + (1465703943456561/50000000000000 : ℝ)*(sp5) + (732851609343727/25000000000000 : ℝ)*(sp6) + (530908611395657/50000000000000 : ℝ)*(sp7) + (530908611395657/50000000000000 : ℝ)*(f.failure) + (732852448508451/25000000000000 : ℝ)*(f.sum) + (112679698659067/18662500000000000000000000000 : ℝ)*base65 + (856623937424864561/233281250000000000000000000000000 : ℝ)*base67 + (250998088583260439/233281250000000000000000000000000 : ℝ)*base70 + (4306277819148302061/233281250000000000000000000000000 : ℝ)*base71 + (64194500144317/18662500000000000000000000000 : ℝ)*base73 + (6585374016706697939/233281250000000000000000000000000 : ℝ)*base76 + (191936624520489561/233281250000000000000000000000000 : ℝ)*base77 + (1311513092199354189/233281250000000000000000000000000 : ℝ)*base80 + (117208497432133/18662500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (17861873/2500000000000000000000 : ℝ)*base90 + (17861873/2500000000000000000000 : ℝ)*base92 + (17861873/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1689_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (94018711/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8633/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9801/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (491/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17243/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1689_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1689_s4_0 (p : ℝ) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1491731733/10000000000 : ℝ)*x 0 + (5483836079/10000000000 : ℝ)*x 1 + (5135158129/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1491731733/10000000000 : ℝ)^5135 ≤ (9286822799507/100000000000000 : ℝ)^4111 := by
    have hnat : (1491731733 : ℕ)^5135*100000000000000^4111 ≤ 9286822799507^4111*10000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1491731733 10000000000 9286822799507 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5483836079/10000000000 : ℝ)^5135 ≤ (47216477518757/100000000000000 : ℝ)^4111 := by
    have hnat : (5483836079 : ℕ)^5135*100000000000000^4111 ≤ 47216477518757^4111*10000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5483836079 10000000000 47216477518757 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5135158129/10000000000 : ℝ)^5135 ≤ (1739867986747/4000000000000 : ℝ)^4111 := by
    have hnat : (5135158129 : ℕ)^5135*4000000000000^4111 ≤ 1739867986747^4111*10000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5135158129 10000000000 1739867986747 4000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5135/1024 : ℝ)) 5135 4111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1491731733/10000000000 : ℝ), (5483836079/10000000000 : ℝ), (5135158129/10000000000 : ℝ)] ![(9286822799507/100000000000000 : ℝ), (47216477518757/100000000000000 : ℝ), (1739867986747/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1491731733/10000000000 : ℝ)|^5135 ≤ (9286822799507/100000000000000 : ℝ)^4111
        have hw : |(-1491731733/10000000000 : ℝ)|=(1491731733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5483836079/10000000000 : ℝ)|^5135 ≤ (47216477518757/100000000000000 : ℝ)^4111
        have hw : |(5483836079/10000000000 : ℝ)|=(5483836079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5135158129/10000000000 : ℝ)|^5135 ≤ (1739867986747/4000000000000 : ℝ)^4111
        have hw : |(5135158129/10000000000 : ℝ)|=(5135158129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1689_s4_1 (p : ℝ) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350539167/10000000000 : ℝ)*x 0 + (-836432159/5000000000 : ℝ)*x 1 + (5135158033/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350539167/10000000000 : ℝ)^5135 ≤ (22893631650933/50000000000000 : ℝ)^4111 := by
    have hnat : (5350539167 : ℕ)^5135*50000000000000^4111 ≤ 22893631650933^4111*10000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350539167 10000000000 22893631650933 50000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (836432159/5000000000 : ℝ)^5135 ≤ (214320760579/2000000000000 : ℝ)^4111 := by
    have hnat : (836432159 : ℕ)^5135*2000000000000^4111 ≤ 214320760579^4111*5000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      836432159 5000000000 214320760579 2000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5135158033/10000000000 : ℝ)^5135 ≤ (10874174663243/25000000000000 : ℝ)^4111 := by
    have hnat : (5135158033 : ℕ)^5135*25000000000000^4111 ≤ 10874174663243^4111*10000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5135158033 10000000000 10874174663243 25000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5135/1024 : ℝ)) 5135 4111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350539167/10000000000 : ℝ), (-836432159/5000000000 : ℝ), (5135158033/10000000000 : ℝ)] ![(22893631650933/50000000000000 : ℝ), (214320760579/2000000000000 : ℝ), (10874174663243/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350539167/10000000000 : ℝ)|^5135 ≤ (22893631650933/50000000000000 : ℝ)^4111
        have hw : |(5350539167/10000000000 : ℝ)|=(5350539167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-836432159/5000000000 : ℝ)|^5135 ≤ (214320760579/2000000000000 : ℝ)^4111
        have hw : |(-836432159/5000000000 : ℝ)|=(836432159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5135158033/10000000000 : ℝ)|^5135 ≤ (10874174663243/25000000000000 : ℝ)^4111
        have hw : |(5135158033/10000000000 : ℝ)|=(5135158033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1689_s4_2 (p : ℝ) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070107809/2000000000 : ℝ)*x 0 + (2567578943/5000000000 : ℝ)*x 1 + (-418216169/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070107809/2000000000 : ℝ)^5135 ≤ (45787261997799/100000000000000 : ℝ)^4111 := by
    have hnat : (1070107809 : ℕ)^5135*100000000000000^4111 ≤ 45787261997799^4111*2000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070107809 2000000000 45787261997799 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2567578943/5000000000 : ℝ)^5135 ≤ (43496697097677/100000000000000 : ℝ)^4111 := by
    have hnat : (2567578943 : ℕ)^5135*100000000000000^4111 ≤ 43496697097677^4111*5000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2567578943 5000000000 43496697097677 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (418216169/2500000000 : ℝ)^5135 ≤ (2143208178691/20000000000000 : ℝ)^4111 := by
    have hnat : (418216169 : ℕ)^5135*20000000000000^4111 ≤ 2143208178691^4111*2500000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      418216169 2500000000 2143208178691 20000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5135/1024 : ℝ)) 5135 4111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070107809/2000000000 : ℝ), (2567578943/5000000000 : ℝ), (-418216169/2500000000 : ℝ)] ![(45787261997799/100000000000000 : ℝ), (43496697097677/100000000000000 : ℝ), (2143208178691/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070107809/2000000000 : ℝ)|^5135 ≤ (45787261997799/100000000000000 : ℝ)^4111
        have hw : |(1070107809/2000000000 : ℝ)|=(1070107809/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2567578943/5000000000 : ℝ)|^5135 ≤ (43496697097677/100000000000000 : ℝ)^4111
        have hw : |(2567578943/5000000000 : ℝ)|=(2567578943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-418216169/2500000000 : ℝ)|^5135 ≤ (2143208178691/20000000000000 : ℝ)^4111
        have hw : |(-418216169/2500000000 : ℝ)|=(418216169/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1689_s4_3 (p : ℝ) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (826524809/2000000000 : ℝ)*x 0 + (3670074637/10000000000 : ℝ)*x 1 + (2316343593/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (826524809/2000000000 : ℝ)^5135 ≤ (33161368637867/100000000000000 : ℝ)^4111 := by
    have hnat : (826524809 : ℕ)^5135*100000000000000^4111 ≤ 33161368637867^4111*2000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      826524809 2000000000 33161368637867 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3670074637/10000000000 : ℝ)^5135 ≤ (14295874360093/50000000000000 : ℝ)^4111 := by
    have hnat : (3670074637 : ℕ)^5135*50000000000000^4111 ≤ 14295874360093^4111*10000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3670074637 10000000000 14295874360093 50000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2316343593/5000000000 : ℝ)^5135 ≤ (38246882624159/100000000000000 : ℝ)^4111 := by
    have hnat : (2316343593 : ℕ)^5135*100000000000000^4111 ≤ 38246882624159^4111*5000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2316343593 5000000000 38246882624159 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5135/1024 : ℝ)) 5135 4111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(826524809/2000000000 : ℝ), (3670074637/10000000000 : ℝ), (2316343593/5000000000 : ℝ)] ![(33161368637867/100000000000000 : ℝ), (14295874360093/50000000000000 : ℝ), (38246882624159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(826524809/2000000000 : ℝ)|^5135 ≤ (33161368637867/100000000000000 : ℝ)^4111
        have hw : |(826524809/2000000000 : ℝ)|=(826524809/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3670074637/10000000000 : ℝ)|^5135 ≤ (14295874360093/50000000000000 : ℝ)^4111
        have hw : |(3670074637/10000000000 : ℝ)|=(3670074637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2316343593/5000000000 : ℝ)|^5135 ≤ (38246882624159/100000000000000 : ℝ)^4111
        have hw : |(2316343593/5000000000 : ℝ)|=(2316343593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1689_s4_4 (p : ℝ) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-745946779/5000000000 : ℝ)*x 0 + (513894871/1000000000 : ℝ)*x 1 + (2739994667/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (745946779/5000000000 : ℝ)^5135 ≤ (9288081205809/100000000000000 : ℝ)^4111 := by
    have hnat : (745946779 : ℕ)^5135*100000000000000^4111 ≤ 9288081205809^4111*5000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      745946779 5000000000 9288081205809 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (513894871/1000000000 : ℝ)^5135 ≤ (870736172117/2000000000000 : ℝ)^4111 := by
    have hnat : (513894871 : ℕ)^5135*2000000000000^4111 ≤ 870736172117^4111*1000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513894871 1000000000 870736172117 2000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2739994667/5000000000 : ℝ)^5135 ≤ (47175110184167/100000000000000 : ℝ)^4111 := by
    have hnat : (2739994667 : ℕ)^5135*100000000000000^4111 ≤ 47175110184167^4111*5000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2739994667 5000000000 47175110184167 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5135/1024 : ℝ)) 5135 4111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-745946779/5000000000 : ℝ), (513894871/1000000000 : ℝ), (2739994667/5000000000 : ℝ)] ![(9288081205809/100000000000000 : ℝ), (870736172117/2000000000000 : ℝ), (47175110184167/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-745946779/5000000000 : ℝ)|^5135 ≤ (9288081205809/100000000000000 : ℝ)^4111
        have hw : |(-745946779/5000000000 : ℝ)|=(745946779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(513894871/1000000000 : ℝ)|^5135 ≤ (870736172117/2000000000000 : ℝ)^4111
        have hw : |(513894871/1000000000 : ℝ)|=(513894871/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2739994667/5000000000 : ℝ)|^5135 ≤ (47175110184167/100000000000000 : ℝ)^4111
        have hw : |(2739994667/5000000000 : ℝ)|=(2739994667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1689_s4_5 (p : ℝ) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1051466183/2000000000 : ℝ)*x 0 + (-265606661/2000000000 : ℝ)*x 1 + (1369997337/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051466183/2000000000 : ℝ)^5135 ≤ (11198281107039/25000000000000 : ℝ)^4111 := by
    have hnat : (1051466183 : ℕ)^5135*25000000000000^4111 ≤ 11198281107039^4111*2000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051466183 2000000000 11198281107039 25000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (265606661/2000000000 : ℝ)^5135 ≤ (321270609191/4000000000000 : ℝ)^4111 := by
    have hnat : (265606661 : ℕ)^5135*4000000000000^4111 ≤ 321270609191^4111*2000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265606661 2000000000 321270609191 4000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1369997337/2500000000 : ℝ)^5135 ≤ (11793777583677/25000000000000 : ℝ)^4111 := by
    have hnat : (1369997337 : ℕ)^5135*25000000000000^4111 ≤ 11793777583677^4111*2500000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1369997337 2500000000 11793777583677 25000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5135/1024 : ℝ)) 5135 4111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1051466183/2000000000 : ℝ), (-265606661/2000000000 : ℝ), (1369997337/2500000000 : ℝ)] ![(11198281107039/25000000000000 : ℝ), (321270609191/4000000000000 : ℝ), (11793777583677/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1051466183/2000000000 : ℝ)|^5135 ≤ (11198281107039/25000000000000 : ℝ)^4111
        have hw : |(1051466183/2000000000 : ℝ)|=(1051466183/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-265606661/2000000000 : ℝ)|^5135 ≤ (321270609191/4000000000000 : ℝ)^4111
        have hw : |(-265606661/2000000000 : ℝ)|=(265606661/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1369997337/2500000000 : ℝ)|^5135 ≤ (11793777583677/25000000000000 : ℝ)^4111
        have hw : |(1369997337/2500000000 : ℝ)|=(1369997337/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1689_s4_6 (p : ℝ) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (328583179/625000000 : ℝ)*x 0 + (1095997891/2000000000 : ℝ)*x 1 + (-166004153/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (328583179/625000000 : ℝ)^5135 ≤ (8958624777079/20000000000000 : ℝ)^4111 := by
    have hnat : (328583179 : ℕ)^5135*20000000000000^4111 ≤ 8958624777079^4111*625000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328583179 625000000 8958624777079 20000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1095997891/2000000000 : ℝ)^5135 ≤ (47175111485269/100000000000000 : ℝ)^4111 := by
    have hnat : (1095997891 : ℕ)^5135*100000000000000^4111 ≤ 47175111485269^4111*2000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095997891 2000000000 47175111485269 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (166004153/1250000000 : ℝ)^5135 ≤ (64254116943/800000000000 : ℝ)^4111 := by
    have hnat : (166004153 : ℕ)^5135*800000000000^4111 ≤ 64254116943^4111*1250000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166004153 1250000000 64254116943 800000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5135/1024 : ℝ)) 5135 4111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(328583179/625000000 : ℝ), (1095997891/2000000000 : ℝ), (-166004153/1250000000 : ℝ)] ![(8958624777079/20000000000000 : ℝ), (47175111485269/100000000000000 : ℝ), (64254116943/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(328583179/625000000 : ℝ)|^5135 ≤ (8958624777079/20000000000000 : ℝ)^4111
        have hw : |(328583179/625000000 : ℝ)|=(328583179/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1095997891/2000000000 : ℝ)|^5135 ≤ (47175111485269/100000000000000 : ℝ)^4111
        have hw : |(1095997891/2000000000 : ℝ)|=(1095997891/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-166004153/1250000000 : ℝ)|^5135 ≤ (64254116943/800000000000 : ℝ)^4111
        have hw : |(-166004153/1250000000 : ℝ)|=(166004153/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1689_s4_7 (p : ℝ) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2066536281/5000000000 : ℝ)*x 0 + (4622222733/10000000000 : ℝ)*x 1 + (1840347627/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2066536281/5000000000 : ℝ)^5135 ≤ (207286651269/625000000000 : ℝ)^4111 := by
    have hnat : (2066536281 : ℕ)^5135*625000000000^4111 ≤ 207286651269^4111*5000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2066536281 5000000000 207286651269 625000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4622222733/10000000000 : ℝ)^5135 ≤ (19069500148509/50000000000000 : ℝ)^4111 := by
    have hnat : (4622222733 : ℕ)^5135*50000000000000^4111 ≤ 19069500148509^4111*10000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4622222733 10000000000 19069500148509 50000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1840347627/5000000000 : ℝ)^5135 ≤ (7173783869941/25000000000000 : ℝ)^4111 := by
    have hnat : (1840347627 : ℕ)^5135*25000000000000^4111 ≤ 7173783869941^4111*5000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1840347627 5000000000 7173783869941 25000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5135/1024 : ℝ)) 5135 4111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2066536281/5000000000 : ℝ), (4622222733/10000000000 : ℝ), (1840347627/5000000000 : ℝ)] ![(207286651269/625000000000 : ℝ), (19069500148509/50000000000000 : ℝ), (7173783869941/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2066536281/5000000000 : ℝ)|^5135 ≤ (207286651269/625000000000 : ℝ)^4111
        have hw : |(2066536281/5000000000 : ℝ)|=(2066536281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4622222733/10000000000 : ℝ)|^5135 ≤ (19069500148509/50000000000000 : ℝ)^4111
        have hw : |(4622222733/10000000000 : ℝ)|=(4622222733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1840347627/5000000000 : ℝ)|^5135 ≤ (7173783869941/25000000000000 : ℝ)^4111
        have hw : |(1840347627/5000000000 : ℝ)|=(1840347627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1689_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (94018711/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17243/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (491/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (9821/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17241/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17243/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (491/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17243/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (491/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17243/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (491/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17243/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (491/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17243/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (491/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17243/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (491/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (491/5000 : ℝ) ^ (5127/1024 : ℝ) ≤ (898809338562993/100000000000000000000 : ℝ) := by
    have hpowers : (491/5000 : ℝ)^5127 ≤ (898809338562993/100000000000000000000 : ℝ)^1024 := by
      have hnat : (491 : ℕ)^5127*100000000000000000000^1024 ≤ 898809338562993^1024*5000^5127 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        491 5000 898809338562993 100000000000000000000 5127 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (491/5000 : ℝ)) (X := (898809338562993/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5127 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17243/100000 : ℝ) ^ (5127/1024 : ℝ) ≤ (3012143580756323/20000000000000000000 : ℝ) := by
    have hpowers : (17243/100000 : ℝ)^5127 ≤ (3012143580756323/20000000000000000000 : ℝ)^1024 := by
      have hnat : (17243 : ℕ)^5127*20000000000000000000^1024 ≤ 3012143580756323^1024*100000^5127 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17243 100000 3012143580756323 20000000000000000000 5127 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17243/100000 : ℝ)) (X := (3012143580756323/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5127 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000898809338562993/50000000000000000000 : ℝ) ≤ (10000035903028771/10000000000000000 : ℝ) ^ (5127/1024 : ℝ) := by
    have hpowers : (50000898809338562993/50000000000000000000 : ℝ)^1024 ≤ (10000035903028771/10000000000000000 : ℝ)^5127 := by
      have hnat : (50000898809338562993 : ℕ)^1024*10000000000000000^5127 ≤ 10000035903028771^5127*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000898809338562993 50000000000000000000 10000035903028771 10000000000000000 1024 5127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000035903028771/10000000000000000 : ℝ)) (X := (50000898809338562993/50000000000000000000 : ℝ)) (by norm_num) 5127 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (3125498735226323269/3125000000000000000 : ℝ) ≤ (2000063746878729/2000000000000000 : ℝ) ^ (5127/1024 : ℝ) := by
    have hpowers : (3125498735226323269/3125000000000000000 : ℝ)^1024 ≤ (2000063746878729/2000000000000000 : ℝ)^5127 := by
      have hnat : (3125498735226323269 : ℕ)^1024*2000000000000000^5127 ≤ 2000063746878729^5127*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125498735226323269 3125000000000000000 2000063746878729 2000000000000000 1024 5127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000063746878729/2000000000000000 : ℝ)) (X := (3125498735226323269/3125000000000000000 : ℝ)) (by norm_num) 5127 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10003012143580756323/10000000000000000000 : ℝ) ≤ (10000601565758519/10000000000000000 : ℝ) ^ (5127/1024 : ℝ) := by
    have hpowers : (10003012143580756323/10000000000000000000 : ℝ)^1024 ≤ (10000601565758519/10000000000000000 : ℝ)^5127 := by
      have hnat : (10003012143580756323 : ℕ)^1024*10000000000000000^5127 ≤ 10000601565758519^5127*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10003012143580756323 10000000000000000000 10000601565758519 10000000000000000 1024 5127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000601565758519/10000000000000000 : ℝ)) (X := (10003012143580756323/10000000000000000000 : ℝ)) (by norm_num) 5127 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(898809338562993/100000000000000000000 : ℝ) ≤ ((74224711700176441773/74230000000000000000 : ℝ)+2*(141415682437/371150000000000 : ℝ)*(491/5000 : ℝ))^(5127/1024 : ℝ) := by
    rw [show (74224711700176441773/74230000000000000000 : ℝ)+2*(141415682437/371150000000000 : ℝ)*(491/5000 : ℝ)=(10000035903028771/10000000000000000 : ℝ) by norm_num, show 1+2*(898809338562993/100000000000000000000 : ℝ)=(50000898809338562993/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3012143580756323/20000000000000000000 : ℝ)+(898809338562993/100000000000000000000 : ℝ) ≤ ((74224711700176441773/74230000000000000000 : ℝ)+(141415682437/371150000000000 : ℝ)*((17243/100000 : ℝ)+(491/5000 : ℝ)))^(5127/1024 : ℝ) := by
    rw [show (74224711700176441773/74230000000000000000 : ℝ)+(141415682437/371150000000000 : ℝ)*((17243/100000 : ℝ)+(491/5000 : ℝ))=(2000063746878729/2000000000000000 : ℝ) by norm_num, show 1+(3012143580756323/20000000000000000000 : ℝ)+(898809338562993/100000000000000000000 : ℝ)=(3125498735226323269/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3012143580756323/20000000000000000000 : ℝ) ≤ ((74224711700176441773/74230000000000000000 : ℝ)+2*(141415682437/371150000000000 : ℝ)*(17243/100000 : ℝ))^(5127/1024 : ℝ) := by
    rw [show (74224711700176441773/74230000000000000000 : ℝ)+2*(141415682437/371150000000000 : ℝ)*(17243/100000 : ℝ)=(10000601565758519/10000000000000000 : ℝ) by norm_num, show 1+2*(3012143580756323/20000000000000000000 : ℝ)=(10003012143580756323/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (74224711700176441773/74230000000000000000 : ℝ)*(X 1 0+X 2 0)+(141415682437/371150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5127/1024 : ℝ)) (lo := (491/5000 : ℝ)) (hi := (17243/100000 : ℝ)) (c := (74224711700176441773/74230000000000000000 : ℝ)) (alpha := (141415682437/371150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (74224711700176441773/74230000000000000000 : ℝ)*(X 0 1+X 2 1)+(141415682437/371150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5127/1024 : ℝ)) (lo := (491/5000 : ℝ)) (hi := (17243/100000 : ℝ)) (c := (74224711700176441773/74230000000000000000 : ℝ)) (alpha := (141415682437/371150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (74224711700176441773/74230000000000000000 : ℝ)*(X 0 2+X 1 2)+(141415682437/371150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5127/1024 : ℝ)) (lo := (491/5000 : ℝ)) (hi := (17243/100000 : ℝ)) (c := (74224711700176441773/74230000000000000000 : ℝ)) (alpha := (141415682437/371150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1491731733/10000000000 : ℝ)*X 0 0+(5483836079/10000000000 : ℝ)*X 0 1+(5135158129/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1689_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350539167/10000000000 : ℝ)*X 1 0+(-836432159/5000000000 : ℝ)*X 1 1+(5135158033/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1689_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1070107809/2000000000 : ℝ)*X 2 0+(2567578943/5000000000 : ℝ)*X 2 1+(-418216169/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1689_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((826524809/2000000000 : ℝ)*X 0 0+(3670074637/10000000000 : ℝ)*X 0 1+(2316343593/5000000000 : ℝ)*X 0 2+(826524809/2000000000 : ℝ)*X 1 0+(3670074637/10000000000 : ℝ)*X 1 1+(2316343593/5000000000 : ℝ)*X 1 2+(826524809/2000000000 : ℝ)*X 2 0+(3670074637/10000000000 : ℝ)*X 2 1+(2316343593/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1689_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-745946779/5000000000 : ℝ)*X 0 0+(513894871/1000000000 : ℝ)*X 0 1+(2739994667/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1689_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1051466183/2000000000 : ℝ)*X 1 0+(-265606661/2000000000 : ℝ)*X 1 1+(1369997337/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1689_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((328583179/625000000 : ℝ)*X 2 0+(1095997891/2000000000 : ℝ)*X 2 1+(-166004153/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1689_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2066536281/5000000000 : ℝ)*X 0 0+(4622222733/10000000000 : ℝ)*X 0 1+(1840347627/5000000000 : ℝ)*X 0 2+(2066536281/5000000000 : ℝ)*X 1 0+(4622222733/10000000000 : ℝ)*X 1 1+(1840347627/5000000000 : ℝ)*X 1 2+(2066536281/5000000000 : ℝ)*X 2 0+(4622222733/10000000000 : ℝ)*X 2 1+(1840347627/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1689_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2607190965704922041714088399/231968750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (27764863/1250000000000 : ℝ)*(base19) + (202267041/10000000000000 : ℝ)*(base23) + (230188641/50000000000000 : ℝ)*(upper3) + (7122841/10000000000000 : ℝ)*(upper4) + (71689423/50000000000000 : ℝ)*(upper5) + (244179365613071/12500000000000 : ℝ)*(major0) + (244179365613071/12500000000000 : ℝ)*(major1) + (244179365613071/12500000000000 : ℝ)*(major2) + (1433998972557853/50000000000000 : ℝ)*(sp0) + (2868012910977299/100000000000000 : ℝ)*(sp1) + (358501638686991/12500000000000 : ℝ)*(sp2) + (519422960071351/50000000000000 : ℝ)*(sp3) + (17187050633/100000000000000 : ℝ)*(sp4) + (8422853219/100000000000000 : ℝ)*(sp7) + (519427171497961/50000000000000 : ℝ)*(f.failure) + (2868015132166339/100000000000000 : ℝ)*(f.sum) + (63638676121873/9278750000000000000000000000 : ℝ)*base65 + (11560184102192260117/927875000000000000000000000000000 : ℝ)*base68 + (3295318279535635117/927875000000000000000000000000000 : ℝ)*base70 + (2329172988868260117/927875000000000000000000000000000 : ℝ)*base72 + (30504590914753/37115000000000000000000000000 : ℝ)*base74 + (8464575200027260117/927875000000000000000000000000000 : ℝ)*base76 + (2779321177970885117/927875000000000000000000000000000 : ℝ)*base78 + (871765362346239883/927875000000000000000000000000000 : ℝ)*base79 + (69519473334691/18557500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (32348271/2500000000000000000000 : ℝ)*base89 + (32348271/2500000000000000000000 : ℝ)*base91 + (32348271/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5248837563132836121021193113/1855750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (54951633/20000000000000 : ℝ)*(base19) + (208021993/50000000000000 : ℝ)*(base23) + (2642443/3125000000000 : ℝ)*(lower1) + (43737883/100000000000000 : ℝ)*(upper3) + (70814927/100000000000000 : ℝ)*(lower4) + (579913/1562500000000 : ℝ)*(upper5) + (998575354749473/50000000000000 : ℝ)*(major0) + (998575354749473/50000000000000 : ℝ)*(major1) + (998575354749473/50000000000000 : ℝ)*(major2) + (1975997483/100000000000000 : ℝ)*(sp2) + (2932198532487461/100000000000000 : ℝ)*(sp4) + (183262391108081/6250000000000 : ℝ)*(sp5) + (366524517555749/12500000000000 : ℝ)*(sp6) + (1062102792229807/100000000000000 : ℝ)*(sp7) + (1062102792229807/100000000000000 : ℝ)*(f.failure) + (2932198532487461/100000000000000 : ℝ)*(f.sum) + (32461594037059/9278750000000000000000000000 : ℝ)*base66 + (24856747390255635629/3711500000000000000000000000000000 : ℝ)*base67 + (17910492864779135629/3711500000000000000000000000000000 : ℝ)*base69 + (40793799437473864371/3711500000000000000000000000000000 : ℝ)*base72 + (34023031221939/37115000000000000000000000000 : ℝ)*base73 + (63663816038411864371/3711500000000000000000000000000000 : ℝ)*base76 + (24090884873121635629/3711500000000000000000000000000000 : ℝ)*base77 + (17791944299793635629/3711500000000000000000000000000000 : ℝ)*base79 + (2651788903163/18557500000000000000000000000 : ℝ)*base82 + (30081223/5000000000000000000000 : ℝ)*base90 + (30081223/5000000000000000000000 : ℝ)*base92 + (30081223/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1689_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (94018711/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17243/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (491/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9821/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17241/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1689_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1689_box_0 (p : ℝ) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-577957859/5000000000 : ℝ)*x 0 + (2714309577/5000000000 : ℝ)*x 1 + (542861917/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (577957859/5000000000 : ℝ)^5135 ≤ (6753244879503/100000000000000 : ℝ)^4111 := by
    have hnat : (577957859 : ℕ)^5135*100000000000000^4111 ≤ 6753244879503^4111*5000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      577957859 5000000000 6753244879503 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2714309577/5000000000 : ℝ)^5135 ≤ (23311688731449/50000000000000 : ℝ)^4111 := by
    have hnat : (2714309577 : ℕ)^5135*50000000000000^4111 ≤ 23311688731449^4111*5000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714309577 5000000000 23311688731449 50000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (542861917/1000000000 : ℝ)^5135 ≤ (46623377634541/100000000000000 : ℝ)^4111 := by
    have hnat : (542861917 : ℕ)^5135*100000000000000^4111 ≤ 46623377634541^4111*1000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542861917 1000000000 46623377634541 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5135/1024 : ℝ)) 5135 4111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-577957859/5000000000 : ℝ), (2714309577/5000000000 : ℝ), (542861917/1000000000 : ℝ)] ![(6753244879503/100000000000000 : ℝ), (23311688731449/50000000000000 : ℝ), (46623377634541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-577957859/5000000000 : ℝ)|^5135 ≤ (6753244879503/100000000000000 : ℝ)^4111
        have hw : |(-577957859/5000000000 : ℝ)|=(577957859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2714309577/5000000000 : ℝ)|^5135 ≤ (23311688731449/50000000000000 : ℝ)^4111
        have hw : |(2714309577/5000000000 : ℝ)|=(2714309577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(542861917/1000000000 : ℝ)|^5135 ≤ (46623377634541/100000000000000 : ℝ)^4111
        have hw : |(542861917/1000000000 : ℝ)|=(542861917/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1689_box_1 (p : ℝ) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1306513823/2500000000 : ℝ)*x 0 + (-144386469/1000000000 : ℝ)*x 1 + (217144771/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1306513823/2500000000 : ℝ)^5135 ≤ (44460524147101/100000000000000 : ℝ)^4111 := by
    have hnat : (1306513823 : ℕ)^5135*100000000000000^4111 ≤ 44460524147101^4111*2500000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1306513823 2500000000 44460524147101 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (144386469/1000000000 : ℝ)^5135 ≤ (8916097081091/100000000000000 : ℝ)^4111 := by
    have hnat : (144386469 : ℕ)^5135*100000000000000^4111 ≤ 8916097081091^4111*1000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      144386469 1000000000 8916097081091 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (217144771/400000000 : ℝ)^5135 ≤ (46623378760951/100000000000000 : ℝ)^4111 := by
    have hnat : (217144771 : ℕ)^5135*100000000000000^4111 ≤ 46623378760951^4111*400000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217144771 400000000 46623378760951 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5135/1024 : ℝ)) 5135 4111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1306513823/2500000000 : ℝ), (-144386469/1000000000 : ℝ), (217144771/400000000 : ℝ)] ![(44460524147101/100000000000000 : ℝ), (8916097081091/100000000000000 : ℝ), (46623378760951/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1306513823/2500000000 : ℝ)|^5135 ≤ (44460524147101/100000000000000 : ℝ)^4111
        have hw : |(1306513823/2500000000 : ℝ)|=(1306513823/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-144386469/1000000000 : ℝ)|^5135 ≤ (8916097081091/100000000000000 : ℝ)^4111
        have hw : |(-144386469/1000000000 : ℝ)|=(144386469/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(217144771/400000000 : ℝ)|^5135 ≤ (46623378760951/100000000000000 : ℝ)^4111
        have hw : |(217144771/400000000 : ℝ)|=(217144771/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1689_box_2 (p : ℝ) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (26130277/50000000 : ℝ)*x 0 + (1085723829/2000000000 : ℝ)*x 1 + (-1443864721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26130277/50000000 : ℝ)^5135 ≤ (11115131323693/25000000000000 : ℝ)^4111 := by
    have hnat : (26130277 : ℕ)^5135*25000000000000^4111 ≤ 11115131323693^4111*50000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26130277 50000000 11115131323693 25000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1085723829/2000000000 : ℝ)^5135 ≤ (11655844341587/25000000000000 : ℝ)^4111 := by
    have hnat : (1085723829 : ℕ)^5135*25000000000000^4111 ≤ 11655844341587^4111*2000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085723829 2000000000 11655844341587 25000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1443864721/10000000000 : ℝ)^5135 ≤ (2229024330051/25000000000000 : ℝ)^4111 := by
    have hnat : (1443864721 : ℕ)^5135*25000000000000^4111 ≤ 2229024330051^4111*10000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1443864721 10000000000 2229024330051 25000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5135/1024 : ℝ)) 5135 4111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(26130277/50000000 : ℝ), (1085723829/2000000000 : ℝ), (-1443864721/10000000000 : ℝ)] ![(11115131323693/25000000000000 : ℝ), (11655844341587/25000000000000 : ℝ), (2229024330051/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(26130277/50000000 : ℝ)|^5135 ≤ (11115131323693/25000000000000 : ℝ)^4111
        have hw : |(26130277/50000000 : ℝ)|=(26130277/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1085723829/2000000000 : ℝ)|^5135 ≤ (11655844341587/25000000000000 : ℝ)^4111
        have hw : |(1085723829/2000000000 : ℝ)|=(1085723829/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1443864721/10000000000 : ℝ)|^5135 ≤ (2229024330051/25000000000000 : ℝ)^4111
        have hw : |(-1443864721/10000000000 : ℝ)|=(1443864721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1689_box_3 (p : ℝ) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4517067933/10000000000 : ℝ)*x 0 + (3963085003/10000000000 : ℝ)*x 1 + (3963084991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4517067933/10000000000 : ℝ)^5135 ≤ (37058310242383/100000000000000 : ℝ)^4111 := by
    have hnat : (4517067933 : ℕ)^5135*100000000000000^4111 ≤ 37058310242383^4111*10000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4517067933 10000000000 37058310242383 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3963085003/10000000000 : ℝ)^5135 ≤ (31470844928601/100000000000000 : ℝ)^4111 := by
    have hnat : (3963085003 : ℕ)^5135*100000000000000^4111 ≤ 31470844928601^4111*10000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3963085003 10000000000 31470844928601 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3963084991/10000000000 : ℝ)^5135 ≤ (31470844809573/100000000000000 : ℝ)^4111 := by
    have hnat : (3963084991 : ℕ)^5135*100000000000000^4111 ≤ 31470844809573^4111*10000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3963084991 10000000000 31470844809573 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5135/1024 : ℝ)) 5135 4111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4517067933/10000000000 : ℝ), (3963085003/10000000000 : ℝ), (3963084991/10000000000 : ℝ)] ![(37058310242383/100000000000000 : ℝ), (31470844928601/100000000000000 : ℝ), (31470844809573/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4517067933/10000000000 : ℝ)|^5135 ≤ (37058310242383/100000000000000 : ℝ)^4111
        have hw : |(4517067933/10000000000 : ℝ)|=(4517067933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3963085003/10000000000 : ℝ)|^5135 ≤ (31470844928601/100000000000000 : ℝ)^4111
        have hw : |(3963085003/10000000000 : ℝ)|=(3963085003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3963084991/10000000000 : ℝ)|^5135 ≤ (31470844809573/100000000000000 : ℝ)^4111
        have hw : |(3963084991/10000000000 : ℝ)|=(3963084991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1689_box_4 (p : ℝ) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1848519337/10000000000 : ℝ)*x 0 + (1035219699/2000000000 : ℝ)*x 1 + (1294024167/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1848519337/10000000000 : ℝ)^5135 ≤ (12139443859131/100000000000000 : ℝ)^4111 := by
    have hnat : (1848519337 : ℕ)^5135*100000000000000^4111 ≤ 12139443859131^4111*10000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1848519337 10000000000 12139443859131 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1035219699/2000000000 : ℝ)^5135 ≤ (10982571936477/25000000000000 : ℝ)^4111 := by
    have hnat : (1035219699 : ℕ)^5135*25000000000000^4111 ≤ 10982571936477^4111*2000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035219699 2000000000 10982571936477 25000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1294024167/2500000000 : ℝ)^5135 ≤ (2196513418877/5000000000000 : ℝ)^4111 := by
    have hnat : (1294024167 : ℕ)^5135*5000000000000^4111 ≤ 2196513418877^4111*2500000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294024167 2500000000 2196513418877 5000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5135/1024 : ℝ)) 5135 4111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1848519337/10000000000 : ℝ), (1035219699/2000000000 : ℝ), (1294024167/2500000000 : ℝ)] ![(12139443859131/100000000000000 : ℝ), (10982571936477/25000000000000 : ℝ), (2196513418877/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1848519337/10000000000 : ℝ)|^5135 ≤ (12139443859131/100000000000000 : ℝ)^4111
        have hw : |(-1848519337/10000000000 : ℝ)|=(1848519337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1035219699/2000000000 : ℝ)|^5135 ≤ (10982571936477/25000000000000 : ℝ)^4111
        have hw : |(1035219699/2000000000 : ℝ)|=(1035219699/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1294024167/2500000000 : ℝ)|^5135 ≤ (2196513418877/5000000000000 : ℝ)^4111
        have hw : |(1294024167/2500000000 : ℝ)|=(1294024167/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1689_box_5 (p : ℝ) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5398193657/10000000000 : ℝ)*x 0 + (-97116883/625000000 : ℝ)*x 1 + (5176098121/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5398193657/10000000000 : ℝ)^5135 ≤ (2314860473991/5000000000000 : ℝ)^4111 := by
    have hnat : (5398193657 : ℕ)^5135*5000000000000^4111 ≤ 2314860473991^4111*10000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5398193657 10000000000 2314860473991 5000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (97116883/625000000 : ℝ)^5135 ≤ (1954501345411/20000000000000 : ℝ)^4111 := by
    have hnat : (97116883 : ℕ)^5135*20000000000000^4111 ≤ 1954501345411^4111*625000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      97116883 625000000 1954501345411 20000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5176098121/10000000000 : ℝ)^5135 ≤ (5491285472633/12500000000000 : ℝ)^4111 := by
    have hnat : (5176098121 : ℕ)^5135*12500000000000^4111 ≤ 5491285472633^4111*10000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176098121 10000000000 5491285472633 12500000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5135/1024 : ℝ)) 5135 4111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5398193657/10000000000 : ℝ), (-97116883/625000000 : ℝ), (5176098121/10000000000 : ℝ)] ![(2314860473991/5000000000000 : ℝ), (1954501345411/20000000000000 : ℝ), (5491285472633/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5398193657/10000000000 : ℝ)|^5135 ≤ (2314860473991/5000000000000 : ℝ)^4111
        have hw : |(5398193657/10000000000 : ℝ)|=(5398193657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-97116883/625000000 : ℝ)|^5135 ≤ (1954501345411/20000000000000 : ℝ)^4111
        have hw : |(-97116883/625000000 : ℝ)|=(97116883/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5176098121/10000000000 : ℝ)|^5135 ≤ (5491285472633/12500000000000 : ℝ)^4111
        have hw : |(5176098121/10000000000 : ℝ)|=(5176098121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1689_box_6 (p : ℝ) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (10796389/20000000 : ℝ)*x 0 + (517609693/1000000000 : ℝ)*x 1 + (-310774117/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10796389/20000000 : ℝ)^5135 ≤ (23148609255317/50000000000000 : ℝ)^4111 := by
    have hnat : (10796389 : ℕ)^5135*50000000000000^4111 ≤ 23148609255317^4111*20000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10796389 20000000 23148609255317 50000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (517609693/1000000000 : ℝ)^5135 ≤ (43930271155051/100000000000000 : ℝ)^4111 := by
    have hnat : (517609693 : ℕ)^5135*100000000000000^4111 ≤ 43930271155051^4111*1000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517609693 1000000000 43930271155051 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (310774117/2000000000 : ℝ)^5135 ≤ (1954502063421/20000000000000 : ℝ)^4111 := by
    have hnat : (310774117 : ℕ)^5135*20000000000000^4111 ≤ 1954502063421^4111*2000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      310774117 2000000000 1954502063421 20000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5135/1024 : ℝ)) 5135 4111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(10796389/20000000 : ℝ), (517609693/1000000000 : ℝ), (-310774117/2000000000 : ℝ)] ![(23148609255317/50000000000000 : ℝ), (43930271155051/100000000000000 : ℝ), (1954502063421/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(10796389/20000000 : ℝ)|^5135 ≤ (23148609255317/50000000000000 : ℝ)^4111
        have hw : |(10796389/20000000 : ℝ)|=(10796389/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(517609693/1000000000 : ℝ)|^5135 ≤ (43930271155051/100000000000000 : ℝ)^4111
        have hw : |(517609693/1000000000 : ℝ)|=(517609693/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-310774117/2000000000 : ℝ)|^5135 ≤ (1954502063421/20000000000000 : ℝ)^4111
        have hw : |(-310774117/2000000000 : ℝ)|=(310774117/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1689_box_7 (p : ℝ) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3733659999/10000000000 : ℝ)*x 0 + (1088481571/2500000000 : ℝ)*x 1 + (870785087/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3733659999/10000000000 : ℝ)^5135 ≤ (5842365826789/20000000000000 : ℝ)^4111 := by
    have hnat : (3733659999 : ℕ)^5135*20000000000000^4111 ≤ 5842365826789^4111*10000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3733659999 10000000000 5842365826789 20000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1088481571/2500000000 : ℝ)^5135 ≤ (35394089734983/100000000000000 : ℝ)^4111 := by
    have hnat : (1088481571 : ℕ)^5135*100000000000000^4111 ≤ 35394089734983^4111*2500000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088481571 2500000000 35394089734983 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (870785087/2000000000 : ℝ)^5135 ≤ (2212130069633/6250000000000 : ℝ)^4111 := by
    have hnat : (870785087 : ℕ)^5135*6250000000000^4111 ≤ 2212130069633^4111*2000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      870785087 2000000000 2212130069633 6250000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5135/1024 : ℝ)) 5135 4111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3733659999/10000000000 : ℝ), (1088481571/2500000000 : ℝ), (870785087/2000000000 : ℝ)] ![(5842365826789/20000000000000 : ℝ), (35394089734983/100000000000000 : ℝ), (2212130069633/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3733659999/10000000000 : ℝ)|^5135 ≤ (5842365826789/20000000000000 : ℝ)^4111
        have hw : |(3733659999/10000000000 : ℝ)|=(3733659999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1088481571/2500000000 : ℝ)|^5135 ≤ (35394089734983/100000000000000 : ℝ)^4111
        have hw : |(1088481571/2500000000 : ℝ)|=(1088481571/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(870785087/2000000000 : ℝ)|^5135 ≤ (2212130069633/6250000000000 : ℝ)^4111
        have hw : |(870785087/2000000000 : ℝ)|=(870785087/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1689_box_8 (p : ℝ) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1699928319/10000000000 : ℝ)*x 0 + (124771171/250000000 : ℝ)*x 1 + (1094447003/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1699928319/10000000000 : ℝ)^5135 ≤ (1366627844667/12500000000000 : ℝ)^4111 := by
    have hnat : (1699928319 : ℕ)^5135*12500000000000^4111 ≤ 1366627844667^4111*10000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1699928319 10000000000 1366627844667 12500000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (124771171/250000000 : ℝ)^5135 ≤ (10493808464881/25000000000000 : ℝ)^4111 := by
    have hnat : (124771171 : ℕ)^5135*25000000000000^4111 ≤ 10493808464881^4111*250000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      124771171 250000000 10493808464881 25000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1094447003/2000000000 : ℝ)^5135 ≤ (47091743356909/100000000000000 : ℝ)^4111 := by
    have hnat : (1094447003 : ℕ)^5135*100000000000000^4111 ≤ 47091743356909^4111*2000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094447003 2000000000 47091743356909 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5135/1024 : ℝ)) 5135 4111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1699928319/10000000000 : ℝ), (124771171/250000000 : ℝ), (1094447003/2000000000 : ℝ)] ![(1366627844667/12500000000000 : ℝ), (10493808464881/25000000000000 : ℝ), (47091743356909/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1699928319/10000000000 : ℝ)|^5135 ≤ (1366627844667/12500000000000 : ℝ)^4111
        have hw : |(-1699928319/10000000000 : ℝ)|=(1699928319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(124771171/250000000 : ℝ)|^5135 ≤ (10493808464881/25000000000000 : ℝ)^4111
        have hw : |(124771171/250000000 : ℝ)|=(124771171/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1094447003/2000000000 : ℝ)|^5135 ≤ (47091743356909/100000000000000 : ℝ)^4111
        have hw : |(1094447003/2000000000 : ℝ)|=(1094447003/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1689_box_9 (p : ℝ) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2598166971/5000000000 : ℝ)*x 0 + (-284805213/2000000000 : ℝ)*x 1 + (2736117813/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2598166971/5000000000 : ℝ)^5135 ≤ (44144911845533/100000000000000 : ℝ)^4111 := by
    have hnat : (2598166971 : ℕ)^5135*100000000000000^4111 ≤ 44144911845533^4111*5000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598166971 5000000000 44144911845533 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (284805213/2000000000 : ℝ)^5135 ≤ (8763338208863/100000000000000 : ℝ)^4111 := by
    have hnat : (284805213 : ℕ)^5135*100000000000000^4111 ≤ 8763338208863^4111*2000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      284805213 2000000000 8763338208863 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2736117813/5000000000 : ℝ)^5135 ≤ (23545874962311/50000000000000 : ℝ)^4111 := by
    have hnat : (2736117813 : ℕ)^5135*50000000000000^4111 ≤ 23545874962311^4111*5000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2736117813 5000000000 23545874962311 50000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5135/1024 : ℝ)) 5135 4111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2598166971/5000000000 : ℝ), (-284805213/2000000000 : ℝ), (2736117813/5000000000 : ℝ)] ![(44144911845533/100000000000000 : ℝ), (8763338208863/100000000000000 : ℝ), (23545874962311/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2598166971/5000000000 : ℝ)|^5135 ≤ (44144911845533/100000000000000 : ℝ)^4111
        have hw : |(2598166971/5000000000 : ℝ)|=(2598166971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-284805213/2000000000 : ℝ)|^5135 ≤ (8763338208863/100000000000000 : ℝ)^4111
        have hw : |(-284805213/2000000000 : ℝ)|=(284805213/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2736117813/5000000000 : ℝ)|^5135 ≤ (23545874962311/50000000000000 : ℝ)^4111
        have hw : |(2736117813/5000000000 : ℝ)|=(2736117813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1689_box_10 (p : ℝ) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (649541793/1250000000 : ℝ)*x 0 + (1368058851/2500000000 : ℝ)*x 1 + (-1424025821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (649541793/1250000000 : ℝ)^5135 ≤ (22072458055677/50000000000000 : ℝ)^4111 := by
    have hnat : (649541793 : ℕ)^5135*50000000000000^4111 ≤ 22072458055677^4111*1250000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      649541793 1250000000 22072458055677 50000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1368058851/2500000000 : ℝ)^5135 ≤ (47091747538317/100000000000000 : ℝ)^4111 := by
    have hnat : (1368058851 : ℕ)^5135*100000000000000^4111 ≤ 47091747538317^4111*2500000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1368058851 2500000000 47091747538317 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1424025821/10000000000 : ℝ)^5135 ≤ (1095417041661/12500000000000 : ℝ)^4111 := by
    have hnat : (1424025821 : ℕ)^5135*12500000000000^4111 ≤ 1095417041661^4111*10000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1424025821 10000000000 1095417041661 12500000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5135/1024 : ℝ)) 5135 4111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(649541793/1250000000 : ℝ), (1368058851/2500000000 : ℝ), (-1424025821/10000000000 : ℝ)] ![(22072458055677/50000000000000 : ℝ), (47091747538317/100000000000000 : ℝ), (1095417041661/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(649541793/1250000000 : ℝ)|^5135 ≤ (22072458055677/50000000000000 : ℝ)^4111
        have hw : |(649541793/1250000000 : ℝ)|=(649541793/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1368058851/2500000000 : ℝ)|^5135 ≤ (47091747538317/100000000000000 : ℝ)^4111
        have hw : |(1368058851/2500000000 : ℝ)|=(1368058851/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1424025821/10000000000 : ℝ)|^5135 ≤ (1095417041661/12500000000000 : ℝ)^4111
        have hw : |(-1424025821/10000000000 : ℝ)|=(1424025821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1689_box_11 (p : ℝ) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2323675591/5000000000 : ℝ)*x 0 + (1947700517/5000000000 : ℝ)*x 1 + (973850127/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2323675591/5000000000 : ℝ)^5135 ≤ (38398161891019/100000000000000 : ℝ)^4111 := by
    have hnat : (2323675591 : ℕ)^5135*100000000000000^4111 ≤ 38398161891019^4111*5000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2323675591 5000000000 38398161891019 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1947700517/5000000000 : ℝ)^5135 ≤ (30800921643297/100000000000000 : ℝ)^4111 := by
    have hnat : (1947700517 : ℕ)^5135*100000000000000^4111 ≤ 30800921643297^4111*5000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1947700517 5000000000 30800921643297 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (973850127/2500000000 : ℝ)^5135 ≤ (30800916448241/100000000000000 : ℝ)^4111 := by
    have hnat : (973850127 : ℕ)^5135*100000000000000^4111 ≤ 30800916448241^4111*2500000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      973850127 2500000000 30800916448241 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5135/1024 : ℝ)) 5135 4111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2323675591/5000000000 : ℝ), (1947700517/5000000000 : ℝ), (973850127/2500000000 : ℝ)] ![(38398161891019/100000000000000 : ℝ), (30800921643297/100000000000000 : ℝ), (30800916448241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2323675591/5000000000 : ℝ)|^5135 ≤ (38398161891019/100000000000000 : ℝ)^4111
        have hw : |(2323675591/5000000000 : ℝ)|=(2323675591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1947700517/5000000000 : ℝ)|^5135 ≤ (30800921643297/100000000000000 : ℝ)^4111
        have hw : |(1947700517/5000000000 : ℝ)|=(1947700517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(973850127/2500000000 : ℝ)|^5135 ≤ (30800916448241/100000000000000 : ℝ)^4111
        have hw : |(973850127/2500000000 : ℝ)|=(973850127/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1689_box_12 (p : ℝ) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1299731317/10000000000 : ℝ)*x 0 + (5604651279/10000000000 : ℝ)*x 1 + (643848151/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1299731317/10000000000 : ℝ)^5135 ≤ (3909266830841/50000000000000 : ℝ)^4111 := by
    have hnat : (1299731317 : ℕ)^5135*50000000000000^4111 ≤ 3909266830841^4111*10000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1299731317 10000000000 3909266830841 50000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5604651279/10000000000 : ℝ)^5135 ≤ (48519365813119/100000000000000 : ℝ)^4111 := by
    have hnat : (5604651279 : ℕ)^5135*100000000000000^4111 ≤ 48519365813119^4111*10000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5604651279 10000000000 48519365813119 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (643848151/1250000000 : ℝ)^5135 ≤ (1364440640853/3125000000000 : ℝ)^4111 := by
    have hnat : (643848151 : ℕ)^5135*3125000000000^4111 ≤ 1364440640853^4111*1250000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      643848151 1250000000 1364440640853 3125000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5135/1024 : ℝ)) 5135 4111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1299731317/10000000000 : ℝ), (5604651279/10000000000 : ℝ), (643848151/1250000000 : ℝ)] ![(3909266830841/50000000000000 : ℝ), (48519365813119/100000000000000 : ℝ), (1364440640853/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1299731317/10000000000 : ℝ)|^5135 ≤ (3909266830841/50000000000000 : ℝ)^4111
        have hw : |(-1299731317/10000000000 : ℝ)|=(1299731317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5604651279/10000000000 : ℝ)|^5135 ≤ (48519365813119/100000000000000 : ℝ)^4111
        have hw : |(5604651279/10000000000 : ℝ)|=(5604651279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(643848151/1250000000 : ℝ)|^5135 ≤ (1364440640853/3125000000000 : ℝ)^4111
        have hw : |(643848151/1250000000 : ℝ)|=(643848151/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1689_box_13 (p : ℝ) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5415475503/10000000000 : ℝ)*x 0 + (-782211311/5000000000 : ℝ)*x 1 + (321924117/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5415475503/10000000000 : ℝ)^5135 ≤ (9296483726411/20000000000000 : ℝ)^4111 := by
    have hnat : (5415475503 : ℕ)^5135*20000000000000^4111 ≤ 9296483726411^4111*10000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415475503 10000000000 9296483726411 20000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (782211311/5000000000 : ℝ)^5135 ≤ (9855473823249/100000000000000 : ℝ)^4111 := by
    have hnat : (782211311 : ℕ)^5135*100000000000000^4111 ≤ 9855473823249^4111*5000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      782211311 5000000000 9855473823249 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (321924117/625000000 : ℝ)^5135 ≤ (21831053768947/50000000000000 : ℝ)^4111 := by
    have hnat : (321924117 : ℕ)^5135*50000000000000^4111 ≤ 21831053768947^4111*625000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      321924117 625000000 21831053768947 50000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5135/1024 : ℝ)) 5135 4111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5415475503/10000000000 : ℝ), (-782211311/5000000000 : ℝ), (321924117/625000000 : ℝ)] ![(9296483726411/20000000000000 : ℝ), (9855473823249/100000000000000 : ℝ), (21831053768947/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5415475503/10000000000 : ℝ)|^5135 ≤ (9296483726411/20000000000000 : ℝ)^4111
        have hw : |(5415475503/10000000000 : ℝ)|=(5415475503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-782211311/5000000000 : ℝ)|^5135 ≤ (9855473823249/100000000000000 : ℝ)^4111
        have hw : |(-782211311/5000000000 : ℝ)|=(782211311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(321924117/625000000 : ℝ)|^5135 ≤ (21831053768947/50000000000000 : ℝ)^4111
        have hw : |(321924117/625000000 : ℝ)|=(321924117/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1689_box_14 (p : ℝ) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1353869189/2500000000 : ℝ)*x 0 + (2575391909/5000000000 : ℝ)*x 1 + (-782211839/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1353869189/2500000000 : ℝ)^5135 ≤ (11620608016443/25000000000000 : ℝ)^4111 := by
    have hnat : (1353869189 : ℕ)^5135*25000000000000^4111 ≤ 11620608016443^4111*2500000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353869189 2500000000 11620608016443 25000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2575391909/5000000000 : ℝ)^5135 ≤ (4366208578963/10000000000000 : ℝ)^4111 := by
    have hnat : (2575391909 : ℕ)^5135*10000000000000^4111 ≤ 4366208578963^4111*5000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2575391909 5000000000 4366208578963 10000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (782211839/5000000000 : ℝ)^5135 ≤ (9855482132853/100000000000000 : ℝ)^4111 := by
    have hnat : (782211839 : ℕ)^5135*100000000000000^4111 ≤ 9855482132853^4111*5000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      782211839 5000000000 9855482132853 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5135/1024 : ℝ)) 5135 4111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1353869189/2500000000 : ℝ), (2575391909/5000000000 : ℝ), (-782211839/5000000000 : ℝ)] ![(11620608016443/25000000000000 : ℝ), (4366208578963/10000000000000 : ℝ), (9855482132853/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1353869189/2500000000 : ℝ)|^5135 ≤ (11620608016443/25000000000000 : ℝ)^4111
        have hw : |(1353869189/2500000000 : ℝ)|=(1353869189/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2575391909/5000000000 : ℝ)|^5135 ≤ (4366208578963/10000000000000 : ℝ)^4111
        have hw : |(2575391909/5000000000 : ℝ)|=(2575391909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-782211839/5000000000 : ℝ)|^5135 ≤ (9855482132853/100000000000000 : ℝ)^4111
        have hw : |(-782211839/5000000000 : ℝ)|=(782211839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1689_box_15 (p : ℝ) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (146086109/400000000 : ℝ)*x 0 + (2196499903/5000000000 : ℝ)*x 1 + (4392996289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (146086109/400000000 : ℝ)^5135 ≤ (28417456259881/100000000000000 : ℝ)^4111 := by
    have hnat : (146086109 : ℕ)^5135*100000000000000^4111 ≤ 28417456259881^4111*400000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      146086109 400000000 28417456259881 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2196499903/5000000000 : ℝ)^5135 ≤ (35791289753327/100000000000000 : ℝ)^4111 := by
    have hnat : (2196499903 : ℕ)^5135*100000000000000^4111 ≤ 35791289753327^4111*5000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2196499903 5000000000 35791289753327 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4392996289/10000000000 : ℝ)^5135 ≤ (35791253961699/100000000000000 : ℝ)^4111 := by
    have hnat : (4392996289 : ℕ)^5135*100000000000000^4111 ≤ 35791253961699^4111*10000000000^5135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4392996289 10000000000 35791253961699 100000000000000 5135 4111 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5135/1024 : ℝ)) 5135 4111 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(146086109/400000000 : ℝ), (2196499903/5000000000 : ℝ), (4392996289/10000000000 : ℝ)] ![(28417456259881/100000000000000 : ℝ), (35791289753327/100000000000000 : ℝ), (35791253961699/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(146086109/400000000 : ℝ)|^5135 ≤ (28417456259881/100000000000000 : ℝ)^4111
        have hw : |(146086109/400000000 : ℝ)|=(146086109/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2196499903/5000000000 : ℝ)|^5135 ≤ (35791289753327/100000000000000 : ℝ)^4111
        have hw : |(2196499903/5000000000 : ℝ)|=(2196499903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4392996289/10000000000 : ℝ)|^5135 ≤ (35791253961699/100000000000000 : ℝ)^4111
        have hw : |(4392996289/10000000000 : ℝ)|=(4392996289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1689_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (94018711/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17241/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9821/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(13313/20000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(28953/50000 : ℝ) ∧ (8077/10000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (90117/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17241/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9821/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17241/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9821/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17241/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9821/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17241/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9821/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17241/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9821/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17241/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9821/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9821/100000 : ℝ) ^ (5127/1024 : ℝ) ≤ (449633849988887/50000000000000000000 : ℝ) := by
    have hpowers : (9821/100000 : ℝ)^5127 ≤ (449633849988887/50000000000000000000 : ℝ)^1024 := by
      have hnat : (9821 : ℕ)^5127*50000000000000000000^1024 ≤ 449633849988887^1024*100000^5127 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9821 100000 449633849988887 50000000000000000000 5127 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9821/100000 : ℝ)) (X := (449633849988887/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5127 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17241/100000 : ℝ) ^ (5127/1024 : ℝ) ≤ (15051973599065079/100000000000000000000 : ℝ) := by
    have hpowers : (17241/100000 : ℝ)^5127 ≤ (15051973599065079/100000000000000000000 : ℝ)^1024 := by
      have hnat : (17241 : ℕ)^5127*100000000000000000000^1024 ≤ 15051973599065079^1024*100000^5127 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17241 100000 15051973599065079 100000000000000000000 5127 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17241/100000 : ℝ)) (X := (15051973599065079/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5127 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000449633849988887/25000000000000000000 : ℝ) ≤ (2500008980334483/2500000000000000 : ℝ) ^ (5127/1024 : ℝ) := by
    have hpowers : (25000449633849988887/25000000000000000000 : ℝ)^1024 ≤ (2500008980334483/2500000000000000 : ℝ)^5127 := by
      have hnat : (25000449633849988887 : ℕ)^1024*2500000000000000^5127 ≤ 2500008980334483^5127*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000449633849988887 25000000000000000000 2500008980334483 2500000000000000 1024 5127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500008980334483/2500000000000000 : ℝ)) (X := (25000449633849988887/25000000000000000000 : ℝ)) (by norm_num) 5127 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100015951241299042853/100000000000000000000 : ℝ) ≤ (5000159284461083/5000000000000000 : ℝ) ^ (5127/1024 : ℝ) := by
    have hpowers : (100015951241299042853/100000000000000000000 : ℝ)^1024 ≤ (5000159284461083/5000000000000000 : ℝ)^5127 := by
      have hnat : (100015951241299042853 : ℕ)^1024*5000000000000000^5127 ≤ 5000159284461083^5127*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100015951241299042853 100000000000000000000 5000159284461083 5000000000000000 1024 5127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000159284461083/5000000000000000 : ℝ)) (X := (100015951241299042853/100000000000000000000 : ℝ)) (by norm_num) 5127 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50015051973599065079/50000000000000000000 : ℝ) ≤ (12500751520633/12500000000000 : ℝ) ^ (5127/1024 : ℝ) := by
    have hpowers : (50015051973599065079/50000000000000000000 : ℝ)^1024 ≤ (12500751520633/12500000000000 : ℝ)^5127 := by
      have hnat : (50015051973599065079 : ℕ)^1024*12500000000000^5127 ≤ 12500751520633^5127*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015051973599065079 50000000000000000000 12500751520633 12500000000000 1024 5127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12500751520633/12500000000000 : ℝ)) (X := (50015051973599065079/50000000000000000000 : ℝ)) (by norm_num) 5127 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(449633849988887/50000000000000000000 : ℝ) ≤ ((2649811241874211829/2650000000000000000 : ℝ)+2*(141323792117/371000000000000 : ℝ)*(9821/100000 : ℝ))^(5127/1024 : ℝ) := by
    rw [show (2649811241874211829/2650000000000000000 : ℝ)+2*(141323792117/371000000000000 : ℝ)*(9821/100000 : ℝ)=(2500008980334483/2500000000000000 : ℝ) by norm_num, show 1+2*(449633849988887/50000000000000000000 : ℝ)=(25000449633849988887/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15051973599065079/100000000000000000000 : ℝ)+(449633849988887/50000000000000000000 : ℝ) ≤ ((2649811241874211829/2650000000000000000 : ℝ)+(141323792117/371000000000000 : ℝ)*((17241/100000 : ℝ)+(9821/100000 : ℝ)))^(5127/1024 : ℝ) := by
    rw [show (2649811241874211829/2650000000000000000 : ℝ)+(141323792117/371000000000000 : ℝ)*((17241/100000 : ℝ)+(9821/100000 : ℝ))=(5000159284461083/5000000000000000 : ℝ) by norm_num, show 1+(15051973599065079/100000000000000000000 : ℝ)+(449633849988887/50000000000000000000 : ℝ)=(100015951241299042853/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15051973599065079/100000000000000000000 : ℝ) ≤ ((2649811241874211829/2650000000000000000 : ℝ)+2*(141323792117/371000000000000 : ℝ)*(17241/100000 : ℝ))^(5127/1024 : ℝ) := by
    rw [show (2649811241874211829/2650000000000000000 : ℝ)+2*(141323792117/371000000000000 : ℝ)*(17241/100000 : ℝ)=(12500751520633/12500000000000 : ℝ) by norm_num, show 1+2*(15051973599065079/100000000000000000000 : ℝ)=(50015051973599065079/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2649811241874211829/2650000000000000000 : ℝ)*(X 1 0+X 2 0)+(141323792117/371000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5127/1024 : ℝ)) (lo := (9821/100000 : ℝ)) (hi := (17241/100000 : ℝ)) (c := (2649811241874211829/2650000000000000000 : ℝ)) (alpha := (141323792117/371000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2649811241874211829/2650000000000000000 : ℝ)*(X 0 1+X 2 1)+(141323792117/371000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5127/1024 : ℝ)) (lo := (9821/100000 : ℝ)) (hi := (17241/100000 : ℝ)) (c := (2649811241874211829/2650000000000000000 : ℝ)) (alpha := (141323792117/371000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2649811241874211829/2650000000000000000 : ℝ)*(X 0 2+X 1 2)+(141323792117/371000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5127/1024 : ℝ)) (lo := (9821/100000 : ℝ)) (hi := (17241/100000 : ℝ)) (c := (2649811241874211829/2650000000000000000 : ℝ)) (alpha := (141323792117/371000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-577957859/5000000000 : ℝ)*X 0 0+(2714309577/5000000000 : ℝ)*X 0 1+(542861917/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1689_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1306513823/2500000000 : ℝ)*X 1 0+(-144386469/1000000000 : ℝ)*X 1 1+(217144771/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1689_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((26130277/50000000 : ℝ)*X 2 0+(1085723829/2000000000 : ℝ)*X 2 1+(-1443864721/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1689_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4517067933/10000000000 : ℝ)*X 0 0+(3963085003/10000000000 : ℝ)*X 0 1+(3963084991/10000000000 : ℝ)*X 0 2+(4517067933/10000000000 : ℝ)*X 1 0+(3963085003/10000000000 : ℝ)*X 1 1+(3963084991/10000000000 : ℝ)*X 1 2+(4517067933/10000000000 : ℝ)*X 2 0+(3963085003/10000000000 : ℝ)*X 2 1+(3963084991/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1689_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1848519337/10000000000 : ℝ)*X 0 0+(1035219699/2000000000 : ℝ)*X 0 1+(1294024167/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1689_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5398193657/10000000000 : ℝ)*X 1 0+(-97116883/625000000 : ℝ)*X 1 1+(5176098121/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1689_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((10796389/20000000 : ℝ)*X 2 0+(517609693/1000000000 : ℝ)*X 2 1+(-310774117/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1689_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3733659999/10000000000 : ℝ)*X 0 0+(1088481571/2500000000 : ℝ)*X 0 1+(870785087/2000000000 : ℝ)*X 0 2+(3733659999/10000000000 : ℝ)*X 1 0+(1088481571/2500000000 : ℝ)*X 1 1+(870785087/2000000000 : ℝ)*X 1 2+(3733659999/10000000000 : ℝ)*X 2 0+(1088481571/2500000000 : ℝ)*X 2 1+(870785087/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1689_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1699928319/10000000000 : ℝ)*X 0 0+(124771171/250000000 : ℝ)*X 0 1+(1094447003/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1689_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2598166971/5000000000 : ℝ)*X 1 0+(-284805213/2000000000 : ℝ)*X 1 1+(2736117813/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1689_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((649541793/1250000000 : ℝ)*X 2 0+(1368058851/2500000000 : ℝ)*X 2 1+(-1424025821/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1689_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2323675591/5000000000 : ℝ)*X 0 0+(1947700517/5000000000 : ℝ)*X 0 1+(973850127/2500000000 : ℝ)*X 0 2+(2323675591/5000000000 : ℝ)*X 1 0+(1947700517/5000000000 : ℝ)*X 1 1+(973850127/2500000000 : ℝ)*X 1 2+(2323675591/5000000000 : ℝ)*X 2 0+(1947700517/5000000000 : ℝ)*X 2 1+(973850127/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1689_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1299731317/10000000000 : ℝ)*X 0 0+(5604651279/10000000000 : ℝ)*X 0 1+(643848151/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1689_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5415475503/10000000000 : ℝ)*X 1 0+(-782211311/5000000000 : ℝ)*X 1 1+(321924117/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1689_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1353869189/2500000000 : ℝ)*X 2 0+(2575391909/5000000000 : ℝ)*X 2 1+(-782211839/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1689_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((146086109/400000000 : ℝ)*X 0 0+(2196499903/5000000000 : ℝ)*X 0 1+(4392996289/10000000000 : ℝ)*X 0 2+(146086109/400000000 : ℝ)*X 1 0+(2196499903/5000000000 : ℝ)*X 1 1+(4392996289/10000000000 : ℝ)*X 1 2+(146086109/400000000 : ℝ)*X 2 0+(2196499903/5000000000 : ℝ)*X 2 1+(4392996289/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1689_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-13313/20000 : ℝ) ≤ (-77170446720943181134379875417443/115937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (40966989/100000000000000 : ℝ)*(upper1) + (9160333/50000000000000 : ℝ)*(lower2) + (15263951/100000000000000 : ℝ)*(lower5) + (325741734948127/25000000000000 : ℝ)*(major0) + (325741734948127/25000000000000 : ℝ)*(major1) + (325741734948127/25000000000000 : ℝ)*(major2) + (5332351409/100000000000000 : ℝ)*(sp2) + (433220477/25000000000000 : ℝ)*(sp3) + (30237240665697/1562500000000 : ℝ)*(sp4) + (387032195137957/20000000000000 : ℝ)*(sp5) + (96759316302021/5000000000000 : ℝ)*(sp6) + (69292785843769/10000000000000 : ℝ)*(sp7) + (4127893611/50000000000000 : ℝ)*(sp8) + (6136540409/20000000000000 : ℝ)*(sp13) + (346464795659799/50000000000000 : ℝ)*(f.failure) + (193519165839183/10000000000000 : ℝ)*(f.sum) + (15788379297141/4637500000000000000000000000 : ℝ)*base66 + (1696378185761509981/463750000000000000000000000000000 : ℝ)*base67 + (630997252598490019/463750000000000000000000000000000 : ℝ)*base70 + (306842794724009981/463750000000000000000000000000000 : ℝ)*base71 + (5858307332533/2318750000000000000000000000 : ℝ)*base74 + (1974963440375259981/463750000000000000000000000000000 : ℝ)*base75 + (960010916449009981/463750000000000000000000000000000 : ℝ)*base77 + (4199194055117759981/463750000000000000000000000000000 : ℝ)*base79 + (30427296921743/9275000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (3500911/2500000000000000000000 : ℝ)*base90 + (3500911/2500000000000000000000 : ℝ)*base92 + (3500911/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (28953/50000 : ℝ) ≤ (10742067996740332988213578497/18550000000000000000000000000 : ℝ) := by norm_num
    linear_combination (25924547/100000000000000 : ℝ)*(lower0) + (6908441/25000000000000 : ℝ)*(lower1) + (3129011/50000000000000 : ℝ)*(lower2) + (15569/250000000000 : ℝ)*(lower3) + (4631609/100000000000000 : ℝ)*(lower5) + (1401714953675247/100000000000000 : ℝ)*(major0) + (1401714953675247/100000000000000 : ℝ)*(major1) + (1401714953675247/100000000000000 : ℝ)*(major2) + (203868232257557/10000000000000 : ℝ)*(sp0) + (203868232257557/10000000000000 : ℝ)*(sp1) + (995447763683/48828125000 : ℝ)*(sp2) + (46590273783731/6250000000000 : ℝ)*(sp3) + (296783761/100000000000000 : ℝ)*(sp7) + (2651276393/50000000000000 : ℝ)*(sp10) + (745444677323457/100000000000000 : ℝ)*(f.failure) + (203868232257557/10000000000000 : ℝ)*(f.sum) + (69784189058951/18550000000000000000000000000 : ℝ)*base66 + (3908875304101772659/1855000000000000000000000000000000 : ℝ)*base68 + (2661498191353227341/1855000000000000000000000000000000 : ℝ)*base69 + (4422968393873227341/1855000000000000000000000000000000 : ℝ)*base71 + (20415118239701/18550000000000000000000000000 : ℝ)*base74 + (4518158455396772659/1855000000000000000000000000000000 : ℝ)*base76 + (293368260246772659/1855000000000000000000000000000000 : ℝ)*base78 + (5788754087278227341/1855000000000000000000000000000000 : ℝ)*base79 + (17975158749349/18550000000000000000000000000 : ℝ)*base81 + (7203927/5000000000000000000000 : ℝ)*base89 + (7203927/5000000000000000000000 : ℝ)*base91 + (7203927/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (8077/10000 : ℝ) ≤ (749160883216800589476983983893297/927500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (79290307/100000000000000 : ℝ)*(lower3) + (11303067/12500000000000 : ℝ)*(upper4) + (36656309/50000000000000 : ℝ)*(lower5) + (1433231828584589/100000000000000 : ℝ)*(major0) + (1433231828584589/100000000000000 : ℝ)*(major1) + (1433231828584589/100000000000000 : ℝ)*(major2) + (883043473/12500000000000 : ℝ)*(sp0) + (13585912077/25000000000000 : ℝ)*(sp1) + (56671057933/100000000000000 : ℝ)*(sp2) + (15322151499/50000000000000 : ℝ)*(sp3) + (1038663467847779/50000000000000 : ℝ)*(sp8) + (415455931279007/20000000000000 : ℝ)*(sp9) + (207727732898541/10000000000000 : ℝ)*(sp10) + (190543747965663/25000000000000 : ℝ)*(sp11) + (15244112723313/2000000000000 : ℝ)*(f.failure) + (2077334000043343/100000000000000 : ℝ)*(f.sum) + (48268078936713/18550000000000000000000000000 : ℝ)*base65 + (29202289167071972967/1855000000000000000000000000000000 : ℝ)*base67 + (18601149173641972967/1855000000000000000000000000000000 : ℝ)*base69 + (16482500212541972967/1855000000000000000000000000000000 : ℝ)*base71 + (87819508127063/18550000000000000000000000000 : ℝ)*base73 + (3298380542841972967/1855000000000000000000000000000000 : ℝ)*base75 + (11317465417971972967/1855000000000000000000000000000000 : ℝ)*base77 + (12686868992076972967/1855000000000000000000000000000000 : ℝ)*base79 + (64697163814863/18550000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1090457/100000000000000000000 : ℝ)*base90 + (1090457/100000000000000000000 : ℝ)*base92 + (1090457/100000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-90117/100000 : ℝ) ≤ (-14925203960183835413508213104217/16562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (29647079/25000000000000 : ℝ)*(upper1) + (6092301/12500000000000 : ℝ)*(lower2) + (256729813/100000000000000 : ℝ)*(upper3) + (2308179/50000000000000 : ℝ)*(upper5) + (370057195279709/25000000000000 : ℝ)*(major0) + (370057195279709/25000000000000 : ℝ)*(major1) + (370057195279709/25000000000000 : ℝ)*(major2) + (402851191/12500000000000 : ℝ)*(sp4) + (131542238633/100000000000000 : ℝ)*(sp6) + (24405109609/100000000000000 : ℝ)*(sp7) + (1101646722803351/50000000000000 : ℝ)*(sp12) + (220329666841623/10000000000000 : ℝ)*(sp13) + (2203165126177597/100000000000000 : ℝ)*(sp14) + (78717463504679/10000000000000 : ℝ)*(sp15) + (393599520078199/50000000000000 : ℝ)*(f.failure) + (220329666841623/10000000000000 : ℝ)*(f.sum) + (619643291517/1325000000000000000000000000 : ℝ)*base66 + (50544881417072239/66250000000000000000000000000000 : ℝ)*base68 + (166486755970822239/66250000000000000000000000000000 : ℝ)*base70 + (72439702831677761/66250000000000000000000000000000 : ℝ)*base71 + (1878970760071/662500000000000000000000000 : ℝ)*base74 + (389933817870822239/66250000000000000000000000000000 : ℝ)*base76 + (103582581575822239/66250000000000000000000000000000 : ℝ)*base78 + (154735581859572239/66250000000000000000000000000000 : ℝ)*base80 + (889980373377/331250000000000000000000000 : ℝ)*base81 + (10818511/2500000000000000000000 : ℝ)*base90 + (10818511/2500000000000000000000 : ℝ)*base92 + (10818511/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1689_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (94018711/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17241/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9821/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(13313/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(28953/50000 : ℝ) else (8077/10000 : ℝ) ≤ X j i ∧ X j i ≤ (90117/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1689_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1689_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (94018711/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8633/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9801/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(13313/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(28953/50000 : ℝ) else (8077/10000 : ℝ) ≤ X j i ∧ X j i ≤ (90117/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1689_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1689_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1689_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5127/1024 : ℝ) ≤ p) (hpb : p ≤ (5135/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (94018711/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8633/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9801/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(13313/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(28953/50000 : ℝ) else (8077/10000 : ℝ) ≤ X j i ∧ X j i ≤ (90117/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1689_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
