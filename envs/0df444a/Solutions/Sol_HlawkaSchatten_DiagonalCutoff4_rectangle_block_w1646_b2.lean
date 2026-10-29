-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1646_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:11:59.309025+00:00
-- url     : https://prove2.me/submissions/bbb9d09e-0159-47f4-9e10-1d19a064ad36

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
theorem support_rectangle_w1646_s6_0 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-404427863/2500000000 : ℝ)*x 0 + (5448533949/10000000000 : ℝ)*x 1 + (1295950269/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (404427863/2500000000 : ℝ)^4903 ≤ (2500359002377/25000000000000 : ℝ)^3879 := by
    have hnat : (404427863 : ℕ)^4903*25000000000000^3879 ≤ 2500359002377^3879*2500000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      404427863 2500000000 2500359002377 25000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5448533949/10000000000 : ℝ)^4903 ≤ (46415314672093/100000000000000 : ℝ)^3879 := by
    have hnat : (5448533949 : ℕ)^4903*100000000000000^3879 ≤ 46415314672093^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5448533949 10000000000 46415314672093 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1295950269/2500000000 : ℝ)^4903 ≤ (10895812326093/25000000000000 : ℝ)^3879 := by
    have hnat : (1295950269 : ℕ)^4903*25000000000000^3879 ≤ 10895812326093^3879*2500000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295950269 2500000000 10895812326093 25000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-404427863/2500000000 : ℝ), (5448533949/10000000000 : ℝ), (1295950269/2500000000 : ℝ)] ![(2500359002377/25000000000000 : ℝ), (46415314672093/100000000000000 : ℝ), (10895812326093/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-404427863/2500000000 : ℝ)|^4903 ≤ (2500359002377/25000000000000 : ℝ)^3879
        have hw : |(-404427863/2500000000 : ℝ)|=(404427863/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5448533949/10000000000 : ℝ)|^4903 ≤ (46415314672093/100000000000000 : ℝ)^3879
        have hw : |(5448533949/10000000000 : ℝ)|=(5448533949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1295950269/2500000000 : ℝ)|^4903 ≤ (10895812326093/25000000000000 : ℝ)^3879
        have hw : |(1295950269/2500000000 : ℝ)|=(1295950269/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1646_s6_1 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348294289/10000000000 : ℝ)*x 0 + (-1754010033/10000000000 : ℝ)*x 1 + (1036760219/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348294289/10000000000 : ℝ)^4903 ≤ (45338595050607/100000000000000 : ℝ)^3879 := by
    have hnat : (5348294289 : ℕ)^4903*100000000000000^3879 ≤ 45338595050607^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348294289 10000000000 45338595050607 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1754010033/10000000000 : ℝ)^4903 ≤ (5539077716213/50000000000000 : ℝ)^3879 := by
    have hnat : (1754010033 : ℕ)^4903*50000000000000^3879 ≤ 5539077716213^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1754010033 10000000000 5539077716213 50000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1036760219/2000000000 : ℝ)^4903 ≤ (21791624753143/50000000000000 : ℝ)^3879 := by
    have hnat : (1036760219 : ℕ)^4903*50000000000000^3879 ≤ 21791624753143^3879*2000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036760219 2000000000 21791624753143 50000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348294289/10000000000 : ℝ), (-1754010033/10000000000 : ℝ), (1036760219/2000000000 : ℝ)] ![(45338595050607/100000000000000 : ℝ), (5539077716213/50000000000000 : ℝ), (21791624753143/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348294289/10000000000 : ℝ)|^4903 ≤ (45338595050607/100000000000000 : ℝ)^3879
        have hw : |(5348294289/10000000000 : ℝ)|=(5348294289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1754010033/10000000000 : ℝ)|^4903 ≤ (5539077716213/50000000000000 : ℝ)^3879
        have hw : |(-1754010033/10000000000 : ℝ)|=(1754010033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1036760219/2000000000 : ℝ)|^4903 ≤ (21791624753143/50000000000000 : ℝ)^3879
        have hw : |(1036760219/2000000000 : ℝ)|=(1036760219/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1646_s6_2 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348294289/10000000000 : ℝ)*x 0 + (518380109/1000000000 : ℝ)*x 1 + (-1754010039/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348294289/10000000000 : ℝ)^4903 ≤ (45338595050607/100000000000000 : ℝ)^3879 := by
    have hnat : (5348294289 : ℕ)^4903*100000000000000^3879 ≤ 45338595050607^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348294289 10000000000 45338595050607 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (518380109/1000000000 : ℝ)^4903 ≤ (43583249453151/100000000000000 : ℝ)^3879 := by
    have hnat : (518380109 : ℕ)^4903*100000000000000^3879 ≤ 43583249453151^3879*1000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518380109 1000000000 43583249453151 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1754010039/10000000000 : ℝ)^4903 ≤ (443126219213/4000000000000 : ℝ)^3879 := by
    have hnat : (1754010039 : ℕ)^4903*4000000000000^3879 ≤ 443126219213^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1754010039 10000000000 443126219213 4000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348294289/10000000000 : ℝ), (518380109/1000000000 : ℝ), (-1754010039/10000000000 : ℝ)] ![(45338595050607/100000000000000 : ℝ), (43583249453151/100000000000000 : ℝ), (443126219213/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348294289/10000000000 : ℝ)|^4903 ≤ (45338595050607/100000000000000 : ℝ)^3879
        have hw : |(5348294289/10000000000 : ℝ)|=(5348294289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(518380109/1000000000 : ℝ)|^4903 ≤ (43583249453151/100000000000000 : ℝ)^3879
        have hw : |(518380109/1000000000 : ℝ)|=(518380109/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1754010039/10000000000 : ℝ)|^4903 ≤ (443126219213/4000000000000 : ℝ)^3879
        have hw : |(-1754010039/10000000000 : ℝ)|=(1754010039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1646_s6_3 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1045956843/2500000000 : ℝ)*x 0 + (3853209503/10000000000 : ℝ)*x 1 + (906937919/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1045956843/2500000000 : ℝ)^4903 ≤ (33241046813247/100000000000000 : ℝ)^3879 := by
    have hnat : (1045956843 : ℕ)^4903*100000000000000^3879 ≤ 33241046813247^3879*2500000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045956843 2500000000 33241046813247 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3853209503/10000000000 : ℝ)^4903 ≤ (2995613467869/10000000000000 : ℝ)^3879 := by
    have hnat : (3853209503 : ℕ)^4903*10000000000000^3879 ≤ 2995613467869^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3853209503 10000000000 2995613467869 10000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (906937919/2000000000 : ℝ)^4903 ≤ (36802818490683/100000000000000 : ℝ)^3879 := by
    have hnat : (906937919 : ℕ)^4903*100000000000000^3879 ≤ 36802818490683^3879*2000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      906937919 2000000000 36802818490683 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1045956843/2500000000 : ℝ), (3853209503/10000000000 : ℝ), (906937919/2000000000 : ℝ)] ![(33241046813247/100000000000000 : ℝ), (2995613467869/10000000000000 : ℝ), (36802818490683/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1045956843/2500000000 : ℝ)|^4903 ≤ (33241046813247/100000000000000 : ℝ)^3879
        have hw : |(1045956843/2500000000 : ℝ)|=(1045956843/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3853209503/10000000000 : ℝ)|^4903 ≤ (2995613467869/10000000000000 : ℝ)^3879
        have hw : |(3853209503/10000000000 : ℝ)|=(3853209503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(906937919/2000000000 : ℝ)|^4903 ≤ (36802818490683/100000000000000 : ℝ)^3879
        have hw : |(906937919/2000000000 : ℝ)|=(906937919/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1646_s6_4 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-808888449/5000000000 : ℝ)*x 0 + (5185798953/10000000000 : ℝ)*x 1 + (5446514473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (808888449/5000000000 : ℝ)^4903 ≤ (10001947442619/100000000000000 : ℝ)^3879 := by
    have hnat : (808888449 : ℕ)^4903*100000000000000^3879 ≤ 10001947442619^3879*5000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      808888449 5000000000 10001947442619 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5185798953/10000000000 : ℝ)^4903 ≤ (21802240977879/50000000000000 : ℝ)^3879 := by
    have hnat : (5185798953 : ℕ)^4903*50000000000000^3879 ≤ 21802240977879^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5185798953 10000000000 21802240977879 50000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5446514473/10000000000 : ℝ)^4903 ≤ (2319678529201/5000000000000 : ℝ)^3879 := by
    have hnat : (5446514473 : ℕ)^4903*5000000000000^3879 ≤ 2319678529201^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5446514473 10000000000 2319678529201 5000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-808888449/5000000000 : ℝ), (5185798953/10000000000 : ℝ), (5446514473/10000000000 : ℝ)] ![(10001947442619/100000000000000 : ℝ), (21802240977879/50000000000000 : ℝ), (2319678529201/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-808888449/5000000000 : ℝ)|^4903 ≤ (10001947442619/100000000000000 : ℝ)^3879
        have hw : |(-808888449/5000000000 : ℝ)|=(808888449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5185798953/10000000000 : ℝ)|^4903 ≤ (21802240977879/50000000000000 : ℝ)^3879
        have hw : |(5185798953/10000000000 : ℝ)|=(5185798953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5446514473/10000000000 : ℝ)|^4903 ≤ (2319678529201/5000000000000 : ℝ)^3879
        have hw : |(5446514473/10000000000 : ℝ)|=(5446514473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1646_s6_5 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4183994349/10000000000 : ℝ)*x 0 + (2264772833/5000000000 : ℝ)*x 1 + (3858407017/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4183994349/10000000000 : ℝ)^4903 ≤ (8310680923317/25000000000000 : ℝ)^3879 := by
    have hnat : (4183994349 : ℕ)^4903*25000000000000^3879 ≤ 8310680923317^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4183994349 10000000000 8310680923317 25000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2264772833/5000000000 : ℝ)^4903 ≤ (4593757299803/12500000000000 : ℝ)^3879 := by
    have hnat : (2264772833 : ℕ)^4903*12500000000000^3879 ≤ 4593757299803^3879*5000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2264772833 5000000000 4593757299803 12500000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3858407017/10000000000 : ℝ)^4903 ≤ (15003608946911/50000000000000 : ℝ)^3879 := by
    have hnat : (3858407017 : ℕ)^4903*50000000000000^3879 ≤ 15003608946911^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3858407017 10000000000 15003608946911 50000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4183994349/10000000000 : ℝ), (2264772833/5000000000 : ℝ), (3858407017/10000000000 : ℝ)] ![(8310680923317/25000000000000 : ℝ), (4593757299803/12500000000000 : ℝ), (15003608946911/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4183994349/10000000000 : ℝ)|^4903 ≤ (8310680923317/25000000000000 : ℝ)^3879
        have hw : |(4183994349/10000000000 : ℝ)|=(4183994349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2264772833/5000000000 : ℝ)|^4903 ≤ (4593757299803/12500000000000 : ℝ)^3879
        have hw : |(2264772833/5000000000 : ℝ)|=(2264772833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3858407017/10000000000 : ℝ)|^4903 ≤ (15003608946911/50000000000000 : ℝ)^3879
        have hw : |(3858407017/10000000000 : ℝ)|=(3858407017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1646_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11169431/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (651/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10649/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (213/2000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (651/4000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (651/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10649/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (651/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10649/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (651/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10649/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (651/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10649/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (651/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10649/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (651/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10649/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10649/100000 : ℝ) ^ (4899/1024 : ℝ) ≤ (444120319686881/20000000000000000000 : ℝ) := by
    have hpowers : (10649/100000 : ℝ)^4899 ≤ (444120319686881/20000000000000000000 : ℝ)^1024 := by
      have hnat : (10649 : ℕ)^4899*20000000000000000000^1024 ≤ 444120319686881^1024*100000^4899 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10649 100000 444120319686881 20000000000000000000 4899 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10649/100000 : ℝ)) (X := (444120319686881/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4899 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (651/4000 : ℝ) ^ (4899/1024 : ℝ) ≤ (16895644810626587/100000000000000000000 : ℝ) := by
    have hpowers : (651/4000 : ℝ)^4899 ≤ (16895644810626587/100000000000000000000 : ℝ)^1024 := by
      have hnat : (651 : ℕ)^4899*100000000000000000000^1024 ≤ 16895644810626587^1024*4000^4899 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        651 4000 16895644810626587 100000000000000000000 4899 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (651/4000 : ℝ)) (X := (16895644810626587/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4899 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000444120319686881/10000000000000000000 : ℝ) ≤ (10000092829397759/10000000000000000 : ℝ) ^ (4899/1024 : ℝ) := by
    have hpowers : (10000444120319686881/10000000000000000000 : ℝ)^1024 ≤ (10000092829397759/10000000000000000 : ℝ)^4899 := by
      have hnat : (10000444120319686881 : ℕ)^1024*10000000000000000^4899 ≤ 10000092829397759^4899*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000444120319686881 10000000000000000000 10000092829397759 10000000000000000 1024 4899 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000092829397759/10000000000000000 : ℝ)) (X := (10000444120319686881/10000000000000000000 : ℝ)) (by norm_num) 4899 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (781399345675070789/781250000000000000 : ℝ) ≤ (10000399541877273/10000000000000000 : ℝ) ^ (4899/1024 : ℝ) := by
    have hpowers : (781399345675070789/781250000000000000 : ℝ)^1024 ≤ (10000399541877273/10000000000000000 : ℝ)^4899 := by
      have hnat : (781399345675070789 : ℕ)^1024*10000000000000000^4899 ≤ 10000399541877273^4899*781250000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        781399345675070789 781250000000000000 10000399541877273 10000000000000000 1024 4899 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000399541877273/10000000000000000 : ℝ)) (X := (781399345675070789/781250000000000000 : ℝ)) (by norm_num) 4899 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50016895644810626587/50000000000000000000 : ℝ) ≤ (10000706254356787/10000000000000000 : ℝ) ^ (4899/1024 : ℝ) := by
    have hpowers : (50016895644810626587/50000000000000000000 : ℝ)^1024 ≤ (10000706254356787/10000000000000000 : ℝ)^4899 := by
      have hnat : (50016895644810626587 : ℕ)^1024*10000000000000000^4899 ≤ 10000706254356787^4899*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50016895644810626587 50000000000000000000 10000706254356787 10000000000000000 1024 4899 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000706254356787/10000000000000000 : ℝ)) (X := (50016895644810626587/50000000000000000000 : ℝ)) (by norm_num) 4899 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(444120319686881/20000000000000000000 : ℝ) ≤ ((28126994947901551481/28130000000000000000 : ℝ)+2*(153356239757/281300000000000 : ℝ)*(10649/100000 : ℝ))^(4899/1024 : ℝ) := by
    rw [show (28126994947901551481/28130000000000000000 : ℝ)+2*(153356239757/281300000000000 : ℝ)*(10649/100000 : ℝ)=(10000092829397759/10000000000000000 : ℝ) by norm_num, show 1+2*(444120319686881/20000000000000000000 : ℝ)=(10000444120319686881/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16895644810626587/100000000000000000000 : ℝ)+(444120319686881/20000000000000000000 : ℝ) ≤ ((28126994947901551481/28130000000000000000 : ℝ)+(153356239757/281300000000000 : ℝ)*((651/4000 : ℝ)+(10649/100000 : ℝ)))^(4899/1024 : ℝ) := by
    rw [show (28126994947901551481/28130000000000000000 : ℝ)+(153356239757/281300000000000 : ℝ)*((651/4000 : ℝ)+(10649/100000 : ℝ))=(10000399541877273/10000000000000000 : ℝ) by norm_num, show 1+(16895644810626587/100000000000000000000 : ℝ)+(444120319686881/20000000000000000000 : ℝ)=(781399345675070789/781250000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16895644810626587/100000000000000000000 : ℝ) ≤ ((28126994947901551481/28130000000000000000 : ℝ)+2*(153356239757/281300000000000 : ℝ)*(651/4000 : ℝ))^(4899/1024 : ℝ) := by
    rw [show (28126994947901551481/28130000000000000000 : ℝ)+2*(153356239757/281300000000000 : ℝ)*(651/4000 : ℝ)=(10000706254356787/10000000000000000 : ℝ) by norm_num, show 1+2*(16895644810626587/100000000000000000000 : ℝ)=(50016895644810626587/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (28126994947901551481/28130000000000000000 : ℝ)*(X 1 0+X 2 0)+(153356239757/281300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4899/1024 : ℝ)) (lo := (10649/100000 : ℝ)) (hi := (651/4000 : ℝ)) (c := (28126994947901551481/28130000000000000000 : ℝ)) (alpha := (153356239757/281300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (28126994947901551481/28130000000000000000 : ℝ)*(X 0 1+X 2 1)+(153356239757/281300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4899/1024 : ℝ)) (lo := (10649/100000 : ℝ)) (hi := (651/4000 : ℝ)) (c := (28126994947901551481/28130000000000000000 : ℝ)) (alpha := (153356239757/281300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (28126994947901551481/28130000000000000000 : ℝ)*(X 0 2+X 1 2)+(153356239757/281300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4899/1024 : ℝ)) (lo := (10649/100000 : ℝ)) (hi := (651/4000 : ℝ)) (c := (28126994947901551481/28130000000000000000 : ℝ)) (alpha := (153356239757/281300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-404427863/2500000000 : ℝ)*X 0 0+(5448533949/10000000000 : ℝ)*X 0 1+(1295950269/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348294289/10000000000 : ℝ)*X 1 0+(-1754010033/10000000000 : ℝ)*X 1 1+(1036760219/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348294289/10000000000 : ℝ)*X 2 0+(518380109/1000000000 : ℝ)*X 2 1+(-1754010039/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1045956843/2500000000 : ℝ)*X 0 0+(3853209503/10000000000 : ℝ)*X 0 1+(906937919/2000000000 : ℝ)*X 0 2+(1045956843/2500000000 : ℝ)*X 1 0+(3853209503/10000000000 : ℝ)*X 1 1+(906937919/2000000000 : ℝ)*X 1 2+(1045956843/2500000000 : ℝ)*X 2 0+(3853209503/10000000000 : ℝ)*X 2 1+(906937919/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-808888449/5000000000 : ℝ)*X 0 0+(5185798953/10000000000 : ℝ)*X 0 1+(5446514473/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4183994349/10000000000 : ℝ)*X 0 0+(2264772833/5000000000 : ℝ)*X 0 1+(3858407017/10000000000 : ℝ)*X 0 2+(4183994349/10000000000 : ℝ)*X 1 0+(2264772833/5000000000 : ℝ)*X 1 1+(3858407017/10000000000 : ℝ)*X 1 2+(4183994349/10000000000 : ℝ)*X 2 0+(2264772833/5000000000 : ℝ)*X 2 1+(3858407017/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_s6_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1655242846010227105530251643/703250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (380646539/100000000000000 : ℝ)*(base19) + (35434169/10000000000000 : ℝ)*(base23) + (109911/781250000000 : ℝ)*(lower2) + (33132327/50000000000000 : ℝ)*(upper3) + (21224407/50000000000000 : ℝ)*(upper5) + (2622400255590401/100000000000000 : ℝ)*(major0) + (2622400255590401/100000000000000 : ℝ)*(major1) + (2622400255590401/100000000000000 : ℝ)*(major2) + (1888698812118111/50000000000000 : ℝ)*(sp0) + (944350493168257/25000000000000 : ℝ)*(sp1) + (3777401998977877/100000000000000 : ℝ)*(sp2) + (1467396048153417/100000000000000 : ℝ)*(sp3) + (945816669/20000000000000 : ℝ)*(sp4) + (1015625493/50000000000000 : ℝ)*(sp5) + (366849519851101/25000000000000 : ℝ)*(f.failure) + (1888701176659783/50000000000000 : ℝ)*(f.sum) + (100710334641097/14065000000000000000000000000 : ℝ)*base65 + (7575550592763366119/2813000000000000000000000000000000 : ℝ)*base68 + (257263981535366119/2813000000000000000000000000000000 : ℝ)*base70 + (19595663984483366119/2813000000000000000000000000000000 : ℝ)*base72 + (52774850713931/7032500000000000000000000000 : ℝ)*base73 + (3186302028225633881/2813000000000000000000000000000000 : ℝ)*base75 + (1816680790976366119/2813000000000000000000000000000000 : ℝ)*base78 + (1289191717434366119/2813000000000000000000000000000000 : ℝ)*base80 + (56787764587747/14065000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (1331031/156250000000000000000 : ℝ)*base89 + (1331031/156250000000000000000 : ℝ)*base91 + (1331031/156250000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1646_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11169431/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (651/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10649/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (213/2000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (651/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1646_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1646_box_0 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1358286303/10000000000 : ℝ)*x 0 + (1352262411/2500000000 : ℝ)*x 1 + (540904879/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1358286303/10000000000 : ℝ)^4903 ≤ (1002359613177/12500000000000 : ℝ)^3879 := by
    have hnat : (1358286303 : ℕ)^4903*12500000000000^3879 ≤ 1002359613177^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358286303 10000000000 1002359613177 12500000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352262411/2500000000 : ℝ)^4903 ≤ (45990566130089/100000000000000 : ℝ)^3879 := by
    have hnat : (1352262411 : ℕ)^4903*100000000000000^3879 ≤ 45990566130089^3879*2500000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352262411 2500000000 45990566130089 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (540904879/1000000000 : ℝ)^4903 ≤ (9198111390419/20000000000000 : ℝ)^3879 := by
    have hnat : (540904879 : ℕ)^4903*20000000000000^3879 ≤ 9198111390419^3879*1000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540904879 1000000000 9198111390419 20000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1358286303/10000000000 : ℝ), (1352262411/2500000000 : ℝ), (540904879/1000000000 : ℝ)] ![(1002359613177/12500000000000 : ℝ), (45990566130089/100000000000000 : ℝ), (9198111390419/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1358286303/10000000000 : ℝ)|^4903 ≤ (1002359613177/12500000000000 : ℝ)^3879
        have hw : |(-1358286303/10000000000 : ℝ)|=(1358286303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352262411/2500000000 : ℝ)|^4903 ≤ (45990566130089/100000000000000 : ℝ)^3879
        have hw : |(1352262411/2500000000 : ℝ)|=(1352262411/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(540904879/1000000000 : ℝ)|^4903 ≤ (9198111390419/20000000000000 : ℝ)^3879
        have hw : |(540904879/1000000000 : ℝ)|=(540904879/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1646_box_1 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1050227119/2000000000 : ℝ)*x 0 + (-1580225163/10000000000 : ℝ)*x 1 + (54090491/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050227119/2000000000 : ℝ)^4903 ≤ (44300040664877/100000000000000 : ℝ)^3879 := by
    have hnat : (1050227119 : ℕ)^4903*100000000000000^3879 ≤ 44300040664877^3879*2000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050227119 2000000000 44300040664877 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1580225163/10000000000 : ℝ)^4903 ≤ (1941879806253/20000000000000 : ℝ)^3879 := by
    have hnat : (1580225163 : ℕ)^4903*20000000000000^3879 ≤ 1941879806253^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1580225163 10000000000 1941879806253 20000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (54090491/100000000 : ℝ)^4903 ≤ (9198112056737/20000000000000 : ℝ)^3879 := by
    have hnat : (54090491 : ℕ)^4903*20000000000000^3879 ≤ 9198112056737^3879*100000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54090491 100000000 9198112056737 20000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050227119/2000000000 : ℝ), (-1580225163/10000000000 : ℝ), (54090491/100000000 : ℝ)] ![(44300040664877/100000000000000 : ℝ), (1941879806253/20000000000000 : ℝ), (9198112056737/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050227119/2000000000 : ℝ)|^4903 ≤ (44300040664877/100000000000000 : ℝ)^3879
        have hw : |(1050227119/2000000000 : ℝ)|=(1050227119/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1580225163/10000000000 : ℝ)|^4903 ≤ (1941879806253/20000000000000 : ℝ)^3879
        have hw : |(-1580225163/10000000000 : ℝ)|=(1580225163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(54090491/100000000 : ℝ)|^4903 ≤ (9198112056737/20000000000000 : ℝ)^3879
        have hw : |(54090491/100000000 : ℝ)|=(54090491/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1646_box_2 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1050227141/2000000000 : ℝ)*x 0 + (2704524617/5000000000 : ℝ)*x 1 + (-1580224827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050227141/2000000000 : ℝ)^4903 ≤ (11075010459461/25000000000000 : ℝ)^3879 := by
    have hnat : (1050227141 : ℕ)^4903*25000000000000^3879 ≤ 11075010459461^3879*2000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050227141 2000000000 11075010459461 25000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2704524617/5000000000 : ℝ)^4903 ≤ (2874410107737/6250000000000 : ℝ)^3879 := by
    have hnat : (2704524617 : ℕ)^4903*6250000000000^3879 ≤ 2874410107737^3879*5000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704524617 5000000000 2874410107737 6250000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1580224827/10000000000 : ℝ)^4903 ≤ (485469821089/5000000000000 : ℝ)^3879 := by
    have hnat : (1580224827 : ℕ)^4903*5000000000000^3879 ≤ 485469821089^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1580224827 10000000000 485469821089 5000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050227141/2000000000 : ℝ), (2704524617/5000000000 : ℝ), (-1580224827/10000000000 : ℝ)] ![(11075010459461/25000000000000 : ℝ), (2874410107737/6250000000000 : ℝ), (485469821089/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050227141/2000000000 : ℝ)|^4903 ≤ (11075010459461/25000000000000 : ℝ)^3879
        have hw : |(1050227141/2000000000 : ℝ)|=(1050227141/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2704524617/5000000000 : ℝ)|^4903 ≤ (2874410107737/6250000000000 : ℝ)^3879
        have hw : |(2704524617/5000000000 : ℝ)|=(2704524617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1580224827/10000000000 : ℝ)|^4903 ≤ (485469821089/5000000000000 : ℝ)^3879
        have hw : |(-1580224827/10000000000 : ℝ)|=(1580224827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1646_box_3 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4460893173/10000000000 : ℝ)*x 0 + (1014344687/2500000000 : ℝ)*x 1 + (4057378891/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4460893173/10000000000 : ℝ)^4903 ≤ (36047424892861/100000000000000 : ℝ)^3879 := by
    have hnat : (4460893173 : ℕ)^4903*100000000000000^3879 ≤ 36047424892861^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4460893173 10000000000 36047424892861 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1014344687/2500000000 : ℝ)^4903 ≤ (3997035854127/12500000000000 : ℝ)^3879 := by
    have hnat : (1014344687 : ℕ)^4903*12500000000000^3879 ≤ 3997035854127^3879*2500000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1014344687 2500000000 3997035854127 12500000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4057378891/10000000000 : ℝ)^4903 ≤ (3197628825751/10000000000000 : ℝ)^3879 := by
    have hnat : (4057378891 : ℕ)^4903*10000000000000^3879 ≤ 3197628825751^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4057378891 10000000000 3197628825751 10000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4460893173/10000000000 : ℝ), (1014344687/2500000000 : ℝ), (4057378891/10000000000 : ℝ)] ![(36047424892861/100000000000000 : ℝ), (3997035854127/12500000000000 : ℝ), (3197628825751/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4460893173/10000000000 : ℝ)|^4903 ≤ (36047424892861/100000000000000 : ℝ)^3879
        have hw : |(4460893173/10000000000 : ℝ)|=(4460893173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1014344687/2500000000 : ℝ)|^4903 ≤ (3997035854127/12500000000000 : ℝ)^3879
        have hw : |(1014344687/2500000000 : ℝ)|=(1014344687/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4057378891/10000000000 : ℝ)|^4903 ≤ (3197628825751/10000000000000 : ℝ)^3879
        have hw : |(4057378891/10000000000 : ℝ)|=(4057378891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1646_box_4 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-943873251/5000000000 : ℝ)*x 0 + (5215634907/10000000000 : ℝ)*x 1 + (1043127011/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (943873251/5000000000 : ℝ)^4903 ≤ (1215635172359/10000000000000 : ℝ)^3879 := by
    have hnat : (943873251 : ℕ)^4903*10000000000000^3879 ≤ 1215635172359^3879*5000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      943873251 5000000000 1215635172359 10000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5215634907/10000000000 : ℝ)^4903 ≤ (43921823342353/100000000000000 : ℝ)^3879 := by
    have hnat : (5215634907 : ℕ)^4903*100000000000000^3879 ≤ 43921823342353^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215634907 10000000000 43921823342353 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043127011/2000000000 : ℝ)^4903 ≤ (43921824917703/100000000000000 : ℝ)^3879 := by
    have hnat : (1043127011 : ℕ)^4903*100000000000000^3879 ≤ 43921824917703^3879*2000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043127011 2000000000 43921824917703 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-943873251/5000000000 : ℝ), (5215634907/10000000000 : ℝ), (1043127011/2000000000 : ℝ)] ![(1215635172359/10000000000000 : ℝ), (43921823342353/100000000000000 : ℝ), (43921824917703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-943873251/5000000000 : ℝ)|^4903 ≤ (1215635172359/10000000000000 : ℝ)^3879
        have hw : |(-943873251/5000000000 : ℝ)|=(943873251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5215634907/10000000000 : ℝ)|^4903 ≤ (43921823342353/100000000000000 : ℝ)^3879
        have hw : |(5215634907/10000000000 : ℝ)|=(5215634907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043127011/2000000000 : ℝ)|^4903 ≤ (43921824917703/100000000000000 : ℝ)^3879
        have hw : |(1043127011/2000000000 : ℝ)|=(1043127011/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1646_box_5 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5383962117/10000000000 : ℝ)*x 0 + (-1663052979/10000000000 : ℝ)*x 1 + (1043127009/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5383962117/10000000000 : ℝ)^4903 ≤ (45721114075917/100000000000000 : ℝ)^3879 := by
    have hnat : (5383962117 : ℕ)^4903*100000000000000^3879 ≤ 45721114075917^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5383962117 10000000000 45721114075917 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1663052979/10000000000 : ℝ)^4903 ≤ (5178530551031/50000000000000 : ℝ)^3879 := by
    have hnat : (1663052979 : ℕ)^4903*50000000000000^3879 ≤ 5178530551031^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1663052979 10000000000 5178530551031 50000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043127009/2000000000 : ℝ)^4903 ≤ (2196091240563/5000000000000 : ℝ)^3879 := by
    have hnat : (1043127009 : ℕ)^4903*5000000000000^3879 ≤ 2196091240563^3879*2000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043127009 2000000000 2196091240563 5000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5383962117/10000000000 : ℝ), (-1663052979/10000000000 : ℝ), (1043127009/2000000000 : ℝ)] ![(45721114075917/100000000000000 : ℝ), (5178530551031/50000000000000 : ℝ), (2196091240563/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5383962117/10000000000 : ℝ)|^4903 ≤ (45721114075917/100000000000000 : ℝ)^3879
        have hw : |(5383962117/10000000000 : ℝ)|=(5383962117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1663052979/10000000000 : ℝ)|^4903 ≤ (5178530551031/50000000000000 : ℝ)^3879
        have hw : |(-1663052979/10000000000 : ℝ)|=(1663052979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043127009/2000000000 : ℝ)|^4903 ≤ (2196091240563/5000000000000 : ℝ)^3879
        have hw : |(1043127009/2000000000 : ℝ)|=(1043127009/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1646_box_6 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5383962099/10000000000 : ℝ)*x 0 + (208625409/400000000 : ℝ)*x 1 + (-1663052761/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5383962099/10000000000 : ℝ)^4903 ≤ (45721113882707/100000000000000 : ℝ)^3879 := by
    have hnat : (5383962099 : ℕ)^4903*100000000000000^3879 ≤ 45721113882707^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5383962099 10000000000 45721113882707 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (208625409/400000000 : ℝ)^4903 ≤ (21960913363613/50000000000000 : ℝ)^3879 := by
    have hnat : (208625409 : ℕ)^4903*50000000000000^3879 ≤ 21960913363613^3879*400000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208625409 400000000 21960913363613 50000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1663052761/10000000000 : ℝ)^4903 ≤ (323658105813/3125000000000 : ℝ)^3879 := by
    have hnat : (1663052761 : ℕ)^4903*3125000000000^3879 ≤ 323658105813^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1663052761 10000000000 323658105813 3125000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5383962099/10000000000 : ℝ), (208625409/400000000 : ℝ), (-1663052761/10000000000 : ℝ)] ![(45721113882707/100000000000000 : ℝ), (21960913363613/50000000000000 : ℝ), (323658105813/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5383962099/10000000000 : ℝ)|^4903 ≤ (45721113882707/100000000000000 : ℝ)^3879
        have hw : |(5383962099/10000000000 : ℝ)|=(5383962099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(208625409/400000000 : ℝ)|^4903 ≤ (21960913363613/50000000000000 : ℝ)^3879
        have hw : |(208625409/400000000 : ℝ)|=(208625409/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1663052761/10000000000 : ℝ)|^4903 ≤ (323658105813/3125000000000 : ℝ)^3879
        have hw : |(-1663052761/10000000000 : ℝ)|=(1663052761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1646_box_7 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (390030881/1000000000 : ℝ)*x 0 + (4337344343/10000000000 : ℝ)*x 1 + (433734443/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (390030881/1000000000 : ℝ)^4903 ≤ (152098536731/500000000000 : ℝ)^3879 := by
    have hnat : (390030881 : ℕ)^4903*500000000000^3879 ≤ 152098536731^3879*1000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      390030881 1000000000 152098536731 500000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4337344343/10000000000 : ℝ)^4903 ≤ (17395072938623/50000000000000 : ℝ)^3879 := by
    have hnat : (4337344343 : ℕ)^4903*50000000000000^3879 ≤ 17395072938623^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4337344343 10000000000 17395072938623 50000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (433734443/1000000000 : ℝ)^4903 ≤ (34790146759297/100000000000000 : ℝ)^3879 := by
    have hnat : (433734443 : ℕ)^4903*100000000000000^3879 ≤ 34790146759297^3879*1000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433734443 1000000000 34790146759297 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(390030881/1000000000 : ℝ), (4337344343/10000000000 : ℝ), (433734443/1000000000 : ℝ)] ![(152098536731/500000000000 : ℝ), (17395072938623/50000000000000 : ℝ), (34790146759297/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(390030881/1000000000 : ℝ)|^4903 ≤ (152098536731/500000000000 : ℝ)^3879
        have hw : |(390030881/1000000000 : ℝ)|=(390030881/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4337344343/10000000000 : ℝ)|^4903 ≤ (17395072938623/50000000000000 : ℝ)^3879
        have hw : |(4337344343/10000000000 : ℝ)|=(4337344343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(433734443/1000000000 : ℝ)|^4903 ≤ (34790146759297/100000000000000 : ℝ)^3879
        have hw : |(433734443/1000000000 : ℝ)|=(433734443/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1646_box_8 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1774839599/10000000000 : ℝ)*x 0 + (5076625991/10000000000 : ℝ)*x 1 + (217542167/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1774839599/10000000000 : ℝ)^4903 ≤ (11244702102917/100000000000000 : ℝ)^3879 := by
    have hnat : (1774839599 : ℕ)^4903*100000000000000^3879 ≤ 11244702102917^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1774839599 10000000000 11244702102917 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5076625991/10000000000 : ℝ)^4903 ≤ (8489483326359/20000000000000 : ℝ)^3879 := by
    have hnat : (5076625991 : ℕ)^4903*20000000000000^3879 ≤ 8489483326359^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5076625991 10000000000 8489483326359 20000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (217542167/400000000 : ℝ)^4903 ≤ (46307881252047/100000000000000 : ℝ)^3879 := by
    have hnat : (217542167 : ℕ)^4903*100000000000000^3879 ≤ 46307881252047^3879*400000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217542167 400000000 46307881252047 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1774839599/10000000000 : ℝ), (5076625991/10000000000 : ℝ), (217542167/400000000 : ℝ)] ![(11244702102917/100000000000000 : ℝ), (8489483326359/20000000000000 : ℝ), (46307881252047/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1774839599/10000000000 : ℝ)|^4903 ≤ (11244702102917/100000000000000 : ℝ)^3879
        have hw : |(-1774839599/10000000000 : ℝ)|=(1774839599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5076625991/10000000000 : ℝ)|^4903 ≤ (8489483326359/20000000000000 : ℝ)^3879
        have hw : |(5076625991/10000000000 : ℝ)|=(5076625991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(217542167/400000000 : ℝ)|^4903 ≤ (46307881252047/100000000000000 : ℝ)^3879
        have hw : |(217542167/400000000 : ℝ)|=(217542167/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1646_box_9 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1046174711/2000000000 : ℝ)*x 0 + (-1567158277/10000000000 : ℝ)*x 1 + (5438554219/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1046174711/2000000000 : ℝ)^4903 ≤ (22042044957003/50000000000000 : ℝ)^3879 := by
    have hnat : (1046174711 : ℕ)^4903*50000000000000^3879 ≤ 22042044957003^3879*2000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046174711 2000000000 22042044957003 50000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1567158277/10000000000 : ℝ)^4903 ≤ (960802835181/10000000000000 : ℝ)^3879 := by
    have hnat : (1567158277 : ℕ)^4903*10000000000000^3879 ≤ 960802835181^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1567158277 10000000000 960802835181 10000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5438554219/10000000000 : ℝ)^4903 ≤ (46307881725597/100000000000000 : ℝ)^3879 := by
    have hnat : (5438554219 : ℕ)^4903*100000000000000^3879 ≤ 46307881725597^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438554219 10000000000 46307881725597 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1046174711/2000000000 : ℝ), (-1567158277/10000000000 : ℝ), (5438554219/10000000000 : ℝ)] ![(22042044957003/50000000000000 : ℝ), (960802835181/10000000000000 : ℝ), (46307881725597/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1046174711/2000000000 : ℝ)|^4903 ≤ (22042044957003/50000000000000 : ℝ)^3879
        have hw : |(1046174711/2000000000 : ℝ)|=(1046174711/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1567158277/10000000000 : ℝ)|^4903 ≤ (960802835181/10000000000000 : ℝ)^3879
        have hw : |(-1567158277/10000000000 : ℝ)|=(1567158277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5438554219/10000000000 : ℝ)|^4903 ≤ (46307881725597/100000000000000 : ℝ)^3879
        have hw : |(5438554219/10000000000 : ℝ)|=(5438554219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1646_box_10 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5230872833/10000000000 : ℝ)*x 0 + (679819359/1250000000 : ℝ)*x 1 + (-783579181/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5230872833/10000000000 : ℝ)^4903 ≤ (44084082222933/100000000000000 : ℝ)^3879 := by
    have hnat : (5230872833 : ℕ)^4903*100000000000000^3879 ≤ 44084082222933^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230872833 10000000000 44084082222933 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (679819359/1250000000 : ℝ)^4903 ≤ (11576972188379/25000000000000 : ℝ)^3879 := by
    have hnat : (679819359 : ℕ)^4903*25000000000000^3879 ≤ 11576972188379^3879*1250000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      679819359 1250000000 11576972188379 25000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (783579181/5000000000 : ℝ)^4903 ≤ (4804014505251/50000000000000 : ℝ)^3879 := by
    have hnat : (783579181 : ℕ)^4903*50000000000000^3879 ≤ 4804014505251^3879*5000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      783579181 5000000000 4804014505251 50000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5230872833/10000000000 : ℝ), (679819359/1250000000 : ℝ), (-783579181/5000000000 : ℝ)] ![(44084082222933/100000000000000 : ℝ), (11576972188379/25000000000000 : ℝ), (4804014505251/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5230872833/10000000000 : ℝ)|^4903 ≤ (44084082222933/100000000000000 : ℝ)^3879
        have hw : |(5230872833/10000000000 : ℝ)|=(5230872833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(679819359/1250000000 : ℝ)|^4903 ≤ (11576972188379/25000000000000 : ℝ)^3879
        have hw : |(679819359/1250000000 : ℝ)|=(679819359/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-783579181/5000000000 : ℝ)|^4903 ≤ (4804014505251/50000000000000 : ℝ)^3879
        have hw : |(-783579181/5000000000 : ℝ)|=(783579181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1646_box_11 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4544028567/10000000000 : ℝ)*x 0 + (4014593677/10000000000 : ℝ)*x 1 + (501824171/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4544028567/10000000000 : ℝ)^4903 ≤ (36898646547589/100000000000000 : ℝ)^3879 := by
    have hnat : (4544028567 : ℕ)^4903*100000000000000^3879 ≤ 36898646547589^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4544028567 10000000000 36898646547589 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4014593677/10000000000 : ℝ)^4903 ≤ (7887669562327/25000000000000 : ℝ)^3879 := by
    have hnat : (4014593677 : ℕ)^4903*25000000000000^3879 ≤ 7887669562327^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4014593677 10000000000 7887669562327 25000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (501824171/1250000000 : ℝ)^4903 ≤ (985958599369/3125000000000 : ℝ)^3879 := by
    have hnat : (501824171 : ℕ)^4903*3125000000000^3879 ≤ 985958599369^3879*1250000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      501824171 1250000000 985958599369 3125000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4544028567/10000000000 : ℝ), (4014593677/10000000000 : ℝ), (501824171/1250000000 : ℝ)] ![(36898646547589/100000000000000 : ℝ), (7887669562327/25000000000000 : ℝ), (985958599369/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4544028567/10000000000 : ℝ)|^4903 ≤ (36898646547589/100000000000000 : ℝ)^3879
        have hw : |(4544028567/10000000000 : ℝ)|=(4544028567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4014593677/10000000000 : ℝ)|^4903 ≤ (7887669562327/25000000000000 : ℝ)^3879
        have hw : |(4014593677/10000000000 : ℝ)|=(4014593677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(501824171/1250000000 : ℝ)|^4903 ≤ (985958599369/3125000000000 : ℝ)^3879
        have hw : |(501824171/1250000000 : ℝ)|=(501824171/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1646_box_12 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1469477491/10000000000 : ℝ)*x 0 + (2771357373/5000000000 : ℝ)*x 1 + (2597903431/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1469477491/10000000000 : ℝ)^4903 ≤ (8857394275139/100000000000000 : ℝ)^3879 := by
    have hnat : (1469477491 : ℕ)^4903*100000000000000^3879 ≤ 8857394275139^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1469477491 10000000000 8857394275139 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2771357373/5000000000 : ℝ)^4903 ≤ (23715865571267/50000000000000 : ℝ)^3879 := by
    have hnat : (2771357373 : ℕ)^4903*50000000000000^3879 ≤ 23715865571267^3879*5000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2771357373 5000000000 23715865571267 50000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2597903431/5000000000 : ℝ)^4903 ≤ (43710874569363/100000000000000 : ℝ)^3879 := by
    have hnat : (2597903431 : ℕ)^4903*100000000000000^3879 ≤ 43710874569363^3879*5000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2597903431 5000000000 43710874569363 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1469477491/10000000000 : ℝ), (2771357373/5000000000 : ℝ), (2597903431/5000000000 : ℝ)] ![(8857394275139/100000000000000 : ℝ), (23715865571267/50000000000000 : ℝ), (43710874569363/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1469477491/10000000000 : ℝ)|^4903 ≤ (8857394275139/100000000000000 : ℝ)^3879
        have hw : |(-1469477491/10000000000 : ℝ)|=(1469477491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2771357373/5000000000 : ℝ)|^4903 ≤ (23715865571267/50000000000000 : ℝ)^3879
        have hw : |(2771357373/5000000000 : ℝ)|=(2771357373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2597903431/5000000000 : ℝ)|^4903 ≤ (43710874569363/100000000000000 : ℝ)^3879
        have hw : |(2597903431/5000000000 : ℝ)|=(2597903431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1646_box_13 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (269879429/500000000 : ℝ)*x 0 + (-835629161/5000000000 : ℝ)*x 1 + (5195807229/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (269879429/500000000 : ℝ)^4903 ≤ (9173485557833/20000000000000 : ℝ)^3879 := by
    have hnat : (269879429 : ℕ)^4903*20000000000000^3879 ≤ 9173485557833^3879*500000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269879429 500000000 9173485557833 20000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (835629161/5000000000 : ℝ)^4903 ≤ (10421693713551/100000000000000 : ℝ)^3879 := by
    have hnat : (835629161 : ℕ)^4903*100000000000000^3879 ≤ 10421693713551^3879*5000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      835629161 5000000000 10421693713551 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5195807229/10000000000 : ℝ)^4903 ≤ (43710878471879/100000000000000 : ℝ)^3879 := by
    have hnat : (5195807229 : ℕ)^4903*100000000000000^3879 ≤ 43710878471879^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195807229 10000000000 43710878471879 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(269879429/500000000 : ℝ), (-835629161/5000000000 : ℝ), (5195807229/10000000000 : ℝ)] ![(9173485557833/20000000000000 : ℝ), (10421693713551/100000000000000 : ℝ), (43710878471879/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(269879429/500000000 : ℝ)|^4903 ≤ (9173485557833/20000000000000 : ℝ)^3879
        have hw : |(269879429/500000000 : ℝ)|=(269879429/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-835629161/5000000000 : ℝ)|^4903 ≤ (10421693713551/100000000000000 : ℝ)^3879
        have hw : |(-835629161/5000000000 : ℝ)|=(835629161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5195807229/10000000000 : ℝ)|^4903 ≤ (43710878471879/100000000000000 : ℝ)^3879
        have hw : |(5195807229/10000000000 : ℝ)|=(5195807229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1646_box_14 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1079517619/2000000000 : ℝ)*x 0 + (5195807613/10000000000 : ℝ)*x 1 + (-835629233/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079517619/2000000000 : ℝ)^4903 ≤ (11466855644939/25000000000000 : ℝ)^3879 := by
    have hnat : (1079517619 : ℕ)^4903*25000000000000^3879 ≤ 11466855644939^3879*2000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079517619 2000000000 11466855644939 25000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5195807613/10000000000 : ℝ)^4903 ≤ (21855441277583/50000000000000 : ℝ)^3879 := by
    have hnat : (5195807613 : ℕ)^4903*50000000000000^3879 ≤ 21855441277583^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195807613 10000000000 21855441277583 50000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (835629233/5000000000 : ℝ)^4903 ≤ (10421694848561/100000000000000 : ℝ)^3879 := by
    have hnat : (835629233 : ℕ)^4903*100000000000000^3879 ≤ 10421694848561^3879*5000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      835629233 5000000000 10421694848561 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1079517619/2000000000 : ℝ), (5195807613/10000000000 : ℝ), (-835629233/5000000000 : ℝ)] ![(11466855644939/25000000000000 : ℝ), (21855441277583/50000000000000 : ℝ), (10421694848561/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1079517619/2000000000 : ℝ)|^4903 ≤ (11466855644939/25000000000000 : ℝ)^3879
        have hw : |(1079517619/2000000000 : ℝ)|=(1079517619/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5195807613/10000000000 : ℝ)|^4903 ≤ (21855441277583/50000000000000 : ℝ)^3879
        have hw : |(5195807613/10000000000 : ℝ)|=(5195807613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-835629233/5000000000 : ℝ)|^4903 ≤ (10421694848561/100000000000000 : ℝ)^3879
        have hw : |(-835629233/5000000000 : ℝ)|=(835629233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1646_box_15 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3841213241/10000000000 : ℝ)*x 0 + (4365991871/10000000000 : ℝ)*x 1 + (4365993403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3841213241/10000000000 : ℝ)^4903 ≤ (14919150075221/50000000000000 : ℝ)^3879 := by
    have hnat : (3841213241 : ℕ)^4903*50000000000000^3879 ≤ 14919150075221^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3841213241 10000000000 14919150075221 50000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4365991871/10000000000 : ℝ)^4903 ≤ (35080842142709/100000000000000 : ℝ)^3879 := by
    have hnat : (4365991871 : ℕ)^4903*100000000000000^3879 ≤ 35080842142709^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4365991871 10000000000 35080842142709 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4365993403/10000000000 : ℝ)^4903 ≤ (7016171540387/20000000000000 : ℝ)^3879 := by
    have hnat : (4365993403 : ℕ)^4903*20000000000000^3879 ≤ 7016171540387^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4365993403 10000000000 7016171540387 20000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3841213241/10000000000 : ℝ), (4365991871/10000000000 : ℝ), (4365993403/10000000000 : ℝ)] ![(14919150075221/50000000000000 : ℝ), (35080842142709/100000000000000 : ℝ), (7016171540387/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3841213241/10000000000 : ℝ)|^4903 ≤ (14919150075221/50000000000000 : ℝ)^3879
        have hw : |(3841213241/10000000000 : ℝ)|=(3841213241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4365991871/10000000000 : ℝ)|^4903 ≤ (35080842142709/100000000000000 : ℝ)^3879
        have hw : |(4365991871/10000000000 : ℝ)|=(4365991871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4365993403/10000000000 : ℝ)|^4903 ≤ (7016171540387/20000000000000 : ℝ)^3879
        have hw : |(4365993403/10000000000 : ℝ)|=(4365993403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1646_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11169431/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (651/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (213/2000 : ℝ)*pair X i i ≤ pair X i h) :
    -(65051/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58583/100000 : ℝ) ∧ (81123/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (11023/12500 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (651/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (213/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (651/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (213/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (651/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (213/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (651/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (213/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (651/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (213/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (651/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (213/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (213/2000 : ℝ) ^ (4899/1024 : ℝ) ≤ (555399851313703/25000000000000000000 : ℝ) := by
    have hpowers : (213/2000 : ℝ)^4899 ≤ (555399851313703/25000000000000000000 : ℝ)^1024 := by
      have hnat : (213 : ℕ)^4899*25000000000000000000^1024 ≤ 555399851313703^1024*2000^4899 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        213 2000 555399851313703 25000000000000000000 4899 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (213/2000 : ℝ)) (X := (555399851313703/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4899 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (651/4000 : ℝ) ^ (4899/1024 : ℝ) ≤ (16895644810626587/100000000000000000000 : ℝ) := by
    have hpowers : (651/4000 : ℝ)^4899 ≤ (16895644810626587/100000000000000000000 : ℝ)^1024 := by
      have hnat : (651 : ℕ)^4899*100000000000000000000^1024 ≤ 16895644810626587^1024*4000^4899 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        651 4000 16895644810626587 100000000000000000000 4899 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (651/4000 : ℝ)) (X := (16895644810626587/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4899 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500555399851313703/12500000000000000000 : ℝ) ≤ (5000046435554529/5000000000000000 : ℝ) ^ (4899/1024 : ℝ) := by
    have hpowers : (12500555399851313703/12500000000000000000 : ℝ)^1024 ≤ (5000046435554529/5000000000000000 : ℝ)^4899 := by
      have hnat : (12500555399851313703 : ℕ)^1024*5000000000000000^4899 ≤ 5000046435554529^4899*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500555399851313703 12500000000000000000 5000046435554529 5000000000000000 1024 4899 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000046435554529/5000000000000000 : ℝ)) (X := (12500555399851313703/12500000000000000000 : ℝ)) (by norm_num) 4899 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100019117244215881399/100000000000000000000 : ℝ) ≤ (5000199781365251/5000000000000000 : ℝ) ^ (4899/1024 : ℝ) := by
    have hpowers : (100019117244215881399/100000000000000000000 : ℝ)^1024 ≤ (5000199781365251/5000000000000000 : ℝ)^4899 := by
      have hnat : (100019117244215881399 : ℕ)^1024*5000000000000000^4899 ≤ 5000199781365251^4899*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100019117244215881399 100000000000000000000 5000199781365251 5000000000000000 1024 4899 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000199781365251/5000000000000000 : ℝ)) (X := (100019117244215881399/100000000000000000000 : ℝ)) (by norm_num) 4899 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50016895644810626587/50000000000000000000 : ℝ) ≤ (5000353127175973/5000000000000000 : ℝ) ^ (4899/1024 : ℝ) := by
    have hpowers : (50016895644810626587/50000000000000000000 : ℝ)^1024 ≤ (5000353127175973/5000000000000000 : ℝ)^4899 := by
      have hnat : (50016895644810626587 : ℕ)^1024*5000000000000000^4899 ≤ 5000353127175973^4899*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50016895644810626587 50000000000000000000 5000353127175973 5000000000000000 1024 4899 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000353127175973/5000000000000000 : ℝ)) (X := (50016895644810626587/50000000000000000000 : ℝ)) (by norm_num) 4899 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(555399851313703/25000000000000000000 : ℝ) ≤ ((374959932456344627/375000000000000000 : ℝ)+2*(76672905361/140625000000000 : ℝ)*(213/2000 : ℝ))^(4899/1024 : ℝ) := by
    rw [show (374959932456344627/375000000000000000 : ℝ)+2*(76672905361/140625000000000 : ℝ)*(213/2000 : ℝ)=(5000046435554529/5000000000000000 : ℝ) by norm_num, show 1+2*(555399851313703/25000000000000000000 : ℝ)=(12500555399851313703/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16895644810626587/100000000000000000000 : ℝ)+(555399851313703/25000000000000000000 : ℝ) ≤ ((374959932456344627/375000000000000000 : ℝ)+(76672905361/140625000000000 : ℝ)*((651/4000 : ℝ)+(213/2000 : ℝ)))^(4899/1024 : ℝ) := by
    rw [show (374959932456344627/375000000000000000 : ℝ)+(76672905361/140625000000000 : ℝ)*((651/4000 : ℝ)+(213/2000 : ℝ))=(5000199781365251/5000000000000000 : ℝ) by norm_num, show 1+(16895644810626587/100000000000000000000 : ℝ)+(555399851313703/25000000000000000000 : ℝ)=(100019117244215881399/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16895644810626587/100000000000000000000 : ℝ) ≤ ((374959932456344627/375000000000000000 : ℝ)+2*(76672905361/140625000000000 : ℝ)*(651/4000 : ℝ))^(4899/1024 : ℝ) := by
    rw [show (374959932456344627/375000000000000000 : ℝ)+2*(76672905361/140625000000000 : ℝ)*(651/4000 : ℝ)=(5000353127175973/5000000000000000 : ℝ) by norm_num, show 1+2*(16895644810626587/100000000000000000000 : ℝ)=(50016895644810626587/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (374959932456344627/375000000000000000 : ℝ)*(X 1 0+X 2 0)+(76672905361/140625000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4899/1024 : ℝ)) (lo := (213/2000 : ℝ)) (hi := (651/4000 : ℝ)) (c := (374959932456344627/375000000000000000 : ℝ)) (alpha := (76672905361/140625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (374959932456344627/375000000000000000 : ℝ)*(X 0 1+X 2 1)+(76672905361/140625000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4899/1024 : ℝ)) (lo := (213/2000 : ℝ)) (hi := (651/4000 : ℝ)) (c := (374959932456344627/375000000000000000 : ℝ)) (alpha := (76672905361/140625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (374959932456344627/375000000000000000 : ℝ)*(X 0 2+X 1 2)+(76672905361/140625000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4899/1024 : ℝ)) (lo := (213/2000 : ℝ)) (hi := (651/4000 : ℝ)) (c := (374959932456344627/375000000000000000 : ℝ)) (alpha := (76672905361/140625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1358286303/10000000000 : ℝ)*X 0 0+(1352262411/2500000000 : ℝ)*X 0 1+(540904879/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1050227119/2000000000 : ℝ)*X 1 0+(-1580225163/10000000000 : ℝ)*X 1 1+(54090491/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1050227141/2000000000 : ℝ)*X 2 0+(2704524617/5000000000 : ℝ)*X 2 1+(-1580224827/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4460893173/10000000000 : ℝ)*X 0 0+(1014344687/2500000000 : ℝ)*X 0 1+(4057378891/10000000000 : ℝ)*X 0 2+(4460893173/10000000000 : ℝ)*X 1 0+(1014344687/2500000000 : ℝ)*X 1 1+(4057378891/10000000000 : ℝ)*X 1 2+(4460893173/10000000000 : ℝ)*X 2 0+(1014344687/2500000000 : ℝ)*X 2 1+(4057378891/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-943873251/5000000000 : ℝ)*X 0 0+(5215634907/10000000000 : ℝ)*X 0 1+(1043127011/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5383962117/10000000000 : ℝ)*X 1 0+(-1663052979/10000000000 : ℝ)*X 1 1+(1043127009/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5383962099/10000000000 : ℝ)*X 2 0+(208625409/400000000 : ℝ)*X 2 1+(-1663052761/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((390030881/1000000000 : ℝ)*X 0 0+(4337344343/10000000000 : ℝ)*X 0 1+(433734443/1000000000 : ℝ)*X 0 2+(390030881/1000000000 : ℝ)*X 1 0+(4337344343/10000000000 : ℝ)*X 1 1+(433734443/1000000000 : ℝ)*X 1 2+(390030881/1000000000 : ℝ)*X 2 0+(4337344343/10000000000 : ℝ)*X 2 1+(433734443/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1774839599/10000000000 : ℝ)*X 0 0+(5076625991/10000000000 : ℝ)*X 0 1+(217542167/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1046174711/2000000000 : ℝ)*X 1 0+(-1567158277/10000000000 : ℝ)*X 1 1+(5438554219/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5230872833/10000000000 : ℝ)*X 2 0+(679819359/1250000000 : ℝ)*X 2 1+(-783579181/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4544028567/10000000000 : ℝ)*X 0 0+(4014593677/10000000000 : ℝ)*X 0 1+(501824171/1250000000 : ℝ)*X 0 2+(4544028567/10000000000 : ℝ)*X 1 0+(4014593677/10000000000 : ℝ)*X 1 1+(501824171/1250000000 : ℝ)*X 1 2+(4544028567/10000000000 : ℝ)*X 2 0+(4014593677/10000000000 : ℝ)*X 2 1+(501824171/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1469477491/10000000000 : ℝ)*X 0 0+(2771357373/5000000000 : ℝ)*X 0 1+(2597903431/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((269879429/500000000 : ℝ)*X 1 0+(-835629161/5000000000 : ℝ)*X 1 1+(5195807229/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1079517619/2000000000 : ℝ)*X 2 0+(5195807613/10000000000 : ℝ)*X 2 1+(-835629233/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((3841213241/10000000000 : ℝ)*X 0 0+(4365991871/10000000000 : ℝ)*X 0 1+(4365993403/10000000000 : ℝ)*X 0 2+(3841213241/10000000000 : ℝ)*X 1 0+(4365991871/10000000000 : ℝ)*X 1 1+(4365993403/10000000000 : ℝ)*X 1 2+(3841213241/10000000000 : ℝ)*X 2 0+(4365991871/10000000000 : ℝ)*X 2 1+(4365993403/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-65051/100000 : ℝ) ≤ (-1016382523034865133509734584901/1562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5188977/100000000000000 : ℝ)*(upper0) + (6081257/20000000000000 : ℝ)*(lower2) + (16568693/100000000000000 : ℝ)*(lower3) + (21166573/100000000000000 : ℝ)*(upper5) + (437837840025737/25000000000000 : ℝ)*(major0) + (437837840025737/25000000000000 : ℝ)*(major1) + (437837840025737/25000000000000 : ℝ)*(major2) + (268967679/50000000000000 : ℝ)*(sp3) + (2544394176215029/100000000000000 : ℝ)*(sp4) + (1272193551586077/50000000000000 : ℝ)*(sp5) + (636090356716317/25000000000000 : ℝ)*(sp6) + (979990833213577/100000000000000 : ℝ)*(sp7) + (56584343/800000000000 : ℝ)*(sp13) + (32749349761/100000000000000 : ℝ)*(sp14) + (122498921393617/12500000000000 : ℝ)*(f.failure) + (2544394176215029/100000000000000 : ℝ)*(f.sum) + (7431076094669/14062500000000000000000000000 : ℝ)*base66 + (103327042379701297/28125000000000000000000000000000 : ℝ)*base67 + (131985317510923703/28125000000000000000000000000000 : ℝ)*base70 + (80364302670298703/28125000000000000000000000000000 : ℝ)*base72 + (607123110632537/28125000000000000000000000000 : ℝ)*base73 + (6892031229673703/28125000000000000000000000000000 : ℝ)*base76 + (267128795735923703/28125000000000000000000000000000 : ℝ)*base78 + (448618272348451297/28125000000000000000000000000000 : ℝ)*base79 + (28053156855331/14062500000000000000000000000 : ℝ)*base81 + (796927/78125000000000000000 : ℝ)*base89 + (796927/78125000000000000000 : ℝ)*base91 + (796927/78125000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (58583/100000 : ℝ) ≤ (1830785713080581537097960102801/3125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4231949/2500000000000 : ℝ)*(lower1) + (160112531/100000000000000 : ℝ)*(lower2) + (149231833/100000000000000 : ℝ)*(lower5) + (1841200503890963/100000000000000 : ℝ)*(major0) + (1841200503890963/100000000000000 : ℝ)*(major1) + (1841200503890963/100000000000000 : ℝ)*(major2) + (131630164412681/5000000000000 : ℝ)*(sp0) + (1316286787848639/50000000000000 : ℝ)*(sp1) + (658149980408601/25000000000000 : ℝ)*(sp2) + (1030262904304781/100000000000000 : ℝ)*(sp3) + (5080176911/100000000000000 : ℝ)*(sp6) + (4720726299/100000000000000 : ℝ)*(sp7) + (856778847/50000000000000 : ℝ)*(sp8) + (31426114037/100000000000000 : ℝ)*(sp9) + (25756690625777/2500000000000 : ℝ)*(f.failure) + (1316302500905657/50000000000000 : ℝ)*(f.sum) + (18528315867553/28125000000000000000000000000 : ℝ)*base66 + (857849433260361403/112500000000000000000000000000000 : ℝ)*base67 + (137643706839638597/112500000000000000000000000000000 : ℝ)*base70 + (77166132002138597/112500000000000000000000000000000 : ℝ)*base72 + (91669893620911/14062500000000000000000000000 : ℝ)*base73 + (1359239542802138597/112500000000000000000000000000000 : ℝ)*base76 + (58231151702138597/112500000000000000000000000000000 : ℝ)*base78 + (283620620402138597/112500000000000000000000000000000 : ℝ)*base80 + (37568178129089/14062500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (54137/15625000000000000000 : ℝ)*base89 + (54137/15625000000000000000 : ℝ)*base91 + (54137/15625000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (81123/100000 : ℝ) ≤ (5070371307263493734471114433049/6250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (22178437/100000000000000 : ℝ)*(upper1) + (43382207/50000000000000 : ℝ)*(upper2) + (2250691/6250000000000 : ℝ)*(upper3) + (71474543/100000000000000 : ℝ)*(lower5) + (1936925227317471/100000000000000 : ℝ)*(major0) + (1936925227317471/100000000000000 : ℝ)*(major1) + (1936925227317471/100000000000000 : ℝ)*(major2) + (567869461/100000000000000 : ℝ)*(sp0) + (55630077053/100000000000000 : ℝ)*(sp2) + (11271176649/100000000000000 : ℝ)*(sp3) + (21585752115197/781250000000 : ℝ)*(sp8) + (2762976838614677/100000000000000 : ℝ)*(sp9) + (345365151067203/12500000000000 : ℝ)*(sp10) + (216764072907641/20000000000000 : ℝ)*(sp11) + (541915817857427/50000000000000 : ℝ)*(f.failure) + (2762976838614677/100000000000000 : ℝ)*(f.sum) + (3503888939167/9375000000000000000000000000 : ℝ)*base66 + (265019139841994317/37500000000000000000000000000000 : ℝ)*base67 + (330681508141994317/37500000000000000000000000000000 : ℝ)*base69 + (89659012216994317/37500000000000000000000000000000 : ℝ)*base71 + (176131597889/73242187500000000000000000 : ℝ)*base74 + (406596760404494317/37500000000000000000000000000000 : ℝ)*base75 + (344836033891994317/37500000000000000000000000000000 : ℝ)*base77 + (207040367716994317/37500000000000000000000000000000 : ℝ)*base79 + (2637794713763/585937500000000000000000000 : ℝ)*base81 + (1839037/312500000000000000000 : ℝ)*base89 + (1839037/312500000000000000000 : ℝ)*base91 + (1839037/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-11023/12500 : ℝ) ≤ (-688921490819128108480706793/781250000000000000000000000 : ℝ) := by norm_num
    linear_combination (45416701/50000000000000 : ℝ)*(lower1) + (123955261/100000000000000 : ℝ)*(lower4) + (872357/3125000000000 : ℝ)*(upper5) + (1980803753078613/100000000000000 : ℝ)*(major0) + (1980803753078613/100000000000000 : ℝ)*(major1) + (1980803753078613/100000000000000 : ℝ)*(major2) + (310674773/10000000000000 : ℝ)*(sp0) + (12933911521/50000000000000 : ℝ)*(sp5) + (7117654639/50000000000000 : ℝ)*(sp6) + (11229598037/100000000000000 : ℝ)*(sp7) + (720653487261063/25000000000000 : ℝ)*(sp12) + (144129559398447/5000000000000 : ℝ)*(sp13) + (180162676280169/6250000000000 : ℝ)*(sp14) + (1108373204375487/100000000000000 : ℝ)*(sp15) + (277096108493381/25000000000000 : ℝ)*(f.failure) + (1441308527895991/50000000000000 : ℝ)*(f.sum) + (38351132510099/9375000000000000000000000000 : ℝ)*base65 + (195999518052610351/37500000000000000000000000000000 : ℝ)*base67 + (105389148759889649/37500000000000000000000000000000 : ℝ)*base70 + (129037062890110351/37500000000000000000000000000000 : ℝ)*base71 + (10427263184737/4687500000000000000000000000 : ℝ)*base73 + (79820532234889649/37500000000000000000000000000000 : ℝ)*base76 + (29680122909889649/37500000000000000000000000000000 : ℝ)*base78 + (54890955927610351/37500000000000000000000000000000 : ℝ)*base79 + (41101268753849/9375000000000000000000000000 : ℝ)*base81 + (223711/156250000000000000000 : ℝ)*base89 + (223711/156250000000000000000 : ℝ)*base91 + (223711/156250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1646_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11169431/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (651/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (213/2000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(65051/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58583/100000 : ℝ) else (81123/100000 : ℝ) ≤ X j i ∧ X j i ≤ (11023/12500 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1646_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1646_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11169431/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (651/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10649/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(65051/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58583/100000 : ℝ) else (81123/100000 : ℝ) ≤ X j i ∧ X j i ≤ (11023/12500 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1646_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1646_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11169431/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (651/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10649/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(65051/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58583/100000 : ℝ) else (81123/100000 : ℝ) ≤ X j i ∧ X j i ≤ (11023/12500 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1646_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
