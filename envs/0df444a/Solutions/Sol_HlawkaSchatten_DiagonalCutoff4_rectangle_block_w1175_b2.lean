-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1175_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:47:35.06225+00:00
-- url     : https://prove2.me/submissions/4db8675a-2cd6-4987-b099-283d5b02feaa

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
theorem support_rectangle_w1175_s6_0 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1075589627/5000000000 : ℝ)*x 0 + (1078543671/2000000000 : ℝ)*x 1 + (6582487/12500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075589627/5000000000 : ℝ)^523 ≤ (6537324385051/50000000000000 : ℝ)^395 := by
    have hnat : (1075589627 : ℕ)^523*50000000000000^395 ≤ 6537324385051^395*5000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075589627 5000000000 6537324385051 50000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078543671/2000000000 : ℝ)^523 ≤ (44146864862141/100000000000000 : ℝ)^395 := by
    have hnat : (1078543671 : ℕ)^523*100000000000000^395 ≤ 44146864862141^395*2000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078543671 2000000000 44146864862141 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6582487/12500000 : ℝ)^523 ≤ (21389243183013/50000000000000 : ℝ)^395 := by
    have hnat : (6582487 : ℕ)^523*50000000000000^395 ≤ 21389243183013^395*12500000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6582487 12500000 21389243183013 50000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1075589627/5000000000 : ℝ), (1078543671/2000000000 : ℝ), (6582487/12500000 : ℝ)] ![(6537324385051/50000000000000 : ℝ), (44146864862141/100000000000000 : ℝ), (21389243183013/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1075589627/5000000000 : ℝ)|^523 ≤ (6537324385051/50000000000000 : ℝ)^395
        have hw : |(-1075589627/5000000000 : ℝ)|=(1075589627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078543671/2000000000 : ℝ)|^523 ≤ (44146864862141/100000000000000 : ℝ)^395
        have hw : |(1078543671/2000000000 : ℝ)|=(1078543671/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6582487/12500000 : ℝ)|^523 ≤ (21389243183013/50000000000000 : ℝ)^395
        have hw : |(6582487/12500000 : ℝ)|=(6582487/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1175_s6_1 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2672349551/5000000000 : ℝ)*x 0 + (-2215454199/10000000000 : ℝ)*x 1 + (1053197933/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672349551/5000000000 : ℝ)^523 ≤ (2181356381609/5000000000000 : ℝ)^395 := by
    have hnat : (2672349551 : ℕ)^523*5000000000000^395 ≤ 2181356381609^395*5000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672349551 5000000000 2181356381609 5000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2215454199/10000000000 : ℝ)^523 ≤ (3398596322321/25000000000000 : ℝ)^395 := by
    have hnat : (2215454199 : ℕ)^523*25000000000000^395 ≤ 3398596322321^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2215454199 10000000000 3398596322321 25000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053197933/2000000000 : ℝ)^523 ≤ (8555697413033/20000000000000 : ℝ)^395 := by
    have hnat : (1053197933 : ℕ)^523*20000000000000^395 ≤ 8555697413033^395*2000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053197933 2000000000 8555697413033 20000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672349551/5000000000 : ℝ), (-2215454199/10000000000 : ℝ), (1053197933/2000000000 : ℝ)] ![(2181356381609/5000000000000 : ℝ), (3398596322321/25000000000000 : ℝ), (8555697413033/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672349551/5000000000 : ℝ)|^523 ≤ (2181356381609/5000000000000 : ℝ)^395
        have hw : |(2672349551/5000000000 : ℝ)|=(2672349551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2215454199/10000000000 : ℝ)|^523 ≤ (3398596322321/25000000000000 : ℝ)^395
        have hw : |(-2215454199/10000000000 : ℝ)|=(2215454199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053197933/2000000000 : ℝ)|^523 ≤ (8555697413033/20000000000000 : ℝ)^395
        have hw : |(1053197933/2000000000 : ℝ)|=(1053197933/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1175_s6_2 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (41755463/78125000 : ℝ)*x 0 + (5265989413/10000000000 : ℝ)*x 1 + (-553863579/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41755463/78125000 : ℝ)^523 ≤ (21813564691523/50000000000000 : ℝ)^395 := by
    have hnat : (41755463 : ℕ)^523*50000000000000^395 ≤ 21813564691523^395*78125000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41755463 78125000 21813564691523 50000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265989413/10000000000 : ℝ)^523 ≤ (21389242177329/50000000000000 : ℝ)^395 := by
    have hnat : (5265989413 : ℕ)^523*50000000000000^395 ≤ 21389242177329^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265989413 10000000000 21389242177329 50000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (553863579/2500000000 : ℝ)^523 ≤ (13594386239861/100000000000000 : ℝ)^395 := by
    have hnat : (553863579 : ℕ)^523*100000000000000^395 ≤ 13594386239861^395*2500000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      553863579 2500000000 13594386239861 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41755463/78125000 : ℝ), (5265989413/10000000000 : ℝ), (-553863579/2500000000 : ℝ)] ![(21813564691523/50000000000000 : ℝ), (21389242177329/50000000000000 : ℝ), (13594386239861/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41755463/78125000 : ℝ)|^523 ≤ (21813564691523/50000000000000 : ℝ)^395
        have hw : |(41755463/78125000 : ℝ)|=(41755463/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265989413/10000000000 : ℝ)|^523 ≤ (21389242177329/50000000000000 : ℝ)^395
        have hw : |(5265989413/10000000000 : ℝ)|=(5265989413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-553863579/2500000000 : ℝ)|^523 ≤ (13594386239861/100000000000000 : ℝ)^395
        have hw : |(-553863579/2500000000 : ℝ)|=(553863579/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1175_s6_3 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2180015523/5000000000 : ℝ)*x 0 + (264685933/625000000 : ℝ)*x 1 + (4488732251/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2180015523/5000000000 : ℝ)^523 ≤ (33317004884159/100000000000000 : ℝ)^395 := by
    have hnat : (2180015523 : ℕ)^523*100000000000000^395 ≤ 33317004884159^395*5000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180015523 5000000000 33317004884159 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (264685933/625000000 : ℝ)^523 ≤ (16028822792853/50000000000000 : ℝ)^395 := by
    have hnat : (264685933 : ℕ)^523*50000000000000^395 ≤ 16028822792853^395*625000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264685933 625000000 16028822792853 50000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4488732251/10000000000 : ℝ)^523 ≤ (4328168689701/12500000000000 : ℝ)^395 := by
    have hnat : (4488732251 : ℕ)^523*12500000000000^395 ≤ 4328168689701^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4488732251 10000000000 4328168689701 12500000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2180015523/5000000000 : ℝ), (264685933/625000000 : ℝ), (4488732251/10000000000 : ℝ)] ![(33317004884159/100000000000000 : ℝ), (16028822792853/50000000000000 : ℝ), (4328168689701/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2180015523/5000000000 : ℝ)|^523 ≤ (33317004884159/100000000000000 : ℝ)^395
        have hw : |(2180015523/5000000000 : ℝ)|=(2180015523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(264685933/625000000 : ℝ)|^523 ≤ (16028822792853/50000000000000 : ℝ)^395
        have hw : |(264685933/625000000 : ℝ)|=(264685933/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4488732251/10000000000 : ℝ)|^523 ≤ (4328168689701/12500000000000 : ℝ)^395
        have hw : |(4488732251/10000000000 : ℝ)|=(4488732251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1175_s6_4 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2151184249/10000000000 : ℝ)*x 0 + (1316577401/2500000000 : ℝ)*x 1 + (5392397091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2151184249/10000000000 : ℝ)^523 ≤ (6537344483553/50000000000000 : ℝ)^395 := by
    have hnat : (2151184249 : ℕ)^523*50000000000000^395 ≤ 6537344483553^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151184249 10000000000 6537344483553 50000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316577401/2500000000 : ℝ)^523 ≤ (42781928356729/100000000000000 : ℝ)^395 := by
    have hnat : (1316577401 : ℕ)^523*100000000000000^395 ≤ 42781928356729^395*2500000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316577401 2500000000 42781928356729 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392397091/10000000000 : ℝ)^523 ≤ (22071691327541/50000000000000 : ℝ)^395 := by
    have hnat : (5392397091 : ℕ)^523*50000000000000^395 ≤ 22071691327541^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392397091 10000000000 22071691327541 50000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2151184249/10000000000 : ℝ), (1316577401/2500000000 : ℝ), (5392397091/10000000000 : ℝ)] ![(6537344483553/50000000000000 : ℝ), (42781928356729/100000000000000 : ℝ), (22071691327541/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2151184249/10000000000 : ℝ)|^523 ≤ (6537344483553/50000000000000 : ℝ)^395
        have hw : |(-2151184249/10000000000 : ℝ)|=(2151184249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316577401/2500000000 : ℝ)|^523 ≤ (42781928356729/100000000000000 : ℝ)^395
        have hw : |(1316577401/2500000000 : ℝ)|=(1316577401/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392397091/10000000000 : ℝ)|^523 ≤ (22071691327541/50000000000000 : ℝ)^395
        have hw : |(5392397091/10000000000 : ℝ)|=(5392397091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1175_s6_5 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (664064313/1250000000 : ℝ)*x 0 + (-522261653/2500000000 : ℝ)*x 1 + (5392397089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664064313/1250000000 : ℝ)^523 ≤ (21639811128769/50000000000000 : ℝ)^395 := by
    have hnat : (664064313 : ℕ)^523*50000000000000^395 ≤ 21639811128769^395*1250000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664064313 1250000000 21639811128769 50000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (522261653/2500000000 : ℝ)^523 ≤ (6288497547323/50000000000000 : ℝ)^395 := by
    have hnat : (522261653 : ℕ)^523*50000000000000^395 ≤ 6288497547323^395*2500000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522261653 2500000000 6288497547323 50000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392397089/10000000000 : ℝ)^523 ≤ (11035845658351/25000000000000 : ℝ)^395 := by
    have hnat : (5392397089 : ℕ)^523*25000000000000^395 ≤ 11035845658351^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392397089 10000000000 11035845658351 25000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664064313/1250000000 : ℝ), (-522261653/2500000000 : ℝ), (5392397089/10000000000 : ℝ)] ![(21639811128769/50000000000000 : ℝ), (6288497547323/50000000000000 : ℝ), (11035845658351/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664064313/1250000000 : ℝ)|^523 ≤ (21639811128769/50000000000000 : ℝ)^395
        have hw : |(664064313/1250000000 : ℝ)|=(664064313/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-522261653/2500000000 : ℝ)|^523 ≤ (6288497547323/50000000000000 : ℝ)^395
        have hw : |(-522261653/2500000000 : ℝ)|=(522261653/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392397089/10000000000 : ℝ)|^523 ≤ (11035845658351/25000000000000 : ℝ)^395
        have hw : |(5392397089/10000000000 : ℝ)|=(5392397089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1175_s6_6 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2656257251/5000000000 : ℝ)*x 0 + (539239709/1000000000 : ℝ)*x 1 + (-2089046613/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656257251/5000000000 : ℝ)^523 ≤ (8655924447193/20000000000000 : ℝ)^395 := by
    have hnat : (2656257251 : ℕ)^523*20000000000000^395 ≤ 8655924447193^395*5000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656257251 5000000000 8655924447193 20000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539239709/1000000000 : ℝ)^523 ≤ (44143382644243/100000000000000 : ℝ)^395 := by
    have hnat : (539239709 : ℕ)^523*100000000000000^395 ≤ 44143382644243^395*1000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539239709 1000000000 44143382644243 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2089046613/10000000000 : ℝ)^523 ≤ (12576995102617/100000000000000 : ℝ)^395 := by
    have hnat : (2089046613 : ℕ)^523*100000000000000^395 ≤ 12576995102617^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2089046613 10000000000 12576995102617 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656257251/5000000000 : ℝ), (539239709/1000000000 : ℝ), (-2089046613/10000000000 : ℝ)] ![(8655924447193/20000000000000 : ℝ), (44143382644243/100000000000000 : ℝ), (12576995102617/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656257251/5000000000 : ℝ)|^523 ≤ (8655924447193/20000000000000 : ℝ)^395
        have hw : |(2656257251/5000000000 : ℝ)|=(2656257251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539239709/1000000000 : ℝ)|^523 ≤ (44143382644243/100000000000000 : ℝ)^395
        have hw : |(539239709/1000000000 : ℝ)|=(539239709/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2089046613/10000000000 : ℝ)|^523 ≤ (12576995102617/100000000000000 : ℝ)^395
        have hw : |(-2089046613/10000000000 : ℝ)|=(2089046613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1175_s6_7 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2180020269/5000000000 : ℝ)*x 0 + (897618227/2000000000 : ℝ)*x 1 + (847123727/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2180020269/5000000000 : ℝ)^523 ≤ (33317100921217/100000000000000 : ℝ)^395 := by
    have hnat : (2180020269 : ℕ)^523*100000000000000^395 ≤ 33317100921217^395*5000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180020269 5000000000 33317100921217 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (897618227/2000000000 : ℝ)^523 ≤ (8654700405967/25000000000000 : ℝ)^395 := by
    have hnat : (897618227 : ℕ)^523*25000000000000^395 ≤ 8654700405967^395*2000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      897618227 2000000000 8654700405967 25000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (847123727/2000000000 : ℝ)^523 ≤ (32064097436271/100000000000000 : ℝ)^395 := by
    have hnat : (847123727 : ℕ)^523*100000000000000^395 ≤ 32064097436271^395*2000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      847123727 2000000000 32064097436271 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2180020269/5000000000 : ℝ), (897618227/2000000000 : ℝ), (847123727/2000000000 : ℝ)] ![(33317100921217/100000000000000 : ℝ), (8654700405967/25000000000000 : ℝ), (32064097436271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2180020269/5000000000 : ℝ)|^523 ≤ (33317100921217/100000000000000 : ℝ)^395
        have hw : |(2180020269/5000000000 : ℝ)|=(2180020269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(897618227/2000000000 : ℝ)|^523 ≤ (8654700405967/25000000000000 : ℝ)^395
        have hw : |(897618227/2000000000 : ℝ)|=(897618227/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(847123727/2000000000 : ℝ)|^523 ≤ (32064097436271/100000000000000 : ℝ)^395
        have hw : |(847123727/2000000000 : ℝ)|=(847123727/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1175_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30023597/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7051/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11363/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1139/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7037/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7051/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11363/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7051/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11363/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7051/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11363/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7051/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11363/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7051/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11363/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7051/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11363/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11363/100000 : ℝ) ^ (8367/2048 : ℝ) ≤ (6922048634987167/50000000000000000000 : ℝ) := by
    have hpowers : (11363/100000 : ℝ)^8367 ≤ (6922048634987167/50000000000000000000 : ℝ)^2048 := by
      have hnat : (11363 : ℕ)^8367*50000000000000000000^2048 ≤ 6922048634987167^2048*100000^8367 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11363 100000 6922048634987167 50000000000000000000 8367 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11363/100000 : ℝ)) (X := (6922048634987167/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8367 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7051/50000 : ℝ) ^ (8367/2048 : ℝ) ≤ (33452574201548387/100000000000000000000 : ℝ) := by
    have hpowers : (7051/50000 : ℝ)^8367 ≤ (33452574201548387/100000000000000000000 : ℝ)^2048 := by
      have hnat : (7051 : ℕ)^8367*100000000000000000000^2048 ≤ 33452574201548387^2048*50000^8367 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7051 50000 33452574201548387 100000000000000000000 8367 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7051/50000 : ℝ)) (X := (33452574201548387/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8367 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006922048634987167/25000000000000000000 : ℝ) ≤ (2500169414050927/2500000000000000 : ℝ) ^ (8367/2048 : ℝ) := by
    have hpowers : (25006922048634987167/25000000000000000000 : ℝ)^2048 ≤ (2500169414050927/2500000000000000 : ℝ)^8367 := by
      have hnat : (25006922048634987167 : ℕ)^2048*2500000000000000^8367 ≤ 2500169414050927^8367*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006922048634987167 25000000000000000000 2500169414050927 2500000000000000 2048 8367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500169414050927/2500000000000000 : ℝ)) (X := (25006922048634987167/25000000000000000000 : ℝ)) (by norm_num) 8367 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047296671471522721/100000000000000000000 : ℝ) ≤ (5000578739621217/5000000000000000 : ℝ) ^ (8367/2048 : ℝ) := by
    have hpowers : (100047296671471522721/100000000000000000000 : ℝ)^2048 ≤ (5000578739621217/5000000000000000 : ℝ)^8367 := by
      have hnat : (100047296671471522721 : ℕ)^2048*5000000000000000^8367 ≤ 5000578739621217^8367*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047296671471522721 100000000000000000000 5000578739621217 5000000000000000 2048 8367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000578739621217/5000000000000000 : ℝ)) (X := (100047296671471522721/100000000000000000000 : ℝ)) (by norm_num) 8367 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033452574201548387/50000000000000000000 : ℝ) ≤ (250040932557029/250000000000000 : ℝ) ^ (8367/2048 : ℝ) := by
    have hpowers : (50033452574201548387/50000000000000000000 : ℝ)^2048 ≤ (250040932557029/250000000000000 : ℝ)^8367 := by
      have hnat : (50033452574201548387 : ℕ)^2048*250000000000000^8367 ≤ 250040932557029^8367*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033452574201548387 50000000000000000000 250040932557029 250000000000000 2048 8367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250040932557029/250000000000000 : ℝ)) (X := (50033452574201548387/50000000000000000000 : ℝ)) (by norm_num) 8367 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6922048634987167/50000000000000000000 : ℝ) ≤ ((155573588874794711/155625000000000000 : ℝ)+2*(239911519363/136950000000000 : ℝ)*(11363/100000 : ℝ))^(8367/2048 : ℝ) := by
    rw [show (155573588874794711/155625000000000000 : ℝ)+2*(239911519363/136950000000000 : ℝ)*(11363/100000 : ℝ)=(2500169414050927/2500000000000000 : ℝ) by norm_num, show 1+2*(6922048634987167/50000000000000000000 : ℝ)=(25006922048634987167/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33452574201548387/100000000000000000000 : ℝ)+(6922048634987167/50000000000000000000 : ℝ) ≤ ((155573588874794711/155625000000000000 : ℝ)+(239911519363/136950000000000 : ℝ)*((7051/50000 : ℝ)+(11363/100000 : ℝ)))^(8367/2048 : ℝ) := by
    rw [show (155573588874794711/155625000000000000 : ℝ)+(239911519363/136950000000000 : ℝ)*((7051/50000 : ℝ)+(11363/100000 : ℝ))=(5000578739621217/5000000000000000 : ℝ) by norm_num, show 1+(33452574201548387/100000000000000000000 : ℝ)+(6922048634987167/50000000000000000000 : ℝ)=(100047296671471522721/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33452574201548387/100000000000000000000 : ℝ) ≤ ((155573588874794711/155625000000000000 : ℝ)+2*(239911519363/136950000000000 : ℝ)*(7051/50000 : ℝ))^(8367/2048 : ℝ) := by
    rw [show (155573588874794711/155625000000000000 : ℝ)+2*(239911519363/136950000000000 : ℝ)*(7051/50000 : ℝ)=(250040932557029/250000000000000 : ℝ) by norm_num, show 1+2*(33452574201548387/100000000000000000000 : ℝ)=(50033452574201548387/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (155573588874794711/155625000000000000 : ℝ)*(X 1 0+X 2 0)+(239911519363/136950000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8367/2048 : ℝ)) (lo := (11363/100000 : ℝ)) (hi := (7051/50000 : ℝ)) (c := (155573588874794711/155625000000000000 : ℝ)) (alpha := (239911519363/136950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (155573588874794711/155625000000000000 : ℝ)*(X 0 1+X 2 1)+(239911519363/136950000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8367/2048 : ℝ)) (lo := (11363/100000 : ℝ)) (hi := (7051/50000 : ℝ)) (c := (155573588874794711/155625000000000000 : ℝ)) (alpha := (239911519363/136950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (155573588874794711/155625000000000000 : ℝ)*(X 0 2+X 1 2)+(239911519363/136950000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8367/2048 : ℝ)) (lo := (11363/100000 : ℝ)) (hi := (7051/50000 : ℝ)) (c := (155573588874794711/155625000000000000 : ℝ)) (alpha := (239911519363/136950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1075589627/5000000000 : ℝ)*X 0 0+(1078543671/2000000000 : ℝ)*X 0 1+(6582487/12500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672349551/5000000000 : ℝ)*X 1 0+(-2215454199/10000000000 : ℝ)*X 1 1+(1053197933/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((41755463/78125000 : ℝ)*X 2 0+(5265989413/10000000000 : ℝ)*X 2 1+(-553863579/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2180015523/5000000000 : ℝ)*X 0 0+(264685933/625000000 : ℝ)*X 0 1+(4488732251/10000000000 : ℝ)*X 0 2+(2180015523/5000000000 : ℝ)*X 1 0+(264685933/625000000 : ℝ)*X 1 1+(4488732251/10000000000 : ℝ)*X 1 2+(2180015523/5000000000 : ℝ)*X 2 0+(264685933/625000000 : ℝ)*X 2 1+(4488732251/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2151184249/10000000000 : ℝ)*X 0 0+(1316577401/2500000000 : ℝ)*X 0 1+(5392397091/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((664064313/1250000000 : ℝ)*X 1 0+(-522261653/2500000000 : ℝ)*X 1 1+(5392397089/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656257251/5000000000 : ℝ)*X 2 0+(539239709/1000000000 : ℝ)*X 2 1+(-2089046613/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2180020269/5000000000 : ℝ)*X 0 0+(897618227/2000000000 : ℝ)*X 0 1+(847123727/2000000000 : ℝ)*X 0 2+(2180020269/5000000000 : ℝ)*X 1 0+(897618227/2000000000 : ℝ)*X 1 1+(847123727/2000000000 : ℝ)*X 1 2+(2180020269/5000000000 : ℝ)*X 2 0+(897618227/2000000000 : ℝ)*X 2 1+(847123727/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1184448469823276852736069/259375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11255027/2500000000000 : ℝ)*(base19) + (628244437/100000000000000 : ℝ)*(base23) + (66893861/50000000000000 : ℝ)*(lower2) + (95305129/50000000000000 : ℝ)*(upper3) + (25278547/25000000000000 : ℝ)*(lower4) + (591584030275007/10000000000000 : ℝ)*(major0) + (591584030275007/10000000000000 : ℝ)*(major1) + (591584030275007/10000000000000 : ℝ)*(major2) + (3945440388219661/50000000000000 : ℝ)*(sp0) + (3945443082493653/50000000000000 : ℝ)*(sp1) + (1972721496735987/25000000000000 : ℝ)*(sp2) + (1970390328991171/50000000000000 : ℝ)*(sp3) + (729843633/12500000000000 : ℝ)*(sp4) + (13180111121/100000000000000 : ℝ)*(sp7) + (3940793838093463/100000000000000 : ℝ)*(f.failure) + (3945443307594193/50000000000000 : ℝ)*(f.sum) + (219798908053/24900000000000000000000000 : ℝ)*base65 + (8829363534881409/518750000000000000000000000000 : ℝ)*base67 + (3677565972431409/518750000000000000000000000000 : ℝ)*base69 + (8314290245537659/518750000000000000000000000000 : ℝ)*base71 + (175003094491/249000000000000000000000000 : ℝ)*base73 + (5868471080693909/518750000000000000000000000000 : ℝ)*base75 + (914189183162659/518750000000000000000000000000 : ℝ)*base77 + (7786646695418909/518750000000000000000000000000 : ℝ)*base79 + (846497257783/249000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (18553589/2000000000000000000000 : ℝ)*base90 + (18553589/2000000000000000000000 : ℝ)*base92 + (18553589/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (64620737312177811625258501/14265625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (828053923/100000000000000 : ℝ)*(base19) + (449206027/50000000000000 : ℝ)*(base23) + (90947631/100000000000000 : ℝ)*(upper3) + (33738969/100000000000000 : ℝ)*(lower4) + (93556513/100000000000000 : ℝ)*(upper5) + (5945913759017669/100000000000000 : ℝ)*(major0) + (5945913759017669/100000000000000 : ℝ)*(major1) + (5945913759017669/100000000000000 : ℝ)*(major2) + (22862623749/100000000000000 : ℝ)*(sp1) + (1530373381/6250000000000 : ℝ)*(sp2) + (1586200063112123/20000000000000 : ℝ)*(sp4) + (7930976624882943/100000000000000 : ℝ)*(sp5) + (1586194986234893/20000000000000 : ℝ)*(sp6) + (990206762870163/25000000000000 : ℝ)*(sp7) + (990206762870163/25000000000000 : ℝ)*(f.failure) + (1586200063112123/20000000000000 : ℝ)*(f.sum) + (23545683156199/13695000000000000000000000000 : ℝ)*base65 + (865501077876607583/57062500000000000000000000000000 : ℝ)*base67 + (338960163564954917/57062500000000000000000000000000 : ℝ)*base70 + (453002943629232583/57062500000000000000000000000000 : ℝ)*base71 + (24019650507859/13695000000000000000000000000 : ℝ)*base73 + (719187660753107583/57062500000000000000000000000000 : ℝ)*base75 + (807647630569732583/57062500000000000000000000000000 : ℝ)*base77 + (611121814583232583/57062500000000000000000000000000 : ℝ)*base79 + (61849448231411/13695000000000000000000000000 : ℝ)*base82 + (7763689/500000000000000000000 : ℝ)*base90 + (7763689/500000000000000000000 : ℝ)*base92 + (7763689/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1175_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30023597/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7051/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11363/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1139/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7037/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1175_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1175_s7_0 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2151202431/10000000000 : ℝ)*x 0 + (2696222781/5000000000 : ℝ)*x 1 + (5266247157/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2151202431/10000000000 : ℝ)^523 ≤ (13074835286063/100000000000000 : ℝ)^395 := by
    have hnat : (2151202431 : ℕ)^523*100000000000000^395 ≤ 13074835286063^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151202431 10000000000 13074835286063 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696222781/5000000000 : ℝ)^523 ≤ (2758994251997/6250000000000 : ℝ)^395 := by
    have hnat : (2696222781 : ℕ)^523*6250000000000^395 ≤ 2758994251997^395*5000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696222781 5000000000 2758994251997 6250000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266247157/10000000000 : ℝ)^523 ≤ (42781256666073/100000000000000 : ℝ)^395 := by
    have hnat : (5266247157 : ℕ)^523*100000000000000^395 ≤ 42781256666073^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266247157 10000000000 42781256666073 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2151202431/10000000000 : ℝ), (2696222781/5000000000 : ℝ), (5266247157/10000000000 : ℝ)] ![(13074835286063/100000000000000 : ℝ), (2758994251997/6250000000000 : ℝ), (42781256666073/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2151202431/10000000000 : ℝ)|^523 ≤ (13074835286063/100000000000000 : ℝ)^395
        have hw : |(-2151202431/10000000000 : ℝ)|=(2151202431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696222781/5000000000 : ℝ)|^523 ≤ (2758994251997/6250000000000 : ℝ)^395
        have hw : |(2696222781/5000000000 : ℝ)|=(2696222781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266247157/10000000000 : ℝ)|^523 ≤ (42781256666073/100000000000000 : ℝ)^395
        have hw : |(5266247157/10000000000 : ℝ)|=(5266247157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1175_s7_1 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5344630313/10000000000 : ℝ)*x 0 + (-276900571/1250000000 : ℝ)*x 1 + (5266247339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344630313/10000000000 : ℝ)^523 ≤ (5453298021857/12500000000000 : ℝ)^395 := by
    have hnat : (5344630313 : ℕ)^523*12500000000000^395 ≤ 5453298021857^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344630313 10000000000 5453298021857 12500000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (276900571/1250000000 : ℝ)^523 ≤ (13592357177077/100000000000000 : ℝ)^395 := by
    have hnat : (276900571 : ℕ)^523*100000000000000^395 ≤ 13592357177077^395*1250000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276900571 1250000000 13592357177077 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266247339/10000000000 : ℝ)^523 ≤ (42781258623693/100000000000000 : ℝ)^395 := by
    have hnat : (5266247339 : ℕ)^523*100000000000000^395 ≤ 42781258623693^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266247339 10000000000 42781258623693 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344630313/10000000000 : ℝ), (-276900571/1250000000 : ℝ), (5266247339/10000000000 : ℝ)] ![(5453298021857/12500000000000 : ℝ), (13592357177077/100000000000000 : ℝ), (42781258623693/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344630313/10000000000 : ℝ)|^523 ≤ (5453298021857/12500000000000 : ℝ)^395
        have hw : |(5344630313/10000000000 : ℝ)|=(5344630313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-276900571/1250000000 : ℝ)|^523 ≤ (13592357177077/100000000000000 : ℝ)^395
        have hw : |(-276900571/1250000000 : ℝ)|=(276900571/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266247339/10000000000 : ℝ)|^523 ≤ (42781258623693/100000000000000 : ℝ)^395
        have hw : |(5266247339/10000000000 : ℝ)|=(5266247339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1175_s7_2 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2672315187/5000000000 : ℝ)*x 0 + (1316561881/2500000000 : ℝ)*x 1 + (-2215204243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672315187/5000000000 : ℝ)^523 ≤ (4362638483413/10000000000000 : ℝ)^395 := by
    have hnat : (2672315187 : ℕ)^523*10000000000000^395 ≤ 4362638483413^395*5000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672315187 5000000000 4362638483413 10000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316561881/2500000000 : ℝ)^523 ≤ (42781260613581/100000000000000 : ℝ)^395 := by
    have hnat : (1316561881 : ℕ)^523*100000000000000^395 ≤ 42781260613581^395*2500000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316561881 2500000000 42781260613581 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2215204243/10000000000 : ℝ)^523 ≤ (6796177268341/50000000000000 : ℝ)^395 := by
    have hnat : (2215204243 : ℕ)^523*50000000000000^395 ≤ 6796177268341^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2215204243 10000000000 6796177268341 50000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672315187/5000000000 : ℝ), (1316561881/2500000000 : ℝ), (-2215204243/10000000000 : ℝ)] ![(4362638483413/10000000000000 : ℝ), (42781260613581/100000000000000 : ℝ), (6796177268341/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672315187/5000000000 : ℝ)|^523 ≤ (4362638483413/10000000000000 : ℝ)^395
        have hw : |(2672315187/5000000000 : ℝ)|=(2672315187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316561881/2500000000 : ℝ)|^523 ≤ (42781260613581/100000000000000 : ℝ)^395
        have hw : |(1316561881/2500000000 : ℝ)|=(1316561881/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2215204243/10000000000 : ℝ)|^523 ≤ (6796177268341/50000000000000 : ℝ)^395
        have hw : |(-2215204243/10000000000 : ℝ)|=(2215204243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1175_s7_3 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4360044571/10000000000 : ℝ)*x 0 + (4235504613/10000000000 : ℝ)*x 1 + (2244099521/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4360044571/10000000000 : ℝ)^523 ≤ (16658570862929/50000000000000 : ℝ)^395 := by
    have hnat : (4360044571 : ℕ)^523*50000000000000^395 ≤ 16658570862929^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4360044571 10000000000 16658570862929 50000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4235504613/10000000000 : ℝ)^523 ≤ (16031477287491/50000000000000 : ℝ)^395 := by
    have hnat : (4235504613 : ℕ)^523*50000000000000^395 ≤ 16031477287491^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4235504613 10000000000 16031477287491 50000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2244099521/5000000000 : ℝ)^523 ≤ (17309951843237/50000000000000 : ℝ)^395 := by
    have hnat : (2244099521 : ℕ)^523*50000000000000^395 ≤ 17309951843237^395*5000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2244099521 5000000000 17309951843237 50000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4360044571/10000000000 : ℝ), (4235504613/10000000000 : ℝ), (2244099521/5000000000 : ℝ)] ![(16658570862929/50000000000000 : ℝ), (16031477287491/50000000000000 : ℝ), (17309951843237/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4360044571/10000000000 : ℝ)|^523 ≤ (16658570862929/50000000000000 : ℝ)^395
        have hw : |(4360044571/10000000000 : ℝ)|=(4360044571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4235504613/10000000000 : ℝ)|^523 ≤ (16031477287491/50000000000000 : ℝ)^395
        have hw : |(4235504613/10000000000 : ℝ)|=(4235504613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2244099521/5000000000 : ℝ)|^523 ≤ (17309951843237/50000000000000 : ℝ)^395
        have hw : |(2244099521/5000000000 : ℝ)|=(2244099521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1175_s7_4 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2151206831/10000000000 : ℝ)*x 0 + (1053312961/2000000000 : ℝ)*x 1 + (5392127069/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2151206831/10000000000 : ℝ)^523 ≤ (13074870694957/100000000000000 : ℝ)^395 := by
    have hnat : (2151206831 : ℕ)^523*100000000000000^395 ≤ 13074870694957^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151206831 10000000000 13074870694957 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053312961/2000000000 : ℝ)^523 ≤ (42784673369337/100000000000000 : ℝ)^395 := by
    have hnat : (1053312961 : ℕ)^523*100000000000000^395 ≤ 42784673369337^395*2000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053312961 2000000000 42784673369337 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392127069/10000000000 : ℝ)^523 ≤ (8828091183259/20000000000000 : ℝ)^395 := by
    have hnat : (5392127069 : ℕ)^523*20000000000000^395 ≤ 8828091183259^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392127069 10000000000 8828091183259 20000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2151206831/10000000000 : ℝ), (1053312961/2000000000 : ℝ), (5392127069/10000000000 : ℝ)] ![(13074870694957/100000000000000 : ℝ), (42784673369337/100000000000000 : ℝ), (8828091183259/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2151206831/10000000000 : ℝ)|^523 ≤ (13074870694957/100000000000000 : ℝ)^395
        have hw : |(-2151206831/10000000000 : ℝ)|=(2151206831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053312961/2000000000 : ℝ)|^523 ≤ (42784673369337/100000000000000 : ℝ)^395
        have hw : |(1053312961/2000000000 : ℝ)|=(1053312961/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392127069/10000000000 : ℝ)|^523 ≤ (8828091183259/20000000000000 : ℝ)^395
        have hw : |(5392127069/10000000000 : ℝ)|=(5392127069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1175_s7_5 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (83009073/156250000 : ℝ)*x 0 + (-2089324231/10000000000 : ℝ)*x 1 + (5392127063/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83009073/156250000 : ℝ)^523 ≤ (10820083998059/25000000000000 : ℝ)^395 := by
    have hnat : (83009073 : ℕ)^523*25000000000000^395 ≤ 10820083998059^395*156250000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83009073 156250000 10820083998059 25000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2089324231/10000000000 : ℝ)^523 ≤ (196550127313/1562500000000 : ℝ)^395 := by
    have hnat : (2089324231 : ℕ)^523*1562500000000^395 ≤ 196550127313^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2089324231 10000000000 196550127313 1562500000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392127063/10000000000 : ℝ)^523 ≤ (22070227925631/50000000000000 : ℝ)^395 := by
    have hnat : (5392127063 : ℕ)^523*50000000000000^395 ≤ 22070227925631^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392127063 10000000000 22070227925631 50000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(83009073/156250000 : ℝ), (-2089324231/10000000000 : ℝ), (5392127063/10000000000 : ℝ)] ![(10820083998059/25000000000000 : ℝ), (196550127313/1562500000000 : ℝ), (22070227925631/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(83009073/156250000 : ℝ)|^523 ≤ (10820083998059/25000000000000 : ℝ)^395
        have hw : |(83009073/156250000 : ℝ)|=(83009073/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2089324231/10000000000 : ℝ)|^523 ≤ (196550127313/1562500000000 : ℝ)^395
        have hw : |(-2089324231/10000000000 : ℝ)|=(2089324231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392127063/10000000000 : ℝ)|^523 ≤ (22070227925631/50000000000000 : ℝ)^395
        have hw : |(5392127063/10000000000 : ℝ)|=(5392127063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1175_s7_6 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5312580619/10000000000 : ℝ)*x 0 + (5392127103/10000000000 : ℝ)*x 1 + (-261165531/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312580619/10000000000 : ℝ)^523 ≤ (43280335420539/100000000000000 : ℝ)^395 := by
    have hnat : (5312580619 : ℕ)^523*100000000000000^395 ≤ 43280335420539^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312580619 10000000000 43280335420539 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392127103/10000000000 : ℝ)^523 ≤ (22070228142407/50000000000000 : ℝ)^395 := by
    have hnat : (5392127103 : ℕ)^523*50000000000000^395 ≤ 22070228142407^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392127103 10000000000 22070228142407 50000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (261165531/1250000000 : ℝ)^523 ≤ (393100258861/3125000000000 : ℝ)^395 := by
    have hnat : (261165531 : ℕ)^523*3125000000000^395 ≤ 393100258861^395*1250000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261165531 1250000000 393100258861 3125000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312580619/10000000000 : ℝ), (5392127103/10000000000 : ℝ), (-261165531/1250000000 : ℝ)] ![(43280335420539/100000000000000 : ℝ), (22070228142407/50000000000000 : ℝ), (393100258861/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312580619/10000000000 : ℝ)|^523 ≤ (43280335420539/100000000000000 : ℝ)^395
        have hw : |(5312580619/10000000000 : ℝ)|=(5312580619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392127103/10000000000 : ℝ)|^523 ≤ (22070228142407/50000000000000 : ℝ)^395
        have hw : |(5392127103/10000000000 : ℝ)|=(5392127103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-261165531/1250000000 : ℝ)|^523 ≤ (393100258861/3125000000000 : ℝ)^395
        have hw : |(-261165531/1250000000 : ℝ)|=(261165531/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1175_s7_7 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4360053881/10000000000 : ℝ)*x 0 + (179502543/400000000 : ℝ)*x 1 + (4236142697/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4360053881/10000000000 : ℝ)^523 ≤ (33317235921591/100000000000000 : ℝ)^395 := by
    have hnat : (4360053881 : ℕ)^523*100000000000000^395 ≤ 33317235921591^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4360053881 10000000000 33317235921591 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (179502543/400000000 : ℝ)^523 ≤ (6922682747211/20000000000000 : ℝ)^395 := by
    have hnat : (179502543 : ℕ)^523*20000000000000^395 ≤ 6922682747211^395*400000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179502543 400000000 6922682747211 20000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4236142697/10000000000 : ℝ)^523 ≤ (32069350324239/100000000000000 : ℝ)^395 := by
    have hnat : (4236142697 : ℕ)^523*100000000000000^395 ≤ 32069350324239^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4236142697 10000000000 32069350324239 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4360053881/10000000000 : ℝ), (179502543/400000000 : ℝ), (4236142697/10000000000 : ℝ)] ![(33317235921591/100000000000000 : ℝ), (6922682747211/20000000000000 : ℝ), (32069350324239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4360053881/10000000000 : ℝ)|^523 ≤ (33317235921591/100000000000000 : ℝ)^395
        have hw : |(4360053881/10000000000 : ℝ)|=(4360053881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(179502543/400000000 : ℝ)|^523 ≤ (6922682747211/20000000000000 : ℝ)^395
        have hw : |(179502543/400000000 : ℝ)|=(179502543/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4236142697/10000000000 : ℝ)|^523 ≤ (32069350324239/100000000000000 : ℝ)^395
        have hw : |(4236142697/10000000000 : ℝ)|=(4236142697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1175_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30023597/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7037/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1139/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (2279/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14069/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7037/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1139/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7037/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1139/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7037/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1139/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7037/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1139/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7037/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1139/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7037/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1139/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1139/10000 : ℝ) ^ (8367/2048 : ℝ) ≤ (13978983286309589/100000000000000000000 : ℝ) := by
    have hpowers : (1139/10000 : ℝ)^8367 ≤ (13978983286309589/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1139 : ℕ)^8367*100000000000000000000^2048 ≤ 13978983286309589^2048*10000^8367 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1139 10000 13978983286309589 100000000000000000000 8367 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1139/10000 : ℝ)) (X := (13978983286309589/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8367 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7037/50000 : ℝ) ^ (8367/2048 : ℝ) ≤ (33182043737070089/100000000000000000000 : ℝ) := by
    have hpowers : (7037/50000 : ℝ)^8367 ≤ (33182043737070089/100000000000000000000 : ℝ)^2048 := by
      have hnat : (7037 : ℕ)^8367*100000000000000000000^2048 ≤ 33182043737070089^2048*50000^8367 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7037 50000 33182043737070089 100000000000000000000 8367 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7037/50000 : ℝ)) (X := (33182043737070089/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8367 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013978983286309589/50000000000000000000 : ℝ) ≤ (2000136851611381/2000000000000000 : ℝ) ^ (8367/2048 : ℝ) := by
    have hpowers : (50013978983286309589/50000000000000000000 : ℝ)^2048 ≤ (2000136851611381/2000000000000000 : ℝ)^8367 := by
      have hnat : (50013978983286309589 : ℕ)^2048*2000000000000000^8367 ≤ 2000136851611381^8367*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013978983286309589 50000000000000000000 2000136851611381 2000000000000000 2048 8367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000136851611381/2000000000000000 : ℝ)) (X := (50013978983286309589/50000000000000000000 : ℝ)) (by norm_num) 8367 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023580513511689839/50000000000000000000 : ℝ) ≤ (5000577080120897/5000000000000000 : ℝ) ^ (8367/2048 : ℝ) := by
    have hpowers : (50023580513511689839/50000000000000000000 : ℝ)^2048 ≤ (5000577080120897/5000000000000000 : ℝ)^8367 := by
      have hnat : (50023580513511689839 : ℕ)^2048*5000000000000000^8367 ≤ 5000577080120897^8367*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023580513511689839 50000000000000000000 5000577080120897 5000000000000000 2048 8367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000577080120897/5000000000000000 : ℝ)) (X := (50023580513511689839/50000000000000000000 : ℝ)) (by norm_num) 8367 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033182043737070089/50000000000000000000 : ℝ) ≤ (10001624062426683/10000000000000000 : ℝ) ^ (8367/2048 : ℝ) := by
    have hpowers : (50033182043737070089/50000000000000000000 : ℝ)^2048 ≤ (10001624062426683/10000000000000000 : ℝ)^8367 := by
      have hnat : (50033182043737070089 : ℕ)^2048*10000000000000000^8367 ≤ 10001624062426683^8367*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033182043737070089 50000000000000000000 10001624062426683 10000000000000000 2048 8367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001624062426683/10000000000000000 : ℝ)) (X := (50033182043737070089/50000000000000000000 : ℝ)) (by norm_num) 8367 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13978983286309589/100000000000000000000 : ℝ) ≤ ((16769457610533101/16775000000000000 : ℝ)+2*(469902184889/268400000000000 : ℝ)*(1139/10000 : ℝ))^(8367/2048 : ℝ) := by
    rw [show (16769457610533101/16775000000000000 : ℝ)+2*(469902184889/268400000000000 : ℝ)*(1139/10000 : ℝ)=(2000136851611381/2000000000000000 : ℝ) by norm_num, show 1+2*(13978983286309589/100000000000000000000 : ℝ)=(50013978983286309589/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33182043737070089/100000000000000000000 : ℝ)+(13978983286309589/100000000000000000000 : ℝ) ≤ ((16769457610533101/16775000000000000 : ℝ)+(469902184889/268400000000000 : ℝ)*((7037/50000 : ℝ)+(1139/10000 : ℝ)))^(8367/2048 : ℝ) := by
    rw [show (16769457610533101/16775000000000000 : ℝ)+(469902184889/268400000000000 : ℝ)*((7037/50000 : ℝ)+(1139/10000 : ℝ))=(5000577080120897/5000000000000000 : ℝ) by norm_num, show 1+(33182043737070089/100000000000000000000 : ℝ)+(13978983286309589/100000000000000000000 : ℝ)=(50023580513511689839/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33182043737070089/100000000000000000000 : ℝ) ≤ ((16769457610533101/16775000000000000 : ℝ)+2*(469902184889/268400000000000 : ℝ)*(7037/50000 : ℝ))^(8367/2048 : ℝ) := by
    rw [show (16769457610533101/16775000000000000 : ℝ)+2*(469902184889/268400000000000 : ℝ)*(7037/50000 : ℝ)=(10001624062426683/10000000000000000 : ℝ) by norm_num, show 1+2*(33182043737070089/100000000000000000000 : ℝ)=(50033182043737070089/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (16769457610533101/16775000000000000 : ℝ)*(X 1 0+X 2 0)+(469902184889/268400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8367/2048 : ℝ)) (lo := (1139/10000 : ℝ)) (hi := (7037/50000 : ℝ)) (c := (16769457610533101/16775000000000000 : ℝ)) (alpha := (469902184889/268400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (16769457610533101/16775000000000000 : ℝ)*(X 0 1+X 2 1)+(469902184889/268400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8367/2048 : ℝ)) (lo := (1139/10000 : ℝ)) (hi := (7037/50000 : ℝ)) (c := (16769457610533101/16775000000000000 : ℝ)) (alpha := (469902184889/268400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (16769457610533101/16775000000000000 : ℝ)*(X 0 2+X 1 2)+(469902184889/268400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8367/2048 : ℝ)) (lo := (1139/10000 : ℝ)) (hi := (7037/50000 : ℝ)) (c := (16769457610533101/16775000000000000 : ℝ)) (alpha := (469902184889/268400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2151202431/10000000000 : ℝ)*X 0 0+(2696222781/5000000000 : ℝ)*X 0 1+(5266247157/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344630313/10000000000 : ℝ)*X 1 0+(-276900571/1250000000 : ℝ)*X 1 1+(5266247339/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672315187/5000000000 : ℝ)*X 2 0+(1316561881/2500000000 : ℝ)*X 2 1+(-2215204243/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4360044571/10000000000 : ℝ)*X 0 0+(4235504613/10000000000 : ℝ)*X 0 1+(2244099521/5000000000 : ℝ)*X 0 2+(4360044571/10000000000 : ℝ)*X 1 0+(4235504613/10000000000 : ℝ)*X 1 1+(2244099521/5000000000 : ℝ)*X 1 2+(4360044571/10000000000 : ℝ)*X 2 0+(4235504613/10000000000 : ℝ)*X 2 1+(2244099521/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2151206831/10000000000 : ℝ)*X 0 0+(1053312961/2000000000 : ℝ)*X 0 1+(5392127069/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((83009073/156250000 : ℝ)*X 1 0+(-2089324231/10000000000 : ℝ)*X 1 1+(5392127063/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312580619/10000000000 : ℝ)*X 2 0+(5392127103/10000000000 : ℝ)*X 2 1+(-261165531/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4360053881/10000000000 : ℝ)*X 0 0+(179502543/400000000 : ℝ)*X 0 1+(4236142697/10000000000 : ℝ)*X 0 2+(4360053881/10000000000 : ℝ)*X 1 0+(179502543/400000000 : ℝ)*X 1 1+(4236142697/10000000000 : ℝ)*X 1 2+(4360053881/10000000000 : ℝ)*X 2 0+(179502543/400000000 : ℝ)*X 2 1+(4236142697/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6447229190702834656791/671000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1323629881/100000000000000 : ℝ)*(base19) + (39082257/3125000000000 : ℝ)*(base23) + (184366513/100000000000000 : ℝ)*(upper3) + (17470309/20000000000000 : ℝ)*(upper4) + (121992371/20000000000000 : ℝ)*(upper5) + (297036978251081/5000000000000 : ℝ)*(major0) + (297036978251081/5000000000000 : ℝ)*(major1) + (297036978251081/5000000000000 : ℝ)*(major2) + (1981012980930619/25000000000000 : ℝ)*(sp0) + (7924097186217199/100000000000000 : ℝ)*(sp1) + (7924097259214857/100000000000000 : ℝ)*(sp2) + (123667755435233/3125000000000 : ℝ)*(sp3) + (11646531151/25000000000000 : ℝ)*(sp4) + (12125989053/100000000000000 : ℝ)*(sp7) + (3957380299916509/100000000000000 : ℝ)*(f.failure) + (198102462746177/2500000000000 : ℝ)*(f.sum) + (198185283539/67100000000000000000000000 : ℝ)*base65 + (123649416558567/15250000000000000000000000000 : ℝ)*base67 + (28727518377067/15250000000000000000000000000 : ℝ)*base69 + (142411944411683/15250000000000000000000000000 : ℝ)*base72 + (403597105117/167750000000000000000000000 : ℝ)*base73 + (41155256681183/15250000000000000000000000000 : ℝ)*base76 + (184900128815567/15250000000000000000000000000 : ℝ)*base77 + (606268201065433/15250000000000000000000000000 : ℝ)*base80 + (1179834816027/671000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (137127/2000000000000000000000 : ℝ)*base90 + (137127/2000000000000000000000 : ℝ)*base92 + (137127/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9571158075682123365360447/838750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2073423553/100000000000000 : ℝ)*(base19) + (565031587/25000000000000 : ℝ)*(base23) + (53122783/25000000000000 : ℝ)*(upper3) + (24702529/20000000000000 : ℝ)*(lower4) + (24932959/12500000000000 : ℝ)*(upper5) + (2985391239996531/50000000000000 : ℝ)*(major0) + (2985391239996531/50000000000000 : ℝ)*(major1) + (2985391239996531/50000000000000 : ℝ)*(major2) + (58638323053/100000000000000 : ℝ)*(sp1) + (16054610841/25000000000000 : ℝ)*(sp2) + (3982085705585021/50000000000000 : ℝ)*(sp4) + (1991027674855859/25000000000000 : ℝ)*(sp5) + (796410493260033/10000000000000 : ℝ)*(sp6) + (497174146055273/12500000000000 : ℝ)*(sp7) + (497174146055273/12500000000000 : ℝ)*(f.failure) + (3982085705585021/50000000000000 : ℝ)*(f.sum) + (13924929625361/6710000000000000000000000000 : ℝ)*base66 + (33042337902033/152500000000000000000000000000 : ℝ)*base68 + (54191087857967/152500000000000000000000000000 : ℝ)*base69 + (1399233576839533/152500000000000000000000000000 : ℝ)*base72 + (250652685741/6710000000000000000000000000 : ℝ)*base74 + (953161011534533/152500000000000000000000000000 : ℝ)*base76 + (1166855270152033/152500000000000000000000000000 : ℝ)*base78 + (3295231282592033/152500000000000000000000000000 : ℝ)*base80 + (1855811065299/6710000000000000000000000000 : ℝ)*base81 + (1276981/250000000000000000000 : ℝ)*base89 + (1276981/250000000000000000000 : ℝ)*base91 + (1276981/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1175_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30023597/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7037/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1139/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2279/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14069/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1175_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1175_s8_0 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-537801397/2500000000 : ℝ)*x 0 + (5392396901/10000000000 : ℝ)*x 1 + (5266293831/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537801397/2500000000 : ℝ)^523 ≤ (6537430345971/50000000000000 : ℝ)^395 := by
    have hnat : (537801397 : ℕ)^523*50000000000000^395 ≤ 6537430345971^395*2500000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537801397 2500000000 6537430345971 50000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392396901/10000000000 : ℝ)^523 ≤ (11035845148919/25000000000000 : ℝ)^395 := by
    have hnat : (5392396901 : ℕ)^523*25000000000000^395 ≤ 11035845148919^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392396901 10000000000 11035845148919 25000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266293831/10000000000 : ℝ)^523 ≤ (42781758699389/100000000000000 : ℝ)^395 := by
    have hnat : (5266293831 : ℕ)^523*100000000000000^395 ≤ 42781758699389^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266293831 10000000000 42781758699389 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-537801397/2500000000 : ℝ), (5392396901/10000000000 : ℝ), (5266293831/10000000000 : ℝ)] ![(6537430345971/50000000000000 : ℝ), (11035845148919/25000000000000 : ℝ), (42781758699389/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-537801397/2500000000 : ℝ)|^523 ≤ (6537430345971/50000000000000 : ℝ)^395
        have hw : |(-537801397/2500000000 : ℝ)|=(537801397/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392396901/10000000000 : ℝ)|^523 ≤ (11035845148919/25000000000000 : ℝ)^395
        have hw : |(5392396901/10000000000 : ℝ)|=(5392396901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266293831/10000000000 : ℝ)|^523 ≤ (42781758699389/100000000000000 : ℝ)^395
        have hw : |(5266293831/10000000000 : ℝ)|=(5266293831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1175_s8_1 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1336154657/2500000000 : ℝ)*x 0 + (-443031709/2000000000 : ℝ)*x 1 + (5266293843/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336154657/2500000000 : ℝ)^523 ≤ (8725251577219/20000000000000 : ℝ)^395 := by
    have hnat : (1336154657 : ℕ)^523*20000000000000^395 ≤ 8725251577219^395*2500000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336154657 2500000000 8725251577219 20000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (443031709/2000000000 : ℝ)^523 ≤ (13591983274037/100000000000000 : ℝ)^395 := by
    have hnat : (443031709 : ℕ)^523*100000000000000^395 ≤ 13591983274037^395*2000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      443031709 2000000000 13591983274037 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266293843/10000000000 : ℝ)^523 ≤ (42781758828463/100000000000000 : ℝ)^395 := by
    have hnat : (5266293843 : ℕ)^523*100000000000000^395 ≤ 42781758828463^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266293843 10000000000 42781758828463 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336154657/2500000000 : ℝ), (-443031709/2000000000 : ℝ), (5266293843/10000000000 : ℝ)] ![(8725251577219/20000000000000 : ℝ), (13591983274037/100000000000000 : ℝ), (42781758828463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336154657/2500000000 : ℝ)|^523 ≤ (8725251577219/20000000000000 : ℝ)^395
        have hw : |(1336154657/2500000000 : ℝ)|=(1336154657/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-443031709/2000000000 : ℝ)|^523 ≤ (13591983274037/100000000000000 : ℝ)^395
        have hw : |(-443031709/2000000000 : ℝ)|=(443031709/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266293843/10000000000 : ℝ)|^523 ≤ (42781758828463/100000000000000 : ℝ)^395
        have hw : |(5266293843/10000000000 : ℝ)|=(5266293843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1175_s8_2 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5344618637/10000000000 : ℝ)*x 0 + (2633146913/5000000000 : ℝ)*x 1 + (-553789639/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344618637/10000000000 : ℝ)^523 ≤ (10906564495841/25000000000000 : ℝ)^395 := by
    have hnat : (5344618637 : ℕ)^523*25000000000000^395 ≤ 10906564495841^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344618637 10000000000 10906564495841 25000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633146913/5000000000 : ℝ)^523 ≤ (5347719830701/12500000000000 : ℝ)^395 := by
    have hnat : (2633146913 : ℕ)^523*12500000000000^395 ≤ 5347719830701^395*5000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633146913 5000000000 5347719830701 12500000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (553789639/2500000000 : ℝ)^523 ≤ (3397995840851/25000000000000 : ℝ)^395 := by
    have hnat : (553789639 : ℕ)^523*25000000000000^395 ≤ 3397995840851^395*2500000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      553789639 2500000000 3397995840851 25000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344618637/10000000000 : ℝ), (2633146913/5000000000 : ℝ), (-553789639/2500000000 : ℝ)] ![(10906564495841/25000000000000 : ℝ), (5347719830701/12500000000000 : ℝ), (3397995840851/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344618637/10000000000 : ℝ)|^523 ≤ (10906564495841/25000000000000 : ℝ)^395
        have hw : |(5344618637/10000000000 : ℝ)|=(5344618637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633146913/5000000000 : ℝ)|^523 ≤ (5347719830701/12500000000000 : ℝ)^395
        have hw : |(2633146913/5000000000 : ℝ)|=(2633146913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-553789639/2500000000 : ℝ)|^523 ≤ (3397995840851/25000000000000 : ℝ)^395
        have hw : |(-553789639/2500000000 : ℝ)|=(553789639/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1175_s8_3 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4360046677/10000000000 : ℝ)*x 0 + (4235599827/10000000000 : ℝ)*x 1 + (561012939/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4360046677/10000000000 : ℝ)^523 ≤ (8329290758429/25000000000000 : ℝ)^395 := by
    have hnat : (4360046677 : ℕ)^523*25000000000000^395 ≤ 8329290758429^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4360046677 10000000000 8329290758429 25000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4235599827/10000000000 : ℝ)^523 ≤ (16031954459951/50000000000000 : ℝ)^395 := by
    have hnat : (4235599827 : ℕ)^523*50000000000000^395 ≤ 16031954459951^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4235599827 10000000000 16031954459951 50000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (561012939/1250000000 : ℝ)^523 ≤ (17309464015349/50000000000000 : ℝ)^395 := by
    have hnat : (561012939 : ℕ)^523*50000000000000^395 ≤ 17309464015349^395*1250000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561012939 1250000000 17309464015349 50000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4360046677/10000000000 : ℝ), (4235599827/10000000000 : ℝ), (561012939/1250000000 : ℝ)] ![(8329290758429/25000000000000 : ℝ), (16031954459951/50000000000000 : ℝ), (17309464015349/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4360046677/10000000000 : ℝ)|^523 ≤ (8329290758429/25000000000000 : ℝ)^395
        have hw : |(4360046677/10000000000 : ℝ)|=(4360046677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4235599827/10000000000 : ℝ)|^523 ≤ (16031954459951/50000000000000 : ℝ)^395
        have hw : |(4235599827/10000000000 : ℝ)|=(4235599827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(561012939/1250000000 : ℝ)|^523 ≤ (17309464015349/50000000000000 : ℝ)^395
        have hw : |(561012939/1250000000 : ℝ)|=(561012939/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1175_s8_4 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-537802597/2500000000 : ℝ)*x 0 + (1316652717/2500000000 : ℝ)*x 1 + (1348019679/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537802597/2500000000 : ℝ)^523 ≤ (6537449659923/50000000000000 : ℝ)^395 := by
    have hnat : (537802597 : ℕ)^523*50000000000000^395 ≤ 6537449659923^395*2500000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537802597 2500000000 6537449659923 50000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316652717/2500000000 : ℝ)^523 ≤ (4278516884031/10000000000000 : ℝ)^395 := by
    have hnat : (1316652717 : ℕ)^523*10000000000000^395 ≤ 4278516884031^395*2500000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316652717 2500000000 4278516884031 10000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348019679/2500000000 : ℝ)^523 ≤ (8827986365691/20000000000000 : ℝ)^395 := by
    have hnat : (1348019679 : ℕ)^523*20000000000000^395 ≤ 8827986365691^395*2500000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348019679 2500000000 8827986365691 20000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-537802597/2500000000 : ℝ), (1316652717/2500000000 : ℝ), (1348019679/2500000000 : ℝ)] ![(6537449659923/50000000000000 : ℝ), (4278516884031/10000000000000 : ℝ), (8827986365691/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-537802597/2500000000 : ℝ)|^523 ≤ (6537449659923/50000000000000 : ℝ)^395
        have hw : |(-537802597/2500000000 : ℝ)|=(537802597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316652717/2500000000 : ℝ)|^523 ≤ (4278516884031/10000000000000 : ℝ)^395
        have hw : |(1316652717/2500000000 : ℝ)|=(1316652717/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348019679/2500000000 : ℝ)|^523 ≤ (8827986365691/20000000000000 : ℝ)^395
        have hw : |(1348019679/2500000000 : ℝ)|=(1348019679/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1175_s8_5 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2656296343/5000000000 : ℝ)*x 0 + (-1044686857/5000000000 : ℝ)*x 1 + (674009839/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656296343/5000000000 : ℝ)^523 ≤ (43280465584019/100000000000000 : ℝ)^395 := by
    have hnat : (2656296343 : ℕ)^523*100000000000000^395 ≤ 43280465584019^395*5000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656296343 5000000000 43280465584019 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1044686857/5000000000 : ℝ)^523 ≤ (2515920522837/20000000000000 : ℝ)^395 := by
    have hnat : (1044686857 : ℕ)^523*20000000000000^395 ≤ 2515920522837^395*5000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044686857 5000000000 2515920522837 20000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674009839/1250000000 : ℝ)^523 ≤ (441399317851/1000000000000 : ℝ)^395 := by
    have hnat : (674009839 : ℕ)^523*1000000000000^395 ≤ 441399317851^395*1250000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674009839 1250000000 441399317851 1000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656296343/5000000000 : ℝ), (-1044686857/5000000000 : ℝ), (674009839/1250000000 : ℝ)] ![(43280465584019/100000000000000 : ℝ), (2515920522837/20000000000000 : ℝ), (441399317851/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656296343/5000000000 : ℝ)|^523 ≤ (43280465584019/100000000000000 : ℝ)^395
        have hw : |(2656296343/5000000000 : ℝ)|=(2656296343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1044686857/5000000000 : ℝ)|^523 ≤ (2515920522837/20000000000000 : ℝ)^395
        have hw : |(-1044686857/5000000000 : ℝ)|=(1044686857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674009839/1250000000 : ℝ)|^523 ≤ (441399317851/1000000000000 : ℝ)^395
        have hw : |(674009839/1250000000 : ℝ)|=(674009839/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1175_s8_6 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1062518553/2000000000 : ℝ)*x 0 + (2696039357/5000000000 : ℝ)*x 1 + (-417874721/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062518553/2000000000 : ℝ)^523 ≤ (43280466436171/100000000000000 : ℝ)^395 := by
    have hnat : (1062518553 : ℕ)^523*100000000000000^395 ≤ 43280466436171^395*2000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062518553 2000000000 43280466436171 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696039357/5000000000 : ℝ)^523 ≤ (44139931806777/100000000000000 : ℝ)^395 := by
    have hnat : (2696039357 : ℕ)^523*100000000000000^395 ≤ 44139931806777^395*5000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696039357 5000000000 44139931806777 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (417874721/2000000000 : ℝ)^523 ≤ (12579601745261/100000000000000 : ℝ)^395 := by
    have hnat : (417874721 : ℕ)^523*100000000000000^395 ≤ 12579601745261^395*2000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417874721 2000000000 12579601745261 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062518553/2000000000 : ℝ), (2696039357/5000000000 : ℝ), (-417874721/2000000000 : ℝ)] ![(43280466436171/100000000000000 : ℝ), (44139931806777/100000000000000 : ℝ), (12579601745261/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062518553/2000000000 : ℝ)|^523 ≤ (43280466436171/100000000000000 : ℝ)^395
        have hw : |(1062518553/2000000000 : ℝ)|=(1062518553/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696039357/5000000000 : ℝ)|^523 ≤ (44139931806777/100000000000000 : ℝ)^395
        have hw : |(2696039357/5000000000 : ℝ)|=(2696039357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-417874721/2000000000 : ℝ)|^523 ≤ (12579601745261/100000000000000 : ℝ)^395
        have hw : |(-417874721/2000000000 : ℝ)|=(417874721/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1175_s8_7 (p : ℝ) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4360056349/10000000000 : ℝ)*x 0 + (2243734357/5000000000 : ℝ)*x 1 + (847247371/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4360056349/10000000000 : ℝ)^523 ≤ (33317260892071/100000000000000 : ℝ)^395 := by
    have hnat : (4360056349 : ℕ)^523*100000000000000^395 ≤ 33317260892071^395*10000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4360056349 10000000000 33317260892071 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2243734357/5000000000 : ℝ)^523 ≤ (17306222478631/50000000000000 : ℝ)^395 := by
    have hnat : (2243734357 : ℕ)^523*50000000000000^395 ≤ 17306222478631^395*5000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2243734357 5000000000 17306222478631 50000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (847247371/2000000000 : ℝ)^523 ≤ (32070294130737/100000000000000 : ℝ)^395 := by
    have hnat : (847247371 : ℕ)^523*100000000000000^395 ≤ 32070294130737^395*2000000000^523 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      847247371 2000000000 32070294130737 100000000000000 523 395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (523/128 : ℝ)) 523 395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4360056349/10000000000 : ℝ), (2243734357/5000000000 : ℝ), (847247371/2000000000 : ℝ)] ![(33317260892071/100000000000000 : ℝ), (17306222478631/50000000000000 : ℝ), (32070294130737/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4360056349/10000000000 : ℝ)|^523 ≤ (33317260892071/100000000000000 : ℝ)^395
        have hw : |(4360056349/10000000000 : ℝ)|=(4360056349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2243734357/5000000000 : ℝ)|^523 ≤ (17306222478631/50000000000000 : ℝ)^395
        have hw : |(2243734357/5000000000 : ℝ)|=(2243734357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(847247371/2000000000 : ℝ)|^523 ≤ (32070294130737/100000000000000 : ℝ)^395
        have hw : |(847247371/2000000000 : ℝ)|=(847247371/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1175_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30023597/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14069/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2279/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (2849/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14067/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14069/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2279/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14069/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2279/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14069/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2279/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14069/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2279/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14069/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2279/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14069/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2279/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2279/20000 : ℝ) ^ (8367/2048 : ℝ) ≤ (175050883676051/1250000000000000000 : ℝ) := by
    have hpowers : (2279/20000 : ℝ)^8367 ≤ (175050883676051/1250000000000000000 : ℝ)^2048 := by
      have hnat : (2279 : ℕ)^8367*1250000000000000000^2048 ≤ 175050883676051^2048*20000^8367 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2279 20000 175050883676051 1250000000000000000 8367 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2279/20000 : ℝ)) (X := (175050883676051/1250000000000000000 : ℝ)) (by norm_num) (by norm_num) 8367 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14069/100000 : ℝ) ^ (8367/2048 : ℝ) ≤ (662678182728719/2000000000000000000 : ℝ) := by
    have hpowers : (14069/100000 : ℝ)^8367 ≤ (662678182728719/2000000000000000000 : ℝ)^2048 := by
      have hnat : (14069 : ℕ)^8367*2000000000000000000^2048 ≤ 662678182728719^2048*100000^8367 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14069 100000 662678182728719 2000000000000000000 8367 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14069/100000 : ℝ)) (X := (662678182728719/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8367 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (625175050883676051/625000000000000000 : ℝ) ≤ (10000685485932023/10000000000000000 : ℝ) ^ (8367/2048 : ℝ) := by
    have hpowers : (625175050883676051/625000000000000000 : ℝ)^2048 ≤ (10000685485932023/10000000000000000 : ℝ)^8367 := by
      have hnat : (625175050883676051 : ℕ)^2048*10000000000000000^8367 ≤ 10000685485932023^8367*625000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        625175050883676051 625000000000000000 10000685485932023 10000000000000000 2048 8367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000685485932023/10000000000000000 : ℝ)) (X := (625175050883676051/625000000000000000 : ℝ)) (by norm_num) 8367 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (10004713797983052003/10000000000000000000 : ℝ) ≤ (5000576798156929/5000000000000000 : ℝ) ^ (8367/2048 : ℝ) := by
    have hpowers : (10004713797983052003/10000000000000000000 : ℝ)^2048 ≤ (5000576798156929/5000000000000000 : ℝ)^8367 := by
      have hnat : (10004713797983052003 : ℕ)^2048*5000000000000000^8367 ≤ 5000576798156929^8367*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004713797983052003 10000000000000000000 5000576798156929 5000000000000000 2048 8367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000576798156929/5000000000000000 : ℝ)) (X := (10004713797983052003/10000000000000000000 : ℝ)) (by norm_num) 8367 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (1000662678182728719/1000000000000000000 : ℝ) ≤ (10001621706695693/10000000000000000 : ℝ) ^ (8367/2048 : ℝ) := by
    have hpowers : (1000662678182728719/1000000000000000000 : ℝ)^2048 ≤ (10001621706695693/10000000000000000 : ℝ)^8367 := by
      have hnat : (1000662678182728719 : ℕ)^2048*10000000000000000^8367 ≤ 10001621706695693^8367*1000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000662678182728719 1000000000000000000 10001621706695693 10000000000000000 2048 8367 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001621706695693/10000000000000000 : ℝ)) (X := (1000662678182728719/1000000000000000000 : ℝ)) (by norm_num) 8367 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(175050883676051/1250000000000000000 : ℝ) ≤ ((6682791188445052463/6685000000000000000 : ℝ)+2*(93622076367/53480000000000 : ℝ)*(2279/20000 : ℝ))^(8367/2048 : ℝ) := by
    rw [show (6682791188445052463/6685000000000000000 : ℝ)+2*(93622076367/53480000000000 : ℝ)*(2279/20000 : ℝ)=(10000685485932023/10000000000000000 : ℝ) by norm_num, show 1+2*(175050883676051/1250000000000000000 : ℝ)=(625175050883676051/625000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(662678182728719/2000000000000000000 : ℝ)+(175050883676051/1250000000000000000 : ℝ) ≤ ((6682791188445052463/6685000000000000000 : ℝ)+(93622076367/53480000000000 : ℝ)*((14069/100000 : ℝ)+(2279/20000 : ℝ)))^(8367/2048 : ℝ) := by
    rw [show (6682791188445052463/6685000000000000000 : ℝ)+(93622076367/53480000000000 : ℝ)*((14069/100000 : ℝ)+(2279/20000 : ℝ))=(5000576798156929/5000000000000000 : ℝ) by norm_num, show 1+(662678182728719/2000000000000000000 : ℝ)+(175050883676051/1250000000000000000 : ℝ)=(10004713797983052003/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(662678182728719/2000000000000000000 : ℝ) ≤ ((6682791188445052463/6685000000000000000 : ℝ)+2*(93622076367/53480000000000 : ℝ)*(14069/100000 : ℝ))^(8367/2048 : ℝ) := by
    rw [show (6682791188445052463/6685000000000000000 : ℝ)+2*(93622076367/53480000000000 : ℝ)*(14069/100000 : ℝ)=(10001621706695693/10000000000000000 : ℝ) by norm_num, show 1+2*(662678182728719/2000000000000000000 : ℝ)=(1000662678182728719/1000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6682791188445052463/6685000000000000000 : ℝ)*(X 1 0+X 2 0)+(93622076367/53480000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8367/2048 : ℝ)) (lo := (2279/20000 : ℝ)) (hi := (14069/100000 : ℝ)) (c := (6682791188445052463/6685000000000000000 : ℝ)) (alpha := (93622076367/53480000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6682791188445052463/6685000000000000000 : ℝ)*(X 0 1+X 2 1)+(93622076367/53480000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8367/2048 : ℝ)) (lo := (2279/20000 : ℝ)) (hi := (14069/100000 : ℝ)) (c := (6682791188445052463/6685000000000000000 : ℝ)) (alpha := (93622076367/53480000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6682791188445052463/6685000000000000000 : ℝ)*(X 0 2+X 1 2)+(93622076367/53480000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8367/2048 : ℝ)) (lo := (2279/20000 : ℝ)) (hi := (14069/100000 : ℝ)) (c := (6682791188445052463/6685000000000000000 : ℝ)) (alpha := (93622076367/53480000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-537801397/2500000000 : ℝ)*X 0 0+(5392396901/10000000000 : ℝ)*X 0 1+(5266293831/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336154657/2500000000 : ℝ)*X 1 0+(-443031709/2000000000 : ℝ)*X 1 1+(5266293843/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344618637/10000000000 : ℝ)*X 2 0+(2633146913/5000000000 : ℝ)*X 2 1+(-553789639/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4360046677/10000000000 : ℝ)*X 0 0+(4235599827/10000000000 : ℝ)*X 0 1+(561012939/1250000000 : ℝ)*X 0 2+(4360046677/10000000000 : ℝ)*X 1 0+(4235599827/10000000000 : ℝ)*X 1 1+(561012939/1250000000 : ℝ)*X 1 2+(4360046677/10000000000 : ℝ)*X 2 0+(4235599827/10000000000 : ℝ)*X 2 1+(561012939/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-537802597/2500000000 : ℝ)*X 0 0+(1316652717/2500000000 : ℝ)*X 0 1+(1348019679/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656296343/5000000000 : ℝ)*X 1 0+(-1044686857/5000000000 : ℝ)*X 1 1+(674009839/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062518553/2000000000 : ℝ)*X 2 0+(2696039357/5000000000 : ℝ)*X 2 1+(-417874721/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4360056349/10000000000 : ℝ)*X 0 0+(2243734357/5000000000 : ℝ)*X 0 1+(847247371/2000000000 : ℝ)*X 0 2+(4360056349/10000000000 : ℝ)*X 1 0+(2243734357/5000000000 : ℝ)*X 1 1+(847247371/2000000000 : ℝ)*X 1 2+(4360056349/10000000000 : ℝ)*X 2 0+(2243734357/5000000000 : ℝ)*X 2 1+(847247371/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1175_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (703406304506006236513490499/83562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (204721499/12500000000000 : ℝ)*(base19) + (307815211/20000000000000 : ℝ)*(base23) + (59886317/100000000000000 : ℝ)*(lower2) + (109127021/50000000000000 : ℝ)*(upper3) + (15068069/12500000000000 : ℝ)*(upper5) + (1486312322850491/25000000000000 : ℝ)*(major0) + (1486312322850491/25000000000000 : ℝ)*(major1) + (1486312322850491/25000000000000 : ℝ)*(major2) + (3965034420487879/50000000000000 : ℝ)*(sp0) + (1586022448642529/20000000000000 : ℝ)*(sp1) + (7930112341908581/100000000000000 : ℝ)*(sp2) + (3960359940896553/100000000000000 : ℝ)*(sp3) + (22520004439/50000000000000 : ℝ)*(sp4) + (3060041479/12500000000000 : ℝ)*(sp7) + (1980192210614193/50000000000000 : ℝ)*(f.failure) + (1982528470246159/25000000000000 : ℝ)*(f.sum) + (1814894617997/1337000000000000000000000000 : ℝ)*base65 + (90063695103884381/23875000000000000000000000000000 : ℝ)*base68 + (399238728077759381/23875000000000000000000000000000 : ℝ)*base70 + (67397829389884381/23875000000000000000000000000000 : ℝ)*base72 + (90219243851/334250000000000000000000000 : ℝ)*base74 + (149588904284865619/23875000000000000000000000000000 : ℝ)*base75 + (430857351851740619/23875000000000000000000000000000 : ℝ)*base77 + (95557543754384381/23875000000000000000000000000000 : ℝ)*base80 + (3521531031813/668500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (13112221/1000000000000000000000 : ℝ)*base89 + (13112221/1000000000000000000000 : ℝ)*base91 + (13112221/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (127019018378645312305203651/66850000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (82034953/25000000000000 : ℝ)*(base19) + (584495919/100000000000000 : ℝ)*(base23) + (5038939/6250000000000 : ℝ)*(lower1) + (3369657/5000000000000 : ℝ)*(upper3) + (37296113/100000000000000 : ℝ)*(lower4) + (36742331/100000000000000 : ℝ)*(upper5) + (1195054715990641/20000000000000 : ℝ)*(major0) + (1195054715990641/20000000000000 : ℝ)*(major1) + (1195054715990641/20000000000000 : ℝ)*(major2) + (11219417699/100000000000000 : ℝ)*(sp2) + (7970162214670847/100000000000000 : ℝ)*(sp4) + (1594032377306207/20000000000000 : ℝ)*(sp5) + (7970150410757229/100000000000000 : ℝ)*(sp6) + (995096220475049/25000000000000 : ℝ)*(sp7) + (995096220475049/25000000000000 : ℝ)*(f.failure) + (7970162214670847/100000000000000 : ℝ)*(f.sum) + (2173796462603/2674000000000000000000000000 : ℝ)*base65 + (722271286799981969/19100000000000000000000000000000 : ℝ)*base67 + (388909763562781969/19100000000000000000000000000000 : ℝ)*base69 + (451380189533418031/19100000000000000000000000000000 : ℝ)*base72 + (15365686666761/2674000000000000000000000000 : ℝ)*base74 + (2214352134776018031/19100000000000000000000000000000 : ℝ)*base76 + (410662126700781969/19100000000000000000000000000000 : ℝ)*base77 + (362840139335581969/19100000000000000000000000000000 : ℝ)*base79 + (6380761560701/2674000000000000000000000000 : ℝ)*base81 + (5268747/500000000000000000000 : ℝ)*base90 + (5268747/500000000000000000000 : ℝ)*base92 + (5268747/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1175_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30023597/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14069/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2279/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2849/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14067/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1175_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1175_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30023597/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7051/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11363/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2849/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14067/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1175_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1175_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1175_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8367/2048 : ℝ) ≤ p) (hpb : p ≤ (523/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30023597/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7051/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11363/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2849/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14067/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1175_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
