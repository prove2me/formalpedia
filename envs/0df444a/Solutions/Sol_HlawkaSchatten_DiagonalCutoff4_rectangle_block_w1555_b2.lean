-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1555_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:11:23.590814+00:00
-- url     : https://prove2.me/submissions/77922d47-b035-44a2-a97b-326a7933b01a

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
theorem support_rectangle_w1555_s6_0 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-361262913/2000000000 : ℝ)*x 0 + (5427692331/10000000000 : ℝ)*x 1 + (1304882319/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (361262913/2000000000 : ℝ)^4607 ≤ (11076163854569/100000000000000 : ℝ)^3583 := by
    have hnat : (361262913 : ℕ)^4607*100000000000000^3583 ≤ 11076163854569^3583*2000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      361262913 2000000000 11076163854569 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5427692331/10000000000 : ℝ)^4607 ≤ (712180147251/1562500000000 : ℝ)^3583 := by
    have hnat : (5427692331 : ℕ)^4607*1562500000000^3583 ≤ 712180147251^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427692331 10000000000 712180147251 1562500000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1304882319/2500000000 : ℝ)^4607 ≤ (43344306698197/100000000000000 : ℝ)^3583 := by
    have hnat : (1304882319 : ℕ)^4607*100000000000000^3583 ≤ 43344306698197^3583*2500000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304882319 2500000000 43344306698197 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-361262913/2000000000 : ℝ), (5427692331/10000000000 : ℝ), (1304882319/2500000000 : ℝ)] ![(11076163854569/100000000000000 : ℝ), (712180147251/1562500000000 : ℝ), (43344306698197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-361262913/2000000000 : ℝ)|^4607 ≤ (11076163854569/100000000000000 : ℝ)^3583
        have hw : |(-361262913/2000000000 : ℝ)|=(361262913/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5427692331/10000000000 : ℝ)|^4607 ≤ (712180147251/1562500000000 : ℝ)^3583
        have hw : |(5427692331/10000000000 : ℝ)|=(5427692331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1304882319/2500000000 : ℝ)|^4607 ≤ (43344306698197/100000000000000 : ℝ)^3583
        have hw : |(1304882319/2500000000 : ℝ)|=(1304882319/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1555_s6_1 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349099607/10000000000 : ℝ)*x 0 + (-956418331/5000000000 : ℝ)*x 1 + (2609764991/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349099607/10000000000 : ℝ)^4607 ≤ (44732680988453/100000000000000 : ℝ)^3583 := by
    have hnat : (5349099607 : ℕ)^4607*100000000000000^3583 ≤ 44732680988453^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349099607 10000000000 44732680988453 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (956418331/5000000000 : ℝ)^4607 ≤ (238460095233/2000000000000 : ℝ)^3583 := by
    have hnat : (956418331 : ℕ)^4607*2000000000000^3583 ≤ 238460095233^3583*5000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      956418331 5000000000 238460095233 2000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2609764991/5000000000 : ℝ)^4607 ≤ (43344314236557/100000000000000 : ℝ)^3583 := by
    have hnat : (2609764991 : ℕ)^4607*100000000000000^3583 ≤ 43344314236557^3583*5000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609764991 5000000000 43344314236557 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349099607/10000000000 : ℝ), (-956418331/5000000000 : ℝ), (2609764991/5000000000 : ℝ)] ![(44732680988453/100000000000000 : ℝ), (238460095233/2000000000000 : ℝ), (43344314236557/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349099607/10000000000 : ℝ)|^4607 ≤ (44732680988453/100000000000000 : ℝ)^3583
        have hw : |(5349099607/10000000000 : ℝ)|=(5349099607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-956418331/5000000000 : ℝ)|^4607 ≤ (238460095233/2000000000000 : ℝ)^3583
        have hw : |(-956418331/5000000000 : ℝ)|=(956418331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2609764991/5000000000 : ℝ)|^4607 ≤ (43344314236557/100000000000000 : ℝ)^3583
        have hw : |(2609764991/5000000000 : ℝ)|=(2609764991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1555_s6_2 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349100093/10000000000 : ℝ)*x 0 + (2609764637/5000000000 : ℝ)*x 1 + (-1912836953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349100093/10000000000 : ℝ)^4607 ≤ (44732686214243/100000000000000 : ℝ)^3583 := by
    have hnat : (5349100093 : ℕ)^4607*100000000000000^3583 ≤ 44732686214243^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349100093 10000000000 44732686214243 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609764637/5000000000 : ℝ)^4607 ≤ (21672153338421/50000000000000 : ℝ)^3583 := by
    have hnat : (2609764637 : ℕ)^4607*50000000000000^3583 ≤ 21672153338421^3583*5000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609764637 5000000000 21672153338421 50000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1912836953/10000000000 : ℝ)^4607 ≤ (2384601418777/20000000000000 : ℝ)^3583 := by
    have hnat : (1912836953 : ℕ)^4607*20000000000000^3583 ≤ 2384601418777^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1912836953 10000000000 2384601418777 20000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349100093/10000000000 : ℝ), (2609764637/5000000000 : ℝ), (-1912836953/10000000000 : ℝ)] ![(44732686214243/100000000000000 : ℝ), (21672153338421/50000000000000 : ℝ), (2384601418777/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349100093/10000000000 : ℝ)|^4607 ≤ (44732686214243/100000000000000 : ℝ)^3583
        have hw : |(5349100093/10000000000 : ℝ)|=(5349100093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609764637/5000000000 : ℝ)|^4607 ≤ (21672153338421/50000000000000 : ℝ)^3583
        have hw : |(2609764637/5000000000 : ℝ)|=(2609764637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1912836953/10000000000 : ℝ)|^4607 ≤ (2384601418777/20000000000000 : ℝ)^3583
        have hw : |(-1912836953/10000000000 : ℝ)|=(1912836953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1555_s6_3 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (850031849/2000000000 : ℝ)*x 0 + (4012679439/10000000000 : ℝ)*x 1 + (1124761051/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (850031849/2000000000 : ℝ)^4607 ≤ (33281709749311/100000000000000 : ℝ)^3583 := by
    have hnat : (850031849 : ℕ)^4607*100000000000000^3583 ≤ 33281709749311^3583*2000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      850031849 2000000000 33281709749311 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4012679439/10000000000 : ℝ)^4607 ≤ (30909957344217/100000000000000 : ℝ)^3583 := by
    have hnat : (4012679439 : ℕ)^4607*100000000000000^3583 ≤ 30909957344217^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4012679439 10000000000 30909957344217 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1124761051/2500000000 : ℝ)^4607 ≤ (35808332899637/100000000000000 : ℝ)^3583 := by
    have hnat : (1124761051 : ℕ)^4607*100000000000000^3583 ≤ 35808332899637^3583*2500000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124761051 2500000000 35808332899637 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(850031849/2000000000 : ℝ), (4012679439/10000000000 : ℝ), (1124761051/2500000000 : ℝ)] ![(33281709749311/100000000000000 : ℝ), (30909957344217/100000000000000 : ℝ), (35808332899637/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(850031849/2000000000 : ℝ)|^4607 ≤ (33281709749311/100000000000000 : ℝ)^3583
        have hw : |(850031849/2000000000 : ℝ)|=(850031849/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4012679439/10000000000 : ℝ)|^4607 ≤ (30909957344217/100000000000000 : ℝ)^3583
        have hw : |(4012679439/10000000000 : ℝ)|=(4012679439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1124761051/2500000000 : ℝ)|^4607 ≤ (35808332899637/100000000000000 : ℝ)^3583
        have hw : |(1124761051/2500000000 : ℝ)|=(1124761051/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1555_s6_4 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1806341859/10000000000 : ℝ)*x 0 + (5220610281/10000000000 : ℝ)*x 1 + (5426603349/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1806341859/10000000000 : ℝ)^4607 ≤ (1384547381403/12500000000000 : ℝ)^3583 := by
    have hnat : (1806341859 : ℕ)^4607*12500000000000^3583 ≤ 1384547381403^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1806341859 10000000000 1384547381403 12500000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5220610281/10000000000 : ℝ)^4607 ≤ (21677924769179/50000000000000 : ℝ)^3583 := by
    have hnat : (5220610281 : ℕ)^4607*50000000000000^3583 ≤ 21677924769179^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220610281 10000000000 21677924769179 50000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5426603349/10000000000 : ℝ)^4607 ≤ (9113554280411/20000000000000 : ℝ)^3583 := by
    have hnat : (5426603349 : ℕ)^4607*20000000000000^3583 ≤ 9113554280411^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426603349 10000000000 9113554280411 20000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1806341859/10000000000 : ℝ), (5220610281/10000000000 : ℝ), (5426603349/10000000000 : ℝ)] ![(1384547381403/12500000000000 : ℝ), (21677924769179/50000000000000 : ℝ), (9113554280411/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1806341859/10000000000 : ℝ)|^4607 ≤ (1384547381403/12500000000000 : ℝ)^3583
        have hw : |(-1806341859/10000000000 : ℝ)|=(1806341859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5220610281/10000000000 : ℝ)|^4607 ≤ (21677924769179/50000000000000 : ℝ)^3583
        have hw : |(5220610281/10000000000 : ℝ)|=(5220610281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5426603349/10000000000 : ℝ)|^4607 ≤ (9113554280411/20000000000000 : ℝ)^3583
        have hw : |(5426603349/10000000000 : ℝ)|=(5426603349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1555_s6_5 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (850044629/2000000000 : ℝ)*x 0 + (4496519009/10000000000 : ℝ)*x 1 + (1003805791/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (850044629/2000000000 : ℝ)^4607 ≤ (4160294142287/12500000000000 : ℝ)^3583 := by
    have hnat : (850044629 : ℕ)^4607*12500000000000^3583 ≤ 4160294142287^3583*2000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      850044629 2000000000 4160294142287 12500000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4496519009/10000000000 : ℝ)^4607 ≤ (35782492731891/100000000000000 : ℝ)^3583 := by
    have hnat : (4496519009 : ℕ)^4607*100000000000000^3583 ≤ 35782492731891^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4496519009 10000000000 35782492731891 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1003805791/2500000000 : ℝ)^4607 ≤ (483361783001/1562500000000 : ℝ)^3583 := by
    have hnat : (1003805791 : ℕ)^4607*1562500000000^3583 ≤ 483361783001^3583*2500000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1003805791 2500000000 483361783001 1562500000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(850044629/2000000000 : ℝ), (4496519009/10000000000 : ℝ), (1003805791/2500000000 : ℝ)] ![(4160294142287/12500000000000 : ℝ), (35782492731891/100000000000000 : ℝ), (483361783001/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(850044629/2000000000 : ℝ)|^4607 ≤ (4160294142287/12500000000000 : ℝ)^3583
        have hw : |(850044629/2000000000 : ℝ)|=(850044629/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4496519009/10000000000 : ℝ)|^4607 ≤ (35782492731891/100000000000000 : ℝ)^3583
        have hw : |(4496519009/10000000000 : ℝ)|=(4496519009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1003805791/2500000000 : ℝ)|^4607 ≤ (483361783001/1562500000000 : ℝ)^3583
        have hw : |(1003805791/2500000000 : ℝ)|=(1003805791/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1555_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41705747/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11071/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (346/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3097/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11071/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11071/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11071/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11071/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11071/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11071/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11071/100000 : ℝ) ^ (4605/1024 : ℝ) ≤ (5030846451944193/100000000000000000000 : ℝ) := by
    have hpowers : (11071/100000 : ℝ)^4605 ≤ (5030846451944193/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11071 : ℕ)^4605*100000000000000000000^1024 ≤ 5030846451944193^1024*100000^4605 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11071 100000 5030846451944193 100000000000000000000 4605 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11071/100000 : ℝ)) (X := (5030846451944193/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4605 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3097/20000 : ℝ) ^ (4605/1024 : ℝ) ≤ (4549919849571131/20000000000000000000 : ℝ) := by
    have hpowers : (3097/20000 : ℝ)^4605 ≤ (4549919849571131/20000000000000000000 : ℝ)^1024 := by
      have hnat : (3097 : ℕ)^4605*20000000000000000000^1024 ≤ 4549919849571131^1024*20000^4605 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3097 20000 4549919849571131 20000000000000000000 4605 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3097/20000 : ℝ)) (X := (4549919849571131/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4605 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005030846451944193/50000000000000000000 : ℝ) ≤ (10000223730086467/10000000000000000 : ℝ) ^ (4605/1024 : ℝ) := by
    have hpowers : (50005030846451944193/50000000000000000000 : ℝ)^1024 ≤ (10000223730086467/10000000000000000 : ℝ)^4605 := by
      have hnat : (50005030846451944193 : ℕ)^1024*10000000000000000^4605 ≤ 10000223730086467^4605*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005030846451944193 50000000000000000000 10000223730086467 10000000000000000 1024 4605 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000223730086467/10000000000000000 : ℝ)) (X := (50005030846451944193/50000000000000000000 : ℝ)) (by norm_num) 4605 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12503472555712474981/12500000000000000000 : ℝ) ≤ (1250077209837627/1250000000000000 : ℝ) ^ (4605/1024 : ℝ) := by
    have hpowers : (12503472555712474981/12500000000000000000 : ℝ)^1024 ≤ (1250077209837627/1250000000000000 : ℝ)^4605 := by
      have hnat : (12503472555712474981 : ℕ)^1024*1250000000000000^4605 ≤ 1250077209837627^4605*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503472555712474981 12500000000000000000 1250077209837627 1250000000000000 1024 4605 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250077209837627/1250000000000000 : ℝ)) (X := (12503472555712474981/12500000000000000000 : ℝ)) (by norm_num) 4605 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10004549919849571131/10000000000000000000 : ℝ) ≤ (2000202325463113/2000000000000000 : ℝ) ^ (4605/1024 : ℝ) := by
    have hpowers : (10004549919849571131/10000000000000000000 : ℝ)^1024 ≤ (2000202325463113/2000000000000000 : ℝ)^4605 := by
      have hnat : (10004549919849571131 : ℕ)^1024*2000000000000000^4605 ≤ 2000202325463113^4605*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004549919849571131 10000000000000000000 2000202325463113 2000000000000000 1024 4605 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000202325463113/2000000000000000 : ℝ)) (X := (10004549919849571131/10000000000000000000 : ℝ)) (by norm_num) 4605 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5030846451944193/100000000000000000000 : ℝ) ≤ ((2206613236718916069/2207000000000000000 : ℝ)+2*(393948614549/441400000000000 : ℝ)*(11071/100000 : ℝ))^(4605/1024 : ℝ) := by
    rw [show (2206613236718916069/2207000000000000000 : ℝ)+2*(393948614549/441400000000000 : ℝ)*(11071/100000 : ℝ)=(10000223730086467/10000000000000000 : ℝ) by norm_num, show 1+2*(5030846451944193/100000000000000000000 : ℝ)=(50005030846451944193/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4549919849571131/20000000000000000000 : ℝ)+(5030846451944193/100000000000000000000 : ℝ) ≤ ((2206613236718916069/2207000000000000000 : ℝ)+(393948614549/441400000000000 : ℝ)*((3097/20000 : ℝ)+(11071/100000 : ℝ)))^(4605/1024 : ℝ) := by
    rw [show (2206613236718916069/2207000000000000000 : ℝ)+(393948614549/441400000000000 : ℝ)*((3097/20000 : ℝ)+(11071/100000 : ℝ))=(1250077209837627/1250000000000000 : ℝ) by norm_num, show 1+(4549919849571131/20000000000000000000 : ℝ)+(5030846451944193/100000000000000000000 : ℝ)=(12503472555712474981/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4549919849571131/20000000000000000000 : ℝ) ≤ ((2206613236718916069/2207000000000000000 : ℝ)+2*(393948614549/441400000000000 : ℝ)*(3097/20000 : ℝ))^(4605/1024 : ℝ) := by
    rw [show (2206613236718916069/2207000000000000000 : ℝ)+2*(393948614549/441400000000000 : ℝ)*(3097/20000 : ℝ)=(2000202325463113/2000000000000000 : ℝ) by norm_num, show 1+2*(4549919849571131/20000000000000000000 : ℝ)=(10004549919849571131/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2206613236718916069/2207000000000000000 : ℝ)*(X 1 0+X 2 0)+(393948614549/441400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4605/1024 : ℝ)) (lo := (11071/100000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (2206613236718916069/2207000000000000000 : ℝ)) (alpha := (393948614549/441400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2206613236718916069/2207000000000000000 : ℝ)*(X 0 1+X 2 1)+(393948614549/441400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4605/1024 : ℝ)) (lo := (11071/100000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (2206613236718916069/2207000000000000000 : ℝ)) (alpha := (393948614549/441400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2206613236718916069/2207000000000000000 : ℝ)*(X 0 2+X 1 2)+(393948614549/441400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4605/1024 : ℝ)) (lo := (11071/100000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (2206613236718916069/2207000000000000000 : ℝ)) (alpha := (393948614549/441400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-361262913/2000000000 : ℝ)*X 0 0+(5427692331/10000000000 : ℝ)*X 0 1+(1304882319/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349099607/10000000000 : ℝ)*X 1 0+(-956418331/5000000000 : ℝ)*X 1 1+(2609764991/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349100093/10000000000 : ℝ)*X 2 0+(2609764637/5000000000 : ℝ)*X 2 1+(-1912836953/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((850031849/2000000000 : ℝ)*X 0 0+(4012679439/10000000000 : ℝ)*X 0 1+(1124761051/2500000000 : ℝ)*X 0 2+(850031849/2000000000 : ℝ)*X 1 0+(4012679439/10000000000 : ℝ)*X 1 1+(1124761051/2500000000 : ℝ)*X 1 2+(850031849/2000000000 : ℝ)*X 2 0+(4012679439/10000000000 : ℝ)*X 2 1+(1124761051/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1806341859/10000000000 : ℝ)*X 0 0+(5220610281/10000000000 : ℝ)*X 0 1+(5426603349/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((850044629/2000000000 : ℝ)*X 0 0+(4496519009/10000000000 : ℝ)*X 0 1+(1003805791/2500000000 : ℝ)*X 0 2+(850044629/2000000000 : ℝ)*X 1 0+(4496519009/10000000000 : ℝ)*X 1 1+(1003805791/2500000000 : ℝ)*X 1 2+(850044629/2000000000 : ℝ)*X 2 0+(4496519009/10000000000 : ℝ)*X 2 1+(1003805791/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_s6_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (299473140590369326518181857/55175000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (63296489/50000000000000 : ℝ)*(base19) + (561648469/100000000000000 : ℝ)*(base23) + (28401239/100000000000000 : ℝ)*(lower2) + (55799151/25000000000000 : ℝ)*(upper3) + (27644921/100000000000000 : ℝ)*(lower4) + (1715006956577683/50000000000000 : ℝ)*(major0) + (1715006956577683/50000000000000 : ℝ)*(major1) + (1715006956577683/50000000000000 : ℝ)*(major2) + (1200984807466527/25000000000000 : ℝ)*(sp0) + (2401973812901597/50000000000000 : ℝ)*(sp1) + (4803947190747703/100000000000000 : ℝ)*(sp2) + (2056073196239/100000000000 : ℝ)*(sp3) + (1704506013/20000000000000 : ℝ)*(sp4) + (3348376173/50000000000000 : ℝ)*(sp5) + (1028039946495673/50000000000000 : ℝ)*(f.failure) + (1200986938099043/25000000000000 : ℝ)*(f.sum) + (35854455840529/5517500000000000000000000000 : ℝ)*base66 + (374592184390873127/110350000000000000000000000000000 : ℝ)*base67 + (202381948552373127/110350000000000000000000000000000 : ℝ)*base69 + (125160818250523127/110350000000000000000000000000000 : ℝ)*base71 + (23136354905043/11035000000000000000000000000 : ℝ)*base74 + (1199284177947123127/110350000000000000000000000000000 : ℝ)*base75 + (260660507873173127/110350000000000000000000000000000 : ℝ)*base77 + (1507032397837723127/110350000000000000000000000000000 : ℝ)*base79 + (10409580291877/2758750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (267269/1250000000000000000000 : ℝ)*base90 + (267269/1250000000000000000000 : ℝ)*base92 + (267269/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1555_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41705747/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11071/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (346/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1555_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1555_box_0 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1600068707/10000000000 : ℝ)*x 0 + (5398199719/10000000000 : ℝ)*x 1 + (2699100259/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1600068707/10000000000 : ℝ)^4607 ≤ (9477334430263/100000000000000 : ℝ)^3583 := by
    have hnat : (1600068707 : ℕ)^4607*100000000000000^3583 ≤ 9477334430263^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1600068707 10000000000 9477334430263 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5398199719/10000000000 : ℝ)^4607 ≤ (22630664236131/50000000000000 : ℝ)^3583 := by
    have hnat : (5398199719 : ℕ)^4607*50000000000000^3583 ≤ 22630664236131^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5398199719 10000000000 22630664236131 50000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2699100259/5000000000 : ℝ)^4607 ≤ (45261337086097/100000000000000 : ℝ)^3583 := by
    have hnat : (2699100259 : ℕ)^4607*100000000000000^3583 ≤ 45261337086097^3583*5000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699100259 5000000000 45261337086097 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1600068707/10000000000 : ℝ), (5398199719/10000000000 : ℝ), (2699100259/5000000000 : ℝ)] ![(9477334430263/100000000000000 : ℝ), (22630664236131/50000000000000 : ℝ), (45261337086097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1600068707/10000000000 : ℝ)|^4607 ≤ (9477334430263/100000000000000 : ℝ)^3583
        have hw : |(-1600068707/10000000000 : ℝ)|=(1600068707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5398199719/10000000000 : ℝ)|^4607 ≤ (22630664236131/50000000000000 : ℝ)^3583
        have hw : |(5398199719/10000000000 : ℝ)|=(5398199719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2699100259/5000000000 : ℝ)|^4607 ≤ (45261337086097/100000000000000 : ℝ)^3583
        have hw : |(2699100259/5000000000 : ℝ)|=(2699100259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1555_box_1 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (329444921/625000000 : ℝ)*x 0 + (-1776638063/10000000000 : ℝ)*x 1 + (2699100061/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (329444921/625000000 : ℝ)^4607 ≤ (21947966288001/50000000000000 : ℝ)^3583 := by
    have hnat : (329444921 : ℕ)^4607*50000000000000^3583 ≤ 21947966288001^3583*625000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329444921 625000000 21947966288001 50000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1776638063/10000000000 : ℝ)^4607 ≤ (10842734599741/100000000000000 : ℝ)^3583 := by
    have hnat : (1776638063 : ℕ)^4607*100000000000000^3583 ≤ 10842734599741^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1776638063 10000000000 10842734599741 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2699100061/5000000000 : ℝ)^4607 ≤ (2828833301057/6250000000000 : ℝ)^3583 := by
    have hnat : (2699100061 : ℕ)^4607*6250000000000^3583 ≤ 2828833301057^3583*5000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699100061 5000000000 2828833301057 6250000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(329444921/625000000 : ℝ), (-1776638063/10000000000 : ℝ), (2699100061/5000000000 : ℝ)] ![(21947966288001/50000000000000 : ℝ), (10842734599741/100000000000000 : ℝ), (2828833301057/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(329444921/625000000 : ℝ)|^4607 ≤ (21947966288001/50000000000000 : ℝ)^3583
        have hw : |(329444921/625000000 : ℝ)|=(329444921/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1776638063/10000000000 : ℝ)|^4607 ≤ (10842734599741/100000000000000 : ℝ)^3583
        have hw : |(-1776638063/10000000000 : ℝ)|=(1776638063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2699100061/5000000000 : ℝ)|^4607 ≤ (2828833301057/6250000000000 : ℝ)^3583
        have hw : |(2699100061/5000000000 : ℝ)|=(2699100061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1555_box_2 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5271118321/10000000000 : ℝ)*x 0 + (5398200581/10000000000 : ℝ)*x 1 + (-1776637997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5271118321/10000000000 : ℝ)^4607 ≤ (43895928132341/100000000000000 : ℝ)^3583 := by
    have hnat : (5271118321 : ℕ)^4607*100000000000000^3583 ≤ 43895928132341^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271118321 10000000000 43895928132341 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5398200581/10000000000 : ℝ)^4607 ≤ (22630668882643/50000000000000 : ℝ)^3583 := by
    have hnat : (5398200581 : ℕ)^4607*50000000000000^3583 ≤ 22630668882643^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5398200581 10000000000 22630668882643 50000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1776637997/10000000000 : ℝ)^4607 ≤ (1084273408183/10000000000000 : ℝ)^3583 := by
    have hnat : (1776637997 : ℕ)^4607*10000000000000^3583 ≤ 1084273408183^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1776637997 10000000000 1084273408183 10000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5271118321/10000000000 : ℝ), (5398200581/10000000000 : ℝ), (-1776637997/10000000000 : ℝ)] ![(43895928132341/100000000000000 : ℝ), (22630668882643/50000000000000 : ℝ), (1084273408183/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5271118321/10000000000 : ℝ)|^4607 ≤ (43895928132341/100000000000000 : ℝ)^3583
        have hw : |(5271118321/10000000000 : ℝ)|=(5271118321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5398200581/10000000000 : ℝ)|^4607 ≤ (22630668882643/50000000000000 : ℝ)^3583
        have hw : |(5398200581/10000000000 : ℝ)|=(5398200581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1776637997/10000000000 : ℝ)|^4607 ≤ (1084273408183/10000000000000 : ℝ)^3583
        have hw : |(-1776637997/10000000000 : ℝ)|=(1776637997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1555_box_3 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (556426799/1250000000 : ℝ)*x 0 + (2078125721/5000000000 : ℝ)*x 1 + (4156250461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (556426799/1250000000 : ℝ)^4607 ≤ (35321640068677/100000000000000 : ℝ)^3583 := by
    have hnat : (556426799 : ℕ)^4607*100000000000000^3583 ≤ 35321640068677^3583*1250000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      556426799 1250000000 35321640068677 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2078125721/5000000000 : ℝ)^4607 ≤ (3233918486231/10000000000000 : ℝ)^3583 := by
    have hnat : (2078125721 : ℕ)^4607*10000000000000^3583 ≤ 3233918486231^3583*5000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2078125721 5000000000 3233918486231 10000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4156250461/10000000000 : ℝ)^4607 ≤ (16169587523911/50000000000000 : ℝ)^3583 := by
    have hnat : (4156250461 : ℕ)^4607*50000000000000^3583 ≤ 16169587523911^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4156250461 10000000000 16169587523911 50000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(556426799/1250000000 : ℝ), (2078125721/5000000000 : ℝ), (4156250461/10000000000 : ℝ)] ![(35321640068677/100000000000000 : ℝ), (3233918486231/10000000000000 : ℝ), (16169587523911/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(556426799/1250000000 : ℝ)|^4607 ≤ (35321640068677/100000000000000 : ℝ)^3583
        have hw : |(556426799/1250000000 : ℝ)|=(556426799/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2078125721/5000000000 : ℝ)|^4607 ≤ (3233918486231/10000000000000 : ℝ)^3583
        have hw : |(2078125721/5000000000 : ℝ)|=(2078125721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4156250461/10000000000 : ℝ)|^4607 ≤ (16169587523911/50000000000000 : ℝ)^3583
        have hw : |(4156250461/10000000000 : ℝ)|=(4156250461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1555_box_4 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2017960969/10000000000 : ℝ)*x 0 + (5244766991/10000000000 : ℝ)*x 1 + (5244766913/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2017960969/10000000000 : ℝ)^4607 ≤ (6386030452001/50000000000000 : ℝ)^3583 := by
    have hnat : (2017960969 : ℕ)^4607*50000000000000^3583 ≤ 6386030452001^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2017960969 10000000000 6386030452001 50000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244766991/10000000000 : ℝ)^4607 ≤ (10903492489949/25000000000000 : ℝ)^3583 := by
    have hnat : (5244766991 : ℕ)^4607*25000000000000^3583 ≤ 10903492489949^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244766991 10000000000 10903492489949 25000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244766913/10000000000 : ℝ)^4607 ≤ (43613969125797/100000000000000 : ℝ)^3583 := by
    have hnat : (5244766913 : ℕ)^4607*100000000000000^3583 ≤ 43613969125797^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244766913 10000000000 43613969125797 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2017960969/10000000000 : ℝ), (5244766991/10000000000 : ℝ), (5244766913/10000000000 : ℝ)] ![(6386030452001/50000000000000 : ℝ), (10903492489949/25000000000000 : ℝ), (43613969125797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2017960969/10000000000 : ℝ)|^4607 ≤ (6386030452001/50000000000000 : ℝ)^3583
        have hw : |(-2017960969/10000000000 : ℝ)|=(2017960969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244766991/10000000000 : ℝ)|^4607 ≤ (10903492489949/25000000000000 : ℝ)^3583
        have hw : |(5244766991/10000000000 : ℝ)|=(5244766991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244766913/10000000000 : ℝ)|^4607 ≤ (43613969125797/100000000000000 : ℝ)^3583
        have hw : |(5244766913/10000000000 : ℝ)|=(5244766913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1555_box_5 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2688796933/5000000000 : ℝ)*x 0 + (-368107751/2000000000 : ℝ)*x 1 + (5244766957/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2688796933/5000000000 : ℝ)^4607 ≤ (22519651403943/50000000000000 : ℝ)^3583 := by
    have hnat : (2688796933 : ℕ)^4607*50000000000000^3583 ≤ 22519651403943^3583*5000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688796933 5000000000 22519651403943 50000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (368107751/2000000000 : ℝ)^4607 ≤ (1418340947629/12500000000000 : ℝ)^3583 := by
    have hnat : (368107751 : ℕ)^4607*12500000000000^3583 ≤ 1418340947629^3583*2000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      368107751 2000000000 1418340947629 12500000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244766957/10000000000 : ℝ)^4607 ≤ (21806984798129/50000000000000 : ℝ)^3583 := by
    have hnat : (5244766957 : ℕ)^4607*50000000000000^3583 ≤ 21806984798129^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244766957 10000000000 21806984798129 50000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2688796933/5000000000 : ℝ), (-368107751/2000000000 : ℝ), (5244766957/10000000000 : ℝ)] ![(22519651403943/50000000000000 : ℝ), (1418340947629/12500000000000 : ℝ), (21806984798129/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2688796933/5000000000 : ℝ)|^4607 ≤ (22519651403943/50000000000000 : ℝ)^3583
        have hw : |(2688796933/5000000000 : ℝ)|=(2688796933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-368107751/2000000000 : ℝ)|^4607 ≤ (1418340947629/12500000000000 : ℝ)^3583
        have hw : |(-368107751/2000000000 : ℝ)|=(368107751/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244766957/10000000000 : ℝ)|^4607 ≤ (21806984798129/50000000000000 : ℝ)^3583
        have hw : |(5244766957/10000000000 : ℝ)|=(5244766957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1555_box_6 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1344398461/2500000000 : ℝ)*x 0 + (5244766993/10000000000 : ℝ)*x 1 + (-115033671/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1344398461/2500000000 : ℝ)^4607 ≤ (5629912821371/12500000000000 : ℝ)^3583 := by
    have hnat : (1344398461 : ℕ)^4607*12500000000000^3583 ≤ 5629912821371^3583*2500000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344398461 2500000000 5629912821371 12500000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244766993/10000000000 : ℝ)^4607 ≤ (43613969981181/100000000000000 : ℝ)^3583 := by
    have hnat : (5244766993 : ℕ)^4607*100000000000000^3583 ≤ 43613969981181^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244766993 10000000000 43613969981181 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (115033671/625000000 : ℝ)^4607 ≤ (11346727430423/100000000000000 : ℝ)^3583 := by
    have hnat : (115033671 : ℕ)^4607*100000000000000^3583 ≤ 11346727430423^3583*625000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      115033671 625000000 11346727430423 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1344398461/2500000000 : ℝ), (5244766993/10000000000 : ℝ), (-115033671/625000000 : ℝ)] ![(5629912821371/12500000000000 : ℝ), (43613969981181/100000000000000 : ℝ), (11346727430423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1344398461/2500000000 : ℝ)|^4607 ≤ (5629912821371/12500000000000 : ℝ)^3583
        have hw : |(1344398461/2500000000 : ℝ)|=(1344398461/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244766993/10000000000 : ℝ)|^4607 ≤ (43613969981181/100000000000000 : ℝ)^3583
        have hw : |(5244766993/10000000000 : ℝ)|=(5244766993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-115033671/625000000 : ℝ)|^4607 ≤ (11346727430423/100000000000000 : ℝ)^3583
        have hw : |(-115033671/625000000 : ℝ)|=(115033671/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1555_box_7 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4046282033/10000000000 : ℝ)*x 0 + (1089672013/2500000000 : ℝ)*x 1 + (108967201/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4046282033/10000000000 : ℝ)^4607 ≤ (15621586921871/50000000000000 : ℝ)^3583 := by
    have hnat : (4046282033 : ℕ)^4607*50000000000000^3583 ≤ 15621586921871^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4046282033 10000000000 15621586921871 50000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1089672013/2500000000 : ℝ)^4607 ≤ (4297301640861/12500000000000 : ℝ)^3583 := by
    have hnat : (1089672013 : ℕ)^4607*12500000000000^3583 ≤ 4297301640861^3583*2500000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089672013 2500000000 4297301640861 12500000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (108967201/250000000 : ℝ)^4607 ≤ (3437841300519/10000000000000 : ℝ)^3583 := by
    have hnat : (108967201 : ℕ)^4607*10000000000000^3583 ≤ 3437841300519^3583*250000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108967201 250000000 3437841300519 10000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4046282033/10000000000 : ℝ), (1089672013/2500000000 : ℝ), (108967201/250000000 : ℝ)] ![(15621586921871/50000000000000 : ℝ), (4297301640861/12500000000000 : ℝ), (3437841300519/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4046282033/10000000000 : ℝ)|^4607 ≤ (15621586921871/50000000000000 : ℝ)^3583
        have hw : |(4046282033/10000000000 : ℝ)|=(4046282033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1089672013/2500000000 : ℝ)|^4607 ≤ (4297301640861/12500000000000 : ℝ)^3583
        have hw : |(1089672013/2500000000 : ℝ)|=(1089672013/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(108967201/250000000 : ℝ)|^4607 ≤ (3437841300519/10000000000000 : ℝ)^3583
        have hw : |(108967201/250000000 : ℝ)|=(108967201/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1555_box_8 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-120590347/625000000 : ℝ)*x 0 + (5136822419/10000000000 : ℝ)*x 1 + (5418519709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (120590347/625000000 : ℝ)^4607 ≤ (6028141194661/50000000000000 : ℝ)^3583 := by
    have hnat : (120590347 : ℕ)^4607*50000000000000^3583 ≤ 6028141194661^3583*625000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      120590347 625000000 6028141194661 50000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5136822419/10000000000 : ℝ)^4607 ≤ (42463206266433/100000000000000 : ℝ)^3583 := by
    have hnat : (5136822419 : ℕ)^4607*100000000000000^3583 ≤ 42463206266433^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5136822419 10000000000 42463206266433 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5418519709/10000000000 : ℝ)^4607 ≤ (22740255662671/50000000000000 : ℝ)^3583 := by
    have hnat : (5418519709 : ℕ)^4607*50000000000000^3583 ≤ 22740255662671^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5418519709 10000000000 22740255662671 50000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-120590347/625000000 : ℝ), (5136822419/10000000000 : ℝ), (5418519709/10000000000 : ℝ)] ![(6028141194661/50000000000000 : ℝ), (42463206266433/100000000000000 : ℝ), (22740255662671/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-120590347/625000000 : ℝ)|^4607 ≤ (6028141194661/50000000000000 : ℝ)^3583
        have hw : |(-120590347/625000000 : ℝ)|=(120590347/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5136822419/10000000000 : ℝ)|^4607 ≤ (42463206266433/100000000000000 : ℝ)^3583
        have hw : |(5136822419/10000000000 : ℝ)|=(5136822419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5418519709/10000000000 : ℝ)|^4607 ≤ (22740255662671/50000000000000 : ℝ)^3583
        have hw : |(5418519709/10000000000 : ℝ)|=(5418519709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1555_box_9 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5257013683/10000000000 : ℝ)*x 0 + (-220992511/1250000000 : ℝ)*x 1 + (5418519859/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5257013683/10000000000 : ℝ)^4607 ≤ (8748991767863/20000000000000 : ℝ)^3583 := by
    have hnat : (5257013683 : ℕ)^4607*20000000000000^3583 ≤ 8748991767863^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257013683 10000000000 8748991767863 20000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (220992511/1250000000 : ℝ)^4607 ≤ (538726409923/5000000000000 : ℝ)^3583 := by
    have hnat : (220992511 : ℕ)^4607*5000000000000^3583 ≤ 538726409923^3583*1250000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220992511 1250000000 538726409923 5000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5418519859/10000000000 : ℝ)^4607 ≤ (9096102588839/20000000000000 : ℝ)^3583 := by
    have hnat : (5418519859 : ℕ)^4607*20000000000000^3583 ≤ 9096102588839^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5418519859 10000000000 9096102588839 20000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5257013683/10000000000 : ℝ), (-220992511/1250000000 : ℝ), (5418519859/10000000000 : ℝ)] ![(8748991767863/20000000000000 : ℝ), (538726409923/5000000000000 : ℝ), (9096102588839/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5257013683/10000000000 : ℝ)|^4607 ≤ (8748991767863/20000000000000 : ℝ)^3583
        have hw : |(5257013683/10000000000 : ℝ)|=(5257013683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-220992511/1250000000 : ℝ)|^4607 ≤ (538726409923/5000000000000 : ℝ)^3583
        have hw : |(-220992511/1250000000 : ℝ)|=(220992511/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5418519859/10000000000 : ℝ)|^4607 ≤ (9096102588839/20000000000000 : ℝ)^3583
        have hw : |(5418519859/10000000000 : ℝ)|=(5418519859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1555_box_10 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1051402799/2000000000 : ℝ)*x 0 + (169328747/312500000 : ℝ)*x 1 + (-1767939601/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051402799/2000000000 : ℝ)^4607 ≤ (8748992435507/20000000000000 : ℝ)^3583 := by
    have hnat : (1051402799 : ℕ)^4607*20000000000000^3583 ≤ 8748992435507^3583*2000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051402799 2000000000 8748992435507 20000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169328747/312500000 : ℝ)^4607 ≤ (45480513429851/100000000000000 : ℝ)^3583 := by
    have hnat : (169328747 : ℕ)^4607*100000000000000^3583 ≤ 45480513429851^3583*312500000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169328747 312500000 45480513429851 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1767939601/10000000000 : ℝ)^4607 ≤ (538726219113/5000000000000 : ℝ)^3583 := by
    have hnat : (1767939601 : ℕ)^4607*5000000000000^3583 ≤ 538726219113^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1767939601 10000000000 538726219113 5000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1051402799/2000000000 : ℝ), (169328747/312500000 : ℝ), (-1767939601/10000000000 : ℝ)] ![(8748992435507/20000000000000 : ℝ), (45480513429851/100000000000000 : ℝ), (538726219113/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1051402799/2000000000 : ℝ)|^4607 ≤ (8748992435507/20000000000000 : ℝ)^3583
        have hw : |(1051402799/2000000000 : ℝ)|=(1051402799/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(169328747/312500000 : ℝ)|^4607 ≤ (45480513429851/100000000000000 : ℝ)^3583
        have hw : |(169328747/312500000 : ℝ)|=(169328747/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1767939601/10000000000 : ℝ)|^4607 ≤ (538726219113/5000000000000 : ℝ)^3583
        have hw : |(-1767939601/10000000000 : ℝ)|=(1767939601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1555_box_11 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4503919671/10000000000 : ℝ)*x 0 + (4129408833/10000000000 : ℝ)*x 1 + (258088031/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4503919671/10000000000 : ℝ)^4607 ≤ (7171646997043/20000000000000 : ℝ)^3583 := by
    have hnat : (4503919671 : ℕ)^4607*20000000000000^3583 ≤ 7171646997043^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4503919671 10000000000 7171646997043 20000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4129408833/10000000000 : ℝ)^4607 ≤ (16035442089427/50000000000000 : ℝ)^3583 := by
    have hnat : (4129408833 : ℕ)^4607*50000000000000^3583 ≤ 16035442089427^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4129408833 10000000000 16035442089427 50000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (258088031/625000000 : ℝ)^4607 ≤ (641417616271/2000000000000 : ℝ)^3583 := by
    have hnat : (258088031 : ℕ)^4607*2000000000000^3583 ≤ 641417616271^3583*625000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258088031 625000000 641417616271 2000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4503919671/10000000000 : ℝ), (4129408833/10000000000 : ℝ), (258088031/625000000 : ℝ)] ![(7171646997043/20000000000000 : ℝ), (16035442089427/50000000000000 : ℝ), (641417616271/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4503919671/10000000000 : ℝ)|^4607 ≤ (7171646997043/20000000000000 : ℝ)^3583
        have hw : |(4503919671/10000000000 : ℝ)|=(4503919671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4129408833/10000000000 : ℝ)|^4607 ≤ (16035442089427/50000000000000 : ℝ)^3583
        have hw : |(4129408833/10000000000 : ℝ)|=(4129408833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(258088031/625000000 : ℝ)|^4607 ≤ (641417616271/2000000000000 : ℝ)^3583
        have hw : |(258088031/625000000 : ℝ)|=(258088031/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1555_box_12 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1688315201/10000000000 : ℝ)*x 0 + (1375702691/2500000000 : ℝ)*x 1 + (5229719063/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1688315201/10000000000 : ℝ)^4607 ≤ (2538659020581/25000000000000 : ℝ)^3583 := by
    have hnat : (1688315201 : ℕ)^4607*25000000000000^3583 ≤ 2538659020581^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1688315201 10000000000 2538659020581 25000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1375702691/2500000000 : ℝ)^4607 ≤ (46392224775841/100000000000000 : ℝ)^3583 := by
    have hnat : (1375702691 : ℕ)^4607*100000000000000^3583 ≤ 46392224775841^3583*2500000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1375702691 2500000000 46392224775841 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5229719063/10000000000 : ℝ)^4607 ≤ (1086328478133/2500000000000 : ℝ)^3583 := by
    have hnat : (5229719063 : ℕ)^4607*2500000000000^3583 ≤ 1086328478133^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229719063 10000000000 1086328478133 2500000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1688315201/10000000000 : ℝ), (1375702691/2500000000 : ℝ), (5229719063/10000000000 : ℝ)] ![(2538659020581/25000000000000 : ℝ), (46392224775841/100000000000000 : ℝ), (1086328478133/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1688315201/10000000000 : ℝ)|^4607 ≤ (2538659020581/25000000000000 : ℝ)^3583
        have hw : |(-1688315201/10000000000 : ℝ)|=(1688315201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1375702691/2500000000 : ℝ)|^4607 ≤ (46392224775841/100000000000000 : ℝ)^3583
        have hw : |(1375702691/2500000000 : ℝ)|=(1375702691/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5229719063/10000000000 : ℝ)|^4607 ≤ (1086328478133/2500000000000 : ℝ)^3583
        have hw : |(5229719063/10000000000 : ℝ)|=(5229719063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1555_box_13 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5388037469/10000000000 : ℝ)*x 0 + (-923316753/5000000000 : ℝ)*x 1 + (1307429709/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5388037469/10000000000 : ℝ)^4607 ≤ (11287950271059/25000000000000 : ℝ)^3583 := by
    have hnat : (5388037469 : ℕ)^4607*25000000000000^3583 ≤ 11287950271059^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5388037469 10000000000 11287950271059 25000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (923316753/5000000000 : ℝ)^4607 ≤ (2848765550739/25000000000000 : ℝ)^3583 := by
    have hnat : (923316753 : ℕ)^4607*25000000000000^3583 ≤ 2848765550739^3583*5000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      923316753 5000000000 2848765550739 25000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1307429709/2500000000 : ℝ)^4607 ≤ (21726568350081/50000000000000 : ℝ)^3583 := by
    have hnat : (1307429709 : ℕ)^4607*50000000000000^3583 ≤ 21726568350081^3583*2500000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307429709 2500000000 21726568350081 50000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5388037469/10000000000 : ℝ), (-923316753/5000000000 : ℝ), (1307429709/2500000000 : ℝ)] ![(11287950271059/25000000000000 : ℝ), (2848765550739/25000000000000 : ℝ), (21726568350081/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5388037469/10000000000 : ℝ)|^4607 ≤ (11287950271059/25000000000000 : ℝ)^3583
        have hw : |(5388037469/10000000000 : ℝ)|=(5388037469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-923316753/5000000000 : ℝ)|^4607 ≤ (2848765550739/25000000000000 : ℝ)^3583
        have hw : |(-923316753/5000000000 : ℝ)|=(923316753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1307429709/2500000000 : ℝ)|^4607 ≤ (21726568350081/50000000000000 : ℝ)^3583
        have hw : |(1307429709/2500000000 : ℝ)|=(1307429709/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1555_box_14 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2694018513/5000000000 : ℝ)*x 0 + (2614859653/5000000000 : ℝ)*x 1 + (-923316737/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2694018513/5000000000 : ℝ)^4607 ≤ (45151796310927/100000000000000 : ℝ)^3583 := by
    have hnat : (2694018513 : ℕ)^4607*100000000000000^3583 ≤ 45151796310927^3583*5000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2694018513 5000000000 45151796310927 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2614859653/5000000000 : ℝ)^4607 ≤ (21726570860707/50000000000000 : ℝ)^3583 := by
    have hnat : (2614859653 : ℕ)^4607*50000000000000^3583 ≤ 21726570860707^3583*5000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614859653 5000000000 21726570860707 50000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (923316737/5000000000 : ℝ)^4607 ≤ (569753097453/5000000000000 : ℝ)^3583 := by
    have hnat : (923316737 : ℕ)^4607*5000000000000^3583 ≤ 569753097453^3583*5000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      923316737 5000000000 569753097453 5000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2694018513/5000000000 : ℝ), (2614859653/5000000000 : ℝ), (-923316737/5000000000 : ℝ)] ![(45151796310927/100000000000000 : ℝ), (21726570860707/50000000000000 : ℝ), (569753097453/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2694018513/5000000000 : ℝ)|^4607 ≤ (45151796310927/100000000000000 : ℝ)^3583
        have hw : |(2694018513/5000000000 : ℝ)|=(2694018513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2614859653/5000000000 : ℝ)|^4607 ≤ (21726570860707/50000000000000 : ℝ)^3583
        have hw : |(2614859653/5000000000 : ℝ)|=(2614859653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-923316737/5000000000 : ℝ)|^4607 ≤ (569753097453/5000000000000 : ℝ)^3583
        have hw : |(-923316737/5000000000 : ℝ)|=(923316737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1555_box_15 (p : ℝ) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (160227441/400000000 : ℝ)*x 0 + (218925887/500000000 : ℝ)*x 1 + (4378517719/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (160227441/400000000 : ℝ)^4607 ≤ (30840707888467/100000000000000 : ℝ)^3583 := by
    have hnat : (160227441 : ℕ)^4607*100000000000000^3583 ≤ 30840707888467^3583*400000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      160227441 400000000 30840707888467 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (218925887/500000000 : ℝ)^4607 ≤ (6915929231099/20000000000000 : ℝ)^3583 := by
    have hnat : (218925887 : ℕ)^4607*20000000000000^3583 ≤ 6915929231099^3583*500000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218925887 500000000 6915929231099 20000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4378517719/10000000000 : ℝ)^4607 ≤ (34579645942247/100000000000000 : ℝ)^3583 := by
    have hnat : (4378517719 : ℕ)^4607*100000000000000^3583 ≤ 34579645942247^3583*10000000000^4607 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4378517719 10000000000 34579645942247 100000000000000 4607 3583 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4607/1024 : ℝ)) 4607 3583 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(160227441/400000000 : ℝ), (218925887/500000000 : ℝ), (4378517719/10000000000 : ℝ)] ![(30840707888467/100000000000000 : ℝ), (6915929231099/20000000000000 : ℝ), (34579645942247/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(160227441/400000000 : ℝ)|^4607 ≤ (30840707888467/100000000000000 : ℝ)^3583
        have hw : |(160227441/400000000 : ℝ)|=(160227441/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(218925887/500000000 : ℝ)|^4607 ≤ (6915929231099/20000000000000 : ℝ)^3583
        have hw : |(218925887/500000000 : ℝ)|=(218925887/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4378517719/10000000000 : ℝ)|^4607 ≤ (34579645942247/100000000000000 : ℝ)^3583
        have hw : |(4378517719/10000000000 : ℝ)|=(4378517719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1555_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41705747/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (346/3125 : ℝ)*pair X i i ≤ pair X i h) :
    -(63803/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58831/100000 : ℝ) ∧ (80769/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (43137/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (346/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (346/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (346/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (346/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (346/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (346/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (346/3125 : ℝ) ^ (4605/1024 : ℝ) ≤ (1258222579558673/25000000000000000000 : ℝ) := by
    have hpowers : (346/3125 : ℝ)^4605 ≤ (1258222579558673/25000000000000000000 : ℝ)^1024 := by
      have hnat : (346 : ℕ)^4605*25000000000000000000^1024 ≤ 1258222579558673^1024*3125^4605 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        346 3125 1258222579558673 25000000000000000000 4605 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (346/3125 : ℝ)) (X := (1258222579558673/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4605 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3097/20000 : ℝ) ^ (4605/1024 : ℝ) ≤ (4549919849571131/20000000000000000000 : ℝ) := by
    have hpowers : (3097/20000 : ℝ)^4605 ≤ (4549919849571131/20000000000000000000 : ℝ)^1024 := by
      have hnat : (3097 : ℕ)^4605*20000000000000000000^1024 ≤ 4549919849571131^1024*20000^4605 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3097 20000 4549919849571131 20000000000000000000 4605 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3097/20000 : ℝ)) (X := (4549919849571131/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4605 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501258222579558673/12500000000000000000 : ℝ) ≤ (5000111910488517/5000000000000000 : ℝ) ^ (4605/1024 : ℝ) := by
    have hpowers : (12501258222579558673/12500000000000000000 : ℝ)^1024 ≤ (5000111910488517/5000000000000000 : ℝ)^4605 := by
      have hnat : (12501258222579558673 : ℕ)^1024*5000000000000000^4605 ≤ 5000111910488517^4605*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501258222579558673 12500000000000000000 5000111910488517 5000000000000000 1024 4605 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000111910488517/5000000000000000 : ℝ)) (X := (12501258222579558673/12500000000000000000 : ℝ)) (by norm_num) 4605 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100027782489566090347/100000000000000000000 : ℝ) ≤ (10000617724140039/10000000000000000 : ℝ) ^ (4605/1024 : ℝ) := by
    have hpowers : (100027782489566090347/100000000000000000000 : ℝ)^1024 ≤ (10000617724140039/10000000000000000 : ℝ)^4605 := by
      have hnat : (100027782489566090347 : ℕ)^1024*10000000000000000^4605 ≤ 10000617724140039^4605*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100027782489566090347 100000000000000000000 10000617724140039 10000000000000000 1024 4605 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000617724140039/10000000000000000 : ℝ)) (X := (100027782489566090347/100000000000000000000 : ℝ)) (by norm_num) 4605 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10004549919849571131/10000000000000000000 : ℝ) ≤ (2500252906825761/2500000000000000 : ℝ) ^ (4605/1024 : ℝ) := by
    have hpowers : (10004549919849571131/10000000000000000000 : ℝ)^1024 ≤ (2500252906825761/2500000000000000 : ℝ)^4605 := by
      have hnat : (10004549919849571131 : ℕ)^1024*2500000000000000^4605 ≤ 2500252906825761^4605*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004549919849571131 10000000000000000000 2500252906825761 2500000000000000 1024 4605 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500252906825761/2500000000000000 : ℝ)) (X := (10004549919849571131/10000000000000000000 : ℝ)) (by norm_num) 4605 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1258222579558673/25000000000000000000 : ℝ) ≤ ((7353710855055011387/7355000000000000000 : ℝ)+2*(26260210867/29420000000000 : ℝ)*(346/3125 : ℝ))^(4605/1024 : ℝ) := by
    rw [show (7353710855055011387/7355000000000000000 : ℝ)+2*(26260210867/29420000000000 : ℝ)*(346/3125 : ℝ)=(5000111910488517/5000000000000000 : ℝ) by norm_num, show 1+2*(1258222579558673/25000000000000000000 : ℝ)=(12501258222579558673/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4549919849571131/20000000000000000000 : ℝ)+(1258222579558673/25000000000000000000 : ℝ) ≤ ((7353710855055011387/7355000000000000000 : ℝ)+(26260210867/29420000000000 : ℝ)*((3097/20000 : ℝ)+(346/3125 : ℝ)))^(4605/1024 : ℝ) := by
    rw [show (7353710855055011387/7355000000000000000 : ℝ)+(26260210867/29420000000000 : ℝ)*((3097/20000 : ℝ)+(346/3125 : ℝ))=(10000617724140039/10000000000000000 : ℝ) by norm_num, show 1+(4549919849571131/20000000000000000000 : ℝ)+(1258222579558673/25000000000000000000 : ℝ)=(100027782489566090347/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4549919849571131/20000000000000000000 : ℝ) ≤ ((7353710855055011387/7355000000000000000 : ℝ)+2*(26260210867/29420000000000 : ℝ)*(3097/20000 : ℝ))^(4605/1024 : ℝ) := by
    rw [show (7353710855055011387/7355000000000000000 : ℝ)+2*(26260210867/29420000000000 : ℝ)*(3097/20000 : ℝ)=(2500252906825761/2500000000000000 : ℝ) by norm_num, show 1+2*(4549919849571131/20000000000000000000 : ℝ)=(10004549919849571131/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7353710855055011387/7355000000000000000 : ℝ)*(X 1 0+X 2 0)+(26260210867/29420000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4605/1024 : ℝ)) (lo := (346/3125 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (7353710855055011387/7355000000000000000 : ℝ)) (alpha := (26260210867/29420000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7353710855055011387/7355000000000000000 : ℝ)*(X 0 1+X 2 1)+(26260210867/29420000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4605/1024 : ℝ)) (lo := (346/3125 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (7353710855055011387/7355000000000000000 : ℝ)) (alpha := (26260210867/29420000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7353710855055011387/7355000000000000000 : ℝ)*(X 0 2+X 1 2)+(26260210867/29420000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4605/1024 : ℝ)) (lo := (346/3125 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (7353710855055011387/7355000000000000000 : ℝ)) (alpha := (26260210867/29420000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1600068707/10000000000 : ℝ)*X 0 0+(5398199719/10000000000 : ℝ)*X 0 1+(2699100259/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((329444921/625000000 : ℝ)*X 1 0+(-1776638063/10000000000 : ℝ)*X 1 1+(2699100061/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5271118321/10000000000 : ℝ)*X 2 0+(5398200581/10000000000 : ℝ)*X 2 1+(-1776637997/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((556426799/1250000000 : ℝ)*X 0 0+(2078125721/5000000000 : ℝ)*X 0 1+(4156250461/10000000000 : ℝ)*X 0 2+(556426799/1250000000 : ℝ)*X 1 0+(2078125721/5000000000 : ℝ)*X 1 1+(4156250461/10000000000 : ℝ)*X 1 2+(556426799/1250000000 : ℝ)*X 2 0+(2078125721/5000000000 : ℝ)*X 2 1+(4156250461/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2017960969/10000000000 : ℝ)*X 0 0+(5244766991/10000000000 : ℝ)*X 0 1+(5244766913/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2688796933/5000000000 : ℝ)*X 1 0+(-368107751/2000000000 : ℝ)*X 1 1+(5244766957/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1344398461/2500000000 : ℝ)*X 2 0+(5244766993/10000000000 : ℝ)*X 2 1+(-115033671/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4046282033/10000000000 : ℝ)*X 0 0+(1089672013/2500000000 : ℝ)*X 0 1+(108967201/250000000 : ℝ)*X 0 2+(4046282033/10000000000 : ℝ)*X 1 0+(1089672013/2500000000 : ℝ)*X 1 1+(108967201/250000000 : ℝ)*X 1 2+(4046282033/10000000000 : ℝ)*X 2 0+(1089672013/2500000000 : ℝ)*X 2 1+(108967201/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-120590347/625000000 : ℝ)*X 0 0+(5136822419/10000000000 : ℝ)*X 0 1+(5418519709/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5257013683/10000000000 : ℝ)*X 1 0+(-220992511/1250000000 : ℝ)*X 1 1+(5418519859/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1051402799/2000000000 : ℝ)*X 2 0+(169328747/312500000 : ℝ)*X 2 1+(-1767939601/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4503919671/10000000000 : ℝ)*X 0 0+(4129408833/10000000000 : ℝ)*X 0 1+(258088031/625000000 : ℝ)*X 0 2+(4503919671/10000000000 : ℝ)*X 1 0+(4129408833/10000000000 : ℝ)*X 1 1+(258088031/625000000 : ℝ)*X 1 2+(4503919671/10000000000 : ℝ)*X 2 0+(4129408833/10000000000 : ℝ)*X 2 1+(258088031/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1688315201/10000000000 : ℝ)*X 0 0+(1375702691/2500000000 : ℝ)*X 0 1+(5229719063/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5388037469/10000000000 : ℝ)*X 1 0+(-923316753/5000000000 : ℝ)*X 1 1+(1307429709/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2694018513/5000000000 : ℝ)*X 2 0+(2614859653/5000000000 : ℝ)*X 2 1+(-923316737/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((160227441/400000000 : ℝ)*X 0 0+(218925887/500000000 : ℝ)*X 0 1+(4378517719/10000000000 : ℝ)*X 0 2+(160227441/400000000 : ℝ)*X 1 0+(218925887/500000000 : ℝ)*X 1 1+(4378517719/10000000000 : ℝ)*X 1 2+(160227441/400000000 : ℝ)*X 2 0+(218925887/500000000 : ℝ)*X 2 1+(4378517719/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1555_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-63803/100000 : ℝ) ≤ (-29328309280629704791270913962101/45968750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3633671/100000000000000 : ℝ)*(upper1) + (5170179/100000000000000 : ℝ)*(upper3) + (4534327/50000000000000 : ℝ)*(upper5) + (285773600844903/12500000000000 : ℝ)*(major0) + (285773600844903/12500000000000 : ℝ)*(major1) + (285773600844903/12500000000000 : ℝ)*(major2) + (433600263/100000000000000 : ℝ)*(sp1) + (272642863/100000000000000 : ℝ)*(sp3) + (805803856777323/25000000000000 : ℝ)*(sp4) + (402902013024603/12500000000000 : ℝ)*(sp5) + (2578571334791/80000000000 : ℝ)*(sp6) + (1370427648693269/100000000000000 : ℝ)*(sp7) + (222137559/20000000000000 : ℝ)*(sp8) + (1184654169/50000000000000 : ℝ)*(sp14) + (342606980334033/25000000000000 : ℝ)*(f.failure) + (100725516806159/3125000000000 : ℝ)*(f.sum) + (4765229897127/1471000000000000000000000000 : ℝ)*base66 + (81640513293902039/91937500000000000000000000000000 : ℝ)*base68 + (154140857615964539/91937500000000000000000000000000 : ℝ)*base70 + (117808028356027039/91937500000000000000000000000000 : ℝ)*base72 + (5302141013687/1471000000000000000000000000 : ℝ)*base74 + (15836463354277039/91937500000000000000000000000000 : ℝ)*base76 + (495199388578277039/91937500000000000000000000000000 : ℝ)*base78 + (697671933679589539/91937500000000000000000000000000 : ℝ)*base80 + (9291832293953/1471000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (5787651/625000000000000000000 : ℝ)*base89 + (5787651/625000000000000000000 : ℝ)*base91 + (5787651/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (58831/100000 : ℝ) ≤ (216360377672325026717459973/367750000000000000000000000 : ℝ) := by norm_num
    linear_combination (14769121/20000000000000 : ℝ)*(upper1) + (5107207/4000000000000 : ℝ)*(upper3) + (7741/400000000000 : ℝ)*(upper5) + (1182693740244941/50000000000000 : ℝ)*(major0) + (1182693740244941/50000000000000 : ℝ)*(major1) + (1182693740244941/50000000000000 : ℝ)*(major2) + (658650264151179/20000000000000 : ℝ)*(sp0) + (823313063743059/25000000000000 : ℝ)*(sp1) + (823312381652891/25000000000000 : ℝ)*(sp2) + (177237752249201/12500000000000 : ℝ)*(sp3) + (5826755469/50000000000000 : ℝ)*(sp6) + (289876311/50000000000000 : ℝ)*(sp7) + (8925150267/100000000000000 : ℝ)*(sp9) + (616210413/6250000000000 : ℝ)*(sp12) + (1417902597746231/100000000000000 : ℝ)*(f.failure) + (3293261180122503/100000000000000 : ℝ)*(f.sum) + (177823299199/58840000000000000000000000 : ℝ)*base65 + (1614837772035856833/367750000000000000000000000000000 : ℝ)*base68 + (3064273856230393167/367750000000000000000000000000000 : ℝ)*base69 + (1698665215826356833/367750000000000000000000000000000 : ℝ)*base72 + (766595511229/735500000000000000000000000 : ℝ)*base73 + (714969046969856833/367750000000000000000000000000000 : ℝ)*base76 + (347196928826393167/367750000000000000000000000000000 : ℝ)*base77 + (1344878179321393167/367750000000000000000000000000000 : ℝ)*base79 + (31451971940981/735500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (30289557/2500000000000000000000 : ℝ)*base89 + (30289557/2500000000000000000000 : ℝ)*base91 + (30289557/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (80769/100000 : ℝ) ≤ (297036780093576611637468554115453/367750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4571033/50000000000000 : ℝ)*(lower2) + (79945851/100000000000000 : ℝ)*(lower3) + (173796519/100000000000000 : ℝ)*(upper4) + (1589453/50000000000000 : ℝ)*(lower5) + (2553859782556591/100000000000000 : ℝ)*(major0) + (2553859782556591/100000000000000 : ℝ)*(major1) + (2553859782556591/100000000000000 : ℝ)*(major2) + (13109873147/20000000000000 : ℝ)*(sp1) + (116729392783/100000000000000 : ℝ)*(sp2) + (2059273423/6250000000000 : ℝ)*(sp3) + (3549915754743693/100000000000000 : ℝ)*(sp8) + (1774925102688979/50000000000000 : ℝ)*(sp9) + (354979902535091/10000000000000 : ℝ)*(sp10) + (1530847065929131/100000000000000 : ℝ)*(sp11) + (1530880014303899/100000000000000 : ℝ)*(f.failure) + (3549915754743693/100000000000000 : ℝ)*(f.sum) + (1255882776053/735500000000000000000000000 : ℝ)*base65 + (3775049276706848283/735500000000000000000000000000000 : ℝ)*base68 + (5789015540439348283/735500000000000000000000000000000 : ℝ)*base70 + (2959912488324348283/735500000000000000000000000000000 : ℝ)*base72 + (184224980527/1471000000000000000000000000 : ℝ)*base73 + (6494758868991848283/735500000000000000000000000000000 : ℝ)*base76 + (948285066048848283/735500000000000000000000000000000 : ℝ)*base78 + (3470600963864848283/735500000000000000000000000000000 : ℝ)*base80 + (8821062169/367750000000000000000000000 : ℝ)*base82 + (17807553/2500000000000000000000 : ℝ)*base89 + (17807553/2500000000000000000000 : ℝ)*base91 + (17807553/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-43137/50000 : ℝ) ≤ (-317262101408077846548210866383389/367750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (30459857/50000000000000 : ℝ)*(upper3) + (25243417/50000000000000 : ℝ)*(lower4) + (4167901/100000000000000 : ℝ)*(upper5) + (2593974451536817/100000000000000 : ℝ)*(major0) + (2593974451536817/100000000000000 : ℝ)*(major1) + (2593974451536817/100000000000000 : ℝ)*(major2) + (2038324377/100000000000000 : ℝ)*(sp4) + (53492078319/50000000000000 : ℝ)*(sp5) + (18528079043/100000000000000 : ℝ)*(sp7) + (367628531/50000000000000 : ℝ)*(sp8) + (29294215301367/800000000000 : ℝ)*(sp12) + (915418175523919/25000000000000 : ℝ)*(sp13) + (1830889843126157/50000000000000 : ℝ)*(sp14) + (777453866981971/50000000000000 : ℝ)*(sp15) + (310985252408597/20000000000000 : ℝ)*(f.failure) + (1830889843126157/50000000000000 : ℝ)*(f.sum) + (390387709563/91937500000000000000000000 : ℝ)*base66 + (7871781735766014821/735500000000000000000000000000000 : ℝ)*base68 + (4494116328451514821/735500000000000000000000000000000 : ℝ)*base70 + (6369651786526014821/735500000000000000000000000000000 : ℝ)*base72 + (5375893577131/1471000000000000000000000000 : ℝ)*base74 + (2754070735890514821/735500000000000000000000000000000 : ℝ)*base76 + (5051129477152014821/735500000000000000000000000000000 : ℝ)*base78 + (1343309421530514821/735500000000000000000000000000000 : ℝ)*base80 + (4723175002383/1471000000000000000000000000 : ℝ)*base82 + (2106959/500000000000000000000 : ℝ)*base89 + (2106959/500000000000000000000 : ℝ)*base91 + (2106959/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1555_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41705747/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (346/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63803/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58831/100000 : ℝ) else (80769/100000 : ℝ) ≤ X j i ∧ X j i ≤ (43137/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1555_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1555_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41705747/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11071/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63803/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58831/100000 : ℝ) else (80769/100000 : ℝ) ≤ X j i ∧ X j i ≤ (43137/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1555_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1555_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4605/1024 : ℝ) ≤ p) (hpb : p ≤ (4607/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41705747/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11071/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63803/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58831/100000 : ℝ) else (80769/100000 : ℝ) ≤ X j i ∧ X j i ≤ (43137/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1555_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
