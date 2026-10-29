-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1714_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:54:44.438904+00:00
-- url     : https://prove2.me/submissions/ac3b0743-2605-4d0b-9385-2a8cdde6314f

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
theorem support_rectangle_w1714_s0_0 (p : ℝ) (hpa : (5327/1024 : ℝ) ≤ p) (hpb : p ≤ (5335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1324897723/10000000000 : ℝ)*x 0 + (5689921053/10000000000 : ℝ)*x 1 + (2482194351/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1324897723/10000000000 : ℝ)^5335 ≤ (1024666829813/12500000000000 : ℝ)^4311 := by
    have hnat : (1324897723 : ℕ)^5335*12500000000000^4311 ≤ 1024666829813^4311*10000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1324897723 10000000000 1024666829813 12500000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5689921053/10000000000 : ℝ)^5335 ≤ (4976639266383/10000000000000 : ℝ)^4311 := by
    have hnat : (5689921053 : ℕ)^5335*10000000000000^4311 ≤ 4976639266383^4311*10000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5689921053 10000000000 4976639266383 10000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2482194351/5000000000 : ℝ)^5335 ≤ (42036272682927/100000000000000 : ℝ)^4311 := by
    have hnat : (2482194351 : ℕ)^5335*100000000000000^4311 ≤ 42036272682927^4311*5000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2482194351 5000000000 42036272682927 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5335/1024 : ℝ)) 5335 4311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1324897723/10000000000 : ℝ), (5689921053/10000000000 : ℝ), (2482194351/5000000000 : ℝ)] ![(1024666829813/12500000000000 : ℝ), (4976639266383/10000000000000 : ℝ), (42036272682927/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1324897723/10000000000 : ℝ)|^5335 ≤ (1024666829813/12500000000000 : ℝ)^4311
        have hw : |(-1324897723/10000000000 : ℝ)|=(1324897723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5689921053/10000000000 : ℝ)|^5335 ≤ (4976639266383/10000000000000 : ℝ)^4311
        have hw : |(5689921053/10000000000 : ℝ)|=(5689921053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2482194351/5000000000 : ℝ)|^5335 ≤ (42036272682927/100000000000000 : ℝ)^4311
        have hw : |(2482194351/5000000000 : ℝ)|=(2482194351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1714_s0_1 (p : ℝ) (hpa : (5327/1024 : ℝ) ≤ p) (hpb : p ≤ (5335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2700747153/5000000000 : ℝ)*x 0 + (-1717264309/10000000000 : ℝ)*x 1 + (4964388827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2700747153/5000000000 : ℝ)^5335 ≤ (23331757400413/50000000000000 : ℝ)^4311 := by
    have hnat : (2700747153 : ℕ)^5335*50000000000000^4311 ≤ 23331757400413^4311*5000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700747153 5000000000 23331757400413 50000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1717264309/10000000000 : ℝ)^5335 ≤ (226004223987/2000000000000 : ℝ)^4311 := by
    have hnat : (1717264309 : ℕ)^5335*2000000000000^4311 ≤ 226004223987^4311*10000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1717264309 10000000000 226004223987 2000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4964388827/10000000000 : ℝ)^5335 ≤ (42036273992787/100000000000000 : ℝ)^4311 := by
    have hnat : (4964388827 : ℕ)^5335*100000000000000^4311 ≤ 42036273992787^4311*10000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4964388827 10000000000 42036273992787 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5335/1024 : ℝ)) 5335 4311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2700747153/5000000000 : ℝ), (-1717264309/10000000000 : ℝ), (4964388827/10000000000 : ℝ)] ![(23331757400413/50000000000000 : ℝ), (226004223987/2000000000000 : ℝ), (42036273992787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2700747153/5000000000 : ℝ)|^5335 ≤ (23331757400413/50000000000000 : ℝ)^4311
        have hw : |(2700747153/5000000000 : ℝ)|=(2700747153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1717264309/10000000000 : ℝ)|^5335 ≤ (226004223987/2000000000000 : ℝ)^4311
        have hw : |(-1717264309/10000000000 : ℝ)|=(1717264309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4964388827/10000000000 : ℝ)|^5335 ≤ (42036273992787/100000000000000 : ℝ)^4311
        have hw : |(4964388827/10000000000 : ℝ)|=(4964388827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1714_s0_2 (p : ℝ) (hpa : (5327/1024 : ℝ) ≤ p) (hpb : p ≤ (5335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (135037363/250000000 : ℝ)*x 0 + (4964388847/10000000000 : ℝ)*x 1 + (-1717264001/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (135037363/250000000 : ℝ)^5335 ≤ (11665879272177/25000000000000 : ℝ)^4311 := by
    have hnat : (135037363 : ℕ)^5335*25000000000000^4311 ≤ 11665879272177^4311*250000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135037363 250000000 11665879272177 25000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4964388847/10000000000 : ℝ)^5335 ≤ (8407254840473/20000000000000 : ℝ)^4311 := by
    have hnat : (4964388847 : ℕ)^5335*20000000000000^4311 ≤ 8407254840473^4311*10000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4964388847 10000000000 8407254840473 20000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1717264001/10000000000 : ℝ)^5335 ≤ (11300208691183/100000000000000 : ℝ)^4311 := by
    have hnat : (1717264001 : ℕ)^5335*100000000000000^4311 ≤ 11300208691183^4311*10000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1717264001 10000000000 11300208691183 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5335/1024 : ℝ)) 5335 4311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(135037363/250000000 : ℝ), (4964388847/10000000000 : ℝ), (-1717264001/10000000000 : ℝ)] ![(11665879272177/25000000000000 : ℝ), (8407254840473/20000000000000 : ℝ), (11300208691183/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(135037363/250000000 : ℝ)|^5335 ≤ (11665879272177/25000000000000 : ℝ)^4311
        have hw : |(135037363/250000000 : ℝ)|=(135037363/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4964388847/10000000000 : ℝ)|^5335 ≤ (8407254840473/20000000000000 : ℝ)^4311
        have hw : |(4964388847/10000000000 : ℝ)|=(4964388847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1717264001/10000000000 : ℝ)|^5335 ≤ (11300208691183/100000000000000 : ℝ)^4311
        have hw : |(-1717264001/10000000000 : ℝ)|=(1717264001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1714_s0_3 (p : ℝ) (hpa : (5327/1024 : ℝ) ≤ p) (hpb : p ≤ (5335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4036226501/10000000000 : ℝ)*x 0 + (153074193/500000000 : ℝ)*x 1 + (5184173741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4036226501/10000000000 : ℝ)^5335 ≤ (32537347855341/100000000000000 : ℝ)^4311 := by
    have hnat : (4036226501 : ℕ)^5335*100000000000000^4311 ≤ 32537347855341^4311*10000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4036226501 10000000000 32537347855341 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (153074193/500000000 : ℝ)^5335 ≤ (23111302488397/100000000000000 : ℝ)^4311 := by
    have hnat : (153074193 : ℕ)^5335*100000000000000^4311 ≤ 23111302488397^4311*500000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      153074193 500000000 23111302488397 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5184173741/10000000000 : ℝ)^5335 ≤ (44351349640153/100000000000000 : ℝ)^4311 := by
    have hnat : (5184173741 : ℕ)^5335*100000000000000^4311 ≤ 44351349640153^4311*10000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184173741 10000000000 44351349640153 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5335/1024 : ℝ)) 5335 4311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4036226501/10000000000 : ℝ), (153074193/500000000 : ℝ), (5184173741/10000000000 : ℝ)] ![(32537347855341/100000000000000 : ℝ), (23111302488397/100000000000000 : ℝ), (44351349640153/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4036226501/10000000000 : ℝ)|^5335 ≤ (32537347855341/100000000000000 : ℝ)^4311
        have hw : |(4036226501/10000000000 : ℝ)|=(4036226501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(153074193/500000000 : ℝ)|^5335 ≤ (23111302488397/100000000000000 : ℝ)^4311
        have hw : |(153074193/500000000 : ℝ)|=(153074193/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5184173741/10000000000 : ℝ)|^5335 ≤ (44351349640153/100000000000000 : ℝ)^4311
        have hw : |(5184173741/10000000000 : ℝ)|=(5184173741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1714_s0_4 (p : ℝ) (hpa : (5327/1024 : ℝ) ≤ p) (hpb : p ≤ (5335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-13265069/100000000 : ℝ)*x 0 + (4982139811/10000000000 : ℝ)*x 1 + (5671583077/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13265069/100000000 : ℝ)^5335 ≤ (8209657544943/100000000000000 : ℝ)^4311 := by
    have hnat : (13265069 : ℕ)^5335*100000000000000^4311 ≤ 8209657544943^4311*100000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13265069 100000000 8209657544943 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4982139811/10000000000 : ℝ)^5335 ≤ (42222363327049/100000000000000 : ℝ)^4311 := by
    have hnat : (4982139811 : ℕ)^5335*100000000000000^4311 ≤ 42222363327049^4311*10000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4982139811 10000000000 42222363327049 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5671583077/10000000000 : ℝ)^5335 ≤ (12391994779397/25000000000000 : ℝ)^4311 := by
    have hnat : (5671583077 : ℕ)^5335*25000000000000^4311 ≤ 12391994779397^4311*10000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5671583077 10000000000 12391994779397 25000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5335/1024 : ℝ)) 5335 4311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-13265069/100000000 : ℝ), (4982139811/10000000000 : ℝ), (5671583077/10000000000 : ℝ)] ![(8209657544943/100000000000000 : ℝ), (42222363327049/100000000000000 : ℝ), (12391994779397/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-13265069/100000000 : ℝ)|^5335 ≤ (8209657544943/100000000000000 : ℝ)^4311
        have hw : |(-13265069/100000000 : ℝ)|=(13265069/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4982139811/10000000000 : ℝ)|^5335 ≤ (42222363327049/100000000000000 : ℝ)^4311
        have hw : |(4982139811/10000000000 : ℝ)|=(4982139811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5671583077/10000000000 : ℝ)|^5335 ≤ (12391994779397/25000000000000 : ℝ)^4311
        have hw : |(5671583077/10000000000 : ℝ)|=(5671583077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1714_s0_5 (p : ℝ) (hpa : (5327/1024 : ℝ) ≤ p) (hpb : p ≤ (5335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (650633019/1250000000 : ℝ)*x 0 + (-1010069679/10000000000 : ℝ)*x 1 + (354473913/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (650633019/1250000000 : ℝ)^5335 ≤ (445726276529/1000000000000 : ℝ)^4311 := by
    have hnat : (650633019 : ℕ)^5335*1000000000000^4311 ≤ 445726276529^4311*1250000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      650633019 1250000000 445726276529 1000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1010069679/10000000000 : ℝ)^5335 ≤ (5859398288553/100000000000000 : ℝ)^4311 := by
    have hnat : (1010069679 : ℕ)^5335*100000000000000^4311 ≤ 5859398288553^4311*10000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1010069679 10000000000 5859398288553 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (354473913/625000000 : ℝ)^5335 ≤ (619599675563/1250000000000 : ℝ)^4311 := by
    have hnat : (354473913 : ℕ)^5335*1250000000000^4311 ≤ 619599675563^4311*625000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      354473913 625000000 619599675563 1250000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5335/1024 : ℝ)) 5335 4311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(650633019/1250000000 : ℝ), (-1010069679/10000000000 : ℝ), (354473913/625000000 : ℝ)] ![(445726276529/1000000000000 : ℝ), (5859398288553/100000000000000 : ℝ), (619599675563/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(650633019/1250000000 : ℝ)|^5335 ≤ (445726276529/1000000000000 : ℝ)^4311
        have hw : |(650633019/1250000000 : ℝ)|=(650633019/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1010069679/10000000000 : ℝ)|^5335 ≤ (5859398288553/100000000000000 : ℝ)^4311
        have hw : |(-1010069679/10000000000 : ℝ)|=(1010069679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(354473913/625000000 : ℝ)|^5335 ≤ (619599675563/1250000000000 : ℝ)^4311
        have hw : |(354473913/625000000 : ℝ)|=(354473913/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1714_s0_6 (p : ℝ) (hpa : (5327/1024 : ℝ) ≤ p) (hpb : p ≤ (5335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1301265957/2500000000 : ℝ)*x 0 + (2835791473/5000000000 : ℝ)*x 1 + (-63129353/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1301265957/2500000000 : ℝ)^5335 ≤ (44572624219349/100000000000000 : ℝ)^4311 := by
    have hnat : (1301265957 : ℕ)^5335*100000000000000^4311 ≤ 44572624219349^4311*2500000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1301265957 2500000000 44572624219349 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2835791473/5000000000 : ℝ)^5335 ≤ (387249825787/781250000000 : ℝ)^4311 := by
    have hnat : (2835791473 : ℕ)^5335*781250000000^4311 ≤ 387249825787^4311*5000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2835791473 5000000000 387249825787 781250000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (63129353/625000000 : ℝ)^5335 ≤ (5859398066007/100000000000000 : ℝ)^4311 := by
    have hnat : (63129353 : ℕ)^5335*100000000000000^4311 ≤ 5859398066007^4311*625000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63129353 625000000 5859398066007 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5335/1024 : ℝ)) 5335 4311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1301265957/2500000000 : ℝ), (2835791473/5000000000 : ℝ), (-63129353/625000000 : ℝ)] ![(44572624219349/100000000000000 : ℝ), (387249825787/781250000000 : ℝ), (5859398066007/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1301265957/2500000000 : ℝ)|^5335 ≤ (44572624219349/100000000000000 : ℝ)^4311
        have hw : |(1301265957/2500000000 : ℝ)|=(1301265957/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2835791473/5000000000 : ℝ)|^5335 ≤ (387249825787/781250000000 : ℝ)^4311
        have hw : |(2835791473/5000000000 : ℝ)|=(2835791473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-63129353/625000000 : ℝ)|^5335 ≤ (5859398066007/100000000000000 : ℝ)^4311
        have hw : |(-63129353/625000000 : ℝ)|=(63129353/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1714_s0_7 (p : ℝ) (hpa : (5327/1024 : ℝ) ≤ p) (hpb : p ≤ (5335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2020466001/5000000000 : ℝ)*x 0 + (1026447739/2000000000 : ℝ)*x 1 + (3115133603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2020466001/5000000000 : ℝ)^5335 ≤ (32584297142419/100000000000000 : ℝ)^4311 := by
    have hnat : (2020466001 : ℕ)^5335*100000000000000^4311 ≤ 32584297142419^4311*5000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2020466001 5000000000 32584297142419 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1026447739/2000000000 : ℝ)^5335 ≤ (21901077771441/50000000000000 : ℝ)^4311 := by
    have hnat : (1026447739 : ℕ)^5335*50000000000000^4311 ≤ 21901077771441^4311*2000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026447739 2000000000 21901077771441 50000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3115133603/10000000000 : ℝ)^5335 ≤ (5903386822621/25000000000000 : ℝ)^4311 := by
    have hnat : (3115133603 : ℕ)^5335*25000000000000^4311 ≤ 5903386822621^4311*10000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3115133603 10000000000 5903386822621 25000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5335/1024 : ℝ)) 5335 4311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2020466001/5000000000 : ℝ), (1026447739/2000000000 : ℝ), (3115133603/10000000000 : ℝ)] ![(32584297142419/100000000000000 : ℝ), (21901077771441/50000000000000 : ℝ), (5903386822621/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2020466001/5000000000 : ℝ)|^5335 ≤ (32584297142419/100000000000000 : ℝ)^4311
        have hw : |(2020466001/5000000000 : ℝ)|=(2020466001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1026447739/2000000000 : ℝ)|^5335 ≤ (21901077771441/50000000000000 : ℝ)^4311
        have hw : |(1026447739/2000000000 : ℝ)|=(1026447739/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3115133603/10000000000 : ℝ)|^5335 ≤ (5903386822621/25000000000000 : ℝ)^4311
        have hw : |(3115133603/10000000000 : ℝ)|=(3115133603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1714_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5327/1024 : ℝ) ≤ p) (hpb : p ≤ (5335/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (196285051/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (3083/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2177/10000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (5327/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5327 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5327*1^1024 ≤ 0^1024*1^5327 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5327 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5327 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5327/1024 : ℝ) ≤ (850857841501994163/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5327 ≤ (850857841501994163/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5327*100000000000000000000^1024 ≤ 850857841501994163^1024*5^5327 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 850857841501994163 100000000000000000000 5327 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (850857841501994163/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5327 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5327/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5327 := by
      have hnat : (1 : ℕ)^1024*1^5327 ≤ 1^5327*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5327 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100850857841501994163/100000000000000000000 : ℝ) ≤ (5008149986357867/5000000000000000 : ℝ) ^ (5327/1024 : ℝ) := by
    have hpowers : (100850857841501994163/100000000000000000000 : ℝ)^1024 ≤ (5008149986357867/5000000000000000 : ℝ)^5327 := by
      have hnat : (100850857841501994163 : ℕ)^1024*5000000000000000^5327 ≤ 5008149986357867^5327*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100850857841501994163 100000000000000000000 5008149986357867 5000000000000000 1024 5327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5008149986357867/5000000000000000 : ℝ)) (X := (100850857841501994163/100000000000000000000 : ℝ)) (by norm_num) 5327 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50850857841501994163/50000000000000000000 : ℝ) ≤ (2508149986357867/2500000000000000 : ℝ) ^ (5327/1024 : ℝ) := by
    have hpowers : (50850857841501994163/50000000000000000000 : ℝ)^1024 ≤ (2508149986357867/2500000000000000 : ℝ)^5327 := by
      have hnat : (50850857841501994163 : ℕ)^1024*2500000000000000^5327 ≤ 2508149986357867^5327*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50850857841501994163 50000000000000000000 2508149986357867 2500000000000000 1024 5327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2508149986357867/2500000000000000 : ℝ)) (X := (50850857841501994163/50000000000000000000 : ℝ)) (by norm_num) 5327 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(8149986357867/2000000000000000 : ℝ)*(0 : ℝ))^(5327/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(8149986357867/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(850857841501994163/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(8149986357867/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5327/1024 : ℝ) := by
    rw [show (1 : ℝ)+(8149986357867/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5008149986357867/5000000000000000 : ℝ) by norm_num, show 1+(850857841501994163/100000000000000000000 : ℝ)+(0 : ℝ)=(100850857841501994163/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(850857841501994163/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(8149986357867/2000000000000000 : ℝ)*(2/5 : ℝ))^(5327/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(8149986357867/2000000000000000 : ℝ)*(2/5 : ℝ)=(2508149986357867/2500000000000000 : ℝ) by norm_num, show 1+2*(850857841501994163/100000000000000000000 : ℝ)=(50850857841501994163/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(8149986357867/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5327/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (8149986357867/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(8149986357867/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5327/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (8149986357867/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(8149986357867/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5327/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (8149986357867/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1324897723/10000000000 : ℝ)*X 0 0+(5689921053/10000000000 : ℝ)*X 0 1+(2482194351/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1714_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2700747153/5000000000 : ℝ)*X 1 0+(-1717264309/10000000000 : ℝ)*X 1 1+(4964388827/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1714_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((135037363/250000000 : ℝ)*X 2 0+(4964388847/10000000000 : ℝ)*X 2 1+(-1717264001/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1714_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4036226501/10000000000 : ℝ)*X 0 0+(153074193/500000000 : ℝ)*X 0 1+(5184173741/10000000000 : ℝ)*X 0 2+(4036226501/10000000000 : ℝ)*X 1 0+(153074193/500000000 : ℝ)*X 1 1+(5184173741/10000000000 : ℝ)*X 1 2+(4036226501/10000000000 : ℝ)*X 2 0+(153074193/500000000 : ℝ)*X 2 1+(5184173741/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1714_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-13265069/100000000 : ℝ)*X 0 0+(4982139811/10000000000 : ℝ)*X 0 1+(5671583077/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1714_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((650633019/1250000000 : ℝ)*X 1 0+(-1010069679/10000000000 : ℝ)*X 1 1+(354473913/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1714_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1301265957/2500000000 : ℝ)*X 2 0+(2835791473/5000000000 : ℝ)*X 2 1+(-63129353/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1714_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2020466001/5000000000 : ℝ)*X 0 0+(1026447739/2000000000 : ℝ)*X 0 1+(3115133603/10000000000 : ℝ)*X 0 2+(2020466001/5000000000 : ℝ)*X 1 0+(1026447739/2000000000 : ℝ)*X 1 1+(3115133603/10000000000 : ℝ)*X 1 2+(2020466001/5000000000 : ℝ)*X 2 0+(1026447739/2000000000 : ℝ)*X 2 1+(3115133603/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1714_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (347529406963418434044579/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2687689/20000000000000 : ℝ)*(base1) + (149643613/25000000000000 : ℝ)*(base19) + (26127241/4000000000000 : ℝ)*(base23) + (10619263/50000000000000 : ℝ)*(upper3) + (31608877/20000000000000 : ℝ)*(upper5) + (924703700929821/100000000000000 : ℝ)*(major0) + (924703700929821/100000000000000 : ℝ)*(major1) + (924703700929821/100000000000000 : ℝ)*(major2) + (1378300729811271/100000000000000 : ℝ)*(sp0) + (1378304228941623/100000000000000 : ℝ)*(sp1) + (27566083486701/2000000000000 : ℝ)*(sp2) + (117775397288689/25000000000000 : ℝ)*(sp3) + (4111143249/100000000000000 : ℝ)*(sp4) + (213976807/25000000000000 : ℝ)*(sp7) + (471102458500429/100000000000000 : ℝ)*(f.failure) + (55132193100643/4000000000000 : ℝ)*(f.sum) + (80358640351807/100000000000000000000000000000 : ℝ)*base65 + (656593173851807/200000000000000000000000000000 : ℝ)*base67 + (818467260748193/200000000000000000000000000000 : ℝ)*base70 + (14153588251807/200000000000000000000000000000 : ℝ)*base71 + (428913946951807/100000000000000000000000000000 : ℝ)*base73 + (170585021948193/200000000000000000000000000000 : ℝ)*base76 + (21451884148193/200000000000000000000000000000 : ℝ)*base78 + (513630564251807/200000000000000000000000000000 : ℝ)*base79 + (228157804748193/100000000000000000000000000000 : ℝ)*base82 + (10213121/10000000000000000000000 : ℝ)*base90 + (10213121/10000000000000000000000 : ℝ)*base92 + (10213121/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (116595228868465264986783/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (253046613/10000000000000 : ℝ)*(base19) + (2630773497/100000000000000 : ℝ)*(base23) + (89495847/100000000000000 : ℝ)*(upper2) + (97155551/25000000000000 : ℝ)*(upper3) + (39089801/10000000000000 : ℝ)*(upper5) + (486551264524517/50000000000000 : ℝ)*(major0) + (486551264524517/50000000000000 : ℝ)*(major1) + (486551264524517/50000000000000 : ℝ)*(major2) + (2257667237/25000000000000 : ℝ)*(sp1) + (190498417/2000000000000 : ℝ)*(sp2) + (1450444869340889/100000000000000 : ℝ)*(sp4) + (1450433308205811/100000000000000 : ℝ)*(sp5) + (725216356823271/50000000000000 : ℝ)*(sp6) + (247879938918281/50000000000000 : ℝ)*(sp7) + (247879938918281/50000000000000 : ℝ)*(f.failure) + (1450444869340889/100000000000000 : ℝ)*(f.sum) + (58452793874761/50000000000000000000000000000 : ℝ)*base66 + (871668500425239/100000000000000000000000000000 : ℝ)*base67 + (609115523425239/100000000000000000000000000000 : ℝ)*base69 + (733722908925239/100000000000000000000000000000 : ℝ)*base71 + (51364107875239/50000000000000000000000000000 : ℝ)*base73 + (114851160325239/100000000000000000000000000000 : ℝ)*base75 + (115420167325239/100000000000000000000000000000 : ℝ)*base77 + (975688430125239/100000000000000000000000000000 : ℝ)*base79 + (67862616325239/50000000000000000000000000000 : ℝ)*base81 + (29082669/5000000000000000000000 : ℝ)*base90 + (29082669/5000000000000000000000 : ℝ)*base92 + (29082669/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1714_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5327/1024 : ℝ) ≤ p) (hpb : p ≤ (5335/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (196285051/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3083/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2177/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1714_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1714_s1_0 (p : ℝ) (hpa : (5327/1024 : ℝ) ≤ p) (hpb : p ≤ (5335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1394429711/10000000000 : ℝ)*x 0 + (5481124679/10000000000 : ℝ)*x 1 + (5127363261/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1394429711/10000000000 : ℝ)^5335 ≤ (2183250387053/25000000000000 : ℝ)^4311 := by
    have hnat : (1394429711 : ℕ)^5335*25000000000000^4311 ≤ 2183250387053^4311*10000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1394429711 10000000000 2183250387053 25000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5481124679/10000000000 : ℝ)^5335 ≤ (47516331279607/100000000000000 : ℝ)^4311 := by
    have hnat : (5481124679 : ℕ)^5335*100000000000000^4311 ≤ 47516331279607^4311*10000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5481124679 10000000000 47516331279607 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5127363261/10000000000 : ℝ)^5335 ≤ (43750667153621/100000000000000 : ℝ)^4311 := by
    have hnat : (5127363261 : ℕ)^5335*100000000000000^4311 ≤ 43750667153621^4311*10000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5127363261 10000000000 43750667153621 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5335/1024 : ℝ)) 5335 4311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1394429711/10000000000 : ℝ), (5481124679/10000000000 : ℝ), (5127363261/10000000000 : ℝ)] ![(2183250387053/25000000000000 : ℝ), (47516331279607/100000000000000 : ℝ), (43750667153621/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1394429711/10000000000 : ℝ)|^5335 ≤ (2183250387053/25000000000000 : ℝ)^4311
        have hw : |(-1394429711/10000000000 : ℝ)|=(1394429711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5481124679/10000000000 : ℝ)|^5335 ≤ (47516331279607/100000000000000 : ℝ)^4311
        have hw : |(5481124679/10000000000 : ℝ)|=(5481124679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5127363261/10000000000 : ℝ)|^5335 ≤ (43750667153621/100000000000000 : ℝ)^4311
        have hw : |(5127363261/10000000000 : ℝ)|=(5127363261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1714_s1_1 (p : ℝ) (hpa : (5327/1024 : ℝ) ≤ p) (hpb : p ≤ (5335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345879563/10000000000 : ℝ)*x 0 + (-49321883/312500000 : ℝ)*x 1 + (640920281/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345879563/10000000000 : ℝ)^5335 ≤ (460696643817/1000000000000 : ℝ)^4311 := by
    have hnat : (5345879563 : ℕ)^5335*1000000000000^4311 ≤ 460696643817^4311*10000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345879563 10000000000 460696643817 1000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (49321883/312500000 : ℝ)^5335 ≤ (2035935828447/20000000000000 : ℝ)^4311 := by
    have hnat : (49321883 : ℕ)^5335*20000000000000^4311 ≤ 2035935828447^4311*312500000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49321883 312500000 2035935828447 20000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (640920281/1250000000 : ℝ)^5335 ≤ (21875328228379/50000000000000 : ℝ)^4311 := by
    have hnat : (640920281 : ℕ)^5335*50000000000000^4311 ≤ 21875328228379^4311*1250000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      640920281 1250000000 21875328228379 50000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5335/1024 : ℝ)) 5335 4311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345879563/10000000000 : ℝ), (-49321883/312500000 : ℝ), (640920281/1250000000 : ℝ)] ![(460696643817/1000000000000 : ℝ), (2035935828447/20000000000000 : ℝ), (21875328228379/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345879563/10000000000 : ℝ)|^5335 ≤ (460696643817/1000000000000 : ℝ)^4311
        have hw : |(5345879563/10000000000 : ℝ)|=(5345879563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-49321883/312500000 : ℝ)|^5335 ≤ (2035935828447/20000000000000 : ℝ)^4311
        have hw : |(-49321883/312500000 : ℝ)|=(49321883/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(640920281/1250000000 : ℝ)|^5335 ≤ (21875328228379/50000000000000 : ℝ)^4311
        have hw : |(640920281/1250000000 : ℝ)|=(640920281/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1714_s1_2 (p : ℝ) (hpa : (5327/1024 : ℝ) ≤ p) (hpb : p ≤ (5335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672939113/5000000000 : ℝ)*x 0 + (5127363359/10000000000 : ℝ)*x 1 + (-789150287/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672939113/5000000000 : ℝ)^5335 ≤ (23034825061439/50000000000000 : ℝ)^4311 := by
    have hnat : (2672939113 : ℕ)^5335*50000000000000^4311 ≤ 23034825061439^4311*5000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672939113 5000000000 23034825061439 50000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5127363359/10000000000 : ℝ)^5335 ≤ (2187533409423/5000000000000 : ℝ)^4311 := by
    have hnat : (5127363359 : ℕ)^5335*5000000000000^4311 ≤ 2187533409423^4311*10000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5127363359 10000000000 2187533409423 5000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (789150287/5000000000 : ℝ)^5335 ≤ (159057526257/1562500000000 : ℝ)^4311 := by
    have hnat : (789150287 : ℕ)^5335*1562500000000^4311 ≤ 159057526257^4311*5000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      789150287 5000000000 159057526257 1562500000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5335/1024 : ℝ)) 5335 4311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672939113/5000000000 : ℝ), (5127363359/10000000000 : ℝ), (-789150287/5000000000 : ℝ)] ![(23034825061439/50000000000000 : ℝ), (2187533409423/5000000000000 : ℝ), (159057526257/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672939113/5000000000 : ℝ)|^5335 ≤ (23034825061439/50000000000000 : ℝ)^4311
        have hw : |(2672939113/5000000000 : ℝ)|=(2672939113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5127363359/10000000000 : ℝ)|^5335 ≤ (2187533409423/5000000000000 : ℝ)^4311
        have hw : |(5127363359/10000000000 : ℝ)|=(5127363359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-789150287/5000000000 : ℝ)|^5335 ≤ (159057526257/1562500000000 : ℝ)^4311
        have hw : |(-789150287/5000000000 : ℝ)|=(789150287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1714_s1_3 (p : ℝ) (hpa : (5327/1024 : ℝ) ≤ p) (hpb : p ≤ (5335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4097035137/10000000000 : ℝ)*x 0 + (1799991983/5000000000 : ℝ)*x 1 + (4634981689/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4097035137/10000000000 : ℝ)^5335 ≤ (33145065322339/100000000000000 : ℝ)^4311 := by
    have hnat : (4097035137 : ℕ)^5335*100000000000000^4311 ≤ 33145065322339^4311*10000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4097035137 10000000000 33145065322339 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1799991983/5000000000 : ℝ)^5335 ≤ (28242803156191/100000000000000 : ℝ)^4311 := by
    have hnat : (1799991983 : ℕ)^5335*100000000000000^4311 ≤ 28242803156191^4311*5000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1799991983 5000000000 28242803156191 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4634981689/10000000000 : ℝ)^5335 ≤ (38612131511517/100000000000000 : ℝ)^4311 := by
    have hnat : (4634981689 : ℕ)^5335*100000000000000^4311 ≤ 38612131511517^4311*10000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4634981689 10000000000 38612131511517 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5335/1024 : ℝ)) 5335 4311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4097035137/10000000000 : ℝ), (1799991983/5000000000 : ℝ), (4634981689/10000000000 : ℝ)] ![(33145065322339/100000000000000 : ℝ), (28242803156191/100000000000000 : ℝ), (38612131511517/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4097035137/10000000000 : ℝ)|^5335 ≤ (33145065322339/100000000000000 : ℝ)^4311
        have hw : |(4097035137/10000000000 : ℝ)|=(4097035137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1799991983/5000000000 : ℝ)|^5335 ≤ (28242803156191/100000000000000 : ℝ)^4311
        have hw : |(1799991983/5000000000 : ℝ)|=(1799991983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4634981689/10000000000 : ℝ)|^5335 ≤ (38612131511517/100000000000000 : ℝ)^4311
        have hw : |(4634981689/10000000000 : ℝ)|=(4634981689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1714_s1_4 (p : ℝ) (hpa : (5327/1024 : ℝ) ≤ p) (hpb : p ≤ (5335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1394616089/10000000000 : ℝ)*x 0 + (5131590889/10000000000 : ℝ)*x 1 + (1369207017/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1394616089/10000000000 : ℝ)^5335 ≤ (8734446072509/100000000000000 : ℝ)^4311 := by
    have hnat : (1394616089 : ℕ)^5335*100000000000000^4311 ≤ 8734446072509^4311*10000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1394616089 10000000000 8734446072509 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5131590889/10000000000 : ℝ)^5335 ≤ (21897656768111/50000000000000 : ℝ)^4311 := by
    have hnat : (5131590889 : ℕ)^5335*50000000000000^4311 ≤ 21897656768111^4311*10000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5131590889 10000000000 21897656768111 50000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1369207017/2500000000 : ℝ)^5335 ≤ (23735120188413/50000000000000 : ℝ)^4311 := by
    have hnat : (1369207017 : ℕ)^5335*50000000000000^4311 ≤ 23735120188413^4311*2500000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1369207017 2500000000 23735120188413 50000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5335/1024 : ℝ)) 5335 4311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1394616089/10000000000 : ℝ), (5131590889/10000000000 : ℝ), (1369207017/2500000000 : ℝ)] ![(8734446072509/100000000000000 : ℝ), (21897656768111/50000000000000 : ℝ), (23735120188413/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1394616089/10000000000 : ℝ)|^5335 ≤ (8734446072509/100000000000000 : ℝ)^4311
        have hw : |(-1394616089/10000000000 : ℝ)|=(1394616089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5131590889/10000000000 : ℝ)|^5335 ≤ (21897656768111/50000000000000 : ℝ)^4311
        have hw : |(5131590889/10000000000 : ℝ)|=(5131590889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1369207017/2500000000 : ℝ)|^5335 ≤ (23735120188413/50000000000000 : ℝ)^4311
        have hw : |(1369207017/2500000000 : ℝ)|=(1369207017/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1714_s1_5 (p : ℝ) (hpa : (5327/1024 : ℝ) ≤ p) (hpb : p ≤ (5335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2625573953/5000000000 : ℝ)*x 0 + (-49153397/400000000 : ℝ)*x 1 + (5476827699/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2625573953/5000000000 : ℝ)^5335 ≤ (45061507127887/100000000000000 : ℝ)^4311 := by
    have hnat : (2625573953 : ℕ)^5335*100000000000000^4311 ≤ 45061507127887^4311*5000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2625573953 5000000000 45061507127887 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (49153397/400000000 : ℝ)^5335 ≤ (7468256447629/100000000000000 : ℝ)^4311 := by
    have hnat : (49153397 : ℕ)^5335*100000000000000^4311 ≤ 7468256447629^4311*400000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49153397 400000000 7468256447629 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5476827699/10000000000 : ℝ)^5335 ≤ (47470236418833/100000000000000 : ℝ)^4311 := by
    have hnat : (5476827699 : ℕ)^5335*100000000000000^4311 ≤ 47470236418833^4311*10000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5476827699 10000000000 47470236418833 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5335/1024 : ℝ)) 5335 4311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2625573953/5000000000 : ℝ), (-49153397/400000000 : ℝ), (5476827699/10000000000 : ℝ)] ![(45061507127887/100000000000000 : ℝ), (7468256447629/100000000000000 : ℝ), (47470236418833/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2625573953/5000000000 : ℝ)|^5335 ≤ (45061507127887/100000000000000 : ℝ)^4311
        have hw : |(2625573953/5000000000 : ℝ)|=(2625573953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-49153397/400000000 : ℝ)|^5335 ≤ (7468256447629/100000000000000 : ℝ)^4311
        have hw : |(-49153397/400000000 : ℝ)|=(49153397/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5476827699/10000000000 : ℝ)|^5335 ≤ (47470236418833/100000000000000 : ℝ)^4311
        have hw : |(5476827699/10000000000 : ℝ)|=(5476827699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1714_s1_6 (p : ℝ) (hpa : (5327/1024 : ℝ) ≤ p) (hpb : p ≤ (5335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1050229637/2000000000 : ℝ)*x 0 + (2738413667/5000000000 : ℝ)*x 1 + (-1228835051/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050229637/2000000000 : ℝ)^5335 ≤ (45061510090753/100000000000000 : ℝ)^4311 := by
    have hnat : (1050229637 : ℕ)^5335*100000000000000^4311 ≤ 45061510090753^4311*2000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050229637 2000000000 45061510090753 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2738413667/5000000000 : ℝ)^5335 ≤ (741722382871/1562500000000 : ℝ)^4311 := by
    have hnat : (2738413667 : ℕ)^5335*1562500000000^4311 ≤ 741722382871^4311*5000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2738413667 5000000000 741722382871 1562500000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1228835051/10000000000 : ℝ)^5335 ≤ (746825739529/10000000000000 : ℝ)^4311 := by
    have hnat : (1228835051 : ℕ)^5335*10000000000000^4311 ≤ 746825739529^4311*10000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1228835051 10000000000 746825739529 10000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5335/1024 : ℝ)) 5335 4311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050229637/2000000000 : ℝ), (2738413667/5000000000 : ℝ), (-1228835051/10000000000 : ℝ)] ![(45061510090753/100000000000000 : ℝ), (741722382871/1562500000000 : ℝ), (746825739529/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050229637/2000000000 : ℝ)|^5335 ≤ (45061510090753/100000000000000 : ℝ)^4311
        have hw : |(1050229637/2000000000 : ℝ)|=(1050229637/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2738413667/5000000000 : ℝ)|^5335 ≤ (741722382871/1562500000000 : ℝ)^4311
        have hw : |(2738413667/5000000000 : ℝ)|=(2738413667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1228835051/10000000000 : ℝ)|^5335 ≤ (746825739529/10000000000000 : ℝ)^4311
        have hw : |(-1228835051/10000000000 : ℝ)|=(1228835051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1714_s1_7 (p : ℝ) (hpa : (5327/1024 : ℝ) ≤ p) (hpb : p ≤ (5335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4097576379/10000000000 : ℝ)*x 0 + (115565291/250000000 : ℝ)*x 1 + (903137939/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4097576379/10000000000 : ℝ)^5335 ≤ (8287621032997/25000000000000 : ℝ)^4311 := by
    have hnat : (4097576379 : ℕ)^5335*25000000000000^4311 ≤ 8287621032997^4311*10000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4097576379 10000000000 8287621032997 25000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (115565291/250000000 : ℝ)^5335 ≤ (38484644540711/100000000000000 : ℝ)^4311 := by
    have hnat : (115565291 : ℕ)^5335*100000000000000^4311 ≤ 38484644540711^4311*250000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      115565291 250000000 38484644540711 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (903137939/2500000000 : ℝ)^5335 ≤ (28364871322103/100000000000000 : ℝ)^4311 := by
    have hnat : (903137939 : ℕ)^5335*100000000000000^4311 ≤ 28364871322103^4311*2500000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903137939 2500000000 28364871322103 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5335/1024 : ℝ)) 5335 4311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4097576379/10000000000 : ℝ), (115565291/250000000 : ℝ), (903137939/2500000000 : ℝ)] ![(8287621032997/25000000000000 : ℝ), (38484644540711/100000000000000 : ℝ), (28364871322103/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4097576379/10000000000 : ℝ)|^5335 ≤ (8287621032997/25000000000000 : ℝ)^4311
        have hw : |(4097576379/10000000000 : ℝ)|=(4097576379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(115565291/250000000 : ℝ)|^5335 ≤ (38484644540711/100000000000000 : ℝ)^4311
        have hw : |(115565291/250000000 : ℝ)|=(115565291/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(903137939/2500000000 : ℝ)|^5335 ≤ (28364871322103/100000000000000 : ℝ)^4311
        have hw : |(903137939/2500000000 : ℝ)|=(903137939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1714_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5327/1024 : ℝ) ≤ p) (hpb : p ≤ (5335/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (196285051/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2177/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3083/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (9793/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17351/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2177/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3083/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2177/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3083/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2177/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3083/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2177/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3083/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2177/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3083/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2177/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3083/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3083/50000 : ℝ) ^ (5327/1024 : ℝ) ≤ (50747973477543/100000000000000000000 : ℝ) := by
    have hpowers : (3083/50000 : ℝ)^5327 ≤ (50747973477543/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3083 : ℕ)^5327*100000000000000000000^1024 ≤ 50747973477543^1024*50000^5327 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3083 50000 50747973477543 100000000000000000000 5327 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3083/50000 : ℝ)) (X := (50747973477543/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5327 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2177/10000 : ℝ) ^ (5327/1024 : ℝ) ≤ (8982169989156063/25000000000000000000 : ℝ) := by
    have hpowers : (2177/10000 : ℝ)^5327 ≤ (8982169989156063/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2177 : ℕ)^5327*25000000000000000000^1024 ≤ 8982169989156063^1024*10000^5327 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2177 10000 8982169989156063 25000000000000000000 5327 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2177/10000 : ℝ)) (X := (8982169989156063/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5327 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000050747973477543/50000000000000000000 : ℝ) ≤ (10000001951038241/10000000000000000 : ℝ) ^ (5327/1024 : ℝ) := by
    have hpowers : (50000050747973477543/50000000000000000000 : ℝ)^1024 ≤ (10000001951038241/10000000000000000 : ℝ)^5327 := by
      have hnat : (50000050747973477543 : ℕ)^1024*10000000000000000^5327 ≤ 10000001951038241^5327*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000050747973477543 50000000000000000000 10000001951038241 10000000000000000 1024 5327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000001951038241/10000000000000000 : ℝ)) (X := (50000050747973477543/50000000000000000000 : ℝ)) (by norm_num) 5327 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20007195885586020359/20000000000000000000 : ℝ) ≤ (10000691525840053/10000000000000000 : ℝ) ^ (5327/1024 : ℝ) := by
    have hpowers : (20007195885586020359/20000000000000000000 : ℝ)^1024 ≤ (10000691525840053/10000000000000000 : ℝ)^5327 := by
      have hnat : (20007195885586020359 : ℕ)^1024*10000000000000000^5327 ≤ 10000691525840053^5327*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20007195885586020359 20000000000000000000 10000691525840053 10000000000000000 1024 5327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000691525840053/10000000000000000 : ℝ)) (X := (20007195885586020359/20000000000000000000 : ℝ)) (by norm_num) 5327 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508982169989156063/12500000000000000000 : ℝ) ≤ (2000276220128373/2000000000000000 : ℝ) ^ (5327/1024 : ℝ) := by
    have hpowers : (12508982169989156063/12500000000000000000 : ℝ)^1024 ≤ (2000276220128373/2000000000000000 : ℝ)^5327 := by
      have hnat : (12508982169989156063 : ℕ)^1024*2000000000000000^5327 ≤ 2000276220128373^5327*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508982169989156063 12500000000000000000 2000276220128373 2000000000000000 1024 5327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000276220128373/2000000000000000 : ℝ)) (X := (12508982169989156063/12500000000000000000 : ℝ)) (by norm_num) 5327 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(50747973477543/100000000000000000000 : ℝ) ≤ ((7801576330377238349/7802000000000000000 : ℝ)+2*(172393700453/390100000000000 : ℝ)*(3083/50000 : ℝ))^(5327/1024 : ℝ) := by
    rw [show (7801576330377238349/7802000000000000000 : ℝ)+2*(172393700453/390100000000000 : ℝ)*(3083/50000 : ℝ)=(10000001951038241/10000000000000000 : ℝ) by norm_num, show 1+2*(50747973477543/100000000000000000000 : ℝ)=(50000050747973477543/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8982169989156063/25000000000000000000 : ℝ)+(50747973477543/100000000000000000000 : ℝ) ≤ ((7801576330377238349/7802000000000000000 : ℝ)+(172393700453/390100000000000 : ℝ)*((2177/10000 : ℝ)+(3083/50000 : ℝ)))^(5327/1024 : ℝ) := by
    rw [show (7801576330377238349/7802000000000000000 : ℝ)+(172393700453/390100000000000 : ℝ)*((2177/10000 : ℝ)+(3083/50000 : ℝ))=(10000691525840053/10000000000000000 : ℝ) by norm_num, show 1+(8982169989156063/25000000000000000000 : ℝ)+(50747973477543/100000000000000000000 : ℝ)=(20007195885586020359/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8982169989156063/25000000000000000000 : ℝ) ≤ ((7801576330377238349/7802000000000000000 : ℝ)+2*(172393700453/390100000000000 : ℝ)*(2177/10000 : ℝ))^(5327/1024 : ℝ) := by
    rw [show (7801576330377238349/7802000000000000000 : ℝ)+2*(172393700453/390100000000000 : ℝ)*(2177/10000 : ℝ)=(2000276220128373/2000000000000000 : ℝ) by norm_num, show 1+2*(8982169989156063/25000000000000000000 : ℝ)=(12508982169989156063/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7801576330377238349/7802000000000000000 : ℝ)*(X 1 0+X 2 0)+(172393700453/390100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5327/1024 : ℝ)) (lo := (3083/50000 : ℝ)) (hi := (2177/10000 : ℝ)) (c := (7801576330377238349/7802000000000000000 : ℝ)) (alpha := (172393700453/390100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7801576330377238349/7802000000000000000 : ℝ)*(X 0 1+X 2 1)+(172393700453/390100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5327/1024 : ℝ)) (lo := (3083/50000 : ℝ)) (hi := (2177/10000 : ℝ)) (c := (7801576330377238349/7802000000000000000 : ℝ)) (alpha := (172393700453/390100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7801576330377238349/7802000000000000000 : ℝ)*(X 0 2+X 1 2)+(172393700453/390100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5327/1024 : ℝ)) (lo := (3083/50000 : ℝ)) (hi := (2177/10000 : ℝ)) (c := (7801576330377238349/7802000000000000000 : ℝ)) (alpha := (172393700453/390100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1394429711/10000000000 : ℝ)*X 0 0+(5481124679/10000000000 : ℝ)*X 0 1+(5127363261/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1714_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345879563/10000000000 : ℝ)*X 1 0+(-49321883/312500000 : ℝ)*X 1 1+(640920281/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1714_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672939113/5000000000 : ℝ)*X 2 0+(5127363359/10000000000 : ℝ)*X 2 1+(-789150287/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1714_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4097035137/10000000000 : ℝ)*X 0 0+(1799991983/5000000000 : ℝ)*X 0 1+(4634981689/10000000000 : ℝ)*X 0 2+(4097035137/10000000000 : ℝ)*X 1 0+(1799991983/5000000000 : ℝ)*X 1 1+(4634981689/10000000000 : ℝ)*X 1 2+(4097035137/10000000000 : ℝ)*X 2 0+(1799991983/5000000000 : ℝ)*X 2 1+(4634981689/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1714_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1394616089/10000000000 : ℝ)*X 0 0+(5131590889/10000000000 : ℝ)*X 0 1+(1369207017/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1714_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2625573953/5000000000 : ℝ)*X 1 0+(-49153397/400000000 : ℝ)*X 1 1+(5476827699/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1714_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1050229637/2000000000 : ℝ)*X 2 0+(2738413667/5000000000 : ℝ)*X 2 1+(-1228835051/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1714_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4097576379/10000000000 : ℝ)*X 0 0+(115565291/250000000 : ℝ)*X 0 1+(903137939/2500000000 : ℝ)*X 0 2+(4097576379/10000000000 : ℝ)*X 1 0+(115565291/250000000 : ℝ)*X 1 1+(903137939/2500000000 : ℝ)*X 1 2+(4097576379/10000000000 : ℝ)*X 2 0+(115565291/250000000 : ℝ)*X 2 1+(903137939/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1714_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1088482659370181874069/97525000000000000000000000 : ℝ) := by norm_num
    linear_combination (1054829611/100000000000000 : ℝ)*(base19) + (53043099/10000000000000 : ℝ)*(base23) + (41223341/50000000000000 : ℝ)*(lower2) + (153574491/100000000000000 : ℝ)*(upper3) + (45012279/25000000000000 : ℝ)*(lower4) + (37929614894763/2000000000000 : ℝ)*(major0) + (37929614894763/2000000000000 : ℝ)*(major1) + (37929614894763/2000000000000 : ℝ)*(major2) + (2826771947931177/100000000000000 : ℝ)*(sp0) + (565354602431541/20000000000000 : ℝ)*(sp1) + (1413386768278163/50000000000000 : ℝ)*(sp2) + (483093230275681/50000000000000 : ℝ)*(sp3) + (2119056139/100000000000000 : ℝ)*(sp4) + (58990219/10000000000000 : ℝ)*(sp7) + (60386690653347/6250000000000 : ℝ)*(f.failure) + (706693516746829/25000000000000 : ℝ)*(f.sum) + (3593465396349/975250000000000000000000000 : ℝ)*base66 + (13510425914137713/15604000000000000000000000000000 : ℝ)*base68 + (28116900711618287/15604000000000000000000000000000 : ℝ)*base69 + (84583079978829713/15604000000000000000000000000000 : ℝ)*base72 + (799285985611/1950500000000000000000000000 : ℝ)*base74 + (28271018439254287/15604000000000000000000000000000 : ℝ)*base75 + (32548739850526287/15604000000000000000000000000000 : ℝ)*base77 + (6518652379257713/15604000000000000000000000000000 : ℝ)*base80 + (289488676107/487625000000000000000000000 : ℝ)*base81 + (1715697/625000000000000000000 : ℝ)*base89 + (1715697/625000000000000000000 : ℝ)*base91 + (1715697/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (977497809483753368799743391/195050000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1390309027/100000000000000 : ℝ)*(base19) + (463808051/25000000000000 : ℝ)*(base23) + (10079973/6250000000000 : ℝ)*(upper2) + (176912351/100000000000000 : ℝ)*(upper3) + (272780227/100000000000000 : ℝ)*(upper5) + (1943299517399753/100000000000000 : ℝ)*(major0) + (1943299517399753/100000000000000 : ℝ)*(major1) + (1943299517399753/100000000000000 : ℝ)*(major2) + (9874090129/100000000000000 : ℝ)*(sp1) + (315315121/3125000000000 : ℝ)*(sp2) + (362069922248319/12500000000000 : ℝ)*(sp4) + (579309622717479/20000000000000 : ℝ)*(sp5) + (724136858167619/25000000000000 : ℝ)*(sp6) + (495019744881069/50000000000000 : ℝ)*(sp7) + (495019744881069/50000000000000 : ℝ)*(f.failure) + (362069922248319/12500000000000 : ℝ)*(f.sum) + (33250563779239/19505000000000000000000000000 : ℝ)*base65 + (4634085946292692203/780200000000000000000000000000000 : ℝ)*base68 + (5492731011735892203/780200000000000000000000000000000 : ℝ)*base70 + (1181598386777107797/780200000000000000000000000000000 : ℝ)*base71 + (3458820371499/4876250000000000000000000000 : ℝ)*base74 + (1324249241828092203/780200000000000000000000000000000 : ℝ)*base76 + (3769300084249892203/780200000000000000000000000000000 : ℝ)*base78 + (493964245873492203/780200000000000000000000000000000 : ℝ)*base80 + (48169437617511/19505000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (32400481/5000000000000000000000 : ℝ)*base90 + (32400481/5000000000000000000000 : ℝ)*base92 + (32400481/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1714_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5327/1024 : ℝ) ≤ p) (hpb : p ≤ (5335/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (196285051/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2177/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3083/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9793/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17351/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1714_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1714_s2_0 (p : ℝ) (hpa : (5327/1024 : ℝ) ≤ p) (hpb : p ≤ (5335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-349408893/2500000000 : ℝ)*x 0 + (5467943227/10000000000 : ℝ)*x 1 + (5138394993/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (349408893/2500000000 : ℝ)^5335 ≤ (8757854987537/100000000000000 : ℝ)^4311 := by
    have hnat : (349408893 : ℕ)^5335*100000000000000^4311 ≤ 8757854987537^4311*2500000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      349408893 2500000000 8757854987537 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5467943227/10000000000 : ℝ)^5335 ≤ (5921869692831/12500000000000 : ℝ)^4311 := by
    have hnat : (5467943227 : ℕ)^5335*12500000000000^4311 ≤ 5921869692831^4311*10000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5467943227 10000000000 5921869692831 12500000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5138394993/10000000000 : ℝ)^5335 ≤ (342712401987/781250000000 : ℝ)^4311 := by
    have hnat : (5138394993 : ℕ)^5335*781250000000^4311 ≤ 342712401987^4311*10000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5138394993 10000000000 342712401987 781250000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5335/1024 : ℝ)) 5335 4311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-349408893/2500000000 : ℝ), (5467943227/10000000000 : ℝ), (5138394993/10000000000 : ℝ)] ![(8757854987537/100000000000000 : ℝ), (5921869692831/12500000000000 : ℝ), (342712401987/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-349408893/2500000000 : ℝ)|^5335 ≤ (8757854987537/100000000000000 : ℝ)^4311
        have hw : |(-349408893/2500000000 : ℝ)|=(349408893/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5467943227/10000000000 : ℝ)|^5335 ≤ (5921869692831/12500000000000 : ℝ)^4311
        have hw : |(5467943227/10000000000 : ℝ)|=(5467943227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5138394993/10000000000 : ℝ)|^5335 ≤ (342712401987/781250000000 : ℝ)^4311
        have hw : |(5138394993/10000000000 : ℝ)|=(5138394993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1714_s2_1 (p : ℝ) (hpa : (5327/1024 : ℝ) ≤ p) (hpb : p ≤ (5335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1335575003/2500000000 : ℝ)*x 0 + (-1568475179/10000000000 : ℝ)*x 1 + (5138395453/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1335575003/2500000000 : ℝ)^5335 ≤ (23015746130469/50000000000000 : ℝ)^4311 := by
    have hnat : (1335575003 : ℕ)^5335*50000000000000^4311 ≤ 23015746130469^4311*2500000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1335575003 2500000000 23015746130469 50000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1568475179/10000000000 : ℝ)^5335 ≤ (10101315410237/100000000000000 : ℝ)^4311 := by
    have hnat : (1568475179 : ℕ)^5335*100000000000000^4311 ≤ 10101315410237^4311*10000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1568475179 10000000000 10101315410237 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5138395453/10000000000 : ℝ)^5335 ≤ (43867192314227/100000000000000 : ℝ)^4311 := by
    have hnat : (5138395453 : ℕ)^5335*100000000000000^4311 ≤ 43867192314227^4311*10000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5138395453 10000000000 43867192314227 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5335/1024 : ℝ)) 5335 4311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1335575003/2500000000 : ℝ), (-1568475179/10000000000 : ℝ), (5138395453/10000000000 : ℝ)] ![(23015746130469/50000000000000 : ℝ), (10101315410237/100000000000000 : ℝ), (43867192314227/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1335575003/2500000000 : ℝ)|^5335 ≤ (23015746130469/50000000000000 : ℝ)^4311
        have hw : |(1335575003/2500000000 : ℝ)|=(1335575003/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1568475179/10000000000 : ℝ)|^5335 ≤ (10101315410237/100000000000000 : ℝ)^4311
        have hw : |(-1568475179/10000000000 : ℝ)|=(1568475179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5138395453/10000000000 : ℝ)|^5335 ≤ (43867192314227/100000000000000 : ℝ)^4311
        have hw : |(5138395453/10000000000 : ℝ)|=(5138395453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1714_s2_2 (p : ℝ) (hpa : (5327/1024 : ℝ) ≤ p) (hpb : p ≤ (5335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (667787643/1250000000 : ℝ)*x 0 + (1027679039/2000000000 : ℝ)*x 1 + (-784237003/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (667787643/1250000000 : ℝ)^5335 ≤ (46031504331559/100000000000000 : ℝ)^4311 := by
    have hnat : (667787643 : ℕ)^5335*100000000000000^4311 ≤ 46031504331559^4311*1250000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      667787643 1250000000 46031504331559 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1027679039/2000000000 : ℝ)^5335 ≤ (21933594794231/50000000000000 : ℝ)^4311 := by
    have hnat : (1027679039 : ℕ)^5335*50000000000000^4311 ≤ 21933594794231^4311*2000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1027679039 2000000000 21933594794231 50000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (784237003/5000000000 : ℝ)^5335 ≤ (10101306061463/100000000000000 : ℝ)^4311 := by
    have hnat : (784237003 : ℕ)^5335*100000000000000^4311 ≤ 10101306061463^4311*5000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      784237003 5000000000 10101306061463 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5335/1024 : ℝ)) 5335 4311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(667787643/1250000000 : ℝ), (1027679039/2000000000 : ℝ), (-784237003/5000000000 : ℝ)] ![(46031504331559/100000000000000 : ℝ), (21933594794231/50000000000000 : ℝ), (10101306061463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(667787643/1250000000 : ℝ)|^5335 ≤ (46031504331559/100000000000000 : ℝ)^4311
        have hw : |(667787643/1250000000 : ℝ)|=(667787643/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1027679039/2000000000 : ℝ)|^5335 ≤ (21933594794231/50000000000000 : ℝ)^4311
        have hw : |(1027679039/2000000000 : ℝ)|=(1027679039/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-784237003/5000000000 : ℝ)|^5335 ≤ (10101306061463/100000000000000 : ℝ)^4311
        have hw : |(-784237003/5000000000 : ℝ)|=(784237003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1714_s2_3 (p : ℝ) (hpa : (5327/1024 : ℝ) ≤ p) (hpb : p ≤ (5335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2049760759/5000000000 : ℝ)*x 0 + (727037367/2000000000 : ℝ)*x 1 + (4599343939/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2049760759/5000000000 : ℝ)^5335 ≤ (3316995988873/10000000000000 : ℝ)^4311 := by
    have hnat : (2049760759 : ℕ)^5335*10000000000000^4311 ≤ 3316995988873^4311*5000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2049760759 5000000000 3316995988873 10000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (727037367/2000000000 : ℝ)^5335 ≤ (14292487602003/50000000000000 : ℝ)^4311 := by
    have hnat : (727037367 : ℕ)^5335*50000000000000^4311 ≤ 14292487602003^4311*2000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      727037367 2000000000 14292487602003 50000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4599343939/10000000000 : ℝ)^5335 ≤ (19122532448957/50000000000000 : ℝ)^4311 := by
    have hnat : (4599343939 : ℕ)^5335*50000000000000^4311 ≤ 19122532448957^4311*10000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4599343939 10000000000 19122532448957 50000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5335/1024 : ℝ)) 5335 4311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2049760759/5000000000 : ℝ), (727037367/2000000000 : ℝ), (4599343939/10000000000 : ℝ)] ![(3316995988873/10000000000000 : ℝ), (14292487602003/50000000000000 : ℝ), (19122532448957/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2049760759/5000000000 : ℝ)|^5335 ≤ (3316995988873/10000000000000 : ℝ)^4311
        have hw : |(2049760759/5000000000 : ℝ)|=(2049760759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(727037367/2000000000 : ℝ)|^5335 ≤ (14292487602003/50000000000000 : ℝ)^4311
        have hw : |(727037367/2000000000 : ℝ)|=(727037367/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4599343939/10000000000 : ℝ)|^5335 ≤ (19122532448957/50000000000000 : ℝ)^4311
        have hw : |(4599343939/10000000000 : ℝ)|=(4599343939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1714_s2_4 (p : ℝ) (hpa : (5327/1024 : ℝ) ≤ p) (hpb : p ≤ (5335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-13977853/100000000 : ℝ)*x 0 + (1028413361/2000000000 : ℝ)*x 1 + (2732108167/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13977853/100000000 : ℝ)^5335 ≤ (8759016085209/100000000000000 : ℝ)^4311 := by
    have hnat : (13977853 : ℕ)^5335*100000000000000^4311 ≤ 8759016085209^4311*100000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13977853 100000000 8759016085209 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1028413361/2000000000 : ℝ)^5335 ≤ (43905983368693/100000000000000 : ℝ)^4311 := by
    have hnat : (1028413361 : ℕ)^5335*100000000000000^4311 ≤ 43905983368693^4311*2000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028413361 2000000000 43905983368693 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2732108167/5000000000 : ℝ)^5335 ≤ (2366750026557/5000000000000 : ℝ)^4311 := by
    have hnat : (2732108167 : ℕ)^5335*5000000000000^4311 ≤ 2366750026557^4311*5000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2732108167 5000000000 2366750026557 5000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5335/1024 : ℝ)) 5335 4311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-13977853/100000000 : ℝ), (1028413361/2000000000 : ℝ), (2732108167/5000000000 : ℝ)] ![(8759016085209/100000000000000 : ℝ), (43905983368693/100000000000000 : ℝ), (2366750026557/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-13977853/100000000 : ℝ)|^5335 ≤ (8759016085209/100000000000000 : ℝ)^4311
        have hw : |(-13977853/100000000 : ℝ)|=(13977853/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1028413361/2000000000 : ℝ)|^5335 ≤ (43905983368693/100000000000000 : ℝ)^4311
        have hw : |(1028413361/2000000000 : ℝ)|=(1028413361/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2732108167/5000000000 : ℝ)|^5335 ≤ (2366750026557/5000000000000 : ℝ)^4311
        have hw : |(2732108167/5000000000 : ℝ)|=(2732108167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1714_s2_5 (p : ℝ) (hpa : (5327/1024 : ℝ) ≤ p) (hpb : p ≤ (5335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5254082757/10000000000 : ℝ)*x 0 + (-621326581/5000000000 : ℝ)*x 1 + (5464216331/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5254082757/10000000000 : ℝ)^5335 ≤ (45092676118837/100000000000000 : ℝ)^4311 := by
    have hnat : (5254082757 : ℕ)^5335*100000000000000^4311 ≤ 45092676118837^4311*10000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254082757 10000000000 45092676118837 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (621326581/5000000000 : ℝ)^5335 ≤ (7572323364941/100000000000000 : ℝ)^4311 := by
    have hnat : (621326581 : ℕ)^5335*100000000000000^4311 ≤ 7572323364941^4311*5000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      621326581 5000000000 7572323364941 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5464216331/10000000000 : ℝ)^5335 ≤ (47335000498979/100000000000000 : ℝ)^4311 := by
    have hnat : (5464216331 : ℕ)^5335*100000000000000^4311 ≤ 47335000498979^4311*10000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5464216331 10000000000 47335000498979 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5335/1024 : ℝ)) 5335 4311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5254082757/10000000000 : ℝ), (-621326581/5000000000 : ℝ), (5464216331/10000000000 : ℝ)] ![(45092676118837/100000000000000 : ℝ), (7572323364941/100000000000000 : ℝ), (47335000498979/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5254082757/10000000000 : ℝ)|^5335 ≤ (45092676118837/100000000000000 : ℝ)^4311
        have hw : |(5254082757/10000000000 : ℝ)|=(5254082757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-621326581/5000000000 : ℝ)|^5335 ≤ (7572323364941/100000000000000 : ℝ)^4311
        have hw : |(-621326581/5000000000 : ℝ)|=(621326581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5464216331/10000000000 : ℝ)|^5335 ≤ (47335000498979/100000000000000 : ℝ)^4311
        have hw : |(5464216331/10000000000 : ℝ)|=(5464216331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1714_s2_6 (p : ℝ) (hpa : (5327/1024 : ℝ) ≤ p) (hpb : p ≤ (5335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1050816551/2000000000 : ℝ)*x 0 + (1092843267/2000000000 : ℝ)*x 1 + (-31066329/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050816551/2000000000 : ℝ)^5335 ≤ (9018535219519/20000000000000 : ℝ)^4311 := by
    have hnat : (1050816551 : ℕ)^5335*20000000000000^4311 ≤ 9018535219519^4311*2000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050816551 2000000000 9018535219519 20000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1092843267/2000000000 : ℝ)^5335 ≤ (47335000541861/100000000000000 : ℝ)^4311 := by
    have hnat : (1092843267 : ℕ)^5335*100000000000000^4311 ≤ 47335000541861^4311*2000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092843267 2000000000 47335000541861 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (31066329/250000000 : ℝ)^5335 ≤ (7572323349859/100000000000000 : ℝ)^4311 := by
    have hnat : (31066329 : ℕ)^5335*100000000000000^4311 ≤ 7572323349859^4311*250000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31066329 250000000 7572323349859 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5335/1024 : ℝ)) 5335 4311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050816551/2000000000 : ℝ), (1092843267/2000000000 : ℝ), (-31066329/250000000 : ℝ)] ![(9018535219519/20000000000000 : ℝ), (47335000541861/100000000000000 : ℝ), (7572323349859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050816551/2000000000 : ℝ)|^5335 ≤ (9018535219519/20000000000000 : ℝ)^4311
        have hw : |(1050816551/2000000000 : ℝ)|=(1050816551/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1092843267/2000000000 : ℝ)|^5335 ≤ (47335000541861/100000000000000 : ℝ)^4311
        have hw : |(1092843267/2000000000 : ℝ)|=(1092843267/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-31066329/250000000 : ℝ)|^5335 ≤ (7572323349859/100000000000000 : ℝ)^4311
        have hw : |(-31066329/250000000 : ℝ)|=(31066329/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1714_s2_7 (p : ℝ) (hpa : (5327/1024 : ℝ) ≤ p) (hpb : p ≤ (5335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2049979543/5000000000 : ℝ)*x 0 + (229430101/500000000 : ℝ)*x 1 + (182304441/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2049979543/5000000000 : ℝ)^5335 ≤ (33174341352613/100000000000000 : ℝ)^4311 := by
    have hnat : (2049979543 : ℕ)^5335*100000000000000^4311 ≤ 33174341352613^4311*5000000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2049979543 5000000000 33174341352613 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (229430101/500000000 : ℝ)^5335 ≤ (38134556003171/100000000000000 : ℝ)^4311 := by
    have hnat : (229430101 : ℕ)^5335*100000000000000^4311 ≤ 38134556003171^4311*500000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      229430101 500000000 38134556003171 100000000000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (182304441/500000000 : ℝ)^5335 ≤ (448298478499/1562500000000 : ℝ)^4311 := by
    have hnat : (182304441 : ℕ)^5335*1562500000000^4311 ≤ 448298478499^4311*500000000^5335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      182304441 500000000 448298478499 1562500000000 5335 4311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5335/1024 : ℝ)) 5335 4311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2049979543/5000000000 : ℝ), (229430101/500000000 : ℝ), (182304441/500000000 : ℝ)] ![(33174341352613/100000000000000 : ℝ), (38134556003171/100000000000000 : ℝ), (448298478499/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2049979543/5000000000 : ℝ)|^5335 ≤ (33174341352613/100000000000000 : ℝ)^4311
        have hw : |(2049979543/5000000000 : ℝ)|=(2049979543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(229430101/500000000 : ℝ)|^5335 ≤ (38134556003171/100000000000000 : ℝ)^4311
        have hw : |(229430101/500000000 : ℝ)|=(229430101/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(182304441/500000000 : ℝ)|^5335 ≤ (448298478499/1562500000000 : ℝ)^4311
        have hw : |(182304441/500000000 : ℝ)|=(182304441/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1714_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5327/1024 : ℝ) ≤ p) (hpb : p ≤ (5335/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (196285051/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17351/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9793/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10033/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8537/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17351/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9793/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17351/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9793/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17351/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9793/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17351/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9793/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17351/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9793/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17351/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9793/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9793/100000 : ℝ) ^ (5327/1024 : ℝ) ≤ (563110945437777/100000000000000000000 : ℝ) := by
    have hpowers : (9793/100000 : ℝ)^5327 ≤ (563110945437777/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9793 : ℕ)^5327*100000000000000000000^1024 ≤ 563110945437777^1024*100000^5327 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9793 100000 563110945437777 100000000000000000000 5327 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9793/100000 : ℝ)) (X := (563110945437777/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5327 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17351/100000 : ℝ) ^ (5327/1024 : ℝ) ≤ (5518527251069611/50000000000000000000 : ℝ) := by
    have hpowers : (17351/100000 : ℝ)^5327 ≤ (5518527251069611/50000000000000000000 : ℝ)^1024 := by
      have hnat : (17351 : ℕ)^5327*50000000000000000000^1024 ≤ 5518527251069611^1024*100000^5327 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17351 100000 5518527251069611 50000000000000000000 5327 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17351/100000 : ℝ)) (X := (5518527251069611/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5327 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000563110945437777/50000000000000000000 : ℝ) ≤ (10000021649070219/10000000000000000 : ℝ) ^ (5327/1024 : ℝ) := by
    have hpowers : (50000563110945437777/50000000000000000000 : ℝ)^1024 ≤ (10000021649070219/10000000000000000 : ℝ)^5327 := by
      have hnat : (50000563110945437777 : ℕ)^1024*10000000000000000^5327 ≤ 10000021649070219^5327*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000563110945437777 50000000000000000000 10000021649070219 10000000000000000 1024 5327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000021649070219/10000000000000000 : ℝ)) (X := (50000563110945437777/50000000000000000000 : ℝ)) (by norm_num) 5327 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100011600165447576999/100000000000000000000 : ℝ) ≤ (10000222977528239/10000000000000000 : ℝ) ^ (5327/1024 : ℝ) := by
    have hpowers : (100011600165447576999/100000000000000000000 : ℝ)^1024 ≤ (10000222977528239/10000000000000000 : ℝ)^5327 := by
      have hnat : (100011600165447576999 : ℕ)^1024*10000000000000000^5327 ≤ 10000222977528239^5327*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100011600165447576999 100000000000000000000 10000222977528239 10000000000000000 1024 5327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000222977528239/10000000000000000 : ℝ)) (X := (100011600165447576999/100000000000000000000 : ℝ)) (by norm_num) 5327 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25005518527251069611/25000000000000000000 : ℝ) ≤ (10000424305986259/10000000000000000 : ℝ) ^ (5327/1024 : ℝ) := by
    have hpowers : (25005518527251069611/25000000000000000000 : ℝ)^1024 ≤ (10000424305986259/10000000000000000 : ℝ)^5327 := by
      have hnat : (25005518527251069611 : ℕ)^1024*10000000000000000^5327 ≤ 10000424305986259^5327*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005518527251069611 25000000000000000000 10000424305986259 10000000000000000 1024 5327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000424305986259/10000000000000000 : ℝ)) (X := (25005518527251069611/25000000000000000000 : ℝ)) (by norm_num) 5327 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(563110945437777/100000000000000000000 : ℝ) ≤ ((37788110202246967741/37790000000000000000 : ℝ)+2*(10066422901/37790000000000 : ℝ)*(9793/100000 : ℝ))^(5327/1024 : ℝ) := by
    rw [show (37788110202246967741/37790000000000000000 : ℝ)+2*(10066422901/37790000000000 : ℝ)*(9793/100000 : ℝ)=(10000021649070219/10000000000000000 : ℝ) by norm_num, show 1+2*(563110945437777/100000000000000000000 : ℝ)=(50000563110945437777/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5518527251069611/50000000000000000000 : ℝ)+(563110945437777/100000000000000000000 : ℝ) ≤ ((37788110202246967741/37790000000000000000 : ℝ)+(10066422901/37790000000000 : ℝ)*((17351/100000 : ℝ)+(9793/100000 : ℝ)))^(5327/1024 : ℝ) := by
    rw [show (37788110202246967741/37790000000000000000 : ℝ)+(10066422901/37790000000000 : ℝ)*((17351/100000 : ℝ)+(9793/100000 : ℝ))=(10000222977528239/10000000000000000 : ℝ) by norm_num, show 1+(5518527251069611/50000000000000000000 : ℝ)+(563110945437777/100000000000000000000 : ℝ)=(100011600165447576999/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5518527251069611/50000000000000000000 : ℝ) ≤ ((37788110202246967741/37790000000000000000 : ℝ)+2*(10066422901/37790000000000 : ℝ)*(17351/100000 : ℝ))^(5327/1024 : ℝ) := by
    rw [show (37788110202246967741/37790000000000000000 : ℝ)+2*(10066422901/37790000000000 : ℝ)*(17351/100000 : ℝ)=(10000424305986259/10000000000000000 : ℝ) by norm_num, show 1+2*(5518527251069611/50000000000000000000 : ℝ)=(25005518527251069611/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (37788110202246967741/37790000000000000000 : ℝ)*(X 1 0+X 2 0)+(10066422901/37790000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5327/1024 : ℝ)) (lo := (9793/100000 : ℝ)) (hi := (17351/100000 : ℝ)) (c := (37788110202246967741/37790000000000000000 : ℝ)) (alpha := (10066422901/37790000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (37788110202246967741/37790000000000000000 : ℝ)*(X 0 1+X 2 1)+(10066422901/37790000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5327/1024 : ℝ)) (lo := (9793/100000 : ℝ)) (hi := (17351/100000 : ℝ)) (c := (37788110202246967741/37790000000000000000 : ℝ)) (alpha := (10066422901/37790000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (37788110202246967741/37790000000000000000 : ℝ)*(X 0 2+X 1 2)+(10066422901/37790000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5327/1024 : ℝ)) (lo := (9793/100000 : ℝ)) (hi := (17351/100000 : ℝ)) (c := (37788110202246967741/37790000000000000000 : ℝ)) (alpha := (10066422901/37790000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-349408893/2500000000 : ℝ)*X 0 0+(5467943227/10000000000 : ℝ)*X 0 1+(5138394993/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1714_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1335575003/2500000000 : ℝ)*X 1 0+(-1568475179/10000000000 : ℝ)*X 1 1+(5138395453/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1714_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((667787643/1250000000 : ℝ)*X 2 0+(1027679039/2000000000 : ℝ)*X 2 1+(-784237003/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1714_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2049760759/5000000000 : ℝ)*X 0 0+(727037367/2000000000 : ℝ)*X 0 1+(4599343939/10000000000 : ℝ)*X 0 2+(2049760759/5000000000 : ℝ)*X 1 0+(727037367/2000000000 : ℝ)*X 1 1+(4599343939/10000000000 : ℝ)*X 1 2+(2049760759/5000000000 : ℝ)*X 2 0+(727037367/2000000000 : ℝ)*X 2 1+(4599343939/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1714_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-13977853/100000000 : ℝ)*X 0 0+(1028413361/2000000000 : ℝ)*X 0 1+(2732108167/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1714_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5254082757/10000000000 : ℝ)*X 1 0+(-621326581/5000000000 : ℝ)*X 1 1+(5464216331/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1714_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1050816551/2000000000 : ℝ)*X 2 0+(1092843267/2000000000 : ℝ)*X 2 1+(-31066329/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1714_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2049979543/5000000000 : ℝ)*X 0 0+(229430101/500000000 : ℝ)*X 0 1+(182304441/500000000 : ℝ)*X 0 2+(2049979543/5000000000 : ℝ)*X 1 0+(229430101/500000000 : ℝ)*X 1 1+(182304441/500000000 : ℝ)*X 1 2+(2049979543/5000000000 : ℝ)*X 2 0+(229430101/500000000 : ℝ)*X 2 1+(182304441/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1714_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13941755408776442122971/944750000000000000000000000 : ℝ) := by norm_num
    linear_combination (1219098787/100000000000000 : ℝ)*(base19) + (842861267/50000000000000 : ℝ)*(base23) + (30036063/25000000000000 : ℝ)*(lower2) + (30094791/6250000000000 : ℝ)*(upper5) + (1017920120594827/50000000000000 : ℝ)*(major0) + (1017920120594827/50000000000000 : ℝ)*(major1) + (1017920120594827/50000000000000 : ℝ)*(major2) + (758617249793893/25000000000000 : ℝ)*(sp0) + (379311281810803/12500000000000 : ℝ)*(sp1) + (1517246363262933/50000000000000 : ℝ)*(sp2) + (1037181192511827/100000000000000 : ℝ)*(sp3) + (6353268207/25000000000000 : ℝ)*(sp4) + (734665797/25000000000000 : ℝ)*(sp5) + (877143253/20000000000000 : ℝ)*(sp7) + (259296394557023/25000000000000 : ℝ)*(f.failure) + (7586236030621/250000000000 : ℝ)*(f.sum) + (463641951683/188950000000000000000000000 : ℝ)*base66 + (208839475431975807/1889500000000000000000000000000000 : ℝ)*base67 + (13686598645062024193/1889500000000000000000000000000000 : ℝ)*base70 + (5539086320282524193/1889500000000000000000000000000000 : ℝ)*base72 + (9213534291461/3779000000000000000000000000 : ℝ)*base73 + (18570813558533975807/1889500000000000000000000000000000 : ℝ)*base75 + (10049141995132524193/1889500000000000000000000000000000 : ℝ)*base78 + (1172317281134975807/1889500000000000000000000000000000 : ℝ)*base79 + (378515397259/755800000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (31963173/2500000000000000000000 : ℝ)*base89 + (31963173/2500000000000000000000 : ℝ)*base91 + (31963173/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4191419414922125697908763921/472375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (121788481/10000000000000 : ℝ)*(base19) + (655357649/50000000000000 : ℝ)*(base23) + (189609521/100000000000000 : ℝ)*(upper3) + (1311743/3125000000000 : ℝ)*(lower4) + (23187279/12500000000000 : ℝ)*(upper5) + (1041285305920327/50000000000000 : ℝ)*(major0) + (1041285305920327/50000000000000 : ℝ)*(major1) + (1041285305920327/50000000000000 : ℝ)*(major2) + (11106269167/100000000000000 : ℝ)*(sp1) + (5973551481/50000000000000 : ℝ)*(sp2) + (194009246746377/6250000000000 : ℝ)*(sp4) + (388016952973507/12500000000000 : ℝ)*(sp5) + (776033672530943/25000000000000 : ℝ)*(sp6) + (1060992979970061/100000000000000 : ℝ)*(sp7) + (1060992979970061/100000000000000 : ℝ)*(f.failure) + (194009246746377/6250000000000 : ℝ)*(f.sum) + (1917637866363/1889500000000000000000000000 : ℝ)*base66 + (9582016016997828693/1889500000000000000000000000000000 : ℝ)*base68 + (11180759025946171307/1889500000000000000000000000000000 : ℝ)*base69 + (16059096671346828693/1889500000000000000000000000000000 : ℝ)*base72 + (9436470265137/3779000000000000000000000000 : ℝ)*base74 + (11956715482414328693/1889500000000000000000000000000000 : ℝ)*base76 + (1826740226230828693/1889500000000000000000000000000000 : ℝ)*base78 + (12291248099772828693/1889500000000000000000000000000000 : ℝ)*base80 + (4375146903849/944750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1858111/10000000000000000000000 : ℝ)*base89 + (1858111/10000000000000000000000 : ℝ)*base91 + (1858111/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1714_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5327/1024 : ℝ) ≤ p) (hpb : p ≤ (5335/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (196285051/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17351/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9793/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10033/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8537/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1714_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1714_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5327/1024 : ℝ) ≤ p) (hpb : p ≤ (5335/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (196285051/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10033/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8537/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1714_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1714_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1714_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5327/1024 : ℝ) ≤ p) (hpb : p ≤ (5335/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (196285051/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10033/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8537/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1714_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
