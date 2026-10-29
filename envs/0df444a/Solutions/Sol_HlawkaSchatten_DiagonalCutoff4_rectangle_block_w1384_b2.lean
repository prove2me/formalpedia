-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1384_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:24:14.329991+00:00
-- url     : https://prove2.me/submissions/a336858c-be93-431d-9e9e-b1fa9977c179

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
theorem support_rectangle_w1384_s6_0 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2008234027/10000000000 : ℝ)*x 0 + (270527311/500000000 : ℝ)*x 1 + (5245803561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2008234027/10000000000 : ℝ)^543 ≤ (12239924489607/100000000000000 : ℝ)^415 := by
    have hnat : (2008234027 : ℕ)^543*100000000000000^415 ≤ 12239924489607^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2008234027 10000000000 12239924489607 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (270527311/500000000 : ℝ)^543 ≤ (44767585429013/100000000000000 : ℝ)^415 := by
    have hnat : (270527311 : ℕ)^543*100000000000000^415 ≤ 44767585429013^415*500000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270527311 500000000 44767585429013 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245803561/10000000000 : ℝ)^543 ≤ (42992490060711/100000000000000 : ℝ)^415 := by
    have hnat : (5245803561 : ℕ)^543*100000000000000^415 ≤ 42992490060711^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245803561 10000000000 42992490060711 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2008234027/10000000000 : ℝ), (270527311/500000000 : ℝ), (5245803561/10000000000 : ℝ)] ![(12239924489607/100000000000000 : ℝ), (44767585429013/100000000000000 : ℝ), (42992490060711/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2008234027/10000000000 : ℝ)|^543 ≤ (12239924489607/100000000000000 : ℝ)^415
        have hw : |(-2008234027/10000000000 : ℝ)|=(2008234027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(270527311/500000000 : ℝ)|^543 ≤ (44767585429013/100000000000000 : ℝ)^415
        have hw : |(270527311/500000000 : ℝ)|=(270527311/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245803561/10000000000 : ℝ)|^543 ≤ (42992490060711/100000000000000 : ℝ)^415
        have hw : |(5245803561/10000000000 : ℝ)|=(5245803561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_s6_1 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5348234449/10000000000 : ℝ)*x 0 + (-523034917/2500000000 : ℝ)*x 1 + (5245803561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348234449/10000000000 : ℝ)^543 ≤ (5511773723419/12500000000000 : ℝ)^415 := by
    have hnat : (5348234449 : ℕ)^543*12500000000000^415 ≤ 5511773723419^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348234449 10000000000 5511773723419 12500000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (523034917/2500000000 : ℝ)^543 ≤ (1291332014187/10000000000000 : ℝ)^415 := by
    have hnat : (523034917 : ℕ)^543*10000000000000^415 ≤ 1291332014187^415*2500000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523034917 2500000000 1291332014187 10000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245803561/10000000000 : ℝ)^543 ≤ (42992490060711/100000000000000 : ℝ)^415 := by
    have hnat : (5245803561 : ℕ)^543*100000000000000^415 ≤ 42992490060711^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245803561 10000000000 42992490060711 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348234449/10000000000 : ℝ), (-523034917/2500000000 : ℝ), (5245803561/10000000000 : ℝ)] ![(5511773723419/12500000000000 : ℝ), (1291332014187/10000000000000 : ℝ), (42992490060711/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348234449/10000000000 : ℝ)|^543 ≤ (5511773723419/12500000000000 : ℝ)^415
        have hw : |(5348234449/10000000000 : ℝ)|=(5348234449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-523034917/2500000000 : ℝ)|^543 ≤ (1291332014187/10000000000000 : ℝ)^415
        have hw : |(-523034917/2500000000 : ℝ)|=(523034917/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245803561/10000000000 : ℝ)|^543 ≤ (42992490060711/100000000000000 : ℝ)^415
        have hw : |(5245803561/10000000000 : ℝ)|=(5245803561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_s6_2 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5348234451/10000000000 : ℝ)*x 0 + (131145089/250000000 : ℝ)*x 1 + (-2092139667/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348234451/10000000000 : ℝ)^543 ≤ (44094189808927/100000000000000 : ℝ)^415 := by
    have hnat : (5348234451 : ℕ)^543*100000000000000^415 ≤ 44094189808927^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348234451 10000000000 44094189808927 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131145089/250000000 : ℝ)^543 ≤ (42992490049987/100000000000000 : ℝ)^415 := by
    have hnat : (131145089 : ℕ)^543*100000000000000^415 ≤ 42992490049987^415*250000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131145089 250000000 42992490049987 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2092139667/10000000000 : ℝ)^543 ≤ (6456660066897/50000000000000 : ℝ)^415 := by
    have hnat : (2092139667 : ℕ)^543*50000000000000^415 ≤ 6456660066897^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2092139667 10000000000 6456660066897 50000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348234451/10000000000 : ℝ), (131145089/250000000 : ℝ), (-2092139667/10000000000 : ℝ)] ![(44094189808927/100000000000000 : ℝ), (42992490049987/100000000000000 : ℝ), (6456660066897/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348234451/10000000000 : ℝ)|^543 ≤ (44094189808927/100000000000000 : ℝ)^415
        have hw : |(5348234451/10000000000 : ℝ)|=(5348234451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(131145089/250000000 : ℝ)|^543 ≤ (42992490049987/100000000000000 : ℝ)^415
        have hw : |(131145089/250000000 : ℝ)|=(131145089/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2092139667/10000000000 : ℝ)|^543 ≤ (6456660066897/50000000000000 : ℝ)^415
        have hw : |(-2092139667/10000000000 : ℝ)|=(2092139667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_s6_3 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (539469399/1250000000 : ℝ)*x 0 + (103593919/250000000 : ℝ)*x 1 + (449428277/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (539469399/1250000000 : ℝ)^543 ≤ (33303970100457/100000000000000 : ℝ)^415 := by
    have hnat : (539469399 : ℕ)^543*100000000000000^415 ≤ 33303970100457^415*1250000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539469399 1250000000 33303970100457 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (103593919/250000000 : ℝ)^543 ≤ (7894520262239/25000000000000 : ℝ)^415 := by
    have hnat : (103593919 : ℕ)^543*25000000000000^415 ≤ 7894520262239^415*250000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103593919 250000000 7894520262239 25000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (449428277/1000000000 : ℝ)^543 ≤ (17558974415859/50000000000000 : ℝ)^415 := by
    have hnat : (449428277 : ℕ)^543*50000000000000^415 ≤ 17558974415859^415*1000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449428277 1000000000 17558974415859 50000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(539469399/1250000000 : ℝ), (103593919/250000000 : ℝ), (449428277/1000000000 : ℝ)] ![(33303970100457/100000000000000 : ℝ), (7894520262239/25000000000000 : ℝ), (17558974415859/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(539469399/1250000000 : ℝ)|^543 ≤ (33303970100457/100000000000000 : ℝ)^415
        have hw : |(539469399/1250000000 : ℝ)|=(539469399/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(103593919/250000000 : ℝ)|^543 ≤ (7894520262239/25000000000000 : ℝ)^415
        have hw : |(103593919/250000000 : ℝ)|=(103593919/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(449428277/1000000000 : ℝ)|^543 ≤ (17558974415859/50000000000000 : ℝ)^415
        have hw : |(449428277/1000000000 : ℝ)|=(449428277/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_s6_4 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2008245763/10000000000 : ℝ)*x 0 + (104927909/200000000 : ℝ)*x 1 + (1352487821/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2008245763/10000000000 : ℝ)^543 ≤ (12240018081157/100000000000000 : ℝ)^415 := by
    have hnat : (2008245763 : ℕ)^543*100000000000000^415 ≤ 12240018081157^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2008245763 10000000000 12240018081157 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (104927909/200000000 : ℝ)^543 ≤ (2687427326923/6250000000000 : ℝ)^415 := by
    have hnat : (104927909 : ℕ)^543*6250000000000^415 ≤ 2687427326923^415*200000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104927909 200000000 2687427326923 6250000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1352487821/2500000000 : ℝ)^543 ≤ (11190286167029/25000000000000 : ℝ)^415 := by
    have hnat : (1352487821 : ℕ)^543*25000000000000^415 ≤ 11190286167029^415*2500000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352487821 2500000000 11190286167029 25000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2008245763/10000000000 : ℝ), (104927909/200000000 : ℝ), (1352487821/2500000000 : ℝ)] ![(12240018081157/100000000000000 : ℝ), (2687427326923/6250000000000 : ℝ), (11190286167029/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2008245763/10000000000 : ℝ)|^543 ≤ (12240018081157/100000000000000 : ℝ)^415
        have hw : |(-2008245763/10000000000 : ℝ)|=(2008245763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(104927909/200000000 : ℝ)|^543 ≤ (2687427326923/6250000000000 : ℝ)^415
        have hw : |(104927909/200000000 : ℝ)|=(104927909/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1352487821/2500000000 : ℝ)|^543 ≤ (11190286167029/25000000000000 : ℝ)^415
        have hw : |(1352487821/2500000000 : ℝ)|=(1352487821/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_s6_5 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5305602359/10000000000 : ℝ)*x 0 + (-1927991911/10000000000 : ℝ)*x 1 + (2704975627/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305602359/10000000000 : ℝ)^543 ≤ (43634860545363/100000000000000 : ℝ)^415 := by
    have hnat : (5305602359 : ℕ)^543*100000000000000^415 ≤ 43634860545363^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305602359 10000000000 43634860545363 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1927991911/10000000000 : ℝ)^543 ≤ (2900998773467/25000000000000 : ℝ)^415 := by
    have hnat : (1927991911 : ℕ)^543*25000000000000^415 ≤ 2900998773467^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1927991911 10000000000 2900998773467 25000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2704975627/5000000000 : ℝ)^543 ≤ (44761144343343/100000000000000 : ℝ)^415 := by
    have hnat : (2704975627 : ℕ)^543*100000000000000^415 ≤ 44761144343343^415*5000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704975627 5000000000 44761144343343 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305602359/10000000000 : ℝ), (-1927991911/10000000000 : ℝ), (2704975627/5000000000 : ℝ)] ![(43634860545363/100000000000000 : ℝ), (2900998773467/25000000000000 : ℝ), (44761144343343/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305602359/10000000000 : ℝ)|^543 ≤ (43634860545363/100000000000000 : ℝ)^415
        have hw : |(5305602359/10000000000 : ℝ)|=(5305602359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1927991911/10000000000 : ℝ)|^543 ≤ (2900998773467/25000000000000 : ℝ)^415
        have hw : |(-1927991911/10000000000 : ℝ)|=(1927991911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2704975627/5000000000 : ℝ)|^543 ≤ (44761144343343/100000000000000 : ℝ)^415
        have hw : |(2704975627/5000000000 : ℝ)|=(2704975627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_s6_6 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2652801163/5000000000 : ℝ)*x 0 + (5409951277/10000000000 : ℝ)*x 1 + (-77119677/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652801163/5000000000 : ℝ)^543 ≤ (10908715047563/25000000000000 : ℝ)^415 := by
    have hnat : (2652801163 : ℕ)^543*25000000000000^415 ≤ 10908715047563^415*5000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652801163 5000000000 10908715047563 25000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5409951277/10000000000 : ℝ)^543 ≤ (2797571537021/6250000000000 : ℝ)^415 := by
    have hnat : (5409951277 : ℕ)^543*6250000000000^415 ≤ 2797571537021^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409951277 10000000000 2797571537021 6250000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (77119677/400000000 : ℝ)^543 ≤ (11603995204119/100000000000000 : ℝ)^415 := by
    have hnat : (77119677 : ℕ)^543*100000000000000^415 ≤ 11603995204119^415*400000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      77119677 400000000 11603995204119 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652801163/5000000000 : ℝ), (5409951277/10000000000 : ℝ), (-77119677/400000000 : ℝ)] ![(10908715047563/25000000000000 : ℝ), (2797571537021/6250000000000 : ℝ), (11603995204119/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652801163/5000000000 : ℝ)|^543 ≤ (10908715047563/25000000000000 : ℝ)^415
        have hw : |(2652801163/5000000000 : ℝ)|=(2652801163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5409951277/10000000000 : ℝ)|^543 ≤ (2797571537021/6250000000000 : ℝ)^415
        have hw : |(5409951277/10000000000 : ℝ)|=(5409951277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-77119677/400000000 : ℝ)|^543 ≤ (11603995204119/100000000000000 : ℝ)^415
        have hw : |(-77119677/400000000 : ℝ)|=(77119677/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_s6_7 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4315780193/10000000000 : ℝ)*x 0 + (2246511691/5000000000 : ℝ)*x 1 + (4145022657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4315780193/10000000000 : ℝ)^543 ≤ (6660844506991/20000000000000 : ℝ)^415 := by
    have hnat : (4315780193 : ℕ)^543*20000000000000^415 ≤ 6660844506991^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4315780193 10000000000 6660844506991 20000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2246511691/5000000000 : ℝ)^543 ≤ (7021014683189/20000000000000 : ℝ)^415 := by
    have hnat : (2246511691 : ℕ)^543*20000000000000^415 ≤ 7021014683189^415*5000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246511691 5000000000 7021014683189 20000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4145022657/10000000000 : ℝ)^543 ≤ (31590704033287/100000000000000 : ℝ)^415 := by
    have hnat : (4145022657 : ℕ)^543*100000000000000^415 ≤ 31590704033287^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4145022657 10000000000 31590704033287 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4315780193/10000000000 : ℝ), (2246511691/5000000000 : ℝ), (4145022657/10000000000 : ℝ)] ![(6660844506991/20000000000000 : ℝ), (7021014683189/20000000000000 : ℝ), (31590704033287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4315780193/10000000000 : ℝ)|^543 ≤ (6660844506991/20000000000000 : ℝ)^415
        have hw : |(4315780193/10000000000 : ℝ)|=(4315780193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2246511691/5000000000 : ℝ)|^543 ≤ (7021014683189/20000000000000 : ℝ)^415
        have hw : |(2246511691/5000000000 : ℝ)|=(2246511691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4145022657/10000000000 : ℝ)|^543 ≤ (31590704033287/100000000000000 : ℝ)^415
        have hw : |(4145022657/10000000000 : ℝ)|=(4145022657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1384_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78192963/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7369/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11239/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2811/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14733/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7369/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11239/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7369/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11239/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7369/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11239/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7369/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11239/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7369/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11239/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7369/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11239/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11239/100000 : ℝ) ^ (4343/1024 : ℝ) ≤ (588594004273457/6250000000000000000 : ℝ) := by
    have hpowers : (11239/100000 : ℝ)^4343 ≤ (588594004273457/6250000000000000000 : ℝ)^1024 := by
      have hnat : (11239 : ℕ)^4343*6250000000000000000^1024 ≤ 588594004273457^1024*100000^4343 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11239 100000 588594004273457 6250000000000000000 4343 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11239/100000 : ℝ)) (X := (588594004273457/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4343 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7369/50000 : ℝ) ^ (4343/1024 : ℝ) ≤ (29728465473350261/100000000000000000000 : ℝ) := by
    have hpowers : (7369/50000 : ℝ)^4343 ≤ (29728465473350261/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7369 : ℕ)^4343*100000000000000000000^1024 ≤ 29728465473350261^1024*50000^4343 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7369 50000 29728465473350261 100000000000000000000 4343 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7369/50000 : ℝ)) (X := (29728465473350261/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4343 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125588594004273457/3125000000000000000 : ℝ) ≤ (10000444063099041/10000000000000000 : ℝ) ^ (4343/1024 : ℝ) := by
    have hpowers : (3125588594004273457/3125000000000000000 : ℝ)^1024 ≤ (10000444063099041/10000000000000000 : ℝ)^4343 := by
      have hnat : (3125588594004273457 : ℕ)^1024*10000000000000000^4343 ≤ 10000444063099041^4343*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125588594004273457 3125000000000000000 10000444063099041 10000000000000000 1024 4343 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000444063099041/10000000000000000 : ℝ)) (X := (3125588594004273457/3125000000000000000 : ℝ)) (by norm_num) 4343 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100039145969541725573/100000000000000000000 : ℝ) ≤ (10000922852364553/10000000000000000 : ℝ) ^ (4343/1024 : ℝ) := by
    have hpowers : (100039145969541725573/100000000000000000000 : ℝ)^1024 ≤ (10000922852364553/10000000000000000 : ℝ)^4343 := by
      have hnat : (100039145969541725573 : ℕ)^1024*10000000000000000^4343 ≤ 10000922852364553^4343*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100039145969541725573 100000000000000000000 10000922852364553 10000000000000000 1024 4343 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000922852364553/10000000000000000 : ℝ)) (X := (100039145969541725573/100000000000000000000 : ℝ)) (by norm_num) 4343 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50029728465473350261/50000000000000000000 : ℝ) ≤ (2000280328326013/2000000000000000 : ℝ) ^ (4343/1024 : ℝ) := by
    have hpowers : (50029728465473350261/50000000000000000000 : ℝ)^1024 ≤ (2000280328326013/2000000000000000 : ℝ)^4343 := by
      have hnat : (50029728465473350261 : ℕ)^1024*2000000000000000^4343 ≤ 2000280328326013^4343*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50029728465473350261 50000000000000000000 2000280328326013 2000000000000000 1024 4343 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000280328326013/2000000000000000 : ℝ)) (X := (50029728465473350261/50000000000000000000 : ℝ)) (by norm_num) 4343 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(588594004273457/6250000000000000000 : ℝ) ≤ ((34980791551673365723/34990000000000000000 : ℝ)+2*(59848658189/43737500000000 : ℝ)*(11239/100000 : ℝ))^(4343/1024 : ℝ) := by
    rw [show (34980791551673365723/34990000000000000000 : ℝ)+2*(59848658189/43737500000000 : ℝ)*(11239/100000 : ℝ)=(10000444063099041/10000000000000000 : ℝ) by norm_num, show 1+2*(588594004273457/6250000000000000000 : ℝ)=(3125588594004273457/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(29728465473350261/100000000000000000000 : ℝ)+(588594004273457/6250000000000000000 : ℝ) ≤ ((34980791551673365723/34990000000000000000 : ℝ)+(59848658189/43737500000000 : ℝ)*((7369/50000 : ℝ)+(11239/100000 : ℝ)))^(4343/1024 : ℝ) := by
    rw [show (34980791551673365723/34990000000000000000 : ℝ)+(59848658189/43737500000000 : ℝ)*((7369/50000 : ℝ)+(11239/100000 : ℝ))=(10000922852364553/10000000000000000 : ℝ) by norm_num, show 1+(29728465473350261/100000000000000000000 : ℝ)+(588594004273457/6250000000000000000 : ℝ)=(100039145969541725573/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(29728465473350261/100000000000000000000 : ℝ) ≤ ((34980791551673365723/34990000000000000000 : ℝ)+2*(59848658189/43737500000000 : ℝ)*(7369/50000 : ℝ))^(4343/1024 : ℝ) := by
    rw [show (34980791551673365723/34990000000000000000 : ℝ)+2*(59848658189/43737500000000 : ℝ)*(7369/50000 : ℝ)=(2000280328326013/2000000000000000 : ℝ) by norm_num, show 1+2*(29728465473350261/100000000000000000000 : ℝ)=(50029728465473350261/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (34980791551673365723/34990000000000000000 : ℝ)*(X 1 0+X 2 0)+(59848658189/43737500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4343/1024 : ℝ)) (lo := (11239/100000 : ℝ)) (hi := (7369/50000 : ℝ)) (c := (34980791551673365723/34990000000000000000 : ℝ)) (alpha := (59848658189/43737500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (34980791551673365723/34990000000000000000 : ℝ)*(X 0 1+X 2 1)+(59848658189/43737500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4343/1024 : ℝ)) (lo := (11239/100000 : ℝ)) (hi := (7369/50000 : ℝ)) (c := (34980791551673365723/34990000000000000000 : ℝ)) (alpha := (59848658189/43737500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (34980791551673365723/34990000000000000000 : ℝ)*(X 0 2+X 1 2)+(59848658189/43737500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4343/1024 : ℝ)) (lo := (11239/100000 : ℝ)) (hi := (7369/50000 : ℝ)) (c := (34980791551673365723/34990000000000000000 : ℝ)) (alpha := (59848658189/43737500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2008234027/10000000000 : ℝ)*X 0 0+(270527311/500000000 : ℝ)*X 0 1+(5245803561/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348234449/10000000000 : ℝ)*X 1 0+(-523034917/2500000000 : ℝ)*X 1 1+(5245803561/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348234451/10000000000 : ℝ)*X 2 0+(131145089/250000000 : ℝ)*X 2 1+(-2092139667/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((539469399/1250000000 : ℝ)*X 0 0+(103593919/250000000 : ℝ)*X 0 1+(449428277/1000000000 : ℝ)*X 0 2+(539469399/1250000000 : ℝ)*X 1 0+(103593919/250000000 : ℝ)*X 1 1+(449428277/1000000000 : ℝ)*X 1 2+(539469399/1250000000 : ℝ)*X 2 0+(103593919/250000000 : ℝ)*X 2 1+(449428277/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2008245763/10000000000 : ℝ)*X 0 0+(104927909/200000000 : ℝ)*X 0 1+(1352487821/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305602359/10000000000 : ℝ)*X 1 0+(-1927991911/10000000000 : ℝ)*X 1 1+(2704975627/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652801163/5000000000 : ℝ)*X 2 0+(5409951277/10000000000 : ℝ)*X 2 1+(-77119677/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4315780193/10000000000 : ℝ)*X 0 0+(2246511691/5000000000 : ℝ)*X 0 1+(4145022657/10000000000 : ℝ)*X 0 2+(4315780193/10000000000 : ℝ)*X 1 0+(2246511691/5000000000 : ℝ)*X 1 1+(4145022657/10000000000 : ℝ)*X 1 2+(4315780193/10000000000 : ℝ)*X 2 0+(2246511691/5000000000 : ℝ)*X 2 1+(4145022657/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2055643375844116264939134693/218687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1741418509/100000000000000 : ℝ)*(base19) + (812468929/50000000000000 : ℝ)*(base23) + (15877653/25000000000000 : ℝ)*(lower2) + (47191951/20000000000000 : ℝ)*(upper3) + (3016007/2000000000000 : ℝ)*(upper5) + (557689829759099/12500000000000 : ℝ)*(major0) + (557689829759099/12500000000000 : ℝ)*(major1) + (557689829759099/12500000000000 : ℝ)*(major2) + (1214022155434073/20000000000000 : ℝ)*(sp0) + (1517536274366291/25000000000000 : ℝ)*(sp1) + (1214029042789163/20000000000000 : ℝ)*(sp2) + (2852871790945977/100000000000000 : ℝ)*(sp3) + (36061713309/100000000000000 : ℝ)*(sp4) + (18332985503/100000000000000 : ℝ)*(sp7) + (71322253098287/2500000000000 : ℝ)*(f.failure) + (3035073419441837/50000000000000 : ℝ)*(f.sum) + (11225522892791/17495000000000000000000000000 : ℝ)*base66 + (9604399686015236423/437375000000000000000000000000000 : ℝ)*base68 + (8967304506606986423/437375000000000000000000000000000 : ℝ)*base70 + (2599331392417361423/437375000000000000000000000000000 : ℝ)*base72 + (4197635272463/8747500000000000000000000000 : ℝ)*base74 + (5424366025359111423/437375000000000000000000000000000 : ℝ)*base76 + (2926504481613736423/437375000000000000000000000000000 : ℝ)*base78 + (6886239609508986423/437375000000000000000000000000000 : ℝ)*base80 + (26973445002429/4373750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (754381/125000000000000000000 : ℝ)*base89 + (754381/125000000000000000000 : ℝ)*base91 + (754381/125000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2017823569267687546603557927/218687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1676848847/100000000000000 : ℝ)*(base19) + (357246387/20000000000000 : ℝ)*(base23) + (88569277/50000000000000 : ℝ)*(upper3) + (71002101/100000000000000 : ℝ)*(lower4) + (19274633/10000000000000 : ℝ)*(upper5) + (1123459425116683/25000000000000 : ℝ)*(major0) + (1123459425116683/25000000000000 : ℝ)*(major1) + (1123459425116683/25000000000000 : ℝ)*(major2) + (34980746453/100000000000000 : ℝ)*(sp1) + (36671649779/100000000000000 : ℝ)*(sp2) + (6114118747596067/100000000000000 : ℝ)*(sp4) + (6114082090000767/100000000000000 : ℝ)*(sp5) + (3057040144857177/50000000000000 : ℝ)*(sp6) + (1436778172885817/50000000000000 : ℝ)*(sp7) + (1436778172885817/50000000000000 : ℝ)*(f.failure) + (6114118747596067/100000000000000 : ℝ)*(f.sum) + (68391475385489/17495000000000000000000000000 : ℝ)*base65 + (9230450244138243191/874750000000000000000000000000000 : ℝ)*base68 + (2199183701081243191/874750000000000000000000000000000 : ℝ)*base70 + (2282333271805256809/874750000000000000000000000000000 : ℝ)*base71 + (31902489111481/17495000000000000000000000000 : ℝ)*base74 + (15581223725975493191/874750000000000000000000000000000 : ℝ)*base76 + (8333768299573993191/874750000000000000000000000000000 : ℝ)*base78 + (15171969311601243191/874750000000000000000000000000000 : ℝ)*base80 + (108605390466759/17495000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (8094229/2500000000000000000000 : ℝ)*base90 + (8094229/2500000000000000000000 : ℝ)*base92 + (8094229/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1384_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78192963/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7369/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11239/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2811/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14733/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1384_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1384_s7_0 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2008237737/10000000000 : ℝ)*x 0 + (5410507573/10000000000 : ℝ)*x 1 + (262291991/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2008237737/10000000000 : ℝ)^543 ≤ (97919632607/800000000000 : ℝ)^415 := by
    have hnat : (2008237737 : ℕ)^543*800000000000^415 ≤ 97919632607^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2008237737 10000000000 97919632607 800000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5410507573/10000000000 : ℝ)^543 ≤ (44767167031011/100000000000000 : ℝ)^415 := by
    have hnat : (5410507573 : ℕ)^543*100000000000000^415 ≤ 44767167031011^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410507573 10000000000 44767167031011 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262291991/500000000 : ℝ)^543 ≤ (42992878880709/100000000000000 : ℝ)^415 := by
    have hnat : (262291991 : ℕ)^543*100000000000000^415 ≤ 42992878880709^415*500000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262291991 500000000 42992878880709 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2008237737/10000000000 : ℝ), (5410507573/10000000000 : ℝ), (262291991/500000000 : ℝ)] ![(97919632607/800000000000 : ℝ), (44767167031011/100000000000000 : ℝ), (42992878880709/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2008237737/10000000000 : ℝ)|^543 ≤ (97919632607/800000000000 : ℝ)^415
        have hw : |(-2008237737/10000000000 : ℝ)|=(2008237737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5410507573/10000000000 : ℝ)|^543 ≤ (44767167031011/100000000000000 : ℝ)^415
        have hw : |(5410507573/10000000000 : ℝ)|=(5410507573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(262291991/500000000 : ℝ)|^543 ≤ (42992878880709/100000000000000 : ℝ)^415
        have hw : |(262291991/500000000 : ℝ)|=(262291991/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_s7_1 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5348224703/10000000000 : ℝ)*x 0 + (-1046052269/5000000000 : ℝ)*x 1 + (2622919911/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348224703/10000000000 : ℝ)^543 ≤ (22047042325979/50000000000000 : ℝ)^415 := by
    have hnat : (5348224703 : ℕ)^543*50000000000000^415 ≤ 22047042325979^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348224703 10000000000 22047042325979 50000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1046052269/5000000000 : ℝ)^543 ≤ (12913036430983/100000000000000 : ℝ)^415 := by
    have hnat : (1046052269 : ℕ)^543*100000000000000^415 ≤ 12913036430983^415*5000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046052269 5000000000 12913036430983 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622919911/5000000000 : ℝ)^543 ≤ (10748219725539/25000000000000 : ℝ)^415 := by
    have hnat : (2622919911 : ℕ)^543*25000000000000^415 ≤ 10748219725539^415*5000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622919911 5000000000 10748219725539 25000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348224703/10000000000 : ℝ), (-1046052269/5000000000 : ℝ), (2622919911/5000000000 : ℝ)] ![(22047042325979/50000000000000 : ℝ), (12913036430983/100000000000000 : ℝ), (10748219725539/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348224703/10000000000 : ℝ)|^543 ≤ (22047042325979/50000000000000 : ℝ)^415
        have hw : |(5348224703/10000000000 : ℝ)|=(5348224703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1046052269/5000000000 : ℝ)|^543 ≤ (12913036430983/100000000000000 : ℝ)^415
        have hw : |(-1046052269/5000000000 : ℝ)|=(1046052269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622919911/5000000000 : ℝ)|^543 ≤ (10748219725539/25000000000000 : ℝ)^415
        have hw : |(2622919911/5000000000 : ℝ)|=(2622919911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_s7_2 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2674112359/5000000000 : ℝ)*x 0 + (1311459953/2500000000 : ℝ)*x 1 + (-2092104531/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674112359/5000000000 : ℝ)^543 ≤ (44094084813771/100000000000000 : ℝ)^415 := by
    have hnat : (2674112359 : ℕ)^543*100000000000000^415 ≤ 44094084813771^415*5000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674112359 5000000000 44094084813771 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311459953/2500000000 : ℝ)^543 ≤ (21496439397461/50000000000000 : ℝ)^415 := by
    have hnat : (1311459953 : ℕ)^543*50000000000000^415 ≤ 21496439397461^415*2500000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311459953 2500000000 21496439397461 50000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2092104531/10000000000 : ℝ)^543 ≤ (12913036374451/100000000000000 : ℝ)^415 := by
    have hnat : (2092104531 : ℕ)^543*100000000000000^415 ≤ 12913036374451^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2092104531 10000000000 12913036374451 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674112359/5000000000 : ℝ), (1311459953/2500000000 : ℝ), (-2092104531/10000000000 : ℝ)] ![(44094084813771/100000000000000 : ℝ), (21496439397461/50000000000000 : ℝ), (12913036374451/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674112359/5000000000 : ℝ)|^543 ≤ (44094084813771/100000000000000 : ℝ)^415
        have hw : |(2674112359/5000000000 : ℝ)|=(2674112359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311459953/2500000000 : ℝ)|^543 ≤ (21496439397461/50000000000000 : ℝ)^415
        have hw : |(1311459953/2500000000 : ℝ)|=(1311459953/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2092104531/10000000000 : ℝ)|^543 ≤ (12913036374451/100000000000000 : ℝ)^415
        have hw : |(-2092104531/10000000000 : ℝ)|=(2092104531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_s7_3 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (215787891/500000000 : ℝ)*x 0 + (1035959031/2500000000 : ℝ)*x 1 + (2247101387/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215787891/500000000 : ℝ)^543 ≤ (4162999579411/12500000000000 : ℝ)^415 := by
    have hnat : (215787891 : ℕ)^543*12500000000000^415 ≤ 4162999579411^415*500000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215787891 500000000 4162999579411 12500000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1035959031/2500000000 : ℝ)^543 ≤ (7894718099483/25000000000000 : ℝ)^415 := by
    have hnat : (1035959031 : ℕ)^543*25000000000000^415 ≤ 7894718099483^415*2500000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035959031 2500000000 7894718099483 25000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2247101387/5000000000 : ℝ)^543 ≤ (35117130955537/100000000000000 : ℝ)^415 := by
    have hnat : (2247101387 : ℕ)^543*100000000000000^415 ≤ 35117130955537^415*5000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247101387 5000000000 35117130955537 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(215787891/500000000 : ℝ), (1035959031/2500000000 : ℝ), (2247101387/5000000000 : ℝ)] ![(4162999579411/12500000000000 : ℝ), (7894718099483/25000000000000 : ℝ), (35117130955537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(215787891/500000000 : ℝ)|^543 ≤ (4162999579411/12500000000000 : ℝ)^415
        have hw : |(215787891/500000000 : ℝ)|=(215787891/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1035959031/2500000000 : ℝ)|^543 ≤ (7894718099483/25000000000000 : ℝ)^415
        have hw : |(1035959031/2500000000 : ℝ)|=(1035959031/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2247101387/5000000000 : ℝ)|^543 ≤ (35117130955537/100000000000000 : ℝ)^415
        have hw : |(2247101387/5000000000 : ℝ)|=(2247101387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_s7_4 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1004124739/5000000000 : ℝ)*x 0 + (524643117/1000000000 : ℝ)*x 1 + (1081982633/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1004124739/5000000000 : ℝ)^543 ≤ (1530005963419/12500000000000 : ℝ)^415 := by
    have hnat : (1004124739 : ℕ)^543*12500000000000^415 ≤ 1530005963419^415*5000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004124739 5000000000 1530005963419 12500000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524643117/1000000000 : ℝ)^543 ≤ (21499610142087/50000000000000 : ℝ)^415 := by
    have hnat : (524643117 : ℕ)^543*50000000000000^415 ≤ 21499610142087^415*1000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524643117 1000000000 21499610142087 50000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081982633/2000000000 : ℝ)^543 ≤ (4476073200031/10000000000000 : ℝ)^415 := by
    have hnat : (1081982633 : ℕ)^543*10000000000000^415 ≤ 4476073200031^415*2000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081982633 2000000000 4476073200031 10000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1004124739/5000000000 : ℝ), (524643117/1000000000 : ℝ), (1081982633/2000000000 : ℝ)] ![(1530005963419/12500000000000 : ℝ), (21499610142087/50000000000000 : ℝ), (4476073200031/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1004124739/5000000000 : ℝ)|^543 ≤ (1530005963419/12500000000000 : ℝ)^415
        have hw : |(-1004124739/5000000000 : ℝ)|=(1004124739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524643117/1000000000 : ℝ)|^543 ≤ (21499610142087/50000000000000 : ℝ)^415
        have hw : |(524643117/1000000000 : ℝ)|=(524643117/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081982633/2000000000 : ℝ)|^543 ≤ (4476073200031/10000000000000 : ℝ)^415
        have hw : |(1081982633/2000000000 : ℝ)|=(1081982633/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_s7_5 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (663201493/1250000000 : ℝ)*x 0 + (-1928031167/10000000000 : ℝ)*x 1 + (5409913171/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663201493/1250000000 : ℝ)^543 ≤ (43634963689101/100000000000000 : ℝ)^415 := by
    have hnat : (663201493 : ℕ)^543*100000000000000^415 ≤ 43634963689101^415*1250000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663201493 1250000000 43634963689101 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1928031167/10000000000 : ℝ)^543 ≤ (11604304238329/100000000000000 : ℝ)^415 := by
    have hnat : (1928031167 : ℕ)^543*100000000000000^415 ≤ 11604304238329^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1928031167 10000000000 11604304238329 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5409913171/10000000000 : ℝ)^543 ≤ (2797545754079/6250000000000 : ℝ)^415 := by
    have hnat : (5409913171 : ℕ)^543*6250000000000^415 ≤ 2797545754079^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409913171 10000000000 2797545754079 6250000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663201493/1250000000 : ℝ), (-1928031167/10000000000 : ℝ), (5409913171/10000000000 : ℝ)] ![(43634963689101/100000000000000 : ℝ), (11604304238329/100000000000000 : ℝ), (2797545754079/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663201493/1250000000 : ℝ)|^543 ≤ (43634963689101/100000000000000 : ℝ)^415
        have hw : |(663201493/1250000000 : ℝ)|=(663201493/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1928031167/10000000000 : ℝ)|^543 ≤ (11604304238329/100000000000000 : ℝ)^415
        have hw : |(-1928031167/10000000000 : ℝ)|=(1928031167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5409913171/10000000000 : ℝ)|^543 ≤ (2797545754079/6250000000000 : ℝ)^415
        have hw : |(5409913171/10000000000 : ℝ)|=(5409913171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_s7_6 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5305611957/10000000000 : ℝ)*x 0 + (1352478287/2500000000 : ℝ)*x 1 + (-96401559/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305611957/10000000000 : ℝ)^543 ≤ (21817481914497/50000000000000 : ℝ)^415 := by
    have hnat : (5305611957 : ℕ)^543*50000000000000^415 ≤ 21817481914497^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305611957 10000000000 21817481914497 50000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352478287/2500000000 : ℝ)^543 ≤ (2797545738517/6250000000000 : ℝ)^415 := by
    have hnat : (1352478287 : ℕ)^543*6250000000000^415 ≤ 2797545738517^415*2500000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352478287 2500000000 2797545738517 6250000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (96401559/500000000 : ℝ)^543 ≤ (5802152170353/50000000000000 : ℝ)^415 := by
    have hnat : (96401559 : ℕ)^543*50000000000000^415 ≤ 5802152170353^415*500000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      96401559 500000000 5802152170353 50000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305611957/10000000000 : ℝ), (1352478287/2500000000 : ℝ), (-96401559/500000000 : ℝ)] ![(21817481914497/50000000000000 : ℝ), (2797545738517/6250000000000 : ℝ), (5802152170353/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305611957/10000000000 : ℝ)|^543 ≤ (21817481914497/50000000000000 : ℝ)^415
        have hw : |(5305611957/10000000000 : ℝ)|=(5305611957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352478287/2500000000 : ℝ)|^543 ≤ (2797545738517/6250000000000 : ℝ)^415
        have hw : |(1352478287/2500000000 : ℝ)|=(1352478287/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-96401559/500000000 : ℝ)|^543 ≤ (5802152170353/50000000000000 : ℝ)^415
        have hw : |(-96401559/500000000 : ℝ)|=(96401559/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_s7_7 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (863156561/2000000000 : ℝ)*x 0 + (2246472269/5000000000 : ℝ)*x 1 + (4145100841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (863156561/2000000000 : ℝ)^543 ≤ (33304248908283/100000000000000 : ℝ)^415 := by
    have hnat : (863156561 : ℕ)^543*100000000000000^415 ≤ 33304248908283^415*2000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      863156561 2000000000 33304248908283 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2246472269/5000000000 : ℝ)^543 ≤ (4388033423427/12500000000000 : ℝ)^415 := by
    have hnat : (2246472269 : ℕ)^543*12500000000000^415 ≤ 4388033423427^415*5000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246472269 5000000000 4388033423427 12500000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4145100841/10000000000 : ℝ)^543 ≤ (1579574184487/5000000000000 : ℝ)^415 := by
    have hnat : (4145100841 : ℕ)^543*5000000000000^415 ≤ 1579574184487^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4145100841 10000000000 1579574184487 5000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(863156561/2000000000 : ℝ), (2246472269/5000000000 : ℝ), (4145100841/10000000000 : ℝ)] ![(33304248908283/100000000000000 : ℝ), (4388033423427/12500000000000 : ℝ), (1579574184487/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(863156561/2000000000 : ℝ)|^543 ≤ (33304248908283/100000000000000 : ℝ)^415
        have hw : |(863156561/2000000000 : ℝ)|=(863156561/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2246472269/5000000000 : ℝ)|^543 ≤ (4388033423427/12500000000000 : ℝ)^415
        have hw : |(2246472269/5000000000 : ℝ)|=(2246472269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4145100841/10000000000 : ℝ)|^543 ≤ (1579574184487/5000000000000 : ℝ)^415
        have hw : |(4145100841/10000000000 : ℝ)|=(4145100841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1384_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78192963/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14733/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2811/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2249/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3683/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14733/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2811/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14733/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2811/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14733/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2811/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14733/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2811/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14733/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2811/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14733/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2811/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2811/25000 : ℝ) ^ (4343/1024 : ℝ) ≤ (9435286089775487/100000000000000000000 : ℝ) := by
    have hpowers : (2811/25000 : ℝ)^4343 ≤ (9435286089775487/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2811 : ℕ)^4343*100000000000000000000^1024 ≤ 9435286089775487^1024*25000^4343 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2811 25000 9435286089775487 100000000000000000000 4343 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2811/25000 : ℝ)) (X := (9435286089775487/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4343 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14733/100000 : ℝ) ^ (4343/1024 : ℝ) ≤ (237485708890661/800000000000000000 : ℝ) := by
    have hpowers : (14733/100000 : ℝ)^4343 ≤ (237485708890661/800000000000000000 : ℝ)^1024 := by
      have hnat : (14733 : ℕ)^4343*800000000000000000^1024 ≤ 237485708890661^1024*100000^4343 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14733 100000 237485708890661 800000000000000000 4343 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14733/100000 : ℝ)) (X := (237485708890661/800000000000000000 : ℝ)) (by norm_num) (by norm_num) 4343 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009435286089775487/50000000000000000000 : ℝ) ≤ (5000222450756679/5000000000000000 : ℝ) ^ (4343/1024 : ℝ) := by
    have hpowers : (50009435286089775487/50000000000000000000 : ℝ)^1024 ≤ (5000222450756679/5000000000000000 : ℝ)^4343 := by
      have hnat : (50009435286089775487 : ℕ)^1024*5000000000000000^4343 ≤ 5000222450756679^4343*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009435286089775487 50000000000000000000 5000222450756679 5000000000000000 1024 4343 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000222450756679/5000000000000000 : ℝ)) (X := (50009435286089775487/50000000000000000000 : ℝ)) (by norm_num) 4343 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6252445062481319257/6250000000000000000 : ℝ) ≤ (10000922263797373/10000000000000000 : ℝ) ^ (4343/1024 : ℝ) := by
    have hpowers : (6252445062481319257/6250000000000000000 : ℝ)^1024 ≤ (10000922263797373/10000000000000000 : ℝ)^4343 := by
      have hnat : (6252445062481319257 : ℕ)^1024*10000000000000000^4343 ≤ 10000922263797373^4343*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252445062481319257 6250000000000000000 10000922263797373 10000000000000000 1024 4343 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000922263797373/10000000000000000 : ℝ)) (X := (6252445062481319257/6250000000000000000 : ℝ)) (by norm_num) 4343 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (400237485708890661/400000000000000000 : ℝ) ≤ (2500349906520347/2500000000000000 : ℝ) ^ (4343/1024 : ℝ) := by
    have hpowers : (400237485708890661/400000000000000000 : ℝ)^1024 ≤ (2500349906520347/2500000000000000 : ℝ)^4343 := by
      have hnat : (400237485708890661 : ℕ)^1024*2500000000000000^4343 ≤ 2500349906520347^4343*400000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        400237485708890661 400000000000000000 2500349906520347 2500000000000000 1024 4343 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500349906520347/2500000000000000 : ℝ)) (X := (400237485708890661/400000000000000000 : ℝ)) (by norm_num) 4343 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9435286089775487/100000000000000000000 : ℝ) ≤ ((5813469556389529457/5815000000000000000 : ℝ)+2*(95472456803/69780000000000 : ℝ)*(2811/25000 : ℝ))^(4343/1024 : ℝ) := by
    rw [show (5813469556389529457/5815000000000000000 : ℝ)+2*(95472456803/69780000000000 : ℝ)*(2811/25000 : ℝ)=(5000222450756679/5000000000000000 : ℝ) by norm_num, show 1+2*(9435286089775487/100000000000000000000 : ℝ)=(50009435286089775487/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(237485708890661/800000000000000000 : ℝ)+(9435286089775487/100000000000000000000 : ℝ) ≤ ((5813469556389529457/5815000000000000000 : ℝ)+(95472456803/69780000000000 : ℝ)*((14733/100000 : ℝ)+(2811/25000 : ℝ)))^(4343/1024 : ℝ) := by
    rw [show (5813469556389529457/5815000000000000000 : ℝ)+(95472456803/69780000000000 : ℝ)*((14733/100000 : ℝ)+(2811/25000 : ℝ))=(10000922263797373/10000000000000000 : ℝ) by norm_num, show 1+(237485708890661/800000000000000000 : ℝ)+(9435286089775487/100000000000000000000 : ℝ)=(6252445062481319257/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(237485708890661/800000000000000000 : ℝ) ≤ ((5813469556389529457/5815000000000000000 : ℝ)+2*(95472456803/69780000000000 : ℝ)*(14733/100000 : ℝ))^(4343/1024 : ℝ) := by
    rw [show (5813469556389529457/5815000000000000000 : ℝ)+2*(95472456803/69780000000000 : ℝ)*(14733/100000 : ℝ)=(2500349906520347/2500000000000000 : ℝ) by norm_num, show 1+2*(237485708890661/800000000000000000 : ℝ)=(400237485708890661/400000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5813469556389529457/5815000000000000000 : ℝ)*(X 1 0+X 2 0)+(95472456803/69780000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4343/1024 : ℝ)) (lo := (2811/25000 : ℝ)) (hi := (14733/100000 : ℝ)) (c := (5813469556389529457/5815000000000000000 : ℝ)) (alpha := (95472456803/69780000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5813469556389529457/5815000000000000000 : ℝ)*(X 0 1+X 2 1)+(95472456803/69780000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4343/1024 : ℝ)) (lo := (2811/25000 : ℝ)) (hi := (14733/100000 : ℝ)) (c := (5813469556389529457/5815000000000000000 : ℝ)) (alpha := (95472456803/69780000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5813469556389529457/5815000000000000000 : ℝ)*(X 0 2+X 1 2)+(95472456803/69780000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4343/1024 : ℝ)) (lo := (2811/25000 : ℝ)) (hi := (14733/100000 : ℝ)) (c := (5813469556389529457/5815000000000000000 : ℝ)) (alpha := (95472456803/69780000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2008237737/10000000000 : ℝ)*X 0 0+(5410507573/10000000000 : ℝ)*X 0 1+(262291991/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348224703/10000000000 : ℝ)*X 1 0+(-1046052269/5000000000 : ℝ)*X 1 1+(2622919911/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674112359/5000000000 : ℝ)*X 2 0+(1311459953/2500000000 : ℝ)*X 2 1+(-2092104531/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((215787891/500000000 : ℝ)*X 0 0+(1035959031/2500000000 : ℝ)*X 0 1+(2247101387/5000000000 : ℝ)*X 0 2+(215787891/500000000 : ℝ)*X 1 0+(1035959031/2500000000 : ℝ)*X 1 1+(2247101387/5000000000 : ℝ)*X 1 2+(215787891/500000000 : ℝ)*X 2 0+(1035959031/2500000000 : ℝ)*X 2 1+(2247101387/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1004124739/5000000000 : ℝ)*X 0 0+(524643117/1000000000 : ℝ)*X 0 1+(1081982633/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((663201493/1250000000 : ℝ)*X 1 0+(-1928031167/10000000000 : ℝ)*X 1 1+(5409913171/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305611957/10000000000 : ℝ)*X 2 0+(1352478287/2500000000 : ℝ)*X 2 1+(-96401559/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((863156561/2000000000 : ℝ)*X 0 0+(2246472269/5000000000 : ℝ)*X 0 1+(4145100841/10000000000 : ℝ)*X 0 2+(863156561/2000000000 : ℝ)*X 1 0+(2246472269/5000000000 : ℝ)*X 1 1+(4145100841/10000000000 : ℝ)*X 1 2+(863156561/2000000000 : ℝ)*X 2 0+(2246472269/5000000000 : ℝ)*X 2 1+(4145100841/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (65420750723970137530110681/9085937500000000000000000000000 : ℝ) := by norm_num
    linear_combination (65638637/5000000000000 : ℝ)*(base19) + (1244314793/100000000000000 : ℝ)*(base23) + (22861091/50000000000000 : ℝ)*(lower2) + (17126889/10000000000000 : ℝ)*(upper3) + (120195219/100000000000000 : ℝ)*(upper5) + (278970939784111/6250000000000 : ℝ)*(major0) + (278970939784111/6250000000000 : ℝ)*(major1) + (278970939784111/6250000000000 : ℝ)*(major2) + (6072862661649649/100000000000000 : ℝ)*(sp0) + (1518222255754301/25000000000000 : ℝ)*(sp1) + (6072889091475151/100000000000000 : ℝ)*(sp2) + (570833115486523/20000000000000 : ℝ)*(sp3) + (5534828059/20000000000000 : ℝ)*(sp4) + (13919861647/100000000000000 : ℝ)*(sp7) + (1427089748647131/50000000000000 : ℝ)*(f.failure) + (759111291973743/12500000000000 : ℝ)*(f.sum) + (501217119047/174450000000000000000000000 : ℝ)*base66 + (1356476307676483069/109031250000000000000000000000000 : ℝ)*base68 + (299224330791826819/109031250000000000000000000000000 : ℝ)*base70 + (1682312292147920569/109031250000000000000000000000000 : ℝ)*base72 + (2208563926169/1744500000000000000000000000 : ℝ)*base74 + (164857281197641931/109031250000000000000000000000000 : ℝ)*base75 + (1642427789302108069/109031250000000000000000000000000 : ℝ)*base78 + (14980294459764319/109031250000000000000000000000000 : ℝ)*base80 + (2422431194411/872250000000000000000000000 : ℝ)*base81 + (14339153/2500000000000000000000 : ℝ)*base89 + (14339153/2500000000000000000000 : ℝ)*base91 + (14339153/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1073779533028474495268491613/145375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (328213877/25000000000000 : ℝ)*(base19) + (1431698561/100000000000000 : ℝ)*(base23) + (56192279/12500000000000 : ℝ)*(lower1) + (78371981/50000000000000 : ℝ)*(upper3) + (23970749/50000000000000 : ℝ)*(lower4) + (150779883/100000000000000 : ℝ)*(upper5) + (2247923621228497/50000000000000 : ℝ)*(major0) + (2247923621228497/50000000000000 : ℝ)*(major1) + (2247923621228497/50000000000000 : ℝ)*(major2) + (336053871/20000000000000 : ℝ)*(sp2) + (6116852903905313/100000000000000 : ℝ)*(sp4) + (1529212897762451/25000000000000 : ℝ)*(sp5) + (1529212447984349/25000000000000 : ℝ)*(sp6) + (1437420667399761/50000000000000 : ℝ)*(sp7) + (1437420667399761/50000000000000 : ℝ)*(f.failure) + (6116852903905313/100000000000000 : ℝ)*(f.sum) + (2494344356369/1744500000000000000000000000 : ℝ)*base65 + (6783456988272741613/872250000000000000000000000000000 : ℝ)*base68 + (791226034005008387/872250000000000000000000000000000 : ℝ)*base69 + (124973123642637741613/872250000000000000000000000000000 : ℝ)*base72 + (2188407710743/348900000000000000000000000 : ℝ)*base73 + (46440933212687258387/872250000000000000000000000000000 : ℝ)*base75 + (10992594137298758387/872250000000000000000000000000000 : ℝ)*base77 + (627146164536758387/872250000000000000000000000000000 : ℝ)*base79 + (2130617953931/3489000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (31918157/2500000000000000000000 : ℝ)*base90 + (31918157/2500000000000000000000 : ℝ)*base92 + (31918157/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1384_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78192963/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14733/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2811/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2249/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3683/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1384_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1384_box_0 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-922121749/5000000000 : ℝ)*x 0 + (2694086899/5000000000 : ℝ)*x 1 + (5388173837/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (922121749/5000000000 : ℝ)^543 ≤ (2737233545753/25000000000000 : ℝ)^415 := by
    have hnat : (922121749 : ℕ)^543*25000000000000^415 ≤ 2737233545753^415*5000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      922121749 5000000000 2737233545753 25000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2694086899/5000000000 : ℝ)^543 ≤ (22262766345197/50000000000000 : ℝ)^415 := by
    have hnat : (2694086899 : ℕ)^543*50000000000000^415 ≤ 22262766345197^415*5000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2694086899 5000000000 22262766345197 50000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5388173837/10000000000 : ℝ)^543 ≤ (1781021324483/4000000000000 : ℝ)^415 := by
    have hnat : (5388173837 : ℕ)^543*4000000000000^415 ≤ 1781021324483^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5388173837 10000000000 1781021324483 4000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-922121749/5000000000 : ℝ), (2694086899/5000000000 : ℝ), (5388173837/10000000000 : ℝ)] ![(2737233545753/25000000000000 : ℝ), (22262766345197/50000000000000 : ℝ), (1781021324483/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-922121749/5000000000 : ℝ)|^543 ≤ (2737233545753/25000000000000 : ℝ)^415
        have hw : |(-922121749/5000000000 : ℝ)|=(922121749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2694086899/5000000000 : ℝ)|^543 ≤ (22262766345197/50000000000000 : ℝ)^415
        have hw : |(2694086899/5000000000 : ℝ)|=(2694086899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5388173837/10000000000 : ℝ)|^543 ≤ (1781021324483/4000000000000 : ℝ)^415
        have hw : |(5388173837/10000000000 : ℝ)|=(5388173837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_box_1 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1321417707/2500000000 : ℝ)*x 0 + (-396974657/2000000000 : ℝ)*x 1 + (5388173861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1321417707/2500000000 : ℝ)^543 ≤ (10855125674259/25000000000000 : ℝ)^415 := by
    have hnat : (1321417707 : ℕ)^543*25000000000000^415 ≤ 10855125674259^415*2500000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321417707 2500000000 10855125674259 25000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (396974657/2000000000 : ℝ)^543 ≤ (12053963911089/100000000000000 : ℝ)^415 := by
    have hnat : (396974657 : ℕ)^543*100000000000000^415 ≤ 12053963911089^415*2000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      396974657 2000000000 12053963911089 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5388173861/10000000000 : ℝ)^543 ≤ (44525533371571/100000000000000 : ℝ)^415 := by
    have hnat : (5388173861 : ℕ)^543*100000000000000^415 ≤ 44525533371571^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5388173861 10000000000 44525533371571 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1321417707/2500000000 : ℝ), (-396974657/2000000000 : ℝ), (5388173861/10000000000 : ℝ)] ![(10855125674259/25000000000000 : ℝ), (12053963911089/100000000000000 : ℝ), (44525533371571/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1321417707/2500000000 : ℝ)|^543 ≤ (10855125674259/25000000000000 : ℝ)^415
        have hw : |(1321417707/2500000000 : ℝ)|=(1321417707/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-396974657/2000000000 : ℝ)|^543 ≤ (12053963911089/100000000000000 : ℝ)^415
        have hw : |(-396974657/2000000000 : ℝ)|=(396974657/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5388173861/10000000000 : ℝ)|^543 ≤ (44525533371571/100000000000000 : ℝ)^415
        have hw : |(5388173861/10000000000 : ℝ)|=(5388173861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_box_2 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1057134099/2000000000 : ℝ)*x 0 + (1077634829/2000000000 : ℝ)*x 1 + (-39697467/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057134099/2000000000 : ℝ)^543 ≤ (43420499117797/100000000000000 : ℝ)^415 := by
    have hnat : (1057134099 : ℕ)^543*100000000000000^415 ≤ 43420499117797^415*2000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057134099 2000000000 43420499117797 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1077634829/2000000000 : ℝ)^543 ≤ (1391423013821/3125000000000 : ℝ)^415 := by
    have hnat : (1077634829 : ℕ)^543*3125000000000^415 ≤ 1391423013821^415*2000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077634829 2000000000 1391423013821 3125000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (39697467/200000000 : ℝ)^543 ≤ (12053964427579/100000000000000 : ℝ)^415 := by
    have hnat : (39697467 : ℕ)^543*100000000000000^415 ≤ 12053964427579^415*200000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39697467 200000000 12053964427579 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057134099/2000000000 : ℝ), (1077634829/2000000000 : ℝ), (-39697467/200000000 : ℝ)] ![(43420499117797/100000000000000 : ℝ), (1391423013821/3125000000000 : ℝ), (12053964427579/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057134099/2000000000 : ℝ)|^543 ≤ (43420499117797/100000000000000 : ℝ)^415
        have hw : |(1057134099/2000000000 : ℝ)|=(1057134099/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1077634829/2000000000 : ℝ)|^543 ≤ (1391423013821/3125000000000 : ℝ)^415
        have hw : |(1077634829/2000000000 : ℝ)|=(1077634829/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-39697467/200000000 : ℝ)|^543 ≤ (12053964427579/100000000000000 : ℝ)^415
        have hw : |(-39697467/200000000 : ℝ)|=(39697467/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_box_3 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4462996933/10000000000 : ℝ)*x 0 + (424593699/1000000000 : ℝ)*x 1 + (265371103/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4462996933/10000000000 : ℝ)^543 ≤ (34798426641941/100000000000000 : ℝ)^415 := by
    have hnat : (4462996933 : ℕ)^543*100000000000000^415 ≤ 34798426641941^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4462996933 10000000000 34798426641941 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (424593699/1000000000 : ℝ)^543 ≤ (3260078336607/10000000000000 : ℝ)^415 := by
    have hnat : (424593699 : ℕ)^543*10000000000000^415 ≤ 3260078336607^415*1000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424593699 1000000000 3260078336607 10000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (265371103/625000000 : ℝ)^543 ≤ (32600789976537/100000000000000 : ℝ)^415 := by
    have hnat : (265371103 : ℕ)^543*100000000000000^415 ≤ 32600789976537^415*625000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265371103 625000000 32600789976537 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4462996933/10000000000 : ℝ), (424593699/1000000000 : ℝ), (265371103/625000000 : ℝ)] ![(34798426641941/100000000000000 : ℝ), (3260078336607/10000000000000 : ℝ), (32600789976537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4462996933/10000000000 : ℝ)|^543 ≤ (34798426641941/100000000000000 : ℝ)^415
        have hw : |(4462996933/10000000000 : ℝ)|=(4462996933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(424593699/1000000000 : ℝ)|^543 ≤ (3260078336607/10000000000000 : ℝ)^415
        have hw : |(424593699/1000000000 : ℝ)|=(424593699/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(265371103/625000000 : ℝ)|^543 ≤ (32600789976537/100000000000000 : ℝ)^415
        have hw : |(265371103/625000000 : ℝ)|=(265371103/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_box_4 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-543743991/2500000000 : ℝ)*x 0 + (1316444797/2500000000 : ℝ)*x 1 + (526577891/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (543743991/2500000000 : ℝ)^543 ≤ (13586358404089/100000000000000 : ℝ)^415 := by
    have hnat : (543743991 : ℕ)^543*100000000000000^415 ≤ 13586358404089^415*2500000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543743991 2500000000 13586358404089 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316444797/2500000000 : ℝ)^543 ≤ (2700426392731/6250000000000 : ℝ)^415 := by
    have hnat : (1316444797 : ℕ)^543*6250000000000^415 ≤ 2700426392731^415*2500000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316444797 2500000000 2700426392731 6250000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526577891/1000000000 : ℝ)^543 ≤ (5400852412387/12500000000000 : ℝ)^415 := by
    have hnat : (526577891 : ℕ)^543*12500000000000^415 ≤ 5400852412387^415*1000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526577891 1000000000 5400852412387 12500000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-543743991/2500000000 : ℝ), (1316444797/2500000000 : ℝ), (526577891/1000000000 : ℝ)] ![(13586358404089/100000000000000 : ℝ), (2700426392731/6250000000000 : ℝ), (5400852412387/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-543743991/2500000000 : ℝ)|^543 ≤ (13586358404089/100000000000000 : ℝ)^415
        have hw : |(-543743991/2500000000 : ℝ)|=(543743991/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316444797/2500000000 : ℝ)|^543 ≤ (2700426392731/6250000000000 : ℝ)^415
        have hw : |(1316444797/2500000000 : ℝ)|=(1316444797/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526577891/1000000000 : ℝ)|^543 ≤ (5400852412387/12500000000000 : ℝ)^415
        have hw : |(526577891/1000000000 : ℝ)|=(526577891/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_box_5 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5371486947/10000000000 : ℝ)*x 0 + (-2034272449/10000000000 : ℝ)*x 1 + (1316444671/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5371486947/10000000000 : ℝ)^543 ≤ (22172597597827/50000000000000 : ℝ)^415 := by
    have hnat : (5371486947 : ℕ)^543*50000000000000^415 ≤ 22172597597827^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5371486947 10000000000 22172597597827 50000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2034272449/10000000000 : ℝ)^543 ≤ (1244798792331/10000000000000 : ℝ)^415 := by
    have hnat : (2034272449 : ℕ)^543*10000000000000^415 ≤ 1244798792331^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2034272449 10000000000 1244798792331 10000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316444671/2500000000 : ℝ)^543 ≤ (21603408436383/50000000000000 : ℝ)^415 := by
    have hnat : (1316444671 : ℕ)^543*50000000000000^415 ≤ 21603408436383^415*2500000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316444671 2500000000 21603408436383 50000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5371486947/10000000000 : ℝ), (-2034272449/10000000000 : ℝ), (1316444671/2500000000 : ℝ)] ![(22172597597827/50000000000000 : ℝ), (1244798792331/10000000000000 : ℝ), (21603408436383/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5371486947/10000000000 : ℝ)|^543 ≤ (22172597597827/50000000000000 : ℝ)^415
        have hw : |(5371486947/10000000000 : ℝ)|=(5371486947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2034272449/10000000000 : ℝ)|^543 ≤ (1244798792331/10000000000000 : ℝ)^415
        have hw : |(-2034272449/10000000000 : ℝ)|=(2034272449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316444671/2500000000 : ℝ)|^543 ≤ (21603408436383/50000000000000 : ℝ)^415
        have hw : |(1316444671/2500000000 : ℝ)|=(1316444671/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_box_6 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (537148783/1000000000 : ℝ)*x 0 + (5265778899/10000000000 : ℝ)*x 1 + (-254283871/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537148783/1000000000 : ℝ)^543 ≤ (11086301183453/25000000000000 : ℝ)^415 := by
    have hnat : (537148783 : ℕ)^543*25000000000000^415 ≤ 11086301183453^415*1000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537148783 1000000000 11086301183453 25000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265778899/10000000000 : ℝ)^543 ≤ (43206819181/100000000000 : ℝ)^415 := by
    have hnat : (5265778899 : ℕ)^543*100000000000^415 ≤ 43206819181^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265778899 10000000000 43206819181 100000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (254283871/1250000000 : ℝ)^543 ≤ (1244797606571/10000000000000 : ℝ)^415 := by
    have hnat : (254283871 : ℕ)^543*10000000000000^415 ≤ 1244797606571^415*1250000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      254283871 1250000000 1244797606571 10000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537148783/1000000000 : ℝ), (5265778899/10000000000 : ℝ), (-254283871/1250000000 : ℝ)] ![(11086301183453/25000000000000 : ℝ), (43206819181/100000000000 : ℝ), (1244797606571/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537148783/1000000000 : ℝ)|^543 ≤ (11086301183453/25000000000000 : ℝ)^415
        have hw : |(537148783/1000000000 : ℝ)|=(537148783/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265778899/10000000000 : ℝ)|^543 ≤ (43206819181/100000000000 : ℝ)^415
        have hw : |(5265778899/10000000000 : ℝ)|=(5265778899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-254283871/1250000000 : ℝ)|^543 ≤ (1244797606571/10000000000000 : ℝ)^415
        have hw : |(-254283871/1250000000 : ℝ)|=(254283871/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_box_7 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (833506763/2000000000 : ℝ)*x 0 + (4393616059/10000000000 : ℝ)*x 1 + (4393617243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (833506763/2000000000 : ℝ)^543 ≤ (1272614961543/4000000000000 : ℝ)^415 := by
    have hnat : (833506763 : ℕ)^543*4000000000000^415 ≤ 1272614961543^415*2000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      833506763 2000000000 1272614961543 4000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4393616059/10000000000 : ℝ)^543 ≤ (34092306962003/100000000000000 : ℝ)^415 := by
    have hnat : (4393616059 : ℕ)^543*100000000000000^415 ≤ 34092306962003^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4393616059 10000000000 34092306962003 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4393617243/10000000000 : ℝ)^543 ≤ (8523079745731/25000000000000 : ℝ)^415 := by
    have hnat : (4393617243 : ℕ)^543*25000000000000^415 ≤ 8523079745731^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4393617243 10000000000 8523079745731 25000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(833506763/2000000000 : ℝ), (4393616059/10000000000 : ℝ), (4393617243/10000000000 : ℝ)] ![(1272614961543/4000000000000 : ℝ), (34092306962003/100000000000000 : ℝ), (8523079745731/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(833506763/2000000000 : ℝ)|^543 ≤ (1272614961543/4000000000000 : ℝ)^415
        have hw : |(833506763/2000000000 : ℝ)|=(833506763/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4393616059/10000000000 : ℝ)|^543 ≤ (34092306962003/100000000000000 : ℝ)^415
        have hw : |(4393616059/10000000000 : ℝ)|=(4393616059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4393617243/10000000000 : ℝ)|^543 ≤ (8523079745731/25000000000000 : ℝ)^415
        have hw : |(4393617243/10000000000 : ℝ)|=(4393617243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_box_8 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2105418019/10000000000 : ℝ)*x 0 + (2590662713/5000000000 : ℝ)*x 1 + (2701086557/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2105418019/10000000000 : ℝ)^543 ≤ (162758269637/1250000000000 : ℝ)^415 := by
    have hnat : (2105418019 : ℕ)^543*1250000000000^415 ≤ 162758269637^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2105418019 10000000000 162758269637 1250000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2590662713/5000000000 : ℝ)^543 ≤ (846047597919/2000000000000 : ℝ)^415 := by
    have hnat : (2590662713 : ℕ)^543*2000000000000^415 ≤ 846047597919^415*5000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590662713 5000000000 846047597919 2000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2701086557/5000000000 : ℝ)^543 ≤ (22338479258297/50000000000000 : ℝ)^415 := by
    have hnat : (2701086557 : ℕ)^543*50000000000000^415 ≤ 22338479258297^415*5000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701086557 5000000000 22338479258297 50000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2105418019/10000000000 : ℝ), (2590662713/5000000000 : ℝ), (2701086557/5000000000 : ℝ)] ![(162758269637/1250000000000 : ℝ), (846047597919/2000000000000 : ℝ), (22338479258297/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2105418019/10000000000 : ℝ)|^543 ≤ (162758269637/1250000000000 : ℝ)^415
        have hw : |(-2105418019/10000000000 : ℝ)|=(2105418019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2590662713/5000000000 : ℝ)|^543 ≤ (846047597919/2000000000000 : ℝ)^415
        have hw : |(2590662713/5000000000 : ℝ)|=(2590662713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2701086557/5000000000 : ℝ)|^543 ≤ (22338479258297/50000000000000 : ℝ)^415
        have hw : |(2701086557/5000000000 : ℝ)|=(2701086557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_box_9 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2637925041/5000000000 : ℝ)*x 0 + (-395818733/2000000000 : ℝ)*x 1 + (5402173743/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2637925041/5000000000 : ℝ)^543 ≤ (5414371875803/12500000000000 : ℝ)^415 := by
    have hnat : (2637925041 : ℕ)^543*12500000000000^415 ≤ 5414371875803^415*5000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2637925041 5000000000 5414371875803 12500000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (395818733/2000000000 : ℝ)^543 ≤ (750503728647/6250000000000 : ℝ)^415 := by
    have hnat : (395818733 : ℕ)^543*6250000000000^415 ≤ 750503728647^415*2000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      395818733 2000000000 750503728647 6250000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5402173743/10000000000 : ℝ)^543 ≤ (22338482661497/50000000000000 : ℝ)^415 := by
    have hnat : (5402173743 : ℕ)^543*50000000000000^415 ≤ 22338482661497^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402173743 10000000000 22338482661497 50000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2637925041/5000000000 : ℝ), (-395818733/2000000000 : ℝ), (5402173743/10000000000 : ℝ)] ![(5414371875803/12500000000000 : ℝ), (750503728647/6250000000000 : ℝ), (22338482661497/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2637925041/5000000000 : ℝ)|^543 ≤ (5414371875803/12500000000000 : ℝ)^415
        have hw : |(2637925041/5000000000 : ℝ)|=(2637925041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-395818733/2000000000 : ℝ)|^543 ≤ (750503728647/6250000000000 : ℝ)^415
        have hw : |(-395818733/2000000000 : ℝ)|=(395818733/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5402173743/10000000000 : ℝ)|^543 ≤ (22338482661497/50000000000000 : ℝ)^415
        have hw : |(5402173743/10000000000 : ℝ)|=(5402173743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_box_10 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (659481159/1250000000 : ℝ)*x 0 + (5402173911/10000000000 : ℝ)*x 1 + (-1979094531/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (659481159/1250000000 : ℝ)^543 ≤ (1082874157629/2500000000000 : ℝ)^415 := by
    have hnat : (659481159 : ℕ)^543*2500000000000^415 ≤ 1082874157629^415*1250000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659481159 1250000000 1082874157629 2500000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5402173911/10000000000 : ℝ)^543 ≤ (1116924178523/2500000000000 : ℝ)^415 := by
    have hnat : (5402173911 : ℕ)^543*2500000000000^415 ≤ 1116924178523^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402173911 10000000000 1116924178523 2500000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1979094531/10000000000 : ℝ)^543 ≤ (12008066533407/100000000000000 : ℝ)^415 := by
    have hnat : (1979094531 : ℕ)^543*100000000000000^415 ≤ 12008066533407^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1979094531 10000000000 12008066533407 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(659481159/1250000000 : ℝ), (5402173911/10000000000 : ℝ), (-1979094531/10000000000 : ℝ)] ![(1082874157629/2500000000000 : ℝ), (1116924178523/2500000000000 : ℝ), (12008066533407/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(659481159/1250000000 : ℝ)|^543 ≤ (1082874157629/2500000000000 : ℝ)^415
        have hw : |(659481159/1250000000 : ℝ)|=(659481159/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5402173911/10000000000 : ℝ)|^543 ≤ (1116924178523/2500000000000 : ℝ)^415
        have hw : |(5402173911/10000000000 : ℝ)|=(5402173911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1979094531/10000000000 : ℝ)|^543 ≤ (12008066533407/100000000000000 : ℝ)^415
        have hw : |(-1979094531/10000000000 : ℝ)|=(1979094531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_box_11 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (899246947/2000000000 : ℝ)*x 0 + (4229031251/10000000000 : ℝ)*x 1 + (1057257757/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (899246947/2000000000 : ℝ)^543 ≤ (8784476760477/25000000000000 : ℝ)^415 := by
    have hnat : (899246947 : ℕ)^543*25000000000000^415 ≤ 8784476760477^415*2000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899246947 2000000000 8784476760477 25000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4229031251/10000000000 : ℝ)^543 ≤ (6486209518439/20000000000000 : ℝ)^415 := by
    have hnat : (4229031251 : ℕ)^543*20000000000000^415 ≤ 6486209518439^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4229031251 10000000000 6486209518439 20000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1057257757/2500000000 : ℝ)^543 ≤ (259448362837/800000000000 : ℝ)^415 := by
    have hnat : (1057257757 : ℕ)^543*800000000000^415 ≤ 259448362837^415*2500000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057257757 2500000000 259448362837 800000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(899246947/2000000000 : ℝ), (4229031251/10000000000 : ℝ), (1057257757/2500000000 : ℝ)] ![(8784476760477/25000000000000 : ℝ), (6486209518439/20000000000000 : ℝ), (259448362837/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(899246947/2000000000 : ℝ)|^543 ≤ (8784476760477/25000000000000 : ℝ)^415
        have hw : |(899246947/2000000000 : ℝ)|=(899246947/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4229031251/10000000000 : ℝ)|^543 ≤ (6486209518439/20000000000000 : ℝ)^415
        have hw : |(4229031251/10000000000 : ℝ)|=(4229031251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1057257757/2500000000 : ℝ)|^543 ≤ (259448362837/800000000000 : ℝ)^415
        have hw : |(1057257757/2500000000 : ℝ)|=(1057257757/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_box_12 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1914060179/10000000000 : ℝ)*x 0 + (2735256749/5000000000 : ℝ)*x 1 + (5254678867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1914060179/10000000000 : ℝ)^543 ≤ (11494404286453/100000000000000 : ℝ)^415 := by
    have hnat : (1914060179 : ℕ)^543*100000000000000^415 ≤ 11494404286453^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1914060179 10000000000 11494404286453 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2735256749/5000000000 : ℝ)^543 ≤ (45417907400839/100000000000000 : ℝ)^415 := by
    have hnat : (2735256749 : ℕ)^543*100000000000000^415 ≤ 45417907400839^415*5000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2735256749 5000000000 45417907400839 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5254678867/10000000000 : ℝ)^543 ≤ (21543844148277/50000000000000 : ℝ)^415 := by
    have hnat : (5254678867 : ℕ)^543*50000000000000^415 ≤ 21543844148277^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254678867 10000000000 21543844148277 50000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1914060179/10000000000 : ℝ), (2735256749/5000000000 : ℝ), (5254678867/10000000000 : ℝ)] ![(11494404286453/100000000000000 : ℝ), (45417907400839/100000000000000 : ℝ), (21543844148277/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1914060179/10000000000 : ℝ)|^543 ≤ (11494404286453/100000000000000 : ℝ)^415
        have hw : |(-1914060179/10000000000 : ℝ)|=(1914060179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2735256749/5000000000 : ℝ)|^543 ≤ (45417907400839/100000000000000 : ℝ)^415
        have hw : |(2735256749/5000000000 : ℝ)|=(2735256749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5254678867/10000000000 : ℝ)|^543 ≤ (21543844148277/50000000000000 : ℝ)^415
        have hw : |(5254678867/10000000000 : ℝ)|=(5254678867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_box_13 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2689634153/5000000000 : ℝ)*x 0 + (-1019324813/5000000000 : ℝ)*x 1 + (5254678701/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2689634153/5000000000 : ℝ)^543 ≤ (44429268131187/100000000000000 : ℝ)^415 := by
    have hnat : (2689634153 : ℕ)^543*100000000000000^415 ≤ 44429268131187^415*5000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2689634153 5000000000 44429268131187 100000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1019324813/5000000000 : ℝ)^543 ≤ (1560380667387/12500000000000 : ℝ)^415 := by
    have hnat : (1019324813 : ℕ)^543*12500000000000^415 ≤ 1560380667387^415*5000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1019324813 5000000000 1560380667387 12500000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5254678701/10000000000 : ℝ)^543 ≤ (21543843257771/50000000000000 : ℝ)^415 := by
    have hnat : (5254678701 : ℕ)^543*50000000000000^415 ≤ 21543843257771^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254678701 10000000000 21543843257771 50000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2689634153/5000000000 : ℝ), (-1019324813/5000000000 : ℝ), (5254678701/10000000000 : ℝ)] ![(44429268131187/100000000000000 : ℝ), (1560380667387/12500000000000 : ℝ), (21543843257771/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2689634153/5000000000 : ℝ)|^543 ≤ (44429268131187/100000000000000 : ℝ)^415
        have hw : |(2689634153/5000000000 : ℝ)|=(2689634153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1019324813/5000000000 : ℝ)|^543 ≤ (1560380667387/12500000000000 : ℝ)^415
        have hw : |(-1019324813/5000000000 : ℝ)|=(1019324813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5254678701/10000000000 : ℝ)|^543 ≤ (21543843257771/50000000000000 : ℝ)^415
        have hw : |(5254678701/10000000000 : ℝ)|=(5254678701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_box_14 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5379268331/10000000000 : ℝ)*x 0 + (525467877/1000000000 : ℝ)*x 1 + (-4077299/20000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5379268331/10000000000 : ℝ)^543 ≤ (22214634200679/50000000000000 : ℝ)^415 := by
    have hnat : (5379268331 : ℕ)^543*50000000000000^415 ≤ 22214634200679^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5379268331 10000000000 22214634200679 50000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (525467877/1000000000 : ℝ)^543 ≤ (21543843627921/50000000000000 : ℝ)^415 := by
    have hnat : (525467877 : ℕ)^543*50000000000000^415 ≤ 21543843627921^415*1000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525467877 1000000000 21543843627921 50000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4077299/20000000 : ℝ)^543 ≤ (1248304432961/10000000000000 : ℝ)^415 := by
    have hnat : (4077299 : ℕ)^543*10000000000000^415 ≤ 1248304432961^415*20000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4077299 20000000 1248304432961 10000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5379268331/10000000000 : ℝ), (525467877/1000000000 : ℝ), (-4077299/20000000 : ℝ)] ![(22214634200679/50000000000000 : ℝ), (21543843627921/50000000000000 : ℝ), (1248304432961/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5379268331/10000000000 : ℝ)|^543 ≤ (22214634200679/50000000000000 : ℝ)^415
        have hw : |(5379268331/10000000000 : ℝ)|=(5379268331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(525467877/1000000000 : ℝ)|^543 ≤ (21543843627921/50000000000000 : ℝ)^415
        have hw : |(525467877/1000000000 : ℝ)|=(525467877/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4077299/20000000 : ℝ)|^543 ≤ (1248304432961/10000000000000 : ℝ)^415
        have hw : |(-4077299/20000000 : ℝ)|=(4077299/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1384_box_15 (p : ℝ) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ)) (x : Fin 3 → ℝ) :
    (258767943/625000000 : ℝ)*x 0 + (4406999951/10000000000 : ℝ)*x 1 + (1101750021/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (258767943/625000000 : ℝ)^543 ≤ (6308697811893/20000000000000 : ℝ)^415 := by
    have hnat : (258767943 : ℕ)^543*20000000000000^415 ≤ 6308697811893^415*625000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258767943 625000000 6308697811893 20000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4406999951/10000000000 : ℝ)^543 ≤ (4278531848789/12500000000000 : ℝ)^415 := by
    have hnat : (4406999951 : ℕ)^543*12500000000000^415 ≤ 4278531848789^415*10000000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4406999951 10000000000 4278531848789 12500000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1101750021/2500000000 : ℝ)^543 ≤ (17114128070951/50000000000000 : ℝ)^415 := by
    have hnat : (1101750021 : ℕ)^543*50000000000000^415 ≤ 17114128070951^415*2500000000^543 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101750021 2500000000 17114128070951 50000000000000 543 415 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (543/128 : ℝ)) 543 415 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(258767943/625000000 : ℝ), (4406999951/10000000000 : ℝ), (1101750021/2500000000 : ℝ)] ![(6308697811893/20000000000000 : ℝ), (4278531848789/12500000000000 : ℝ), (17114128070951/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(258767943/625000000 : ℝ)|^543 ≤ (6308697811893/20000000000000 : ℝ)^415
        have hw : |(258767943/625000000 : ℝ)|=(258767943/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4406999951/10000000000 : ℝ)|^543 ≤ (4278531848789/12500000000000 : ℝ)^415
        have hw : |(4406999951/10000000000 : ℝ)|=(4406999951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1101750021/2500000000 : ℝ)|^543 ≤ (17114128070951/50000000000000 : ℝ)^415
        have hw : |(1101750021/2500000000 : ℝ)|=(1101750021/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1384_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78192963/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3683/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2249/20000 : ℝ)*pair X i i ≤ pair X i h) :
    -(31437/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59023/100000 : ℝ) ∧ (80197/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (42257/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3683/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2249/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3683/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2249/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3683/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2249/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3683/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2249/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3683/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2249/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3683/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2249/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2249/20000 : ℝ) ^ (4343/1024 : ℝ) ≤ (377553822839077/4000000000000000000 : ℝ) := by
    have hpowers : (2249/20000 : ℝ)^4343 ≤ (377553822839077/4000000000000000000 : ℝ)^1024 := by
      have hnat : (2249 : ℕ)^4343*4000000000000000000^1024 ≤ 377553822839077^1024*20000^4343 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2249 20000 377553822839077 4000000000000000000 4343 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2249/20000 : ℝ)) (X := (377553822839077/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4343 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3683/25000 : ℝ) ^ (4343/1024 : ℝ) ≤ (14838584440065393/50000000000000000000 : ℝ) := by
    have hpowers : (3683/25000 : ℝ)^4343 ≤ (14838584440065393/50000000000000000000 : ℝ)^1024 := by
      have hnat : (3683 : ℕ)^4343*50000000000000000000^1024 ≤ 14838584440065393^1024*25000^4343 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3683 25000 14838584440065393 50000000000000000000 4343 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3683/25000 : ℝ)) (X := (14838584440065393/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4343 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000377553822839077/2000000000000000000 : ℝ) ≤ (1000044506934127/1000000000000000 : ℝ) ^ (4343/1024 : ℝ) := by
    have hpowers : (2000377553822839077/2000000000000000000 : ℝ)^1024 ≤ (1000044506934127/1000000000000000 : ℝ)^4343 := by
      have hnat : (2000377553822839077 : ℕ)^1024*1000000000000000^4343 ≤ 1000044506934127^4343*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000377553822839077 2000000000000000000 1000044506934127 1000000000000000 1024 4343 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000044506934127/1000000000000000 : ℝ)) (X := (2000377553822839077/2000000000000000000 : ℝ)) (by norm_num) 4343 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100039116014451107711/100000000000000000000 : ℝ) ≤ (500046107314471/500000000000000 : ℝ) ^ (4343/1024 : ℝ) := by
    have hpowers : (100039116014451107711/100000000000000000000 : ℝ)^1024 ≤ (500046107314471/500000000000000 : ℝ)^4343 := by
      have hnat : (100039116014451107711 : ℕ)^1024*500000000000000^4343 ≤ 500046107314471^4343*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100039116014451107711 100000000000000000000 500046107314471 500000000000000 1024 4343 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500046107314471/500000000000000 : ℝ)) (X := (100039116014451107711/100000000000000000000 : ℝ)) (by norm_num) 4343 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25014838584440065393/25000000000000000000 : ℝ) ≤ (1000139922323757/1000000000000000 : ℝ) ^ (4343/1024 : ℝ) := by
    have hpowers : (25014838584440065393/25000000000000000000 : ℝ)^1024 ≤ (1000139922323757/1000000000000000 : ℝ)^4343 := by
      have hnat : (25014838584440065393 : ℕ)^1024*1000000000000000^4343 ≤ 1000139922323757^4343*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014838584440065393 25000000000000000000 1000139922323757 1000000000000000 1024 4343 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000139922323757/1000000000000000 : ℝ)) (X := (25014838584440065393/25000000000000000000 : ℝ)) (by norm_num) 4343 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(377553822839077/4000000000000000000 : ℝ) ≤ ((316916568147537409/317000000000000000 : ℝ)+2*(867412633/634000000000 : ℝ)*(2249/20000 : ℝ))^(4343/1024 : ℝ) := by
    rw [show (316916568147537409/317000000000000000 : ℝ)+2*(867412633/634000000000 : ℝ)*(2249/20000 : ℝ)=(1000044506934127/1000000000000000 : ℝ) by norm_num, show 1+2*(377553822839077/4000000000000000000 : ℝ)=(2000377553822839077/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14838584440065393/50000000000000000000 : ℝ)+(377553822839077/4000000000000000000 : ℝ) ≤ ((316916568147537409/317000000000000000 : ℝ)+(867412633/634000000000 : ℝ)*((3683/25000 : ℝ)+(2249/20000 : ℝ)))^(4343/1024 : ℝ) := by
    rw [show (316916568147537409/317000000000000000 : ℝ)+(867412633/634000000000 : ℝ)*((3683/25000 : ℝ)+(2249/20000 : ℝ))=(500046107314471/500000000000000 : ℝ) by norm_num, show 1+(14838584440065393/50000000000000000000 : ℝ)+(377553822839077/4000000000000000000 : ℝ)=(100039116014451107711/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14838584440065393/50000000000000000000 : ℝ) ≤ ((316916568147537409/317000000000000000 : ℝ)+2*(867412633/634000000000 : ℝ)*(3683/25000 : ℝ))^(4343/1024 : ℝ) := by
    rw [show (316916568147537409/317000000000000000 : ℝ)+2*(867412633/634000000000 : ℝ)*(3683/25000 : ℝ)=(1000139922323757/1000000000000000 : ℝ) by norm_num, show 1+2*(14838584440065393/50000000000000000000 : ℝ)=(25014838584440065393/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (316916568147537409/317000000000000000 : ℝ)*(X 1 0+X 2 0)+(867412633/634000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4343/1024 : ℝ)) (lo := (2249/20000 : ℝ)) (hi := (3683/25000 : ℝ)) (c := (316916568147537409/317000000000000000 : ℝ)) (alpha := (867412633/634000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (316916568147537409/317000000000000000 : ℝ)*(X 0 1+X 2 1)+(867412633/634000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4343/1024 : ℝ)) (lo := (2249/20000 : ℝ)) (hi := (3683/25000 : ℝ)) (c := (316916568147537409/317000000000000000 : ℝ)) (alpha := (867412633/634000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (316916568147537409/317000000000000000 : ℝ)*(X 0 2+X 1 2)+(867412633/634000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4343/1024 : ℝ)) (lo := (2249/20000 : ℝ)) (hi := (3683/25000 : ℝ)) (c := (316916568147537409/317000000000000000 : ℝ)) (alpha := (867412633/634000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-922121749/5000000000 : ℝ)*X 0 0+(2694086899/5000000000 : ℝ)*X 0 1+(5388173837/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1321417707/2500000000 : ℝ)*X 1 0+(-396974657/2000000000 : ℝ)*X 1 1+(5388173861/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1057134099/2000000000 : ℝ)*X 2 0+(1077634829/2000000000 : ℝ)*X 2 1+(-39697467/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4462996933/10000000000 : ℝ)*X 0 0+(424593699/1000000000 : ℝ)*X 0 1+(265371103/625000000 : ℝ)*X 0 2+(4462996933/10000000000 : ℝ)*X 1 0+(424593699/1000000000 : ℝ)*X 1 1+(265371103/625000000 : ℝ)*X 1 2+(4462996933/10000000000 : ℝ)*X 2 0+(424593699/1000000000 : ℝ)*X 2 1+(265371103/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-543743991/2500000000 : ℝ)*X 0 0+(1316444797/2500000000 : ℝ)*X 0 1+(526577891/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5371486947/10000000000 : ℝ)*X 1 0+(-2034272449/10000000000 : ℝ)*X 1 1+(1316444671/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((537148783/1000000000 : ℝ)*X 2 0+(5265778899/10000000000 : ℝ)*X 2 1+(-254283871/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((833506763/2000000000 : ℝ)*X 0 0+(4393616059/10000000000 : ℝ)*X 0 1+(4393617243/10000000000 : ℝ)*X 0 2+(833506763/2000000000 : ℝ)*X 1 0+(4393616059/10000000000 : ℝ)*X 1 1+(4393617243/10000000000 : ℝ)*X 1 2+(833506763/2000000000 : ℝ)*X 2 0+(4393616059/10000000000 : ℝ)*X 2 1+(4393617243/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2105418019/10000000000 : ℝ)*X 0 0+(2590662713/5000000000 : ℝ)*X 0 1+(2701086557/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2637925041/5000000000 : ℝ)*X 1 0+(-395818733/2000000000 : ℝ)*X 1 1+(5402173743/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((659481159/1250000000 : ℝ)*X 2 0+(5402173911/10000000000 : ℝ)*X 2 1+(-1979094531/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((899246947/2000000000 : ℝ)*X 0 0+(4229031251/10000000000 : ℝ)*X 0 1+(1057257757/2500000000 : ℝ)*X 0 2+(899246947/2000000000 : ℝ)*X 1 0+(4229031251/10000000000 : ℝ)*X 1 1+(1057257757/2500000000 : ℝ)*X 1 2+(899246947/2000000000 : ℝ)*X 2 0+(4229031251/10000000000 : ℝ)*X 2 1+(1057257757/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1914060179/10000000000 : ℝ)*X 0 0+(2735256749/5000000000 : ℝ)*X 0 1+(5254678867/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2689634153/5000000000 : ℝ)*X 1 0+(-1019324813/5000000000 : ℝ)*X 1 1+(5254678701/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5379268331/10000000000 : ℝ)*X 2 0+(525467877/1000000000 : ℝ)*X 2 1+(-4077299/20000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((258767943/625000000 : ℝ)*X 0 0+(4406999951/10000000000 : ℝ)*X 0 1+(1101750021/2500000000 : ℝ)*X 0 2+(258767943/625000000 : ℝ)*X 1 0+(4406999951/10000000000 : ℝ)*X 1 1+(1101750021/2500000000 : ℝ)*X 1 2+(258767943/625000000 : ℝ)*X 2 0+(4406999951/10000000000 : ℝ)*X 2 1+(1101750021/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1384_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31437/50000 : ℝ) ≤ (-4982583225679374881039173825653/7925000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (536793557/100000000000000 : ℝ)*(upper0) + (175851513/25000000000000 : ℝ)*(lower2) + (93454727/100000000000000 : ℝ)*(upper5) + (1483678505540187/50000000000000 : ℝ)*(major0) + (1483678505540187/50000000000000 : ℝ)*(major1) + (1483678505540187/50000000000000 : ℝ)*(major2) + (1125157517/10000000000000 : ℝ)*(sp1) + (34653303/20000000000000 : ℝ)*(sp3) + (4058210048830547/100000000000000 : ℝ)*(sp4) + (1014550542425737/25000000000000 : ℝ)*(sp5) + (2028947010669129/50000000000000 : ℝ)*(sp6) + (237182208144799/12500000000000 : ℝ)*(sp7) + (3372447571/100000000000000 : ℝ)*(sp8) + (319399939861/100000000000000 : ℝ)*(sp14) + (1897457838424907/100000000000000 : ℝ)*(f.failure) + (2029106710639059/50000000000000 : ℝ)*(f.sum) + (12149142443/158500000000000000000000000 : ℝ)*base66 + (580580719980144517/15850000000000000000000000000000 : ℝ)*base68 + (36104321943144517/15850000000000000000000000000000 : ℝ)*base70 + (103600035661494517/15850000000000000000000000000000 : ℝ)*base72 + (1644559338909/39625000000000000000000000 : ℝ)*base74 + (24594399660444517/15850000000000000000000000000000 : ℝ)*base76 + (128558739259244517/15850000000000000000000000000000 : ℝ)*base78 + (199955219335644517/15850000000000000000000000000000 : ℝ)*base80 + (27301182289/19812500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (31329441/5000000000000000000000 : ℝ)*base89 + (31329441/5000000000000000000000 : ℝ)*base91 + (31329441/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (59023/100000 : ℝ) ≤ (935561376751480848676373868789/1585000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (79196329/100000000000000 : ℝ)*(lower1) + (82543441/100000000000000 : ℝ)*(upper2) + (16419497/100000000000000 : ℝ)*(lower4) + (303747236853393/10000000000000 : ℝ)*(major0) + (303747236853393/10000000000000 : ℝ)*(major1) + (303747236853393/10000000000000 : ℝ)*(major2) + (1028242360316677/25000000000000 : ℝ)*(sp0) + (2056487221033027/50000000000000 : ℝ)*(sp1) + (411297001418359/10000000000000 : ℝ)*(sp2) + (485572463781877/25000000000000 : ℝ)*(sp3) + (1156341067/50000000000000 : ℝ)*(sp5) + (3370282299/50000000000000 : ℝ)*(sp6) + (561813819/20000000000000 : ℝ)*(sp7) + (7313481481/100000000000000 : ℝ)*(sp12) + (485573166049151/25000000000000 : ℝ)*(f.failure) + (1028244188687047/25000000000000 : ℝ)*(f.sum) + (864074831549/158500000000000000000000000 : ℝ)*base65 + (6656170601588737/3170000000000000000000000000000 : ℝ)*base67 + (5078668047061263/3170000000000000000000000000000 : ℝ)*base70 + (45658604943748737/3170000000000000000000000000000 : ℝ)*base71 + (1134518578727/317000000000000000000000000 : ℝ)*base73 + (297564767651263/3170000000000000000000000000000 : ℝ)*base76 + (27766992501148737/3170000000000000000000000000000 : ℝ)*base77 + (21690686104488737/3170000000000000000000000000000 : ℝ)*base79 + (198114730803/63400000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (4675587/1250000000000000000000 : ℝ)*base90 + (4675587/1250000000000000000000 : ℝ)*base92 + (4675587/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (80197/100000 : ℝ) ≤ (6355778034955393516161673045677/7925000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (78475493/50000000000000 : ℝ)*(upper1) + (46069227/10000000000000 : ℝ)*(upper2) + (208944547/100000000000000 : ℝ)*(upper3) + (18678197/100000000000000 : ℝ)*(lower5) + (3347695338347649/100000000000000 : ℝ)*(major0) + (3347695338347649/100000000000000 : ℝ)*(major1) + (3347695338347649/100000000000000 : ℝ)*(major2) + (166299486143/100000000000000 : ℝ)*(sp1) + (8832124747/12500000000000 : ℝ)*(sp2) + (45633785999/100000000000000 : ℝ)*(sp3) + (4527994848592559/100000000000000 : ℝ)*(sp8) + (4527828549106417/100000000000000 : ℝ)*(sp9) + (4527924191594583/100000000000000 : ℝ)*(sp10) + (1070308581837743/50000000000000 : ℝ)*(sp11) + (1070331398730743/50000000000000 : ℝ)*(f.failure) + (4527994848592559/100000000000000 : ℝ)*(f.sum) + (966804924109/158500000000000000000000000 : ℝ)*base65 + (283846827562201441/31700000000000000000000000000000 : ℝ)*base67 + (43826868037001441/31700000000000000000000000000000 : ℝ)*base69 + (175528610654298559/31700000000000000000000000000000 : ℝ)*base72 + (1153478096229/158500000000000000000000000 : ℝ)*base73 + (915441882209401441/31700000000000000000000000000000 : ℝ)*base75 + (215773047939101441/31700000000000000000000000000000 : ℝ)*base77 + (185229728443901441/31700000000000000000000000000000 : ℝ)*base79 + (3465709480691/317000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (9361509/2500000000000000000000 : ℝ)*base89 + (9361509/2500000000000000000000 : ℝ)*base91 + (9361509/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-42257/50000 : ℝ) ≤ (-3348781107364860147406889254293/3962500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5373477/20000000000000 : ℝ)*(lower0) + (59266283/100000000000000 : ℝ)*(lower1) + (4284021/10000000000000 : ℝ)*(lower2) + (37191339/100000000000000 : ℝ)*(lower3) + (1692324480362241/50000000000000 : ℝ)*(major0) + (1692324480362241/50000000000000 : ℝ)*(major1) + (1692324480362241/50000000000000 : ℝ)*(major2) + (713411293/800000000000 : ℝ)*(sp5) + (12253097841/25000000000000 : ℝ)*(sp6) + (2356587877/25000000000000 : ℝ)*(sp7) + (4633175970504691/100000000000000 : ℝ)*(sp12) + (926617358818613/20000000000000 : ℝ)*(sp13) + (4633126958113327/100000000000000 : ℝ)*(sp14) + (67633847914913/3125000000000 : ℝ)*(sp15) + (541073139907181/25000000000000 : ℝ)*(f.failure) + (4633175970504691/100000000000000 : ℝ)*(f.sum) + (1829294406403/317000000000000000000000000 : ℝ)*base66 + (22167730025026431/15850000000000000000000000000000 : ℝ)*base68 + (82553078712176431/15850000000000000000000000000000 : ℝ)*base70 + (154247774026023569/15850000000000000000000000000000 : ℝ)*base71 + (2050240152081/317000000000000000000000000 : ℝ)*base74 + (29931791454976431/15850000000000000000000000000000 : ℝ)*base76 + (128005706857176431/15850000000000000000000000000000 : ℝ)*base78 + (33804434016826431/15850000000000000000000000000000 : ℝ)*base80 + (817459487313/79250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (2367303/1250000000000000000000 : ℝ)*base89 + (2367303/1250000000000000000000 : ℝ)*base91 + (2367303/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1384_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78192963/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3683/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2249/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31437/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(59023/100000 : ℝ) else (80197/100000 : ℝ) ≤ X j i ∧ X j i ≤ (42257/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1384_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1384_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78192963/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7369/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11239/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31437/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(59023/100000 : ℝ) else (80197/100000 : ℝ) ≤ X j i ∧ X j i ≤ (42257/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1384_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1384_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1384_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4343/1024 : ℝ) ≤ p) (hpb : p ≤ (543/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78192963/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7369/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11239/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31437/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(59023/100000 : ℝ) else (80197/100000 : ℝ) ≤ X j i ∧ X j i ≤ (42257/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1384_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
