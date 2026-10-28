-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1117_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:08:05.239479+00:00
-- url     : https://prove2.me/submissions/a2da06a2-d50c-4a3a-8465-bb20dad66235

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
theorem support_rectangle_w1117_box_0 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-256396499/1250000000 : ℝ)*x 0 + (5376665581/10000000000 : ℝ)*x 1 + (5376665561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (256396499/1250000000 : ℝ)^4155 ≤ (12217741718651/100000000000000 : ℝ)^3131 := by
    have hnat : (256396499 : ℕ)^4155*100000000000000^3131 ≤ 12217741718651^3131*1250000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256396499 1250000000 12217741718651 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5376665581/10000000000 : ℝ)^4155 ≤ (43891129243271/100000000000000 : ℝ)^3131 := by
    have hnat : (5376665581 : ℕ)^4155*100000000000000^3131 ≤ 43891129243271^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376665581 10000000000 43891129243271 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5376665561/10000000000 : ℝ)^4155 ≤ (43891129026609/100000000000000 : ℝ)^3131 := by
    have hnat : (5376665561 : ℕ)^4155*100000000000000^3131 ≤ 43891129026609^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376665561 10000000000 43891129026609 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-256396499/1250000000 : ℝ), (5376665581/10000000000 : ℝ), (5376665561/10000000000 : ℝ)] ![(12217741718651/100000000000000 : ℝ), (43891129243271/100000000000000 : ℝ), (43891129026609/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-256396499/1250000000 : ℝ)|^4155 ≤ (12217741718651/100000000000000 : ℝ)^3131
        have hw : |(-256396499/1250000000 : ℝ)|=(256396499/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5376665581/10000000000 : ℝ)|^4155 ≤ (43891129243271/100000000000000 : ℝ)^3131
        have hw : |(5376665581/10000000000 : ℝ)|=(5376665581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5376665561/10000000000 : ℝ)|^4155 ≤ (43891129026609/100000000000000 : ℝ)^3131
        have hw : |(5376665561/10000000000 : ℝ)|=(5376665561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_box_1 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295743329/10000000000 : ℝ)*x 0 + (-2160852817/10000000000 : ℝ)*x 1 + (5376665831/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295743329/10000000000 : ℝ)^4155 ≤ (43016657422093/100000000000000 : ℝ)^3131 := by
    have hnat : (5295743329 : ℕ)^4155*100000000000000^3131 ≤ 43016657422093^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295743329 10000000000 43016657422093 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2160852817/10000000000 : ℝ)^4155 ≤ (1309221061497/10000000000000 : ℝ)^3131 := by
    have hnat : (2160852817 : ℕ)^4155*10000000000000^3131 ≤ 1309221061497^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2160852817 10000000000 1309221061497 10000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5376665831/10000000000 : ℝ)^4155 ≤ (43891131951539/100000000000000 : ℝ)^3131 := by
    have hnat : (5376665831 : ℕ)^4155*100000000000000^3131 ≤ 43891131951539^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376665831 10000000000 43891131951539 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295743329/10000000000 : ℝ), (-2160852817/10000000000 : ℝ), (5376665831/10000000000 : ℝ)] ![(43016657422093/100000000000000 : ℝ), (1309221061497/10000000000000 : ℝ), (43891131951539/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295743329/10000000000 : ℝ)|^4155 ≤ (43016657422093/100000000000000 : ℝ)^3131
        have hw : |(5295743329/10000000000 : ℝ)|=(5295743329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2160852817/10000000000 : ℝ)|^4155 ≤ (1309221061497/10000000000000 : ℝ)^3131
        have hw : |(-2160852817/10000000000 : ℝ)|=(2160852817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5376665831/10000000000 : ℝ)|^4155 ≤ (43891131951539/100000000000000 : ℝ)^3131
        have hw : |(5376665831/10000000000 : ℝ)|=(5376665831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_box_2 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295743299/10000000000 : ℝ)*x 0 + (5376665861/10000000000 : ℝ)*x 1 + (-432170563/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295743299/10000000000 : ℝ)^4155 ≤ (10754164274677/25000000000000 : ℝ)^3131 := by
    have hnat : (5295743299 : ℕ)^4155*25000000000000^3131 ≤ 10754164274677^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295743299 10000000000 10754164274677 25000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5376665861/10000000000 : ℝ)^4155 ≤ (43891132276531/100000000000000 : ℝ)^3131 := by
    have hnat : (5376665861 : ℕ)^4155*100000000000000^3131 ≤ 43891132276531^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376665861 10000000000 43891132276531 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (432170563/2000000000 : ℝ)^4155 ≤ (1309221059889/10000000000000 : ℝ)^3131 := by
    have hnat : (432170563 : ℕ)^4155*10000000000000^3131 ≤ 1309221059889^3131*2000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432170563 2000000000 1309221059889 10000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295743299/10000000000 : ℝ), (5376665861/10000000000 : ℝ), (-432170563/2000000000 : ℝ)] ![(10754164274677/25000000000000 : ℝ), (43891132276531/100000000000000 : ℝ), (1309221059889/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295743299/10000000000 : ℝ)|^4155 ≤ (10754164274677/25000000000000 : ℝ)^3131
        have hw : |(5295743299/10000000000 : ℝ)|=(5295743299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5376665861/10000000000 : ℝ)|^4155 ≤ (43891132276531/100000000000000 : ℝ)^3131
        have hw : |(5376665861/10000000000 : ℝ)|=(5376665861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-432170563/2000000000 : ℝ)|^4155 ≤ (1309221059889/10000000000000 : ℝ)^3131
        have hw : |(-432170563/2000000000 : ℝ)|=(432170563/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_box_3 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (279751759/625000000 : ℝ)*x 0 + (2158212897/5000000000 : ℝ)*x 1 + (2158212677/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (279751759/625000000 : ℝ)^4155 ≤ (17206264185777/50000000000000 : ℝ)^3131 := by
    have hnat : (279751759 : ℕ)^4155*50000000000000^3131 ≤ 17206264185777^3131*625000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      279751759 625000000 17206264185777 50000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2158212897/5000000000 : ℝ)^4155 ≤ (32793738024423/100000000000000 : ℝ)^3131 := by
    have hnat : (2158212897 : ℕ)^4155*100000000000000^3131 ≤ 32793738024423^3131*5000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158212897 5000000000 32793738024423 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2158212677/5000000000 : ℝ)^4155 ≤ (32793733588263/100000000000000 : ℝ)^3131 := by
    have hnat : (2158212677 : ℕ)^4155*100000000000000^3131 ≤ 32793733588263^3131*5000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158212677 5000000000 32793733588263 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(279751759/625000000 : ℝ), (2158212897/5000000000 : ℝ), (2158212677/5000000000 : ℝ)] ![(17206264185777/50000000000000 : ℝ), (32793738024423/100000000000000 : ℝ), (32793733588263/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(279751759/625000000 : ℝ)|^4155 ≤ (17206264185777/50000000000000 : ℝ)^3131
        have hw : |(279751759/625000000 : ℝ)|=(279751759/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2158212897/5000000000 : ℝ)|^4155 ≤ (32793738024423/100000000000000 : ℝ)^3131
        have hw : |(2158212897/5000000000 : ℝ)|=(2158212897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2158212677/5000000000 : ℝ)|^4155 ≤ (32793733588263/100000000000000 : ℝ)^3131
        have hw : |(2158212677/5000000000 : ℝ)|=(2158212677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_box_4 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2308016209/10000000000 : ℝ)*x 0 + (5280811857/10000000000 : ℝ)*x 1 + (5280812203/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2308016209/10000000000 : ℝ)^4155 ≤ (1786054977993/12500000000000 : ℝ)^3131 := by
    have hnat : (2308016209 : ℕ)^4155*12500000000000^3131 ≤ 1786054977993^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2308016209 10000000000 1786054977993 12500000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5280811857/10000000000 : ℝ)^4155 ≤ (42855778218937/100000000000000 : ℝ)^3131 := by
    have hnat : (5280811857 : ℕ)^4155*100000000000000^3131 ≤ 42855778218937^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280811857 10000000000 42855778218937 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5280812203/10000000000 : ℝ)^4155 ≤ (21427890972597/50000000000000 : ℝ)^3131 := by
    have hnat : (5280812203 : ℕ)^4155*50000000000000^3131 ≤ 21427890972597^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280812203 10000000000 21427890972597 50000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2308016209/10000000000 : ℝ), (5280811857/10000000000 : ℝ), (5280812203/10000000000 : ℝ)] ![(1786054977993/12500000000000 : ℝ), (42855778218937/100000000000000 : ℝ), (21427890972597/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2308016209/10000000000 : ℝ)|^4155 ≤ (1786054977993/12500000000000 : ℝ)^3131
        have hw : |(-2308016209/10000000000 : ℝ)|=(2308016209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5280811857/10000000000 : ℝ)|^4155 ≤ (42855778218937/100000000000000 : ℝ)^3131
        have hw : |(5280811857/10000000000 : ℝ)|=(5280811857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5280812203/10000000000 : ℝ)|^4155 ≤ (21427890972597/50000000000000 : ℝ)^3131
        have hw : |(5280812203/10000000000 : ℝ)|=(5280812203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_box_5 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (536350217/1000000000 : ℝ)*x 0 + (-439696719/2000000000 : ℝ)*x 1 + (5280811997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536350217/1000000000 : ℝ)^4155 ≤ (1093714654149/2500000000000 : ℝ)^3131 := by
    have hnat : (536350217 : ℕ)^4155*2500000000000^3131 ≤ 1093714654149^3131*1000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536350217 1000000000 1093714654149 2500000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (439696719/2000000000 : ℝ)^4155 ≤ (3348908523663/25000000000000 : ℝ)^3131 := by
    have hnat : (439696719 : ℕ)^4155*25000000000000^3131 ≤ 3348908523663^3131*2000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      439696719 2000000000 3348908523663 25000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5280811997/10000000000 : ℝ)^4155 ≤ (42855779726671/100000000000000 : ℝ)^3131 := by
    have hnat : (5280811997 : ℕ)^4155*100000000000000^3131 ≤ 42855779726671^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280811997 10000000000 42855779726671 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(536350217/1000000000 : ℝ), (-439696719/2000000000 : ℝ), (5280811997/10000000000 : ℝ)] ![(1093714654149/2500000000000 : ℝ), (3348908523663/25000000000000 : ℝ), (42855779726671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(536350217/1000000000 : ℝ)|^4155 ≤ (1093714654149/2500000000000 : ℝ)^3131
        have hw : |(536350217/1000000000 : ℝ)|=(536350217/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-439696719/2000000000 : ℝ)|^4155 ≤ (3348908523663/25000000000000 : ℝ)^3131
        have hw : |(-439696719/2000000000 : ℝ)|=(439696719/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5280811997/10000000000 : ℝ)|^4155 ≤ (42855779726671/100000000000000 : ℝ)^3131
        have hw : |(5280811997/10000000000 : ℝ)|=(5280811997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_box_6 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5363501697/10000000000 : ℝ)*x 0 + (1320203041/2500000000 : ℝ)*x 1 + (-439696801/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5363501697/10000000000 : ℝ)^4155 ≤ (43748581046023/100000000000000 : ℝ)^3131 := by
    have hnat : (5363501697 : ℕ)^4155*100000000000000^3131 ≤ 43748581046023^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363501697 10000000000 43748581046023 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1320203041/2500000000 : ℝ)^4155 ≤ (21427890762591/50000000000000 : ℝ)^3131 := by
    have hnat : (1320203041 : ℕ)^4155*50000000000000^3131 ≤ 21427890762591^3131*2500000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320203041 2500000000 21427890762591 50000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (439696801/2000000000 : ℝ)^4155 ≤ (13395637409869/100000000000000 : ℝ)^3131 := by
    have hnat : (439696801 : ℕ)^4155*100000000000000^3131 ≤ 13395637409869^3131*2000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      439696801 2000000000 13395637409869 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5363501697/10000000000 : ℝ), (1320203041/2500000000 : ℝ), (-439696801/2000000000 : ℝ)] ![(43748581046023/100000000000000 : ℝ), (21427890762591/50000000000000 : ℝ), (13395637409869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5363501697/10000000000 : ℝ)|^4155 ≤ (43748581046023/100000000000000 : ℝ)^3131
        have hw : |(5363501697/10000000000 : ℝ)|=(5363501697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1320203041/2500000000 : ℝ)|^4155 ≤ (21427890762591/50000000000000 : ℝ)^3131
        have hw : |(1320203041/2500000000 : ℝ)|=(1320203041/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-439696801/2000000000 : ℝ)|^4155 ≤ (13395637409869/100000000000000 : ℝ)^3131
        have hw : |(-439696801/2000000000 : ℝ)|=(439696801/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_box_7 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2130019691/5000000000 : ℝ)*x 0 + (2212199307/5000000000 : ℝ)*x 1 + (1106099803/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2130019691/5000000000 : ℝ)^4155 ≤ (16113228926611/50000000000000 : ℝ)^3131 := by
    have hnat : (2130019691 : ℕ)^4155*50000000000000^3131 ≤ 16113228926611^3131*5000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2130019691 5000000000 16113228926611 50000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2212199307/5000000000 : ℝ)^4155 ≤ (1058961500943/3125000000000 : ℝ)^3131 := by
    have hnat : (2212199307 : ℕ)^4155*3125000000000^3131 ≤ 1058961500943^3131*5000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2212199307 5000000000 1058961500943 3125000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1106099803/2500000000 : ℝ)^4155 ≤ (33886774108237/100000000000000 : ℝ)^3131 := by
    have hnat : (1106099803 : ℕ)^4155*100000000000000^3131 ≤ 33886774108237^3131*2500000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1106099803 2500000000 33886774108237 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2130019691/5000000000 : ℝ), (2212199307/5000000000 : ℝ), (1106099803/2500000000 : ℝ)] ![(16113228926611/50000000000000 : ℝ), (1058961500943/3125000000000 : ℝ), (33886774108237/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2130019691/5000000000 : ℝ)|^4155 ≤ (16113228926611/50000000000000 : ℝ)^3131
        have hw : |(2130019691/5000000000 : ℝ)|=(2130019691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2212199307/5000000000 : ℝ)|^4155 ≤ (1058961500943/3125000000000 : ℝ)^3131
        have hw : |(2212199307/5000000000 : ℝ)|=(2212199307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1106099803/2500000000 : ℝ)|^4155 ≤ (33886774108237/100000000000000 : ℝ)^3131
        have hw : |(1106099803/2500000000 : ℝ)|=(1106099803/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_box_8 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-112716779/500000000 : ℝ)*x 0 + (2607835171/5000000000 : ℝ)*x 1 + (5386272599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (112716779/500000000 : ℝ)^4155 ≤ (13849112863447/100000000000000 : ℝ)^3131 := by
    have hnat : (112716779 : ℕ)^4155*100000000000000^3131 ≤ 13849112863447^3131*500000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112716779 500000000 13849112863447 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2607835171/5000000000 : ℝ)^4155 ≤ (21077826975977/50000000000000 : ℝ)^3131 := by
    have hnat : (2607835171 : ℕ)^4155*50000000000000^3131 ≤ 21077826975977^3131*5000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607835171 5000000000 21077826975977 50000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5386272599/10000000000 : ℝ)^4155 ≤ (21997616586173/50000000000000 : ℝ)^3131 := by
    have hnat : (5386272599 : ℕ)^4155*50000000000000^3131 ≤ 21997616586173^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386272599 10000000000 21997616586173 50000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-112716779/500000000 : ℝ), (2607835171/5000000000 : ℝ), (5386272599/10000000000 : ℝ)] ![(13849112863447/100000000000000 : ℝ), (21077826975977/50000000000000 : ℝ), (21997616586173/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-112716779/500000000 : ℝ)|^4155 ≤ (13849112863447/100000000000000 : ℝ)^3131
        have hw : |(-112716779/500000000 : ℝ)|=(112716779/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2607835171/5000000000 : ℝ)|^4155 ≤ (21077826975977/50000000000000 : ℝ)^3131
        have hw : |(2607835171/5000000000 : ℝ)|=(2607835171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5386272599/10000000000 : ℝ)|^4155 ≤ (21997616586173/50000000000000 : ℝ)^3131
        have hw : |(5386272599/10000000000 : ℝ)|=(5386272599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_box_9 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5288948767/10000000000 : ℝ)*x 0 + (-1078505893/5000000000 : ℝ)*x 1 + (1346568139/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288948767/10000000000 : ℝ)^4155 ≤ (21471715483927/50000000000000 : ℝ)^3131 := by
    have hnat : (5288948767 : ℕ)^4155*50000000000000^3131 ≤ 21471715483927^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288948767 10000000000 21471715483927 50000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078505893/5000000000 : ℝ)^4155 ≤ (2612267260979/20000000000000 : ℝ)^3131 := by
    have hnat : (1078505893 : ℕ)^4155*20000000000000^3131 ≤ 2612267260979^3131*5000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078505893 5000000000 2612267260979 20000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1346568139/2500000000 : ℝ)^4155 ≤ (10998808176563/25000000000000 : ℝ)^3131 := by
    have hnat : (1346568139 : ℕ)^4155*25000000000000^3131 ≤ 10998808176563^3131*2500000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346568139 2500000000 10998808176563 25000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288948767/10000000000 : ℝ), (-1078505893/5000000000 : ℝ), (1346568139/2500000000 : ℝ)] ![(21471715483927/50000000000000 : ℝ), (2612267260979/20000000000000 : ℝ), (10998808176563/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288948767/10000000000 : ℝ)|^4155 ≤ (21471715483927/50000000000000 : ℝ)^3131
        have hw : |(5288948767/10000000000 : ℝ)|=(5288948767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1078505893/5000000000 : ℝ)|^4155 ≤ (2612267260979/20000000000000 : ℝ)^3131
        have hw : |(-1078505893/5000000000 : ℝ)|=(1078505893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1346568139/2500000000 : ℝ)|^4155 ≤ (10998808176563/25000000000000 : ℝ)^3131
        have hw : |(1346568139/2500000000 : ℝ)|=(1346568139/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_box_10 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5288948783/10000000000 : ℝ)*x 0 + (5386272577/10000000000 : ℝ)*x 1 + (-269626467/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288948783/10000000000 : ℝ)^4155 ≤ (42943431140253/100000000000000 : ℝ)^3131 := by
    have hnat : (5288948783 : ℕ)^4155*100000000000000^3131 ≤ 42943431140253^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288948783 10000000000 42943431140253 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5386272577/10000000000 : ℝ)^4155 ≤ (43995232933879/100000000000000 : ℝ)^3131 := by
    have hnat : (5386272577 : ℕ)^4155*100000000000000^3131 ≤ 43995232933879^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386272577 10000000000 43995232933879 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269626467/1250000000 : ℝ)^4155 ≤ (13061335903111/100000000000000 : ℝ)^3131 := by
    have hnat : (269626467 : ℕ)^4155*100000000000000^3131 ≤ 13061335903111^3131*1250000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269626467 1250000000 13061335903111 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288948783/10000000000 : ℝ), (5386272577/10000000000 : ℝ), (-269626467/1250000000 : ℝ)] ![(42943431140253/100000000000000 : ℝ), (43995232933879/100000000000000 : ℝ), (13061335903111/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288948783/10000000000 : ℝ)|^4155 ≤ (42943431140253/100000000000000 : ℝ)^3131
        have hw : |(5288948783/10000000000 : ℝ)|=(5288948783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5386272577/10000000000 : ℝ)|^4155 ≤ (43995232933879/100000000000000 : ℝ)^3131
        have hw : |(5386272577/10000000000 : ℝ)|=(5386272577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-269626467/1250000000 : ℝ)|^4155 ≤ (13061335903111/100000000000000 : ℝ)^3131
        have hw : |(-269626467/1250000000 : ℝ)|=(269626467/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_box_11 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4497402379/10000000000 : ℝ)*x 0 + (269099867/625000000 : ℝ)*x 1 + (2152798977/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4497402379/10000000000 : ℝ)^4155 ≤ (8657692921909/25000000000000 : ℝ)^3131 := by
    have hnat : (4497402379 : ℕ)^4155*25000000000000^3131 ≤ 8657692921909^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4497402379 10000000000 8657692921909 25000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269099867/625000000 : ℝ)^4155 ≤ (16342306866909/50000000000000 : ℝ)^3131 := by
    have hnat : (269099867 : ℕ)^4155*50000000000000^3131 ≤ 16342306866909^3131*625000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269099867 625000000 16342306866909 50000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2152798977/5000000000 : ℝ)^4155 ≤ (32684614559879/100000000000000 : ℝ)^3131 := by
    have hnat : (2152798977 : ℕ)^4155*100000000000000^3131 ≤ 32684614559879^3131*5000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2152798977 5000000000 32684614559879 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4497402379/10000000000 : ℝ), (269099867/625000000 : ℝ), (2152798977/5000000000 : ℝ)] ![(8657692921909/25000000000000 : ℝ), (16342306866909/50000000000000 : ℝ), (32684614559879/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4497402379/10000000000 : ℝ)|^4155 ≤ (8657692921909/25000000000000 : ℝ)^3131
        have hw : |(4497402379/10000000000 : ℝ)|=(4497402379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269099867/625000000 : ℝ)|^4155 ≤ (16342306866909/50000000000000 : ℝ)^3131
        have hw : |(269099867/625000000 : ℝ)|=(269099867/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2152798977/5000000000 : ℝ)|^4155 ≤ (32684614559879/100000000000000 : ℝ)^3131
        have hw : |(2152798977/5000000000 : ℝ)|=(2152798977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_box_12 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1052593807/5000000000 : ℝ)*x 0 + (2720255279/5000000000 : ℝ)*x 1 + (5272785113/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1052593807/5000000000 : ℝ)^4155 ≤ (12646538493289/100000000000000 : ℝ)^3131 := by
    have hnat : (1052593807 : ℕ)^4155*100000000000000^3131 ≤ 12646538493289^3131*5000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052593807 5000000000 12646538493289 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2720255279/5000000000 : ℝ)^4155 ≤ (44584106022083/100000000000000 : ℝ)^3131 := by
    have hnat : (2720255279 : ℕ)^4155*100000000000000^3131 ≤ 44584106022083^3131*5000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2720255279 5000000000 44584106022083 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5272785113/10000000000 : ℝ)^4155 ≤ (2138467773597/5000000000000 : ℝ)^3131 := by
    have hnat : (5272785113 : ℕ)^4155*5000000000000^3131 ≤ 2138467773597^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5272785113 10000000000 2138467773597 5000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1052593807/5000000000 : ℝ), (2720255279/5000000000 : ℝ), (5272785113/10000000000 : ℝ)] ![(12646538493289/100000000000000 : ℝ), (44584106022083/100000000000000 : ℝ), (2138467773597/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1052593807/5000000000 : ℝ)|^4155 ≤ (12646538493289/100000000000000 : ℝ)^3131
        have hw : |(-1052593807/5000000000 : ℝ)|=(1052593807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2720255279/5000000000 : ℝ)|^4155 ≤ (44584106022083/100000000000000 : ℝ)^3131
        have hw : |(2720255279/5000000000 : ℝ)|=(2720255279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5272785113/10000000000 : ℝ)|^4155 ≤ (2138467773597/5000000000000 : ℝ)^3131
        have hw : |(5272785113/10000000000 : ℝ)|=(5272785113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_box_13 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5369174671/10000000000 : ℝ)*x 0 + (-2201576937/10000000000 : ℝ)*x 1 + (5272784563/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369174671/10000000000 : ℝ)^4155 ≤ (21904999079283/50000000000000 : ℝ)^3131 := by
    have hnat : (5369174671 : ℕ)^4155*50000000000000^3131 ≤ 21904999079283^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369174671 10000000000 21904999079283 50000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2201576937/10000000000 : ℝ)^4155 ≤ (13420652281289/100000000000000 : ℝ)^3131 := by
    have hnat : (2201576937 : ℕ)^4155*100000000000000^3131 ≤ 13420652281289^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2201576937 10000000000 13420652281289 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5272784563/10000000000 : ℝ)^4155 ≤ (21384674775823/50000000000000 : ℝ)^3131 := by
    have hnat : (5272784563 : ℕ)^4155*50000000000000^3131 ≤ 21384674775823^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5272784563 10000000000 21384674775823 50000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369174671/10000000000 : ℝ), (-2201576937/10000000000 : ℝ), (5272784563/10000000000 : ℝ)] ![(21904999079283/50000000000000 : ℝ), (13420652281289/100000000000000 : ℝ), (21384674775823/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369174671/10000000000 : ℝ)|^4155 ≤ (21904999079283/50000000000000 : ℝ)^3131
        have hw : |(5369174671/10000000000 : ℝ)|=(5369174671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2201576937/10000000000 : ℝ)|^4155 ≤ (13420652281289/100000000000000 : ℝ)^3131
        have hw : |(-2201576937/10000000000 : ℝ)|=(2201576937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5272784563/10000000000 : ℝ)|^4155 ≤ (21384674775823/50000000000000 : ℝ)^3131
        have hw : |(5272784563/10000000000 : ℝ)|=(5272784563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_box_14 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2684587289/5000000000 : ℝ)*x 0 + (1318196107/2500000000 : ℝ)*x 1 + (-55039431/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684587289/5000000000 : ℝ)^4155 ≤ (43809997151549/100000000000000 : ℝ)^3131 := by
    have hnat : (2684587289 : ℕ)^4155*100000000000000^3131 ≤ 43809997151549^3131*5000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684587289 5000000000 43809997151549 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1318196107/2500000000 : ℝ)^4155 ≤ (42769348098483/100000000000000 : ℝ)^3131 := by
    have hnat : (1318196107 : ℕ)^4155*100000000000000^3131 ≤ 42769348098483^3131*2500000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318196107 2500000000 42769348098483 100000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (55039431/250000000 : ℝ)^4155 ≤ (6710327366221/50000000000000 : ℝ)^3131 := by
    have hnat : (55039431 : ℕ)^4155*50000000000000^3131 ≤ 6710327366221^3131*250000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55039431 250000000 6710327366221 50000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684587289/5000000000 : ℝ), (1318196107/2500000000 : ℝ), (-55039431/250000000 : ℝ)] ![(43809997151549/100000000000000 : ℝ), (42769348098483/100000000000000 : ℝ), (6710327366221/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684587289/5000000000 : ℝ)|^4155 ≤ (43809997151549/100000000000000 : ℝ)^3131
        have hw : |(2684587289/5000000000 : ℝ)|=(2684587289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1318196107/2500000000 : ℝ)|^4155 ≤ (42769348098483/100000000000000 : ℝ)^3131
        have hw : |(1318196107/2500000000 : ℝ)|=(1318196107/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-55039431/250000000 : ℝ)|^4155 ≤ (6710327366221/50000000000000 : ℝ)^3131
        have hw : |(-55039431/250000000 : ℝ)|=(55039431/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1117_box_15 (p : ℝ) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (132553791/312500000 : ℝ)*x 0 + (4433436033/10000000000 : ℝ)*x 1 + (4433435699/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132553791/312500000 : ℝ)^4155 ≤ (2002668354777/6250000000000 : ℝ)^3131 := by
    have hnat : (132553791 : ℕ)^4155*6250000000000^3131 ≤ 2002668354777^3131*312500000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132553791 312500000 2002668354777 6250000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4433436033/10000000000 : ℝ)^4155 ≤ (849466371427/2500000000000 : ℝ)^3131 := by
    have hnat : (4433436033 : ℕ)^4155*2500000000000^3131 ≤ 849466371427^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4433436033 10000000000 849466371427 2500000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4433435699/10000000000 : ℝ)^4155 ≤ (8494662865011/25000000000000 : ℝ)^3131 := by
    have hnat : (4433435699 : ℕ)^4155*25000000000000^3131 ≤ 8494662865011^3131*10000000000^4155 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4433435699 10000000000 8494662865011 25000000000000 4155 3131 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4155/1024 : ℝ)) 4155 3131 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132553791/312500000 : ℝ), (4433436033/10000000000 : ℝ), (4433435699/10000000000 : ℝ)] ![(2002668354777/6250000000000 : ℝ), (849466371427/2500000000000 : ℝ), (8494662865011/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132553791/312500000 : ℝ)|^4155 ≤ (2002668354777/6250000000000 : ℝ)^3131
        have hw : |(132553791/312500000 : ℝ)|=(132553791/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4433436033/10000000000 : ℝ)|^4155 ≤ (849466371427/2500000000000 : ℝ)^3131
        have hw : |(4433436033/10000000000 : ℝ)|=(4433436033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4433435699/10000000000 : ℝ)|^4155 ≤ (8494662865011/25000000000000 : ℝ)^3131
        have hw : |(4433435699/10000000000 : ℝ)|=(4433435699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1117_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74493081/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7017/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11321/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(15557/25000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59279/100000 : ℝ) ∧ (79731/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (20767/25000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7017/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11321/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7017/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11321/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7017/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11321/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7017/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11321/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7017/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11321/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7017/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11321/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11321/100000 : ℝ) ^ (8309/2048 : ℝ) ≤ (906501760383363/6250000000000000000 : ℝ) := by
    have hpowers : (11321/100000 : ℝ)^8309 ≤ (906501760383363/6250000000000000000 : ℝ)^2048 := by
      have hnat : (11321 : ℕ)^8309*6250000000000000000^2048 ≤ 906501760383363^2048*100000^8309 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11321 100000 906501760383363 6250000000000000000 8309 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11321/100000 : ℝ)) (X := (906501760383363/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 8309 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7017/50000 : ℝ) ^ (8309/2048 : ℝ) ≤ (6934821623819623/20000000000000000000 : ℝ) := by
    have hpowers : (7017/50000 : ℝ)^8309 ≤ (6934821623819623/20000000000000000000 : ℝ)^2048 := by
      have hnat : (7017 : ℕ)^8309*20000000000000000000^2048 ≤ 6934821623819623^2048*50000^8309 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7017 50000 6934821623819623 20000000000000000000 8309 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7017/50000 : ℝ)) (X := (6934821623819623/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8309 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125906501760383363/3125000000000000000 : ℝ) ≤ (10000714911633977/10000000000000000 : ℝ) ^ (8309/2048 : ℝ) := by
    have hpowers : (3125906501760383363/3125000000000000000 : ℝ)^2048 ≤ (10000714911633977/10000000000000000 : ℝ)^8309 := by
      have hnat : (3125906501760383363 : ℕ)^2048*10000000000000000^8309 ≤ 10000714911633977^8309*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125906501760383363 3125000000000000000 10000714911633977 10000000000000000 2048 8309 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000714911633977/10000000000000000 : ℝ)) (X := (3125906501760383363/3125000000000000000 : ℝ)) (by norm_num) 8309 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100049178136285231923/100000000000000000000 : ℝ) ≤ (10001211916804639/10000000000000000 : ℝ) ^ (8309/2048 : ℝ) := by
    have hpowers : (100049178136285231923/100000000000000000000 : ℝ)^2048 ≤ (10001211916804639/10000000000000000 : ℝ)^8309 := by
      have hnat : (100049178136285231923 : ℕ)^2048*10000000000000000^8309 ≤ 10001211916804639^8309*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100049178136285231923 100000000000000000000 10001211916804639 10000000000000000 2048 8309 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001211916804639/10000000000000000 : ℝ)) (X := (100049178136285231923/100000000000000000000 : ℝ)) (by norm_num) 8309 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006934821623819623/10000000000000000000 : ℝ) ≤ (10001708921975301/10000000000000000 : ℝ) ^ (8309/2048 : ℝ) := by
    have hpowers : (10006934821623819623/10000000000000000000 : ℝ)^2048 ≤ (10001708921975301/10000000000000000 : ℝ)^8309 := by
      have hnat : (10006934821623819623 : ℕ)^2048*10000000000000000^8309 ≤ 10001708921975301^8309*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006934821623819623 10000000000000000000 10001708921975301 10000000000000000 2048 8309 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001708921975301/10000000000000000 : ℝ)) (X := (10006934821623819623/10000000000000000000 : ℝ)) (by norm_num) 8309 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(906501760383363/6250000000000000000 : ℝ) ≤ ((27120686364188850597/27130000000000000000 : ℝ)+2*(248502585331/135650000000000 : ℝ)*(11321/100000 : ℝ))^(8309/2048 : ℝ) := by
    rw [show (27120686364188850597/27130000000000000000 : ℝ)+2*(248502585331/135650000000000 : ℝ)*(11321/100000 : ℝ)=(10000714911633977/10000000000000000 : ℝ) by norm_num, show 1+2*(906501760383363/6250000000000000000 : ℝ)=(3125906501760383363/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6934821623819623/20000000000000000000 : ℝ)+(906501760383363/6250000000000000000 : ℝ) ≤ ((27120686364188850597/27130000000000000000 : ℝ)+(248502585331/135650000000000 : ℝ)*((7017/50000 : ℝ)+(11321/100000 : ℝ)))^(8309/2048 : ℝ) := by
    rw [show (27120686364188850597/27130000000000000000 : ℝ)+(248502585331/135650000000000 : ℝ)*((7017/50000 : ℝ)+(11321/100000 : ℝ))=(10001211916804639/10000000000000000 : ℝ) by norm_num, show 1+(6934821623819623/20000000000000000000 : ℝ)+(906501760383363/6250000000000000000 : ℝ)=(100049178136285231923/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6934821623819623/20000000000000000000 : ℝ) ≤ ((27120686364188850597/27130000000000000000 : ℝ)+2*(248502585331/135650000000000 : ℝ)*(7017/50000 : ℝ))^(8309/2048 : ℝ) := by
    rw [show (27120686364188850597/27130000000000000000 : ℝ)+2*(248502585331/135650000000000 : ℝ)*(7017/50000 : ℝ)=(10001708921975301/10000000000000000 : ℝ) by norm_num, show 1+2*(6934821623819623/20000000000000000000 : ℝ)=(10006934821623819623/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27120686364188850597/27130000000000000000 : ℝ)*(X 1 0+X 2 0)+(248502585331/135650000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8309/2048 : ℝ)) (lo := (11321/100000 : ℝ)) (hi := (7017/50000 : ℝ)) (c := (27120686364188850597/27130000000000000000 : ℝ)) (alpha := (248502585331/135650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27120686364188850597/27130000000000000000 : ℝ)*(X 0 1+X 2 1)+(248502585331/135650000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8309/2048 : ℝ)) (lo := (11321/100000 : ℝ)) (hi := (7017/50000 : ℝ)) (c := (27120686364188850597/27130000000000000000 : ℝ)) (alpha := (248502585331/135650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27120686364188850597/27130000000000000000 : ℝ)*(X 0 2+X 1 2)+(248502585331/135650000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8309/2048 : ℝ)) (lo := (11321/100000 : ℝ)) (hi := (7017/50000 : ℝ)) (c := (27120686364188850597/27130000000000000000 : ℝ)) (alpha := (248502585331/135650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-256396499/1250000000 : ℝ)*X 0 0+(5376665581/10000000000 : ℝ)*X 0 1+(5376665561/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5295743329/10000000000 : ℝ)*X 1 0+(-2160852817/10000000000 : ℝ)*X 1 1+(5376665831/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5295743299/10000000000 : ℝ)*X 2 0+(5376665861/10000000000 : ℝ)*X 2 1+(-432170563/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((279751759/625000000 : ℝ)*X 0 0+(2158212897/5000000000 : ℝ)*X 0 1+(2158212677/5000000000 : ℝ)*X 0 2+(279751759/625000000 : ℝ)*X 1 0+(2158212897/5000000000 : ℝ)*X 1 1+(2158212677/5000000000 : ℝ)*X 1 2+(279751759/625000000 : ℝ)*X 2 0+(2158212897/5000000000 : ℝ)*X 2 1+(2158212677/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2308016209/10000000000 : ℝ)*X 0 0+(5280811857/10000000000 : ℝ)*X 0 1+(5280812203/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((536350217/1000000000 : ℝ)*X 1 0+(-439696719/2000000000 : ℝ)*X 1 1+(5280811997/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5363501697/10000000000 : ℝ)*X 2 0+(1320203041/2500000000 : ℝ)*X 2 1+(-439696801/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2130019691/5000000000 : ℝ)*X 0 0+(2212199307/5000000000 : ℝ)*X 0 1+(1106099803/2500000000 : ℝ)*X 0 2+(2130019691/5000000000 : ℝ)*X 1 0+(2212199307/5000000000 : ℝ)*X 1 1+(1106099803/2500000000 : ℝ)*X 1 2+(2130019691/5000000000 : ℝ)*X 2 0+(2212199307/5000000000 : ℝ)*X 2 1+(1106099803/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-112716779/500000000 : ℝ)*X 0 0+(2607835171/5000000000 : ℝ)*X 0 1+(5386272599/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5288948767/10000000000 : ℝ)*X 1 0+(-1078505893/5000000000 : ℝ)*X 1 1+(1346568139/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5288948783/10000000000 : ℝ)*X 2 0+(5386272577/10000000000 : ℝ)*X 2 1+(-269626467/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4497402379/10000000000 : ℝ)*X 0 0+(269099867/625000000 : ℝ)*X 0 1+(2152798977/5000000000 : ℝ)*X 0 2+(4497402379/10000000000 : ℝ)*X 1 0+(269099867/625000000 : ℝ)*X 1 1+(2152798977/5000000000 : ℝ)*X 1 2+(4497402379/10000000000 : ℝ)*X 2 0+(269099867/625000000 : ℝ)*X 2 1+(2152798977/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1052593807/5000000000 : ℝ)*X 0 0+(2720255279/5000000000 : ℝ)*X 0 1+(5272785113/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5369174671/10000000000 : ℝ)*X 1 0+(-2201576937/10000000000 : ℝ)*X 1 1+(5272784563/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2684587289/5000000000 : ℝ)*X 2 0+(1318196107/2500000000 : ℝ)*X 2 1+(-55039431/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((132553791/312500000 : ℝ)*X 0 0+(4433436033/10000000000 : ℝ)*X 0 1+(4433435699/10000000000 : ℝ)*X 0 2+(132553791/312500000 : ℝ)*X 1 0+(4433436033/10000000000 : ℝ)*X 1 1+(4433435699/10000000000 : ℝ)*X 1 2+(132553791/312500000 : ℝ)*X 2 0+(4433436033/10000000000 : ℝ)*X 2 1+(4433435699/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1117_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-15557/25000 : ℝ) ≤ (-844095232061315372178884666473359/1356500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (113196211/50000000000000 : ℝ)*(upper1) + (231837241/50000000000000 : ℝ)*(lower4) + (1158387/400000000000 : ℝ)*(upper5) + (3899435634476117/100000000000000 : ℝ)*(major0) + (3899435634476117/100000000000000 : ℝ)*(major1) + (3899435634476117/100000000000000 : ℝ)*(major2) + (193878859/1000000000000 : ℝ)*(sp2) + (5792128931/25000000000000 : ℝ)*(sp3) + (2601147890956809/50000000000000 : ℝ)*(sp4) + (5202147260063257/100000000000000 : ℝ)*(sp5) + (5202279897743869/100000000000000 : ℝ)*(sp6) + (2617290803553787/100000000000000 : ℝ)*(sp7) + (3503716151/100000000000000 : ℝ)*(sp12) + (9501597907/6250000000000 : ℝ)*(sp13) + (327164246508689/12500000000000 : ℝ)*(f.failure) + (5202299285629769/100000000000000 : ℝ)*(f.sum) + (4147268041307/1695625000000000000000000000 : ℝ)*base66 + (4415498452630908151/2713000000000000000000000000000000 : ℝ)*base68 + (243977984017908151/2713000000000000000000000000000000 : ℝ)*base70 + (29656529266692908151/2713000000000000000000000000000000 : ℝ)*base72 + (37048601304979/13565000000000000000000000000 : ℝ)*base73 + (28869133901201908151/2713000000000000000000000000000000 : ℝ)*base76 + (4266768333555908151/2713000000000000000000000000000000 : ℝ)*base78 + (13178736778946908151/2713000000000000000000000000000000 : ℝ)*base80 + (61116215192221/13565000000000000000000000000 : ℝ)*base82 + (5630809/625000000000000000000 : ℝ)*base89 + (5630809/625000000000000000000 : ℝ)*base91 + (5630809/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (59279/100000 : ℝ) ≤ (8041560102576526590472138509/13565000000000000000000000000 : ℝ) := by norm_num
    linear_combination (32315683/100000000000000 : ℝ)*(lower0) + (6354519/25000000000000 : ℝ)*(upper3) + (50142217/100000000000000 : ℝ)*(upper4) + (94850587/100000000000000 : ℝ)*(lower5) + (495398024759377/12500000000000 : ℝ)*(major0) + (495398024759377/12500000000000 : ℝ)*(major1) + (495398024759377/12500000000000 : ℝ)*(major2) + (5246505618840773/100000000000000 : ℝ)*(sp0) + (1311623373074123/25000000000000 : ℝ)*(sp1) + (5246483769181161/100000000000000 : ℝ)*(sp2) + (266009647815493/10000000000000 : ℝ)*(sp3) + (12126544281/100000000000000 : ℝ)*(sp5) + (5462414903/25000000000000 : ℝ)*(sp6) + (2869318433/50000000000000 : ℝ)*(sp7) + (665025554197949/25000000000000 : ℝ)*(f.failure) + (5246505618840773/100000000000000 : ℝ)*(f.sum) + (4057200371237/3391250000000000000000000000 : ℝ)*base66 + (3657050291019926931/339125000000000000000000000000000 : ℝ)*base68 + (72252664317073069/339125000000000000000000000000000 : ℝ)*base69 + (905829585341051931/339125000000000000000000000000000 : ℝ)*base72 + (794160534884067/13565000000000000000000000000 : ℝ)*base73 + (1909501230463573069/339125000000000000000000000000000 : ℝ)*base75 + (3542004229884176931/339125000000000000000000000000000 : ℝ)*base78 + (9476029638156573069/339125000000000000000000000000000 : ℝ)*base79 + (34448090296187/13565000000000000000000000000 : ℝ)*base81 + (4890869/1250000000000000000000 : ℝ)*base89 + (4890869/1250000000000000000000 : ℝ)*base91 + (4890869/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (79731/100000 : ℝ) ≤ (540794138580675072009941256189921/678250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15115591/100000000000000 : ℝ)*(upper0) + (3390447/100000000000000 : ℝ)*(lower1) + (1209363/4000000000000 : ℝ)*(lower3) + (567061/3125000000000 : ℝ)*(upper4) + (2215600650849477/50000000000000 : ℝ)*(major0) + (2215600650849477/50000000000000 : ℝ)*(major1) + (2215600650849477/50000000000000 : ℝ)*(major2) + (1705888161/100000000000000 : ℝ)*(sp1) + (3652389947/25000000000000 : ℝ)*(sp2) + (749433041/25000000000000 : ℝ)*(sp3) + (234463514313041/4000000000000 : ℝ)*(sp8) + (732698268992233/12500000000000 : ℝ)*(sp9) + (5861573248266237/100000000000000 : ℝ)*(sp10) + (743558458048751/25000000000000 : ℝ)*(sp11) + (11618112616903/390625000000 : ℝ)*(f.failure) + (234463514313041/4000000000000 : ℝ)*(f.sum) + (8765901473617/3391250000000000000000000000 : ℝ)*base65 + (16672074789885012231/1356500000000000000000000000000000 : ℝ)*base68 + (9715775388289512231/1356500000000000000000000000000000 : ℝ)*base70 + (65611249112512231/1356500000000000000000000000000000 : ℝ)*base72 + (27997103207953/13565000000000000000000000000 : ℝ)*base73 + (14694127946589512231/1356500000000000000000000000000000 : ℝ)*base76 + (14421123189631512231/1356500000000000000000000000000000 : ℝ)*base78 + (17130340733170512231/1356500000000000000000000000000000 : ℝ)*base80 + (20471653768969/1695625000000000000000000000 : ℝ)*base82 + (97509/9765625000000000000 : ℝ)*base89 + (97509/9765625000000000000 : ℝ)*base91 + (97509/9765625000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-20767/25000 : ℝ) ≤ (-28169698954773536863893082452951/33912500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (101404543/50000000000000 : ℝ)*(lower0) + (26513/2000000000000 : ℝ)*(lower3) + (50217169/25000000000000 : ℝ)*(lower4) + (111650536990761/2500000000000 : ℝ)*(major0) + (111650536990761/2500000000000 : ℝ)*(major1) + (111650536990761/2500000000000 : ℝ)*(major2) + (858040871/25000000000000 : ℝ)*(sp4) + (25642235203/6250000000000 : ℝ)*(sp5) + (41662020727/6250000000000 : ℝ)*(sp6) + (11625219399/12500000000000 : ℝ)*(sp7) + (596211988904177/10000000000000 : ℝ)*(sp12) + (2980856522721003/50000000000000 : ℝ)*(sp13) + (5961456728873623/100000000000000 : ℝ)*(sp14) + (2997515245667437/100000000000000 : ℝ)*(sp15) + (2997608247422629/100000000000000 : ℝ)*(f.failure) + (2981061660602627/50000000000000 : ℝ)*(f.sum) + (344251497923/67825000000000000000000000 : ℝ)*base66 + (426406916983009317/67825000000000000000000000000000 : ℝ)*base67 + (1188555853804609317/67825000000000000000000000000000 : ℝ)*base69 + (303014883052515683/67825000000000000000000000000000 : ℝ)*base72 + (1930556458259/542600000000000000000000000 : ℝ)*base74 + (1227265319523709317/67825000000000000000000000000000 : ℝ)*base75 + (366516542021415683/67825000000000000000000000000000 : ℝ)*base78 + (3881122340038709317/67825000000000000000000000000000 : ℝ)*base79 + (116496227761/108520000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (56670051/5000000000000000000000 : ℝ)*base90 + (56670051/5000000000000000000000 : ℝ)*base92 + (56670051/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1117_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74493081/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7017/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11321/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15557/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(59279/100000 : ℝ) else (79731/100000 : ℝ) ≤ X j i ∧ X j i ≤ (20767/25000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1117_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1117_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74493081/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7017/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11321/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15557/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(59279/100000 : ℝ) else (79731/100000 : ℝ) ≤ X j i ∧ X j i ≤ (20767/25000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1117_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8309/2048 : ℝ) ≤ p) (hpb : p ≤ (4155/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74493081/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7017/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11321/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15557/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(59279/100000 : ℝ) else (79731/100000 : ℝ) ≤ X j i ∧ X j i ≤ (20767/25000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1117_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
