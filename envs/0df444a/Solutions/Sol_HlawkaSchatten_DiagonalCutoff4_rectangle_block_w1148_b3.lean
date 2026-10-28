-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1148_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:34:32.550974+00:00
-- url     : https://prove2.me/submissions/48f04cb3-eade-4257-ad0a-61c4408012ee

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
theorem support_rectangle_w1148_box_0 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2037326367/10000000000 : ℝ)*x 0 + (5376224569/10000000000 : ℝ)*x 1 + (5376224437/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2037326367/10000000000 : ℝ)^8341 ≤ (485579801439/4000000000000 : ℝ)^6293 := by
    have hnat : (2037326367 : ℕ)^8341*4000000000000^6293 ≤ 485579801439^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2037326367 10000000000 485579801439 4000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5376224569/10000000000 : ℝ)^8341 ≤ (8786050637713/20000000000000 : ℝ)^6293 := by
    have hnat : (5376224569 : ℕ)^8341*20000000000000^6293 ≤ 8786050637713^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376224569 10000000000 8786050637713 20000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5376224437/10000000000 : ℝ)^8341 ≤ (8786050351789/20000000000000 : ℝ)^6293 := by
    have hnat : (5376224437 : ℕ)^8341*20000000000000^6293 ≤ 8786050351789^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376224437 10000000000 8786050351789 20000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2037326367/10000000000 : ℝ), (5376224569/10000000000 : ℝ), (5376224437/10000000000 : ℝ)] ![(485579801439/4000000000000 : ℝ), (8786050637713/20000000000000 : ℝ), (8786050351789/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2037326367/10000000000 : ℝ)|^8341 ≤ (485579801439/4000000000000 : ℝ)^6293
        have hw : |(-2037326367/10000000000 : ℝ)|=(2037326367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5376224569/10000000000 : ℝ)|^8341 ≤ (8786050637713/20000000000000 : ℝ)^6293
        have hw : |(5376224569/10000000000 : ℝ)|=(5376224569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5376224437/10000000000 : ℝ)|^8341 ≤ (8786050351789/20000000000000 : ℝ)^6293
        have hw : |(5376224437/10000000000 : ℝ)|=(5376224437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_box_1 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5296040777/10000000000 : ℝ)*x 0 + (-1073042187/5000000000 : ℝ)*x 1 + (1075244907/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5296040777/10000000000 : ℝ)^8341 ≤ (21531970474249/50000000000000 : ℝ)^6293 := by
    have hnat : (5296040777 : ℕ)^8341*50000000000000^6293 ≤ 21531970474249^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296040777 10000000000 21531970474249 50000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1073042187/5000000000 : ℝ)^8341 ≤ (1300580621487/10000000000000 : ℝ)^6293 := by
    have hnat : (1073042187 : ℕ)^8341*10000000000000^6293 ≤ 1300580621487^6293*5000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073042187 5000000000 1300580621487 10000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1075244907/2000000000 : ℝ)^8341 ≤ (43930252820329/100000000000000 : ℝ)^6293 := by
    have hnat : (1075244907 : ℕ)^8341*100000000000000^6293 ≤ 43930252820329^6293*2000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075244907 2000000000 43930252820329 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5296040777/10000000000 : ℝ), (-1073042187/5000000000 : ℝ), (1075244907/2000000000 : ℝ)] ![(21531970474249/50000000000000 : ℝ), (1300580621487/10000000000000 : ℝ), (43930252820329/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5296040777/10000000000 : ℝ)|^8341 ≤ (21531970474249/50000000000000 : ℝ)^6293
        have hw : |(5296040777/10000000000 : ℝ)|=(5296040777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1073042187/5000000000 : ℝ)|^8341 ≤ (1300580621487/10000000000000 : ℝ)^6293
        have hw : |(-1073042187/5000000000 : ℝ)|=(1073042187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1075244907/2000000000 : ℝ)|^8341 ≤ (43930252820329/100000000000000 : ℝ)^6293
        have hw : |(1075244907/2000000000 : ℝ)|=(1075244907/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_box_2 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (264802029/500000000 : ℝ)*x 0 + (2688112321/5000000000 : ℝ)*x 1 + (-1073042247/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (264802029/500000000 : ℝ)^8341 ≤ (43063938825307/100000000000000 : ℝ)^6293 := by
    have hnat : (264802029 : ℕ)^8341*100000000000000^6293 ≤ 43063938825307^6293*500000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264802029 500000000 43063938825307 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2688112321/5000000000 : ℝ)^8341 ≤ (10982563494797/25000000000000 : ℝ)^6293 := by
    have hnat : (2688112321 : ℕ)^8341*25000000000000^6293 ≤ 10982563494797^6293*5000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688112321 5000000000 10982563494797 25000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1073042247/5000000000 : ℝ)^8341 ≤ (13005807178771/100000000000000 : ℝ)^6293 := by
    have hnat : (1073042247 : ℕ)^8341*100000000000000^6293 ≤ 13005807178771^6293*5000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073042247 5000000000 13005807178771 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(264802029/500000000 : ℝ), (2688112321/5000000000 : ℝ), (-1073042247/5000000000 : ℝ)] ![(43063938825307/100000000000000 : ℝ), (10982563494797/25000000000000 : ℝ), (13005807178771/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(264802029/500000000 : ℝ)|^8341 ≤ (43063938825307/100000000000000 : ℝ)^6293
        have hw : |(264802029/500000000 : ℝ)|=(264802029/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2688112321/5000000000 : ℝ)|^8341 ≤ (10982563494797/25000000000000 : ℝ)^6293
        have hw : |(2688112321/5000000000 : ℝ)|=(2688112321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1073042247/5000000000 : ℝ)|^8341 ≤ (13005807178771/100000000000000 : ℝ)^6293
        have hw : |(-1073042247/5000000000 : ℝ)|=(1073042247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_box_3 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2235655693/5000000000 : ℝ)*x 0 + (4312194431/10000000000 : ℝ)*x 1 + (1078048663/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2235655693/5000000000 : ℝ)^8341 ≤ (34409005188489/100000000000000 : ℝ)^6293 := by
    have hnat : (2235655693 : ℕ)^8341*100000000000000^6293 ≤ 34409005188489^6293*5000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2235655693 5000000000 34409005188489 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4312194431/10000000000 : ℝ)^8341 ≤ (32795496286941/100000000000000 : ℝ)^6293 := by
    have hnat : (4312194431 : ℕ)^8341*100000000000000^6293 ≤ 32795496286941^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4312194431 10000000000 32795496286941 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078048663/2500000000 : ℝ)^8341 ≤ (32795498514701/100000000000000 : ℝ)^6293 := by
    have hnat : (1078048663 : ℕ)^8341*100000000000000^6293 ≤ 32795498514701^6293*2500000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078048663 2500000000 32795498514701 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2235655693/5000000000 : ℝ), (4312194431/10000000000 : ℝ), (1078048663/2500000000 : ℝ)] ![(34409005188489/100000000000000 : ℝ), (32795496286941/100000000000000 : ℝ), (32795498514701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2235655693/5000000000 : ℝ)|^8341 ≤ (34409005188489/100000000000000 : ℝ)^6293
        have hw : |(2235655693/5000000000 : ℝ)|=(2235655693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4312194431/10000000000 : ℝ)|^8341 ≤ (32795496286941/100000000000000 : ℝ)^6293
        have hw : |(4312194431/10000000000 : ℝ)|=(4312194431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078048663/2500000000 : ℝ)|^8341 ≤ (32795498514701/100000000000000 : ℝ)^6293
        have hw : |(1078048663/2500000000 : ℝ)|=(1078048663/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_box_4 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2292102327/10000000000 : ℝ)*x 0 + (5281218119/10000000000 : ℝ)*x 1 + (5281217219/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2292102327/10000000000 : ℝ)^8341 ≤ (3547872026759/25000000000000 : ℝ)^6293 := by
    have hnat : (2292102327 : ℕ)^8341*25000000000000^6293 ≤ 3547872026759^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2292102327 10000000000 3547872026759 25000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5281218119/10000000000 : ℝ)^8341 ≤ (42904260784341/100000000000000 : ℝ)^6293 := by
    have hnat : (5281218119 : ℕ)^8341*100000000000000^6293 ≤ 42904260784341^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281218119 10000000000 42904260784341 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5281217219/10000000000 : ℝ)^8341 ≤ (42904251093327/100000000000000 : ℝ)^6293 := by
    have hnat : (5281217219 : ℕ)^8341*100000000000000^6293 ≤ 42904251093327^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281217219 10000000000 42904251093327 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2292102327/10000000000 : ℝ), (5281218119/10000000000 : ℝ), (5281217219/10000000000 : ℝ)] ![(3547872026759/25000000000000 : ℝ), (42904260784341/100000000000000 : ℝ), (42904251093327/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2292102327/10000000000 : ℝ)|^8341 ≤ (3547872026759/25000000000000 : ℝ)^6293
        have hw : |(-2292102327/10000000000 : ℝ)|=(2292102327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5281218119/10000000000 : ℝ)|^8341 ≤ (42904260784341/100000000000000 : ℝ)^6293
        have hw : |(5281218119/10000000000 : ℝ)|=(5281218119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5281217219/10000000000 : ℝ)|^8341 ≤ (42904251093327/100000000000000 : ℝ)^6293
        have hw : |(5281217219/10000000000 : ℝ)|=(5281217219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_box_5 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5363153777/10000000000 : ℝ)*x 0 + (-1091737727/5000000000 : ℝ)*x 1 + (1056243517/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5363153777/10000000000 : ℝ)^8341 ≤ (43788746600677/100000000000000 : ℝ)^6293 := by
    have hnat : (5363153777 : ℕ)^8341*100000000000000^6293 ≤ 43788746600677^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363153777 10000000000 43788746600677 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1091737727/5000000000 : ℝ)^8341 ≤ (13306998346633/100000000000000 : ℝ)^6293 := by
    have hnat : (1091737727 : ℕ)^8341*100000000000000^6293 ≤ 13306998346633^6293*5000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091737727 5000000000 13306998346633 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1056243517/2000000000 : ℝ)^8341 ≤ (2145212751717/5000000000000 : ℝ)^6293 := by
    have hnat : (1056243517 : ℕ)^8341*5000000000000^6293 ≤ 2145212751717^6293*2000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056243517 2000000000 2145212751717 5000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5363153777/10000000000 : ℝ), (-1091737727/5000000000 : ℝ), (1056243517/2000000000 : ℝ)] ![(43788746600677/100000000000000 : ℝ), (13306998346633/100000000000000 : ℝ), (2145212751717/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5363153777/10000000000 : ℝ)|^8341 ≤ (43788746600677/100000000000000 : ℝ)^6293
        have hw : |(5363153777/10000000000 : ℝ)|=(5363153777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1091737727/5000000000 : ℝ)|^8341 ≤ (13306998346633/100000000000000 : ℝ)^6293
        have hw : |(-1091737727/5000000000 : ℝ)|=(1091737727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1056243517/2000000000 : ℝ)|^8341 ≤ (2145212751717/5000000000000 : ℝ)^6293
        have hw : |(1056243517/2000000000 : ℝ)|=(1056243517/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_box_6 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5363154181/10000000000 : ℝ)*x 0 + (5281217717/10000000000 : ℝ)*x 1 + (-136467171/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5363154181/10000000000 : ℝ)^8341 ≤ (10947187743179/25000000000000 : ℝ)^6293 := by
    have hnat : (5363154181 : ℕ)^8341*25000000000000^6293 ≤ 10947187743179^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363154181 10000000000 10947187743179 25000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5281217717/10000000000 : ℝ)^8341 ≤ (5363032056961/12500000000000 : ℝ)^6293 := by
    have hnat : (5281217717 : ℕ)^8341*12500000000000^6293 ≤ 5363032056961^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281217717 10000000000 5363032056961 12500000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (136467171/625000000 : ℝ)^8341 ≤ (6653496273393/50000000000000 : ℝ)^6293 := by
    have hnat : (136467171 : ℕ)^8341*50000000000000^6293 ≤ 6653496273393^6293*625000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136467171 625000000 6653496273393 50000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5363154181/10000000000 : ℝ), (5281217717/10000000000 : ℝ), (-136467171/625000000 : ℝ)] ![(10947187743179/25000000000000 : ℝ), (5363032056961/12500000000000 : ℝ), (6653496273393/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5363154181/10000000000 : ℝ)|^8341 ≤ (10947187743179/25000000000000 : ℝ)^6293
        have hw : |(5363154181/10000000000 : ℝ)|=(5363154181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5281217717/10000000000 : ℝ)|^8341 ≤ (5363032056961/12500000000000 : ℝ)^6293
        have hw : |(5281217717/10000000000 : ℝ)|=(5281217717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-136467171/625000000 : ℝ)|^8341 ≤ (6653496273393/50000000000000 : ℝ)^6293
        have hw : |(-136467171/625000000 : ℝ)|=(136467171/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_box_7 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4255986233/10000000000 : ℝ)*x 0 + (4419836163/10000000000 : ℝ)*x 1 + (2209918241/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4255986233/10000000000 : ℝ)^8341 ≤ (8057525608849/25000000000000 : ℝ)^6293 := by
    have hnat : (4255986233 : ℕ)^8341*25000000000000^6293 ≤ 8057525608849^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4255986233 10000000000 8057525608849 25000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4419836163/10000000000 : ℝ)^8341 ≤ (8471236788479/25000000000000 : ℝ)^6293 := by
    have hnat : (4419836163 : ℕ)^8341*25000000000000^6293 ≤ 8471236788479^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4419836163 10000000000 8471236788479 25000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2209918241/5000000000 : ℝ)^8341 ≤ (33884950395459/100000000000000 : ℝ)^6293 := by
    have hnat : (2209918241 : ℕ)^8341*100000000000000^6293 ≤ 33884950395459^6293*5000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2209918241 5000000000 33884950395459 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4255986233/10000000000 : ℝ), (4419836163/10000000000 : ℝ), (2209918241/5000000000 : ℝ)] ![(8057525608849/25000000000000 : ℝ), (8471236788479/25000000000000 : ℝ), (33884950395459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4255986233/10000000000 : ℝ)|^8341 ≤ (8057525608849/25000000000000 : ℝ)^6293
        have hw : |(4255986233/10000000000 : ℝ)|=(4255986233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4419836163/10000000000 : ℝ)|^8341 ≤ (8471236788479/25000000000000 : ℝ)^6293
        have hw : |(4419836163/10000000000 : ℝ)|=(4419836163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2209918241/5000000000 : ℝ)|^8341 ≤ (33884950395459/100000000000000 : ℝ)^6293
        have hw : |(2209918241/5000000000 : ℝ)|=(2209918241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_box_8 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2238817503/10000000000 : ℝ)*x 0 + (5216591963/10000000000 : ℝ)*x 1 + (1346458503/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2238817503/10000000000 : ℝ)^8341 ≤ (6877936367209/50000000000000 : ℝ)^6293 := by
    have hnat : (2238817503 : ℕ)^8341*50000000000000^6293 ≤ 6877936367209^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2238817503 10000000000 6877936367209 50000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216591963/10000000000 : ℝ)^8341 ≤ (21104884586519/50000000000000 : ℝ)^6293 := by
    have hnat : (5216591963 : ℕ)^8341*50000000000000^6293 ≤ 21104884586519^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216591963 10000000000 21104884586519 50000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1346458503/2500000000 : ℝ)^8341 ≤ (44034358084233/100000000000000 : ℝ)^6293 := by
    have hnat : (1346458503 : ℕ)^8341*100000000000000^6293 ≤ 44034358084233^6293*2500000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346458503 2500000000 44034358084233 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2238817503/10000000000 : ℝ), (5216591963/10000000000 : ℝ), (1346458503/2500000000 : ℝ)] ![(6877936367209/50000000000000 : ℝ), (21104884586519/50000000000000 : ℝ), (44034358084233/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2238817503/10000000000 : ℝ)|^8341 ≤ (6877936367209/50000000000000 : ℝ)^6293
        have hw : |(-2238817503/10000000000 : ℝ)|=(2238817503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216591963/10000000000 : ℝ)|^8341 ≤ (21104884586519/50000000000000 : ℝ)^6293
        have hw : |(5216591963/10000000000 : ℝ)|=(5216591963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1346458503/2500000000 : ℝ)|^8341 ≤ (44034358084233/100000000000000 : ℝ)^6293
        have hw : |(1346458503/2500000000 : ℝ)|=(1346458503/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_box_9 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2644624509/5000000000 : ℝ)*x 0 + (-1071117129/5000000000 : ℝ)*x 1 + (1346458399/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644624509/5000000000 : ℝ)^8341 ≤ (42990757234659/100000000000000 : ℝ)^6293 := by
    have hnat : (2644624509 : ℕ)^8341*100000000000000^6293 ≤ 42990757234659^6293*5000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644624509 5000000000 42990757234659 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1071117129/5000000000 : ℝ)^8341 ≤ (12974889179711/100000000000000 : ℝ)^6293 := by
    have hnat : (1071117129 : ℕ)^8341*100000000000000^6293 ≤ 12974889179711^6293*5000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071117129 5000000000 12974889179711 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1346458399/2500000000 : ℝ)^8341 ≤ (8806870715229/20000000000000 : ℝ)^6293 := by
    have hnat : (1346458399 : ℕ)^8341*20000000000000^6293 ≤ 8806870715229^6293*2500000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346458399 2500000000 8806870715229 20000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644624509/5000000000 : ℝ), (-1071117129/5000000000 : ℝ), (1346458399/2500000000 : ℝ)] ![(42990757234659/100000000000000 : ℝ), (12974889179711/100000000000000 : ℝ), (8806870715229/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644624509/5000000000 : ℝ)|^8341 ≤ (42990757234659/100000000000000 : ℝ)^6293
        have hw : |(2644624509/5000000000 : ℝ)|=(2644624509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1071117129/5000000000 : ℝ)|^8341 ≤ (12974889179711/100000000000000 : ℝ)^6293
        have hw : |(-1071117129/5000000000 : ℝ)|=(1071117129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1346458399/2500000000 : ℝ)|^8341 ≤ (8806870715229/20000000000000 : ℝ)^6293
        have hw : |(1346458399/2500000000 : ℝ)|=(1346458399/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_box_10 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5289249359/10000000000 : ℝ)*x 0 + (1346458439/2500000000 : ℝ)*x 1 + (-133889599/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289249359/10000000000 : ℝ)^8341 ≤ (42990760908293/100000000000000 : ℝ)^6293 := by
    have hnat : (5289249359 : ℕ)^8341*100000000000000^6293 ≤ 42990760908293^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289249359 10000000000 42990760908293 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1346458439/2500000000 : ℝ)^8341 ≤ (1761374212401/4000000000000 : ℝ)^6293 := by
    have hnat : (1346458439 : ℕ)^8341*4000000000000^6293 ≤ 1761374212401^6293*2500000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346458439 2500000000 1761374212401 4000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (133889599/625000000 : ℝ)^8341 ≤ (12974883768967/100000000000000 : ℝ)^6293 := by
    have hnat : (133889599 : ℕ)^8341*100000000000000^6293 ≤ 12974883768967^6293*625000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133889599 625000000 12974883768967 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289249359/10000000000 : ℝ), (1346458439/2500000000 : ℝ), (-133889599/625000000 : ℝ)] ![(42990760908293/100000000000000 : ℝ), (1761374212401/4000000000000 : ℝ), (12974883768967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289249359/10000000000 : ℝ)|^8341 ≤ (42990760908293/100000000000000 : ℝ)^6293
        have hw : |(5289249359/10000000000 : ℝ)|=(5289249359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1346458439/2500000000 : ℝ)|^8341 ≤ (1761374212401/4000000000000 : ℝ)^6293
        have hw : |(1346458439/2500000000 : ℝ)|=(1346458439/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-133889599/625000000 : ℝ)|^8341 ≤ (12974883768967/100000000000000 : ℝ)^6293
        have hw : |(-133889599/625000000 : ℝ)|=(133889599/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_box_11 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1123204249/2500000000 : ℝ)*x 0 + (4301301313/10000000000 : ℝ)*x 1 + (860260217/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1123204249/2500000000 : ℝ)^8341 ≤ (34628532597049/100000000000000 : ℝ)^6293 := by
    have hnat : (1123204249 : ℕ)^8341*100000000000000^6293 ≤ 34628532597049^6293*2500000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123204249 2500000000 34628532597049 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4301301313/10000000000 : ℝ)^8341 ≤ (32685734842149/100000000000000 : ℝ)^6293 := by
    have hnat : (4301301313 : ℕ)^8341*100000000000000^6293 ≤ 32685734842149^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4301301313 10000000000 32685734842149 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (860260217/2000000000 : ℝ)^8341 ≤ (32685732545717/100000000000000 : ℝ)^6293 := by
    have hnat : (860260217 : ℕ)^8341*100000000000000^6293 ≤ 32685732545717^6293*2000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      860260217 2000000000 32685732545717 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1123204249/2500000000 : ℝ), (4301301313/10000000000 : ℝ), (860260217/2000000000 : ℝ)] ![(34628532597049/100000000000000 : ℝ), (32685734842149/100000000000000 : ℝ), (32685732545717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1123204249/2500000000 : ℝ)|^8341 ≤ (34628532597049/100000000000000 : ℝ)^6293
        have hw : |(1123204249/2500000000 : ℝ)|=(1123204249/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4301301313/10000000000 : ℝ)|^8341 ≤ (32685734842149/100000000000000 : ℝ)^6293
        have hw : |(4301301313/10000000000 : ℝ)|=(4301301313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(860260217/2000000000 : ℝ)|^8341 ≤ (32685732545717/100000000000000 : ℝ)^6293
        have hw : |(860260217/2000000000 : ℝ)|=(860260217/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_box_12 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2090926063/10000000000 : ℝ)*x 0 + (1087915347/2000000000 : ℝ)*x 1 + (2636588221/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2090926063/10000000000 : ℝ)^8341 ≤ (3141152683/25000000000 : ℝ)^6293 := by
    have hnat : (2090926063 : ℕ)^8341*25000000000^6293 ≤ 3141152683^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2090926063 10000000000 3141152683 25000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1087915347/2000000000 : ℝ)^8341 ≤ (22308849061317/50000000000000 : ℝ)^6293 := by
    have hnat : (1087915347 : ℕ)^8341*50000000000000^6293 ≤ 22308849061317^6293*2000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087915347 2000000000 22308849061317 50000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2636588221/5000000000 : ℝ)^8341 ≤ (42817691131271/100000000000000 : ℝ)^6293 := by
    have hnat : (2636588221 : ℕ)^8341*100000000000000^6293 ≤ 42817691131271^6293*5000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636588221 5000000000 42817691131271 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2090926063/10000000000 : ℝ), (1087915347/2000000000 : ℝ), (2636588221/5000000000 : ℝ)] ![(3141152683/25000000000 : ℝ), (22308849061317/50000000000000 : ℝ), (42817691131271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2090926063/10000000000 : ℝ)|^8341 ≤ (3141152683/25000000000 : ℝ)^6293
        have hw : |(-2090926063/10000000000 : ℝ)|=(2090926063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1087915347/2000000000 : ℝ)|^8341 ≤ (22308849061317/50000000000000 : ℝ)^6293
        have hw : |(1087915347/2000000000 : ℝ)|=(1087915347/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2636588221/5000000000 : ℝ)|^8341 ≤ (42817691131271/100000000000000 : ℝ)^6293
        have hw : |(2636588221/5000000000 : ℝ)|=(2636588221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_box_13 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5368831647/10000000000 : ℝ)*x 0 + (-2186582467/10000000000 : ℝ)*x 1 + (2636588431/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368831647/10000000000 : ℝ)^8341 ≤ (43850202402603/100000000000000 : ℝ)^6293 := by
    have hnat : (5368831647 : ℕ)^8341*100000000000000^6293 ≤ 43850202402603^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368831647 10000000000 43850202402603 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2186582467/10000000000 : ℝ)^8341 ≤ (3333025483157/25000000000000 : ℝ)^6293 := by
    have hnat : (2186582467 : ℕ)^8341*25000000000000^6293 ≤ 3333025483157^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2186582467 10000000000 3333025483157 25000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2636588431/5000000000 : ℝ)^8341 ≤ (21408847825751/50000000000000 : ℝ)^6293 := by
    have hnat : (2636588431 : ℕ)^8341*50000000000000^6293 ≤ 21408847825751^6293*5000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636588431 5000000000 21408847825751 50000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368831647/10000000000 : ℝ), (-2186582467/10000000000 : ℝ), (2636588431/5000000000 : ℝ)] ![(43850202402603/100000000000000 : ℝ), (3333025483157/25000000000000 : ℝ), (21408847825751/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368831647/10000000000 : ℝ)|^8341 ≤ (43850202402603/100000000000000 : ℝ)^6293
        have hw : |(5368831647/10000000000 : ℝ)|=(5368831647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2186582467/10000000000 : ℝ)|^8341 ≤ (3333025483157/25000000000000 : ℝ)^6293
        have hw : |(-2186582467/10000000000 : ℝ)|=(2186582467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2636588431/5000000000 : ℝ)|^8341 ≤ (21408847825751/50000000000000 : ℝ)^6293
        have hw : |(2636588431/5000000000 : ℝ)|=(2636588431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_box_14 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2684415889/5000000000 : ℝ)*x 0 + (5273177021/10000000000 : ℝ)*x 1 + (-6833069/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684415889/5000000000 : ℝ)^8341 ≤ (43850203820757/100000000000000 : ℝ)^6293 := by
    have hnat : (2684415889 : ℕ)^8341*100000000000000^6293 ≤ 43850203820757^6293*5000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684415889 5000000000 43850203820757 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5273177021/10000000000 : ℝ)^8341 ≤ (10704424340683/25000000000000 : ℝ)^6293 := by
    have hnat : (5273177021 : ℕ)^8341*25000000000000^6293 ≤ 10704424340683^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5273177021 10000000000 10704424340683 25000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6833069/31250000 : ℝ)^8341 ≤ (13332098805079/100000000000000 : ℝ)^6293 := by
    have hnat : (6833069 : ℕ)^8341*100000000000000^6293 ≤ 13332098805079^6293*31250000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6833069 31250000 13332098805079 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684415889/5000000000 : ℝ), (5273177021/10000000000 : ℝ), (-6833069/31250000 : ℝ)] ![(43850203820757/100000000000000 : ℝ), (10704424340683/25000000000000 : ℝ), (13332098805079/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684415889/5000000000 : ℝ)|^8341 ≤ (43850203820757/100000000000000 : ℝ)^6293
        have hw : |(2684415889/5000000000 : ℝ)|=(2684415889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5273177021/10000000000 : ℝ)|^8341 ≤ (10704424340683/25000000000000 : ℝ)^6293
        have hw : |(5273177021/10000000000 : ℝ)|=(5273177021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6833069/31250000 : ℝ)|^8341 ≤ (13332098805079/100000000000000 : ℝ)^6293
        have hw : |(-6833069/31250000 : ℝ)|=(6833069/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_box_15 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1059382483/2500000000 : ℝ)*x 0 + (885788507/2000000000 : ℝ)*x 1 + (4428941921/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059382483/2500000000 : ℝ)^8341 ≤ (32044979742381/100000000000000 : ℝ)^6293 := by
    have hnat : (1059382483 : ℕ)^8341*100000000000000^6293 ≤ 32044979742381^6293*2500000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059382483 2500000000 32044979742381 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (885788507/2000000000 : ℝ)^8341 ≤ (169887566229/500000000000 : ℝ)^6293 := by
    have hnat : (885788507 : ℕ)^8341*500000000000^6293 ≤ 169887566229^6293*2000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      885788507 2000000000 169887566229 500000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4428941921/10000000000 : ℝ)^8341 ≤ (33977507002413/100000000000000 : ℝ)^6293 := by
    have hnat : (4428941921 : ℕ)^8341*100000000000000^6293 ≤ 33977507002413^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4428941921 10000000000 33977507002413 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1059382483/2500000000 : ℝ), (885788507/2000000000 : ℝ), (4428941921/10000000000 : ℝ)] ![(32044979742381/100000000000000 : ℝ), (169887566229/500000000000 : ℝ), (33977507002413/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1059382483/2500000000 : ℝ)|^8341 ≤ (32044979742381/100000000000000 : ℝ)^6293
        have hw : |(1059382483/2500000000 : ℝ)|=(1059382483/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(885788507/2000000000 : ℝ)|^8341 ≤ (169887566229/500000000000 : ℝ)^6293
        have hw : |(885788507/2000000000 : ℝ)|=(885788507/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4428941921/10000000000 : ℝ)|^8341 ≤ (33977507002413/100000000000000 : ℝ)^6293
        have hw : |(4428941921/10000000000 : ℝ)|=(4428941921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1148_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149590789/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3513/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5681/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(7779/12500 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59303/100000 : ℝ) ∧ (79827/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (41569/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3513/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5681/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3513/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5681/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3513/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5681/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3513/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5681/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3513/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5681/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3513/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5681/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5681/50000 : ℝ) ^ (2085/512 : ℝ) ≤ (14241672332741337/100000000000000000000 : ℝ) := by
    have hpowers : (5681/50000 : ℝ)^2085 ≤ (14241672332741337/100000000000000000000 : ℝ)^512 := by
      have hnat : (5681 : ℕ)^2085*100000000000000000000^512 ≤ 14241672332741337^512*50000^2085 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5681 50000 14241672332741337 100000000000000000000 2085 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5681/50000 : ℝ)) (X := (14241672332741337/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2085 512 (by norm_num) hpowers
    exact h
  have hpowhi : (3513/25000 : ℝ) ^ (2085/512 : ℝ) ≤ (16917388894443951/50000000000000000000 : ℝ) := by
    have hpowers : (3513/25000 : ℝ)^2085 ≤ (16917388894443951/50000000000000000000 : ℝ)^512 := by
      have hnat : (3513 : ℕ)^2085*50000000000000000000^512 ≤ 16917388894443951^512*25000^2085 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3513 25000 16917388894443951 50000000000000000000 2085 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3513/25000 : ℝ)) (X := (16917388894443951/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2085 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014241672332741337/50000000000000000000 : ℝ) ≤ (2000139874396333/2000000000000000 : ℝ) ^ (2085/512 : ℝ) := by
    have hpowers : (50014241672332741337/50000000000000000000 : ℝ)^512 ≤ (2000139874396333/2000000000000000 : ℝ)^2085 := by
      have hnat : (50014241672332741337 : ℕ)^512*2000000000000000^2085 ≤ 2000139874396333^2085*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014241672332741337 50000000000000000000 2000139874396333 2000000000000000 512 2085 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000139874396333/2000000000000000 : ℝ)) (X := (50014241672332741337/50000000000000000000 : ℝ)) (by norm_num) 2085 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048076450121629239/100000000000000000000 : ℝ) ≤ (10001180368330157/10000000000000000 : ℝ) ^ (2085/512 : ℝ) := by
    have hpowers : (100048076450121629239/100000000000000000000 : ℝ)^512 ≤ (10001180368330157/10000000000000000 : ℝ)^2085 := by
      have hnat : (100048076450121629239 : ℕ)^512*10000000000000000^2085 ≤ 10001180368330157^2085*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048076450121629239 100000000000000000000 10001180368330157 10000000000000000 512 2085 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001180368330157/10000000000000000 : ℝ)) (X := (100048076450121629239/100000000000000000000 : ℝ)) (by norm_num) 2085 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016917388894443951/25000000000000000000 : ℝ) ≤ (10001661364678649/10000000000000000 : ℝ) ^ (2085/512 : ℝ) := by
    have hpowers : (25016917388894443951/25000000000000000000 : ℝ)^512 ≤ (10001661364678649/10000000000000000 : ℝ)^2085 := by
      have hnat : (25016917388894443951 : ℕ)^512*10000000000000000^2085 ≤ 10001661364678649^2085*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016917388894443951 25000000000000000000 10001661364678649 10000000000000000 512 2085 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001661364678649/10000000000000000 : ℝ)) (X := (25016917388894443951/25000000000000000000 : ℝ)) (by norm_num) 2085 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14241672332741337/100000000000000000000 : ℝ) ≤ ((13445475574803773321/13450000000000000000 : ℝ)+2*(120249087123/67250000000000 : ℝ)*(5681/50000 : ℝ))^(2085/512 : ℝ) := by
    rw [show (13445475574803773321/13450000000000000000 : ℝ)+2*(120249087123/67250000000000 : ℝ)*(5681/50000 : ℝ)=(2000139874396333/2000000000000000 : ℝ) by norm_num, show 1+2*(14241672332741337/100000000000000000000 : ℝ)=(50014241672332741337/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16917388894443951/50000000000000000000 : ℝ)+(14241672332741337/100000000000000000000 : ℝ) ≤ ((13445475574803773321/13450000000000000000 : ℝ)+(120249087123/67250000000000 : ℝ)*((3513/25000 : ℝ)+(5681/50000 : ℝ)))^(2085/512 : ℝ) := by
    rw [show (13445475574803773321/13450000000000000000 : ℝ)+(120249087123/67250000000000 : ℝ)*((3513/25000 : ℝ)+(5681/50000 : ℝ))=(10001180368330157/10000000000000000 : ℝ) by norm_num, show 1+(16917388894443951/50000000000000000000 : ℝ)+(14241672332741337/100000000000000000000 : ℝ)=(100048076450121629239/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16917388894443951/50000000000000000000 : ℝ) ≤ ((13445475574803773321/13450000000000000000 : ℝ)+2*(120249087123/67250000000000 : ℝ)*(3513/25000 : ℝ))^(2085/512 : ℝ) := by
    rw [show (13445475574803773321/13450000000000000000 : ℝ)+2*(120249087123/67250000000000 : ℝ)*(3513/25000 : ℝ)=(10001661364678649/10000000000000000 : ℝ) by norm_num, show 1+2*(16917388894443951/50000000000000000000 : ℝ)=(25016917388894443951/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13445475574803773321/13450000000000000000 : ℝ)*(X 1 0+X 2 0)+(120249087123/67250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2085/512 : ℝ)) (lo := (5681/50000 : ℝ)) (hi := (3513/25000 : ℝ)) (c := (13445475574803773321/13450000000000000000 : ℝ)) (alpha := (120249087123/67250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13445475574803773321/13450000000000000000 : ℝ)*(X 0 1+X 2 1)+(120249087123/67250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2085/512 : ℝ)) (lo := (5681/50000 : ℝ)) (hi := (3513/25000 : ℝ)) (c := (13445475574803773321/13450000000000000000 : ℝ)) (alpha := (120249087123/67250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13445475574803773321/13450000000000000000 : ℝ)*(X 0 2+X 1 2)+(120249087123/67250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2085/512 : ℝ)) (lo := (5681/50000 : ℝ)) (hi := (3513/25000 : ℝ)) (c := (13445475574803773321/13450000000000000000 : ℝ)) (alpha := (120249087123/67250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2037326367/10000000000 : ℝ)*X 0 0+(5376224569/10000000000 : ℝ)*X 0 1+(5376224437/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5296040777/10000000000 : ℝ)*X 1 0+(-1073042187/5000000000 : ℝ)*X 1 1+(1075244907/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((264802029/500000000 : ℝ)*X 2 0+(2688112321/5000000000 : ℝ)*X 2 1+(-1073042247/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2235655693/5000000000 : ℝ)*X 0 0+(4312194431/10000000000 : ℝ)*X 0 1+(1078048663/2500000000 : ℝ)*X 0 2+(2235655693/5000000000 : ℝ)*X 1 0+(4312194431/10000000000 : ℝ)*X 1 1+(1078048663/2500000000 : ℝ)*X 1 2+(2235655693/5000000000 : ℝ)*X 2 0+(4312194431/10000000000 : ℝ)*X 2 1+(1078048663/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2292102327/10000000000 : ℝ)*X 0 0+(5281218119/10000000000 : ℝ)*X 0 1+(5281217219/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5363153777/10000000000 : ℝ)*X 1 0+(-1091737727/5000000000 : ℝ)*X 1 1+(1056243517/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5363154181/10000000000 : ℝ)*X 2 0+(5281217717/10000000000 : ℝ)*X 2 1+(-136467171/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4255986233/10000000000 : ℝ)*X 0 0+(4419836163/10000000000 : ℝ)*X 0 1+(2209918241/5000000000 : ℝ)*X 0 2+(4255986233/10000000000 : ℝ)*X 1 0+(4419836163/10000000000 : ℝ)*X 1 1+(2209918241/5000000000 : ℝ)*X 1 2+(4255986233/10000000000 : ℝ)*X 2 0+(4419836163/10000000000 : ℝ)*X 2 1+(2209918241/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2238817503/10000000000 : ℝ)*X 0 0+(5216591963/10000000000 : ℝ)*X 0 1+(1346458503/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2644624509/5000000000 : ℝ)*X 1 0+(-1071117129/5000000000 : ℝ)*X 1 1+(1346458399/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5289249359/10000000000 : ℝ)*X 2 0+(1346458439/2500000000 : ℝ)*X 2 1+(-133889599/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1123204249/2500000000 : ℝ)*X 0 0+(4301301313/10000000000 : ℝ)*X 0 1+(860260217/2000000000 : ℝ)*X 0 2+(1123204249/2500000000 : ℝ)*X 1 0+(4301301313/10000000000 : ℝ)*X 1 1+(860260217/2000000000 : ℝ)*X 1 2+(1123204249/2500000000 : ℝ)*X 2 0+(4301301313/10000000000 : ℝ)*X 2 1+(860260217/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2090926063/10000000000 : ℝ)*X 0 0+(1087915347/2000000000 : ℝ)*X 0 1+(2636588221/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5368831647/10000000000 : ℝ)*X 1 0+(-2186582467/10000000000 : ℝ)*X 1 1+(2636588431/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2684415889/5000000000 : ℝ)*X 2 0+(5273177021/10000000000 : ℝ)*X 2 1+(-6833069/31250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1059382483/2500000000 : ℝ)*X 0 0+(885788507/2000000000 : ℝ)*X 0 1+(4428941921/10000000000 : ℝ)*X 0 2+(1059382483/2500000000 : ℝ)*X 1 0+(885788507/2000000000 : ℝ)*X 1 1+(4428941921/10000000000 : ℝ)*X 1 2+(1059382483/2500000000 : ℝ)*X 2 0+(885788507/2000000000 : ℝ)*X 2 1+(4428941921/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-7779/12500 : ℝ) ≤ (-52311501675295274544458203768443/84062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (34517319/12500000000000 : ℝ)*(upper0) + (436732871/100000000000000 : ℝ)*(lower2) + (7617317/12500000000000 : ℝ)*(lower3) + (490687867443539/12500000000000 : ℝ)*(major0) + (490687867443539/12500000000000 : ℝ)*(major1) + (490687867443539/12500000000000 : ℝ)*(major2) + (6295983443/100000000000000 : ℝ)*(sp1) + (10627237313/100000000000000 : ℝ)*(sp3) + (1049511642702017/20000000000000 : ℝ)*(sp4) + (5247581818699383/100000000000000 : ℝ)*(sp5) + (1311816679502633/25000000000000 : ℝ)*(sp6) + (262415023573421/10000000000000 : ℝ)*(sp7) + (14950586371/50000000000000 : ℝ)*(sp8) + (64279334459/20000000000000 : ℝ)*(sp14) + (656040215742881/25000000000000 : ℝ)*(f.failure) + (2623794057341413/50000000000000 : ℝ)*(f.sum) + (7403385158677/6725000000000000000000000000 : ℝ)*base65 + (2257394540173019/168125000000000000000000000000000 : ℝ)*base67 + (1911881208365451981/168125000000000000000000000000000 : ℝ)*base70 + (1595778297437673019/168125000000000000000000000000000 : ℝ)*base71 + (147200870471227/6725000000000000000000000000 : ℝ)*base73 + (172723837446076981/168125000000000000000000000000000 : ℝ)*base76 + (579280046312326981/168125000000000000000000000000000 : ℝ)*base78 + (2480818723011076981/168125000000000000000000000000000 : ℝ)*base80 + (2430614522147/420312500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (10076891/2500000000000000000000 : ℝ)*base90 + (10076891/2500000000000000000000 : ℝ)*base92 + (10076891/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (59303/100000 : ℝ) ≤ (39883003996265031919902656040621/67250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5863641/5000000000000 : ℝ)*(upper2) + (1773617/50000000000000 : ℝ)*(upper3) + (6226501/100000000000000 : ℝ)*(upper5) + (3989756425079223/100000000000000 : ℝ)*(major0) + (3989756425079223/100000000000000 : ℝ)*(major1) + (498719553134903/12500000000000 : ℝ)*(major2) + (1323157618455551/25000000000000 : ℝ)*(sp0) + (1058525075017043/20000000000000 : ℝ)*(sp1) + (2646313656669057/50000000000000 : ℝ)*(sp2) + (333389108778243/12500000000000 : ℝ)*(sp3) + (524921243/10000000000000 : ℝ)*(sp5) + (827739883/25000000000000 : ℝ)*(sp6) + (414125661/50000000000000 : ℝ)*(sp7) + (75237721/50000000000000 : ℝ)*(sp12) + (1333556849238633/50000000000000 : ℝ)*(f.failure) + (1058526124859529/20000000000000 : ℝ)*(f.sum) + (62547973947381/6725000000000000000000000000 : ℝ)*base65 + (9311394949850790417/1345000000000000000000000000000000 : ℝ)*base68 + (2684836027341452137/168125000000000000000000000000000 : ℝ)*base70 + (11819902370105790417/1345000000000000000000000000000000 : ℝ)*base72 + (727059560981/6725000000000000000000000000 : ℝ)*base73 + (250956822308327137/168125000000000000000000000000000 : ℝ)*base76 + (5727711624745390417/1345000000000000000000000000000000 : ℝ)*base78 + (4572075734945390417/1345000000000000000000000000000000 : ℝ)*base80 + (17261424225271/3362500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (9751437/5000000000000000000000 : ℝ)*base89 + (9751437/5000000000000000000000 : ℝ)*base91 + (40248563/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (79827/100000 : ℝ) ≤ (268425111943473468040209519893121/336250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5785157/2500000000000 : ℝ)*(upper0) + (30781951/50000000000000 : ℝ)*(upper1) + (242223451/50000000000000 : ℝ)*(upper4) + (2228806612848733/50000000000000 : ℝ)*(major0) + (2228806612848733/50000000000000 : ℝ)*(major1) + (2228806612848733/50000000000000 : ℝ)*(major2) + (61495994963/25000000000000 : ℝ)*(sp1) + (662657093869/100000000000000 : ℝ)*(sp2) + (236312445093/100000000000000 : ℝ)*(sp3) + (1608183157/4000000000000 : ℝ)*(sp4) + (5908705111964039/100000000000000 : ℝ)*(sp8) + (738562416570389/12500000000000 : ℝ)*(sp9) + (1181616531889819/20000000000000 : ℝ)*(sp10) + (744908786470527/25000000000000 : ℝ)*(sp11) + (2979871458327201/100000000000000 : ℝ)*(f.failure) + (1477186329135741/25000000000000 : ℝ)*(f.sum) + (13581812014757/3362500000000000000000000000 : ℝ)*base66 + (1870894250898352293/672500000000000000000000000000000 : ℝ)*base67 + (4418654157751647707/672500000000000000000000000000000 : ℝ)*base70 + (90759873090852293/672500000000000000000000000000000 : ℝ)*base71 + (18636041371039/6725000000000000000000000000 : ℝ)*base74 + (12452591701004147707/672500000000000000000000000000000 : ℝ)*base76 + (3044625264978352293/672500000000000000000000000000000 : ℝ)*base77 + (44660986468063352293/672500000000000000000000000000000 : ℝ)*base79 + (17253502887807/3362500000000000000000000000 : ℝ)*base82 + (17751589/10000000000000000000000 : ℝ)*base89 + (17751589/10000000000000000000000 : ℝ)*base91 + (17751589/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-41569/50000 : ℝ) ≤ (-279542828107858041829378532470377/336250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (171991089/50000000000000 : ℝ)*(lower0) + (9840743/12500000000000 : ℝ)*(lower2) + (47068399/100000000000000 : ℝ)*(upper3) + (219623561/50000000000000 : ℝ)*(upper5) + (2246285734930821/50000000000000 : ℝ)*(major0) + (2246285734930821/50000000000000 : ℝ)*(major1) + (2246285734930821/50000000000000 : ℝ)*(major2) + (3203080707/25000000000000 : ℝ)*(sp4) + (125728220427/50000000000000 : ℝ)*(sp7) + (3462408901/20000000000000 : ℝ)*(sp8) + (1502395978103783/25000000000000 : ℝ)*(sp12) + (1201922807356493/20000000000000 : ℝ)*(sp13) + (1201922807356493/20000000000000 : ℝ)*(sp14) + (1501494625510591/50000000000000 : ℝ)*(sp15) + (750810176865509/25000000000000 : ℝ)*(f.failure) + (1201922807356493/20000000000000 : ℝ)*(f.sum) + (34538599443343/6725000000000000000000000000 : ℝ)*base66 + (4384017306569526541/672500000000000000000000000000000 : ℝ)*base67 + (5271494616287973459/672500000000000000000000000000000 : ℝ)*base70 + (578417370725473459/672500000000000000000000000000000 : ℝ)*base72 + (9932931817607/6725000000000000000000000000 : ℝ)*base73 + (11372095242002973459/672500000000000000000000000000000 : ℝ)*base76 + (216139418937026541/672500000000000000000000000000000 : ℝ)*base77 + (9020487327335473459/672500000000000000000000000000000 : ℝ)*base80 + (16020884280341/3362500000000000000000000000 : ℝ)*base81 + (11803399/2500000000000000000000 : ℝ)*base90 + (11803399/2500000000000000000000 : ℝ)*base92 + (11803399/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1148_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149590789/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3513/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5681/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(7779/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(59303/100000 : ℝ) else (79827/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41569/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1148_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1148_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149590789/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3513/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5681/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(7779/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(59303/100000 : ℝ) else (79827/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41569/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1148_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149590789/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3513/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5681/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(7779/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(59303/100000 : ℝ) else (79827/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41569/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1148_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
