-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1271_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:20:15.8033+00:00
-- url     : https://prove2.me/submissions/13625ee2-b2b9-440b-89bb-e40d7359c9ce

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
theorem support_rectangle_w1271_s3_0 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-262952637/1250000000 : ℝ)*x 0 + (5417091281/10000000000 : ℝ)*x 1 + (2621429/5000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (262952637/1250000000 : ℝ)^8465 ≤ (3197651167839/25000000000000 : ℝ)^6417 := by
    have hnat : (262952637 : ℕ)^8465*25000000000000^6417 ≤ 3197651167839^6417*1250000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262952637 1250000000 3197651167839 25000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5417091281/10000000000 : ℝ)^8465 ≤ (2784050056767/6250000000000 : ℝ)^6417 := by
    have hnat : (5417091281 : ℕ)^8465*6250000000000^6417 ≤ 2784050056767^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417091281 10000000000 2784050056767 6250000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621429/5000000 : ℝ)^8465 ≤ (42664594407297/100000000000000 : ℝ)^6417 := by
    have hnat : (2621429 : ℕ)^8465*100000000000000^6417 ≤ 42664594407297^6417*5000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621429 5000000 42664594407297 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-262952637/1250000000 : ℝ), (5417091281/10000000000 : ℝ), (2621429/5000000 : ℝ)] ![(3197651167839/25000000000000 : ℝ), (2784050056767/6250000000000 : ℝ), (42664594407297/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-262952637/1250000000 : ℝ)|^8465 ≤ (3197651167839/25000000000000 : ℝ)^6417
        have hw : |(-262952637/1250000000 : ℝ)|=(262952637/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5417091281/10000000000 : ℝ)|^8465 ≤ (2784050056767/6250000000000 : ℝ)^6417
        have hw : |(5417091281/10000000000 : ℝ)|=(5417091281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621429/5000000 : ℝ)|^8465 ≤ (42664594407297/100000000000000 : ℝ)^6417
        have hw : |(2621429/5000000 : ℝ)|=(2621429/5000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s3_1 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5350835879/10000000000 : ℝ)*x 0 + (-2192456769/10000000000 : ℝ)*x 1 + (262142907/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350835879/10000000000 : ℝ)^8465 ≤ (43827508465819/100000000000000 : ℝ)^6417 := by
    have hnat : (5350835879 : ℕ)^8465*100000000000000^6417 ≤ 43827508465819^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350835879 10000000000 43827508465819 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2192456769/10000000000 : ℝ)^8465 ≤ (13507895605067/100000000000000 : ℝ)^6417 := by
    have hnat : (2192456769 : ℕ)^8465*100000000000000^6417 ≤ 13507895605067^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2192456769 10000000000 13507895605067 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262142907/500000000 : ℝ)^8465 ≤ (4266459591017/10000000000000 : ℝ)^6417 := by
    have hnat : (262142907 : ℕ)^8465*10000000000000^6417 ≤ 4266459591017^6417*500000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262142907 500000000 4266459591017 10000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350835879/10000000000 : ℝ), (-2192456769/10000000000 : ℝ), (262142907/500000000 : ℝ)] ![(43827508465819/100000000000000 : ℝ), (13507895605067/100000000000000 : ℝ), (4266459591017/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350835879/10000000000 : ℝ)|^8465 ≤ (43827508465819/100000000000000 : ℝ)^6417
        have hw : |(5350835879/10000000000 : ℝ)|=(5350835879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2192456769/10000000000 : ℝ)|^8465 ≤ (13507895605067/100000000000000 : ℝ)^6417
        have hw : |(-2192456769/10000000000 : ℝ)|=(2192456769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(262142907/500000000 : ℝ)|^8465 ≤ (4266459591017/10000000000000 : ℝ)^6417
        have hw : |(262142907/500000000 : ℝ)|=(262142907/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s3_2 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5350835873/10000000000 : ℝ)*x 0 + (5242858589/10000000000 : ℝ)*x 1 + (-274057023/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350835873/10000000000 : ℝ)^8465 ≤ (4382750840099/10000000000000 : ℝ)^6417 := by
    have hnat : (5350835873 : ℕ)^8465*10000000000000^6417 ≤ 4382750840099^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350835873 10000000000 4382750840099 10000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242858589/10000000000 : ℝ)^8465 ≤ (42664600730101/100000000000000 : ℝ)^6417 := by
    have hnat : (5242858589 : ℕ)^8465*100000000000000^6417 ≤ 42664600730101^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242858589 10000000000 42664600730101 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (274057023/1250000000 : ℝ)^8465 ≤ (13507890850539/100000000000000 : ℝ)^6417 := by
    have hnat : (274057023 : ℕ)^8465*100000000000000^6417 ≤ 13507890850539^6417*1250000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274057023 1250000000 13507890850539 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350835873/10000000000 : ℝ), (5242858589/10000000000 : ℝ), (-274057023/1250000000 : ℝ)] ![(4382750840099/10000000000000 : ℝ), (42664600730101/100000000000000 : ℝ), (13507890850539/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350835873/10000000000 : ℝ)|^8465 ≤ (4382750840099/10000000000000 : ℝ)^6417
        have hw : |(5350835873/10000000000 : ℝ)|=(5350835873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242858589/10000000000 : ℝ)|^8465 ≤ (42664600730101/100000000000000 : ℝ)^6417
        have hw : |(5242858589/10000000000 : ℝ)|=(5242858589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-274057023/1250000000 : ℝ)|^8465 ≤ (13507890850539/100000000000000 : ℝ)^6417
        have hw : |(-274057023/1250000000 : ℝ)|=(274057023/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s3_3 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (108627897/250000000 : ℝ)*x 0 + (2085438669/5000000000 : ℝ)*x 1 + (4526368509/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (108627897/250000000 : ℝ)^8465 ≤ (130085448231/390625000000 : ℝ)^6417 := by
    have hnat : (108627897 : ℕ)^8465*390625000000^6417 ≤ 130085448231^6417*250000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108627897 250000000 130085448231 390625000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2085438669/5000000000 : ℝ)^8465 ≤ (15775827445089/50000000000000 : ℝ)^6417 := by
    have hnat : (2085438669 : ℕ)^8465*50000000000000^6417 ≤ 15775827445089^6417*5000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085438669 5000000000 15775827445089 50000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4526368509/10000000000 : ℝ)^8465 ≤ (17573235177961/50000000000000 : ℝ)^6417 := by
    have hnat : (4526368509 : ℕ)^8465*50000000000000^6417 ≤ 17573235177961^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4526368509 10000000000 17573235177961 50000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(108627897/250000000 : ℝ), (2085438669/5000000000 : ℝ), (4526368509/10000000000 : ℝ)] ![(130085448231/390625000000 : ℝ), (15775827445089/50000000000000 : ℝ), (17573235177961/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(108627897/250000000 : ℝ)|^8465 ≤ (130085448231/390625000000 : ℝ)^6417
        have hw : |(108627897/250000000 : ℝ)|=(108627897/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2085438669/5000000000 : ℝ)|^8465 ≤ (15775827445089/50000000000000 : ℝ)^6417
        have hw : |(2085438669/5000000000 : ℝ)|=(2085438669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4526368509/10000000000 : ℝ)|^8465 ≤ (17573235177961/50000000000000 : ℝ)^6417
        have hw : |(4526368509/10000000000 : ℝ)|=(4526368509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s3_4 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1051817417/5000000000 : ℝ)*x 0 + (5243479723/10000000000 : ℝ)*x 1 + (541646583/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051817417/5000000000 : ℝ)^8465 ≤ (12790714861423/100000000000000 : ℝ)^6417 := by
    have hnat : (1051817417 : ℕ)^8465*100000000000000^6417 ≤ 12790714861423^6417*5000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051817417 5000000000 12790714861423 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243479723/10000000000 : ℝ)^8465 ≤ (21335634306603/50000000000000 : ℝ)^6417 := by
    have hnat : (5243479723 : ℕ)^8465*50000000000000^6417 ≤ 21335634306603^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243479723 10000000000 21335634306603 50000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (541646583/1000000000 : ℝ)^8465 ≤ (2783626032123/6250000000000 : ℝ)^6417 := by
    have hnat : (541646583 : ℕ)^8465*6250000000000^6417 ≤ 2783626032123^6417*1000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541646583 1000000000 2783626032123 6250000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1051817417/5000000000 : ℝ), (5243479723/10000000000 : ℝ), (541646583/1000000000 : ℝ)] ![(12790714861423/100000000000000 : ℝ), (21335634306603/50000000000000 : ℝ), (2783626032123/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1051817417/5000000000 : ℝ)|^8465 ≤ (12790714861423/100000000000000 : ℝ)^6417
        have hw : |(-1051817417/5000000000 : ℝ)|=(1051817417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243479723/10000000000 : ℝ)|^8465 ≤ (21335634306603/50000000000000 : ℝ)^6417
        have hw : |(5243479723/10000000000 : ℝ)|=(5243479723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(541646583/1000000000 : ℝ)|^8465 ≤ (2783626032123/6250000000000 : ℝ)^6417
        have hw : |(541646583/1000000000 : ℝ)|=(541646583/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s3_5 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (212251891/400000000 : ℝ)*x 0 + (-504712069/2500000000 : ℝ)*x 1 + (21158069/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212251891/400000000 : ℝ)^8465 ≤ (8669382893861/20000000000000 : ℝ)^6417 := by
    have hnat : (212251891 : ℕ)^8465*20000000000000^6417 ≤ 8669382893861^6417*400000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212251891 400000000 8669382893861 20000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (504712069/2500000000 : ℝ)^8465 ≤ (6057535399119/50000000000000 : ℝ)^6417 := by
    have hnat : (504712069 : ℕ)^8465*50000000000000^6417 ≤ 6057535399119^6417*2500000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      504712069 2500000000 6057535399119 50000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21158069/39062500 : ℝ)^8465 ≤ (8907602942673/20000000000000 : ℝ)^6417 := by
    have hnat : (21158069 : ℕ)^8465*20000000000000^6417 ≤ 8907602942673^6417*39062500^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21158069 39062500 8907602942673 20000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212251891/400000000 : ℝ), (-504712069/2500000000 : ℝ), (21158069/39062500 : ℝ)] ![(8669382893861/20000000000000 : ℝ), (6057535399119/50000000000000 : ℝ), (8907602942673/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212251891/400000000 : ℝ)|^8465 ≤ (8669382893861/20000000000000 : ℝ)^6417
        have hw : |(212251891/400000000 : ℝ)|=(212251891/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-504712069/2500000000 : ℝ)|^8465 ≤ (6057535399119/50000000000000 : ℝ)^6417
        have hw : |(-504712069/2500000000 : ℝ)|=(504712069/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(21158069/39062500 : ℝ)|^8465 ≤ (8907602942673/20000000000000 : ℝ)^6417
        have hw : |(21158069/39062500 : ℝ)|=(21158069/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s3_6 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2653148279/5000000000 : ℝ)*x 0 + (5416466107/10000000000 : ℝ)*x 1 + (-403769729/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2653148279/5000000000 : ℝ)^8465 ≤ (43346906742843/100000000000000 : ℝ)^6417 := by
    have hnat : (2653148279 : ℕ)^8465*100000000000000^6417 ≤ 43346906742843^6417*5000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2653148279 5000000000 43346906742843 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5416466107/10000000000 : ℝ)^8465 ≤ (11134504879647/25000000000000 : ℝ)^6417 := by
    have hnat : (5416466107 : ℕ)^8465*25000000000000^6417 ≤ 11134504879647^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416466107 10000000000 11134504879647 25000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (403769729/2000000000 : ℝ)^8465 ≤ (12115073719319/100000000000000 : ℝ)^6417 := by
    have hnat : (403769729 : ℕ)^8465*100000000000000^6417 ≤ 12115073719319^6417*2000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      403769729 2000000000 12115073719319 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2653148279/5000000000 : ℝ), (5416466107/10000000000 : ℝ), (-403769729/2000000000 : ℝ)] ![(43346906742843/100000000000000 : ℝ), (11134504879647/25000000000000 : ℝ), (12115073719319/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2653148279/5000000000 : ℝ)|^8465 ≤ (43346906742843/100000000000000 : ℝ)^6417
        have hw : |(2653148279/5000000000 : ℝ)|=(2653148279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5416466107/10000000000 : ℝ)|^8465 ≤ (11134504879647/25000000000000 : ℝ)^6417
        have hw : |(5416466107/10000000000 : ℝ)|=(5416466107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-403769729/2000000000 : ℝ)|^8465 ≤ (12115073719319/100000000000000 : ℝ)^6417
        have hw : |(-403769729/2000000000 : ℝ)|=(403769729/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s3_7 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4345143141/10000000000 : ℝ)*x 0 + (4525099157/10000000000 : ℝ)*x 1 + (4172152521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4345143141/10000000000 : ℝ)^8465 ≤ (16651075181579/50000000000000 : ℝ)^6417 := by
    have hnat : (4345143141 : ℕ)^8465*50000000000000^6417 ≤ 16651075181579^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4345143141 10000000000 16651075181579 50000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4525099157/10000000000 : ℝ)^8465 ≤ (7026693795697/20000000000000 : ℝ)^6417 := by
    have hnat : (4525099157 : ℕ)^8465*20000000000000^6417 ≤ 7026693795697^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4525099157 10000000000 7026693795697 20000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4172152521/10000000000 : ℝ)^8465 ≤ (31564380639061/100000000000000 : ℝ)^6417 := by
    have hnat : (4172152521 : ℕ)^8465*100000000000000^6417 ≤ 31564380639061^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4172152521 10000000000 31564380639061 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4345143141/10000000000 : ℝ), (4525099157/10000000000 : ℝ), (4172152521/10000000000 : ℝ)] ![(16651075181579/50000000000000 : ℝ), (7026693795697/20000000000000 : ℝ), (31564380639061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4345143141/10000000000 : ℝ)|^8465 ≤ (16651075181579/50000000000000 : ℝ)^6417
        have hw : |(4345143141/10000000000 : ℝ)|=(4345143141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4525099157/10000000000 : ℝ)|^8465 ≤ (7026693795697/20000000000000 : ℝ)^6417
        have hw : |(4525099157/10000000000 : ℝ)|=(4525099157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4172152521/10000000000 : ℝ)|^8465 ≤ (31564380639061/100000000000000 : ℝ)^6417
        have hw : |(4172152521/10000000000 : ℝ)|=(4172152521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s3_8 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-15980869/10000000000 : ℝ)*x 0 + (2955946477/5000000000 : ℝ)*x 1 + (2956034337/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (15980869/10000000000 : ℝ)^8465 ≤ (20470250601/100000000000000 : ℝ)^6417 := by
    have hnat : (15980869 : ℕ)^8465*100000000000000^6417 ≤ 20470250601^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15980869 10000000000 20470250601 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2955946477/5000000000 : ℝ)^8465 ≤ (49988784852953/100000000000000 : ℝ)^6417 := by
    have hnat : (2955946477 : ℕ)^8465*100000000000000^6417 ≤ 49988784852953^6417*5000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2955946477 5000000000 49988784852953 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2956034337/5000000000 : ℝ)^8465 ≤ (49990744889619/100000000000000 : ℝ)^6417 := by
    have hnat : (2956034337 : ℕ)^8465*100000000000000^6417 ≤ 49990744889619^6417*5000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2956034337 5000000000 49990744889619 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-15980869/10000000000 : ℝ), (2955946477/5000000000 : ℝ), (2956034337/5000000000 : ℝ)] ![(20470250601/100000000000000 : ℝ), (49988784852953/100000000000000 : ℝ), (49990744889619/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-15980869/10000000000 : ℝ)|^8465 ≤ (20470250601/100000000000000 : ℝ)^6417
        have hw : |(-15980869/10000000000 : ℝ)|=(15980869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2955946477/5000000000 : ℝ)|^8465 ≤ (49988784852953/100000000000000 : ℝ)^6417
        have hw : |(2955946477/5000000000 : ℝ)|=(2955946477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2956034337/5000000000 : ℝ)|^8465 ≤ (49990744889619/100000000000000 : ℝ)^6417
        have hw : |(2956034337/5000000000 : ℝ)|=(2956034337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s3_9 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (981458153/10000000000 : ℝ)*x 0 + (-4368379019/10000000000 : ℝ)*x 1 + (6941783583/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (981458153/10000000000 : ℝ)^8465 ≤ (2339351070917/50000000000000 : ℝ)^6417 := by
    have hnat : (981458153 : ℕ)^8465*50000000000000^6417 ≤ 2339351070917^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      981458153 10000000000 2339351070917 50000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4368379019/10000000000 : ℝ)^8465 ≤ (8384317945703/25000000000000 : ℝ)^6417 := by
    have hnat : (4368379019 : ℕ)^8465*25000000000000^6417 ≤ 8384317945703^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4368379019 10000000000 8384317945703 25000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6941783583/10000000000 : ℝ)^8465 ≤ (6178402605679/10000000000000 : ℝ)^6417 := by
    have hnat : (6941783583 : ℕ)^8465*10000000000000^6417 ≤ 6178402605679^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6941783583 10000000000 6178402605679 10000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(981458153/10000000000 : ℝ), (-4368379019/10000000000 : ℝ), (6941783583/10000000000 : ℝ)] ![(2339351070917/50000000000000 : ℝ), (8384317945703/25000000000000 : ℝ), (6178402605679/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(981458153/10000000000 : ℝ)|^8465 ≤ (2339351070917/50000000000000 : ℝ)^6417
        have hw : |(981458153/10000000000 : ℝ)|=(981458153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4368379019/10000000000 : ℝ)|^8465 ≤ (8384317945703/25000000000000 : ℝ)^6417
        have hw : |(-4368379019/10000000000 : ℝ)|=(4368379019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6941783583/10000000000 : ℝ)|^8465 ≤ (6178402605679/10000000000000 : ℝ)^6417
        have hw : |(6941783583/10000000000 : ℝ)|=(6941783583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s3_10 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (981448573/10000000000 : ℝ)*x 0 + (3470881017/5000000000 : ℝ)*x 1 + (-4368409949/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (981448573/10000000000 : ℝ)^8465 ≤ (2339320948947/50000000000000 : ℝ)^6417 := by
    have hnat : (981448573 : ℕ)^8465*50000000000000^6417 ≤ 2339320948947^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      981448573 10000000000 2339320948947 50000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3470881017/5000000000 : ℝ)^8465 ≤ (61783773053037/100000000000000 : ℝ)^6417 := by
    have hnat : (3470881017 : ℕ)^8465*100000000000000^6417 ≤ 61783773053037^6417*5000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3470881017 5000000000 61783773053037 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4368409949/10000000000 : ℝ)^8465 ≤ (6707517005361/20000000000000 : ℝ)^6417 := by
    have hnat : (4368409949 : ℕ)^8465*20000000000000^6417 ≤ 6707517005361^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4368409949 10000000000 6707517005361 20000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(981448573/10000000000 : ℝ), (3470881017/5000000000 : ℝ), (-4368409949/10000000000 : ℝ)] ![(2339320948947/50000000000000 : ℝ), (61783773053037/100000000000000 : ℝ), (6707517005361/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(981448573/10000000000 : ℝ)|^8465 ≤ (2339320948947/50000000000000 : ℝ)^6417
        have hw : |(981448573/10000000000 : ℝ)|=(981448573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3470881017/5000000000 : ℝ)|^8465 ≤ (61783773053037/100000000000000 : ℝ)^6417
        have hw : |(3470881017/5000000000 : ℝ)|=(3470881017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4368409949/10000000000 : ℝ)|^8465 ≤ (6707517005361/20000000000000 : ℝ)^6417
        have hw : |(-4368409949/10000000000 : ℝ)|=(4368409949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s3_11 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (376395823/2500000000 : ℝ)*x 0 + (1158656303/2000000000 : ℝ)*x 1 + (5283599879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (376395823/2500000000 : ℝ)^8465 ≤ (1645498206299/20000000000000 : ℝ)^6417 := by
    have hnat : (376395823 : ℕ)^8465*20000000000000^6417 ≤ 1645498206299^6417*2500000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      376395823 2500000000 1645498206299 20000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1158656303/2000000000 : ℝ)^8465 ≤ (48670016732947/100000000000000 : ℝ)^6417 := by
    have hnat : (1158656303 : ℕ)^8465*100000000000000^6417 ≤ 48670016732947^6417*2000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1158656303 2000000000 48670016732947 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5283599879/10000000000 : ℝ)^8465 ≤ (43102492217757/100000000000000 : ℝ)^6417 := by
    have hnat : (5283599879 : ℕ)^8465*100000000000000^6417 ≤ 43102492217757^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5283599879 10000000000 43102492217757 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(376395823/2500000000 : ℝ), (1158656303/2000000000 : ℝ), (5283599879/10000000000 : ℝ)] ![(1645498206299/20000000000000 : ℝ), (48670016732947/100000000000000 : ℝ), (43102492217757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(376395823/2500000000 : ℝ)|^8465 ≤ (1645498206299/20000000000000 : ℝ)^6417
        have hw : |(376395823/2500000000 : ℝ)|=(376395823/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1158656303/2000000000 : ℝ)|^8465 ≤ (48670016732947/100000000000000 : ℝ)^6417
        have hw : |(1158656303/2000000000 : ℝ)|=(1158656303/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5283599879/10000000000 : ℝ)|^8465 ≤ (43102492217757/100000000000000 : ℝ)^6417
        have hw : |(5283599879/10000000000 : ℝ)|=(5283599879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1271_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152016389/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8073/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9619/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5493/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7337/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8073/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9619/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8073/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9619/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8073/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9619/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8073/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9619/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8073/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9619/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8073/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9619/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9619/100000 : ℝ) ^ (529/128 : ℝ) ≤ (6272875125073133/100000000000000000000 : ℝ) := by
    have hpowers : (9619/100000 : ℝ)^529 ≤ (6272875125073133/100000000000000000000 : ℝ)^128 := by
      have hnat : (9619 : ℕ)^529*100000000000000000000^128 ≤ 6272875125073133^128*100000^529 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9619 100000 6272875125073133 100000000000000000000 529 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9619/100000 : ℝ)) (X := (6272875125073133/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 529 128 (by norm_num) hpowers
    exact h
  have hpowhi : (8073/50000 : ℝ) ^ (529/128 : ℝ) ≤ (53343427664608713/100000000000000000000 : ℝ) := by
    have hpowers : (8073/50000 : ℝ)^529 ≤ (53343427664608713/100000000000000000000 : ℝ)^128 := by
      have hnat : (8073 : ℕ)^529*100000000000000000000^128 ≤ 53343427664608713^128*50000^529 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8073 50000 53343427664608713 100000000000000000000 529 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8073/50000 : ℝ)) (X := (53343427664608713/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 529 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006272875125073133/50000000000000000000 : ℝ) ≤ (10000303550033711/10000000000000000 : ℝ) ^ (529/128 : ℝ) := by
    have hpowers : (50006272875125073133/50000000000000000000 : ℝ)^128 ≤ (10000303550033711/10000000000000000 : ℝ)^529 := by
      have hnat : (50006272875125073133 : ℕ)^128*10000000000000000^529 ≤ 10000303550033711^529*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006272875125073133 50000000000000000000 10000303550033711 10000000000000000 128 529 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000303550033711/10000000000000000 : ℝ)) (X := (50006272875125073133/50000000000000000000 : ℝ)) (by norm_num) 529 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (50029808151394840923/50000000000000000000 : ℝ) ≤ (312545068307627/312500000000000 : ℝ) ^ (529/128 : ℝ) := by
    have hpowers : (50029808151394840923/50000000000000000000 : ℝ)^128 ≤ (312545068307627/312500000000000 : ℝ)^529 := by
      have hnat : (50029808151394840923 : ℕ)^128*312500000000000^529 ≤ 312545068307627^529*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50029808151394840923 50000000000000000000 312545068307627 312500000000000 128 529 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312545068307627/312500000000000 : ℝ)) (X := (50029808151394840923/50000000000000000000 : ℝ)) (by norm_num) 529 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (50053343427664608713/50000000000000000000 : ℝ) ≤ (10002580821654417/10000000000000000 : ℝ) ^ (529/128 : ℝ) := by
    have hpowers : (50053343427664608713/50000000000000000000 : ℝ)^128 ≤ (10002580821654417/10000000000000000 : ℝ)^529 := by
      have hnat : (50053343427664608713 : ℕ)^128*10000000000000000^529 ≤ 10002580821654417^529*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50053343427664608713 50000000000000000000 10002580821654417 10000000000000000 128 529 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002580821654417/10000000000000000 : ℝ)) (X := (50053343427664608713/50000000000000000000 : ℝ)) (by norm_num) 529 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6272875125073133/100000000000000000000 : ℝ) ≤ ((65250076195350460683/65270000000000000000 : ℝ)+2*(1138635810353/652700000000000 : ℝ)*(9619/100000 : ℝ))^(529/128 : ℝ) := by
    rw [show (65250076195350460683/65270000000000000000 : ℝ)+2*(1138635810353/652700000000000 : ℝ)*(9619/100000 : ℝ)=(10000303550033711/10000000000000000 : ℝ) by norm_num, show 1+2*(6272875125073133/100000000000000000000 : ℝ)=(50006272875125073133/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(53343427664608713/100000000000000000000 : ℝ)+(6272875125073133/100000000000000000000 : ℝ) ≤ ((65250076195350460683/65270000000000000000 : ℝ)+(1138635810353/652700000000000 : ℝ)*((8073/50000 : ℝ)+(9619/100000 : ℝ)))^(529/128 : ℝ) := by
    rw [show (65250076195350460683/65270000000000000000 : ℝ)+(1138635810353/652700000000000 : ℝ)*((8073/50000 : ℝ)+(9619/100000 : ℝ))=(312545068307627/312500000000000 : ℝ) by norm_num, show 1+(53343427664608713/100000000000000000000 : ℝ)+(6272875125073133/100000000000000000000 : ℝ)=(50029808151394840923/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(53343427664608713/100000000000000000000 : ℝ) ≤ ((65250076195350460683/65270000000000000000 : ℝ)+2*(1138635810353/652700000000000 : ℝ)*(8073/50000 : ℝ))^(529/128 : ℝ) := by
    rw [show (65250076195350460683/65270000000000000000 : ℝ)+2*(1138635810353/652700000000000 : ℝ)*(8073/50000 : ℝ)=(10002580821654417/10000000000000000 : ℝ) by norm_num, show 1+2*(53343427664608713/100000000000000000000 : ℝ)=(50053343427664608713/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (65250076195350460683/65270000000000000000 : ℝ)*(X 1 0+X 2 0)+(1138635810353/652700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (529/128 : ℝ)) (lo := (9619/100000 : ℝ)) (hi := (8073/50000 : ℝ)) (c := (65250076195350460683/65270000000000000000 : ℝ)) (alpha := (1138635810353/652700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (65250076195350460683/65270000000000000000 : ℝ)*(X 0 1+X 2 1)+(1138635810353/652700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (529/128 : ℝ)) (lo := (9619/100000 : ℝ)) (hi := (8073/50000 : ℝ)) (c := (65250076195350460683/65270000000000000000 : ℝ)) (alpha := (1138635810353/652700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (65250076195350460683/65270000000000000000 : ℝ)*(X 0 2+X 1 2)+(1138635810353/652700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (529/128 : ℝ)) (lo := (9619/100000 : ℝ)) (hi := (8073/50000 : ℝ)) (c := (65250076195350460683/65270000000000000000 : ℝ)) (alpha := (1138635810353/652700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-262952637/1250000000 : ℝ)*X 0 0+(5417091281/10000000000 : ℝ)*X 0 1+(2621429/5000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350835879/10000000000 : ℝ)*X 1 0+(-2192456769/10000000000 : ℝ)*X 1 1+(262142907/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350835873/10000000000 : ℝ)*X 2 0+(5242858589/10000000000 : ℝ)*X 2 1+(-274057023/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((108627897/250000000 : ℝ)*X 0 0+(2085438669/5000000000 : ℝ)*X 0 1+(4526368509/10000000000 : ℝ)*X 0 2+(108627897/250000000 : ℝ)*X 1 0+(2085438669/5000000000 : ℝ)*X 1 1+(4526368509/10000000000 : ℝ)*X 1 2+(108627897/250000000 : ℝ)*X 2 0+(2085438669/5000000000 : ℝ)*X 2 1+(4526368509/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1051817417/5000000000 : ℝ)*X 0 0+(5243479723/10000000000 : ℝ)*X 0 1+(541646583/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((212251891/400000000 : ℝ)*X 1 0+(-504712069/2500000000 : ℝ)*X 1 1+(21158069/39062500 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2653148279/5000000000 : ℝ)*X 2 0+(5416466107/10000000000 : ℝ)*X 2 1+(-403769729/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4345143141/10000000000 : ℝ)*X 0 0+(4525099157/10000000000 : ℝ)*X 0 1+(4172152521/10000000000 : ℝ)*X 0 2+(4345143141/10000000000 : ℝ)*X 1 0+(4525099157/10000000000 : ℝ)*X 1 1+(4172152521/10000000000 : ℝ)*X 1 2+(4345143141/10000000000 : ℝ)*X 2 0+(4525099157/10000000000 : ℝ)*X 2 1+(4172152521/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-15980869/10000000000 : ℝ)*X 0 0+(2955946477/5000000000 : ℝ)*X 0 1+(2956034337/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s3_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((981458153/10000000000 : ℝ)*X 1 0+(-4368379019/10000000000 : ℝ)*X 1 1+(6941783583/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s3_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((981448573/10000000000 : ℝ)*X 2 0+(3470881017/5000000000 : ℝ)*X 2 1+(-4368409949/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s3_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((376395823/2500000000 : ℝ)*X 0 0+(1158656303/2000000000 : ℝ)*X 0 1+(5283599879/10000000000 : ℝ)*X 0 2+(376395823/2500000000 : ℝ)*X 1 0+(1158656303/2000000000 : ℝ)*X 1 1+(5283599879/10000000000 : ℝ)*X 1 2+(376395823/2500000000 : ℝ)*X 2 0+(1158656303/2000000000 : ℝ)*X 2 1+(5283599879/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s3_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (338333730686006371820560641/26750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (39220199/100000000000000 : ℝ)*(lower3) + (2138127241413651/50000000000000 : ℝ)*(major0) + (2138127241413651/50000000000000 : ℝ)*(major1) + (2138127241413651/50000000000000 : ℝ)*(major2) + (5739458086485749/100000000000000 : ℝ)*(sp0) + (44839610085533/781250000000 : ℝ)*(sp1) + (5739485796921031/100000000000000 : ℝ)*(sp2) + (28130160858893/1000000000000 : ℝ)*(sp3) + (5689323057/20000000000000 : ℝ)*(sp4) + (15859753821/100000000000000 : ℝ)*(sp5) + (4849657409/100000000000000 : ℝ)*(sp7) + (582398989/100000000000000 : ℝ)*(sp9) + (736180003/100000000000000 : ℝ)*(sp10) + (1075407189/100000000000000 : ℝ)*(sp11) + (2813022010953899/100000000000000 : ℝ)*(f.failure) + (2869743266550517/50000000000000 : ℝ)*(f.sum) + (30002239919601/32635000000000000000000000000 : ℝ)*base65 + (27200821715023283633/3263500000000000000000000000000000 : ℝ)*base67 + (19461770875550283633/3263500000000000000000000000000000 : ℝ)*base69 + (247518533262216367/3263500000000000000000000000000000 : ℝ)*base72 + (183372281243931/32635000000000000000000000000 : ℝ)*base73 + (2284200891503216367/3263500000000000000000000000000000 : ℝ)*base76 + (31304793169518783633/3263500000000000000000000000000000 : ℝ)*base77 + (19268980138473783633/3263500000000000000000000000000000 : ℝ)*base79 + (148615677805291/32635000000000000000000000000 : ℝ)*base81 + (28549289/10000000000000000000000 : ℝ)*base90 + (28549289/10000000000000000000000 : ℝ)*base92 + (28549289/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4052879713507360772348809833/3263500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (42295943/25000000000000 : ℝ)*(lower3) + (4307057558778339/100000000000000 : ℝ)*(major0) + (4307057558778339/100000000000000 : ℝ)*(major1) + (4307057558778339/100000000000000 : ℝ)*(major2) + (7373809399/100000000000000 : ℝ)*(sp0) + (3891568571/25000000000000 : ℝ)*(sp1) + (14690843459/100000000000000 : ℝ)*(sp2) + (1445205277410827/25000000000000 : ℝ)*(sp4) + (2890406767396639/50000000000000 : ℝ)*(sp5) + (5780815377620819/100000000000000 : ℝ)*(sp6) + (708320952589501/25000000000000 : ℝ)*(sp7) + (396252893/25000000000000 : ℝ)*(sp8) + (241849179/25000000000000 : ℝ)*(sp9) + (119733833/10000000000000 : ℝ)*(sp11) + (1416642503848167/50000000000000 : ℝ)*(f.failure) + (2890415034232139/50000000000000 : ℝ)*(f.sum) + (72231194711867/32635000000000000000000000000 : ℝ)*base65 + (84246389551664754463/6527000000000000000000000000000000 : ℝ)*base68 + (479471664503995754463/6527000000000000000000000000000000 : ℝ)*base70 + (117402123330367754463/6527000000000000000000000000000000 : ℝ)*base72 + (226255341551083/32635000000000000000000000000 : ℝ)*base74 + (76773965774519754463/6527000000000000000000000000000000 : ℝ)*base76 + (7147171728892754463/6527000000000000000000000000000000 : ℝ)*base78 + (7417356430475754463/6527000000000000000000000000000000 : ℝ)*base80 + (1298221934864319/16317500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1608963/5000000000000000000000 : ℝ)*base89 + (1608963/5000000000000000000000 : ℝ)*base91 + (1608963/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1271_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152016389/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8073/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9619/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5493/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7337/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1271_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1271_s4_0 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-421146993/2000000000 : ℝ)*x 0 + (5396309759/10000000000 : ℝ)*x 1 + (5262253491/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (421146993/2000000000 : ℝ)^8465 ≤ (2561512468203/20000000000000 : ℝ)^6417 := by
    have hnat : (421146993 : ℕ)^8465*20000000000000^6417 ≤ 2561512468203^6417*2000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      421146993 2000000000 2561512468203 20000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5396309759/10000000000 : ℝ)^8465 ≤ (5539939184631/12500000000000 : ℝ)^6417 := by
    have hnat : (5396309759 : ℕ)^8465*12500000000000^6417 ≤ 5539939184631^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396309759 10000000000 5539939184631 12500000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5262253491/10000000000 : ℝ)^8465 ≤ (42872924169239/100000000000000 : ℝ)^6417 := by
    have hnat : (5262253491 : ℕ)^8465*100000000000000^6417 ≤ 42872924169239^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262253491 10000000000 42872924169239 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-421146993/2000000000 : ℝ), (5396309759/10000000000 : ℝ), (5262253491/10000000000 : ℝ)] ![(2561512468203/20000000000000 : ℝ), (5539939184631/12500000000000 : ℝ), (42872924169239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-421146993/2000000000 : ℝ)|^8465 ≤ (2561512468203/20000000000000 : ℝ)^6417
        have hw : |(-421146993/2000000000 : ℝ)|=(421146993/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5396309759/10000000000 : ℝ)|^8465 ≤ (5539939184631/12500000000000 : ℝ)^6417
        have hw : |(5396309759/10000000000 : ℝ)|=(5396309759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5262253491/10000000000 : ℝ)|^8465 ≤ (42872924169239/100000000000000 : ℝ)^6417
        have hw : |(5262253491/10000000000 : ℝ)|=(5262253491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s4_1 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672791391/5000000000 : ℝ)*x 0 + (-1086890537/5000000000 : ℝ)*x 1 + (657781687/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672791391/5000000000 : ℝ)^8465 ≤ (21885379130219/50000000000000 : ℝ)^6417 := by
    have hnat : (2672791391 : ℕ)^8465*50000000000000^6417 ≤ 21885379130219^6417*5000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672791391 5000000000 21885379130219 50000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1086890537/5000000000 : ℝ)^8465 ≤ (3339079375303/25000000000000 : ℝ)^6417 := by
    have hnat : (1086890537 : ℕ)^8465*25000000000000^6417 ≤ 3339079375303^6417*5000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086890537 5000000000 3339079375303 25000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (657781687/1250000000 : ℝ)^8465 ≤ (42872924222977/100000000000000 : ℝ)^6417 := by
    have hnat : (657781687 : ℕ)^8465*100000000000000^6417 ≤ 42872924222977^6417*1250000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657781687 1250000000 42872924222977 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672791391/5000000000 : ℝ), (-1086890537/5000000000 : ℝ), (657781687/1250000000 : ℝ)] ![(21885379130219/50000000000000 : ℝ), (3339079375303/25000000000000 : ℝ), (42872924222977/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672791391/5000000000 : ℝ)|^8465 ≤ (21885379130219/50000000000000 : ℝ)^6417
        have hw : |(2672791391/5000000000 : ℝ)|=(2672791391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1086890537/5000000000 : ℝ)|^8465 ≤ (3339079375303/25000000000000 : ℝ)^6417
        have hw : |(-1086890537/5000000000 : ℝ)|=(1086890537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(657781687/1250000000 : ℝ)|^8465 ≤ (42872924222977/100000000000000 : ℝ)^6417
        have hw : |(657781687/1250000000 : ℝ)|=(657781687/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s4_2 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (267279137/500000000 : ℝ)*x 0 + (82222711/156250000 : ℝ)*x 1 + (-2173781119/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267279137/500000000 : ℝ)^8465 ≤ (1750830312271/4000000000000 : ℝ)^6417 := by
    have hnat : (267279137 : ℕ)^8465*4000000000000^6417 ≤ 1750830312271^6417*500000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267279137 500000000 1750830312271 4000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (82222711/156250000 : ℝ)^8465 ≤ (42872924308957/100000000000000 : ℝ)^6417 := by
    have hnat : (82222711 : ℕ)^8465*100000000000000^6417 ≤ 42872924308957^6417*156250000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82222711 156250000 42872924308957 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2173781119/10000000000 : ℝ)^8465 ≤ (13356317865947/100000000000000 : ℝ)^6417 := by
    have hnat : (2173781119 : ℕ)^8465*100000000000000^6417 ≤ 13356317865947^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173781119 10000000000 13356317865947 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267279137/500000000 : ℝ), (82222711/156250000 : ℝ), (-2173781119/10000000000 : ℝ)] ![(1750830312271/4000000000000 : ℝ), (42872924308957/100000000000000 : ℝ), (13356317865947/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267279137/500000000 : ℝ)|^8465 ≤ (1750830312271/4000000000000 : ℝ)^6417
        have hw : |(267279137/500000000 : ℝ)|=(267279137/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(82222711/156250000 : ℝ)|^8465 ≤ (42872924308957/100000000000000 : ℝ)^6417
        have hw : |(82222711/156250000 : ℝ)|=(82222711/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2173781119/10000000000 : ℝ)|^8465 ≤ (13356317865947/100000000000000 : ℝ)^6417
        have hw : |(-2173781119/10000000000 : ℝ)|=(2173781119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s4_3 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (869276943/2000000000 : ℝ)*x 0 + (2105851197/5000000000 : ℝ)*x 1 + (4485221133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (869276943/2000000000 : ℝ)^8465 ≤ (16657351797111/50000000000000 : ℝ)^6417 := by
    have hnat : (869276943 : ℕ)^8465*50000000000000^6417 ≤ 16657351797111^6417*2000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      869276943 2000000000 16657351797111 50000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2105851197/5000000000 : ℝ)^8465 ≤ (7989921377819/25000000000000 : ℝ)^6417 := by
    have hnat : (2105851197 : ℕ)^8465*25000000000000^6417 ≤ 7989921377819^6417*5000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2105851197 5000000000 7989921377819 25000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4485221133/10000000000 : ℝ)^8465 ≤ (34725610883233/100000000000000 : ℝ)^6417 := by
    have hnat : (4485221133 : ℕ)^8465*100000000000000^6417 ≤ 34725610883233^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4485221133 10000000000 34725610883233 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(869276943/2000000000 : ℝ), (2105851197/5000000000 : ℝ), (4485221133/10000000000 : ℝ)] ![(16657351797111/50000000000000 : ℝ), (7989921377819/25000000000000 : ℝ), (34725610883233/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(869276943/2000000000 : ℝ)|^8465 ≤ (16657351797111/50000000000000 : ℝ)^6417
        have hw : |(869276943/2000000000 : ℝ)|=(869276943/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2105851197/5000000000 : ℝ)|^8465 ≤ (7989921377819/25000000000000 : ℝ)^6417
        have hw : |(2105851197/5000000000 : ℝ)|=(2105851197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4485221133/10000000000 : ℝ)|^8465 ≤ (34725610883233/100000000000000 : ℝ)^6417
        have hw : |(4485221133/10000000000 : ℝ)|=(4485221133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s4_4 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-10528703/50000000 : ℝ)*x 0 + (5262622121/10000000000 : ℝ)*x 1 + (1079187979/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10528703/50000000 : ℝ)^8465 ≤ (2561521510563/20000000000000 : ℝ)^6417 := by
    have hnat : (10528703 : ℕ)^8465*20000000000000^6417 ≤ 2561521510563^6417*50000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10528703 50000000 2561521510563 20000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5262622121/10000000000 : ℝ)^8465 ≤ (21438443026799/50000000000000 : ℝ)^6417 := by
    have hnat : (5262622121 : ℕ)^8465*50000000000000^6417 ≤ 21438443026799^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262622121 10000000000 21438443026799 50000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1079187979/2000000000 : ℝ)^8465 ≤ (44315506375501/100000000000000 : ℝ)^6417 := by
    have hnat : (1079187979 : ℕ)^8465*100000000000000^6417 ≤ 44315506375501^6417*2000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079187979 2000000000 44315506375501 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-10528703/50000000 : ℝ), (5262622121/10000000000 : ℝ), (1079187979/2000000000 : ℝ)] ![(2561521510563/20000000000000 : ℝ), (21438443026799/50000000000000 : ℝ), (44315506375501/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-10528703/50000000 : ℝ)|^8465 ≤ (2561521510563/20000000000000 : ℝ)^6417
        have hw : |(-10528703/50000000 : ℝ)|=(10528703/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5262622121/10000000000 : ℝ)|^8465 ≤ (21438443026799/50000000000000 : ℝ)^6417
        have hw : |(5262622121/10000000000 : ℝ)|=(5262622121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1079187979/2000000000 : ℝ)|^8465 ≤ (44315506375501/100000000000000 : ℝ)^6417
        have hw : |(1079187979/2000000000 : ℝ)|=(1079187979/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s4_5 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311310959/10000000000 : ℝ)*x 0 + (-2040094781/10000000000 : ℝ)*x 1 + (84311559/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311310959/10000000000 : ℝ)^8465 ≤ (43400950564181/100000000000000 : ℝ)^6417 := by
    have hnat : (5311310959 : ℕ)^8465*100000000000000^6417 ≤ 43400950564181^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311310959 10000000000 43400950564181 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2040094781/10000000000 : ℝ)^8465 ≤ (1535443042453/12500000000000 : ℝ)^6417 := by
    have hnat : (2040094781 : ℕ)^8465*12500000000000^6417 ≤ 1535443042453^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2040094781 10000000000 1535443042453 12500000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84311559/156250000 : ℝ)^8465 ≤ (44315505086271/100000000000000 : ℝ)^6417 := by
    have hnat : (84311559 : ℕ)^8465*100000000000000^6417 ≤ 44315505086271^6417*156250000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84311559 156250000 44315505086271 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311310959/10000000000 : ℝ), (-2040094781/10000000000 : ℝ), (84311559/156250000 : ℝ)] ![(43400950564181/100000000000000 : ℝ), (1535443042453/12500000000000 : ℝ), (44315505086271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311310959/10000000000 : ℝ)|^8465 ≤ (43400950564181/100000000000000 : ℝ)^6417
        have hw : |(5311310959/10000000000 : ℝ)|=(5311310959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2040094781/10000000000 : ℝ)|^8465 ≤ (1535443042453/12500000000000 : ℝ)^6417
        have hw : |(-2040094781/10000000000 : ℝ)|=(2040094781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84311559/156250000 : ℝ)|^8465 ≤ (44315505086271/100000000000000 : ℝ)^6417
        have hw : |(84311559/156250000 : ℝ)|=(84311559/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s4_6 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311311147/10000000000 : ℝ)*x 0 + (1348984879/2500000000 : ℝ)*x 1 + (-12750593/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311311147/10000000000 : ℝ)^8465 ≤ (21700476295349/50000000000000 : ℝ)^6417 := by
    have hnat : (5311311147 : ℕ)^8465*50000000000000^6417 ≤ 21700476295349^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311311147 10000000000 21700476295349 50000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348984879/2500000000 : ℝ)^8465 ≤ (8863100453893/20000000000000 : ℝ)^6417 := by
    have hnat : (1348984879 : ℕ)^8465*20000000000000^6417 ≤ 8863100453893^6417*2500000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348984879 2500000000 8863100453893 20000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (12750593/62500000 : ℝ)^8465 ≤ (191930392593/1562500000000 : ℝ)^6417 := by
    have hnat : (12750593 : ℕ)^8465*1562500000000^6417 ≤ 191930392593^6417*62500000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12750593 62500000 191930392593 1562500000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311311147/10000000000 : ℝ), (1348984879/2500000000 : ℝ), (-12750593/62500000 : ℝ)] ![(21700476295349/50000000000000 : ℝ), (8863100453893/20000000000000 : ℝ), (191930392593/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311311147/10000000000 : ℝ)|^8465 ≤ (21700476295349/50000000000000 : ℝ)^6417
        have hw : |(5311311147/10000000000 : ℝ)|=(5311311147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348984879/2500000000 : ℝ)|^8465 ≤ (8863100453893/20000000000000 : ℝ)^6417
        have hw : |(1348984879/2500000000 : ℝ)|=(1348984879/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-12750593/62500000 : ℝ)|^8465 ≤ (191930392593/1562500000000 : ℝ)^6417
        have hw : |(-12750593/62500000 : ℝ)|=(12750593/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s4_7 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1086599203/2500000000 : ℝ)*x 0 + (4484468903/10000000000 : ℝ)*x 1 + (4212457621/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1086599203/2500000000 : ℝ)^8465 ≤ (16657412954733/50000000000000 : ℝ)^6417 := by
    have hnat : (1086599203 : ℕ)^8465*50000000000000^6417 ≤ 16657412954733^6417*2500000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086599203 2500000000 16657412954733 50000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4484468903/10000000000 : ℝ)^8465 ≤ (216987052681/625000000000 : ℝ)^6417 := by
    have hnat : (4484468903 : ℕ)^8465*625000000000^6417 ≤ 216987052681^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4484468903 10000000000 216987052681 625000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4212457621/10000000000 : ℝ)^8465 ≤ (31967245648511/100000000000000 : ℝ)^6417 := by
    have hnat : (4212457621 : ℕ)^8465*100000000000000^6417 ≤ 31967245648511^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4212457621 10000000000 31967245648511 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1086599203/2500000000 : ℝ), (4484468903/10000000000 : ℝ), (4212457621/10000000000 : ℝ)] ![(16657412954733/50000000000000 : ℝ), (216987052681/625000000000 : ℝ), (31967245648511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1086599203/2500000000 : ℝ)|^8465 ≤ (16657412954733/50000000000000 : ℝ)^6417
        have hw : |(1086599203/2500000000 : ℝ)|=(1086599203/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4484468903/10000000000 : ℝ)|^8465 ≤ (216987052681/625000000000 : ℝ)^6417
        have hw : |(4484468903/10000000000 : ℝ)|=(4484468903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4212457621/10000000000 : ℝ)|^8465 ≤ (31967245648511/100000000000000 : ℝ)^6417
        have hw : |(4212457621/10000000000 : ℝ)|=(4212457621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1271_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152016389/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7337/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5493/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (57/500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14239/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7337/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5493/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7337/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5493/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7337/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5493/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7337/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5493/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7337/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5493/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7337/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5493/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5493/50000 : ℝ) ^ (529/128 : ℝ) ≤ (2715875742381803/25000000000000000000 : ℝ) := by
    have hpowers : (5493/50000 : ℝ)^529 ≤ (2715875742381803/25000000000000000000 : ℝ)^128 := by
      have hnat : (5493 : ℕ)^529*25000000000000000000^128 ≤ 2715875742381803^128*50000^529 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5493 50000 2715875742381803 25000000000000000000 529 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5493/50000 : ℝ)) (X := (2715875742381803/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 529 128 (by norm_num) hpowers
    exact h
  have hpowhi : (7337/50000 : ℝ) ^ (529/128 : ℝ) ≤ (17966822939108683/50000000000000000000 : ℝ) := by
    have hpowers : (7337/50000 : ℝ)^529 ≤ (17966822939108683/50000000000000000000 : ℝ)^128 := by
      have hnat : (7337 : ℕ)^529*50000000000000000000^128 ≤ 17966822939108683^128*50000^529 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7337 50000 17966822939108683 50000000000000000000 529 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7337/50000 : ℝ)) (X := (17966822939108683/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 529 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502715875742381803/12500000000000000000 : ℝ) ≤ (5000262838163703/5000000000000000 : ℝ) ^ (529/128 : ℝ) := by
    have hpowers : (12502715875742381803/12500000000000000000 : ℝ)^128 ≤ (5000262838163703/5000000000000000 : ℝ)^529 := by
      have hnat : (12502715875742381803 : ℕ)^128*5000000000000000^529 ≤ 5000262838163703^529*12500000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502715875742381803 12500000000000000000 5000262838163703 5000000000000000 128 529 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000262838163703/5000000000000000 : ℝ)) (X := (12502715875742381803/12500000000000000000 : ℝ)) (by norm_num) 529 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023398574423872289/50000000000000000000 : ℝ) ≤ (10001132130982291/10000000000000000 : ℝ) ^ (529/128 : ℝ) := by
    have hpowers : (50023398574423872289/50000000000000000000 : ℝ)^128 ≤ (10001132130982291/10000000000000000 : ℝ)^529 := by
      have hnat : (50023398574423872289 : ℕ)^128*10000000000000000^529 ≤ 10001132130982291^529*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023398574423872289 50000000000000000000 10001132130982291 10000000000000000 128 529 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001132130982291/10000000000000000 : ℝ)) (X := (50023398574423872289/50000000000000000000 : ℝ)) (by norm_num) 529 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017966822939108683/25000000000000000000 : ℝ) ≤ (1250217323204647/1250000000000000 : ℝ) ^ (529/128 : ℝ) := by
    have hpowers : (25017966822939108683/25000000000000000000 : ℝ)^128 ≤ (1250217323204647/1250000000000000 : ℝ)^529 := by
      have hnat : (25017966822939108683 : ℕ)^128*1250000000000000^529 ≤ 1250217323204647^529*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017966822939108683 25000000000000000000 1250217323204647 1250000000000000 128 529 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250217323204647/1250000000000000 : ℝ)) (X := (25017966822939108683/25000000000000000000 : ℝ)) (by norm_num) 529 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2715875742381803/25000000000000000000 : ℝ) ≤ ((9217153418154585027/9220000000000000000 : ℝ)+2*(121290930977/73760000000000 : ℝ)*(5493/50000 : ℝ))^(529/128 : ℝ) := by
    rw [show (9217153418154585027/9220000000000000000 : ℝ)+2*(121290930977/73760000000000 : ℝ)*(5493/50000 : ℝ)=(5000262838163703/5000000000000000 : ℝ) by norm_num, show 1+2*(2715875742381803/25000000000000000000 : ℝ)=(12502715875742381803/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17966822939108683/50000000000000000000 : ℝ)+(2715875742381803/25000000000000000000 : ℝ) ≤ ((9217153418154585027/9220000000000000000 : ℝ)+(121290930977/73760000000000 : ℝ)*((7337/50000 : ℝ)+(5493/50000 : ℝ)))^(529/128 : ℝ) := by
    rw [show (9217153418154585027/9220000000000000000 : ℝ)+(121290930977/73760000000000 : ℝ)*((7337/50000 : ℝ)+(5493/50000 : ℝ))=(10001132130982291/10000000000000000 : ℝ) by norm_num, show 1+(17966822939108683/50000000000000000000 : ℝ)+(2715875742381803/25000000000000000000 : ℝ)=(50023398574423872289/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17966822939108683/50000000000000000000 : ℝ) ≤ ((9217153418154585027/9220000000000000000 : ℝ)+2*(121290930977/73760000000000 : ℝ)*(7337/50000 : ℝ))^(529/128 : ℝ) := by
    rw [show (9217153418154585027/9220000000000000000 : ℝ)+2*(121290930977/73760000000000 : ℝ)*(7337/50000 : ℝ)=(1250217323204647/1250000000000000 : ℝ) by norm_num, show 1+2*(17966822939108683/50000000000000000000 : ℝ)=(25017966822939108683/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9217153418154585027/9220000000000000000 : ℝ)*(X 1 0+X 2 0)+(121290930977/73760000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (529/128 : ℝ)) (lo := (5493/50000 : ℝ)) (hi := (7337/50000 : ℝ)) (c := (9217153418154585027/9220000000000000000 : ℝ)) (alpha := (121290930977/73760000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9217153418154585027/9220000000000000000 : ℝ)*(X 0 1+X 2 1)+(121290930977/73760000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (529/128 : ℝ)) (lo := (5493/50000 : ℝ)) (hi := (7337/50000 : ℝ)) (c := (9217153418154585027/9220000000000000000 : ℝ)) (alpha := (121290930977/73760000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9217153418154585027/9220000000000000000 : ℝ)*(X 0 2+X 1 2)+(121290930977/73760000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (529/128 : ℝ)) (lo := (5493/50000 : ℝ)) (hi := (7337/50000 : ℝ)) (c := (9217153418154585027/9220000000000000000 : ℝ)) (alpha := (121290930977/73760000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-421146993/2000000000 : ℝ)*X 0 0+(5396309759/10000000000 : ℝ)*X 0 1+(5262253491/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672791391/5000000000 : ℝ)*X 1 0+(-1086890537/5000000000 : ℝ)*X 1 1+(657781687/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((267279137/500000000 : ℝ)*X 2 0+(82222711/156250000 : ℝ)*X 2 1+(-2173781119/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((869276943/2000000000 : ℝ)*X 0 0+(2105851197/5000000000 : ℝ)*X 0 1+(4485221133/10000000000 : ℝ)*X 0 2+(869276943/2000000000 : ℝ)*X 1 0+(2105851197/5000000000 : ℝ)*X 1 1+(4485221133/10000000000 : ℝ)*X 1 2+(869276943/2000000000 : ℝ)*X 2 0+(2105851197/5000000000 : ℝ)*X 2 1+(4485221133/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-10528703/50000000 : ℝ)*X 0 0+(5262622121/10000000000 : ℝ)*X 0 1+(1079187979/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5311310959/10000000000 : ℝ)*X 1 0+(-2040094781/10000000000 : ℝ)*X 1 1+(84311559/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5311311147/10000000000 : ℝ)*X 2 0+(1348984879/2500000000 : ℝ)*X 2 1+(-12750593/62500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1086599203/2500000000 : ℝ)*X 0 0+(4484468903/10000000000 : ℝ)*X 0 1+(4212457621/10000000000 : ℝ)*X 0 2+(1086599203/2500000000 : ℝ)*X 1 0+(4484468903/10000000000 : ℝ)*X 1 1+(4212457621/10000000000 : ℝ)*X 1 2+(1086599203/2500000000 : ℝ)*X 2 0+(4484468903/10000000000 : ℝ)*X 2 1+(4212457621/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2266295958459410146995649929/461000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5102799/500000000000 : ℝ)*(base19) + (881012683/100000000000000 : ℝ)*(base23) + (21632861/50000000000000 : ℝ)*(lower2) + (173526893/100000000000000 : ℝ)*(upper3) + (33715177/100000000000000 : ℝ)*(upper5) + (5557844925000597/100000000000000 : ℝ)*(major0) + (5557844925000597/100000000000000 : ℝ)*(major1) + (5557844925000597/100000000000000 : ℝ)*(major2) + (1864895875639581/25000000000000 : ℝ)*(sp0) + (3729802974364223/50000000000000 : ℝ)*(sp1) + (1864901522068891/25000000000000 : ℝ)*(sp2) + (1828034123732483/50000000000000 : ℝ)*(sp3) + (11733364961/50000000000000 : ℝ)*(sp4) + (14469379859/100000000000000 : ℝ)*(sp7) + (457010339605603/12500000000000 : ℝ)*(f.failure) + (7459606969288247/100000000000000 : ℝ)*(f.sum) + (621278111571/147520000000000000000000000 : ℝ)*base66 + (4667292423622886119/922000000000000000000000000000000 : ℝ)*base67 + (3729537811318886119/922000000000000000000000000000000 : ℝ)*base69 + (7069859191080886119/922000000000000000000000000000000 : ℝ)*base71 + (30752144164307/3688000000000000000000000000 : ℝ)*base74 + (10637161864794886119/922000000000000000000000000000000 : ℝ)*base75 + (11171884592944886119/922000000000000000000000000000000 : ℝ)*base77 + (4981797892306886119/922000000000000000000000000000000 : ℝ)*base79 + (9521742600819/3688000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (10272433/1250000000000000000000 : ℝ)*base90 + (10272433/1250000000000000000000 : ℝ)*base92 + (10272433/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (640506831914374369551/230500000000000000000000000 : ℝ) := by norm_num
    linear_combination (70001169/10000000000000 : ℝ)*(base23) + (3432699/25000000000000 : ℝ)*(lower2) + (27474819/25000000000000 : ℝ)*(lower3) + (117534317/50000000000000 : ℝ)*(lower4) + (34928760359193/625000000000 : ℝ)*(major0) + (34928760359193/625000000000 : ℝ)*(major1) + (34928760359193/625000000000 : ℝ)*(major2) + (5594257573/100000000000000 : ℝ)*(sp0) + (892259907/12500000000000 : ℝ)*(sp1) + (9893603649/100000000000000 : ℝ)*(sp2) + (7500882400316223/100000000000000 : ℝ)*(sp4) + (3750440428247269/50000000000000 : ℝ)*(sp5) + (937609675119807/12500000000000 : ℝ)*(sp6) + (22976970173389/625000000000 : ℝ)*(sp7) + (22976970173389/625000000000 : ℝ)*(f.failure) + (1500177598914759/20000000000000 : ℝ)*(f.sum) + (362671564797/92200000000000000000000000 : ℝ)*base65 + (5667385015396789/5762500000000000000000000000000 : ℝ)*base68 + (1105982196628211/5762500000000000000000000000000 : ℝ)*base69 + (17679588856553211/5762500000000000000000000000000 : ℝ)*base71 + (389411450271/230500000000000000000000000 : ℝ)*base73 + (37074536007928211/5762500000000000000000000000000 : ℝ)*base75 + (10580374741421789/5762500000000000000000000000000 : ℝ)*base78 + (63567022895671789/5762500000000000000000000000000 : ℝ)*base80 + (2889443665351/461000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base86 + (327679/62500000000000000000 : ℝ)*base90 + (327679/62500000000000000000 : ℝ)*base92 + (327679/62500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1271_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152016389/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7337/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5493/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (57/500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14239/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1271_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1271_s5_0 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2106138627/10000000000 : ℝ)*x 0 + (168490427/312500000 : ℝ)*x 1 + (5266604229/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2106138627/10000000000 : ℝ)^8465 ≤ (512432047047/4000000000000 : ℝ)^6417 := by
    have hnat : (2106138627 : ℕ)^8465*4000000000000^6417 ≤ 512432047047^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2106138627 10000000000 512432047047 4000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (168490427/312500000 : ℝ)^8465 ≤ (44269509047657/100000000000000 : ℝ)^6417 := by
    have hnat : (168490427 : ℕ)^8465*100000000000000^6417 ≤ 44269509047657^6417*312500000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168490427 312500000 44269509047657 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266604229/10000000000 : ℝ)^8465 ≤ (5364961220729/12500000000000 : ℝ)^6417 := by
    have hnat : (5266604229 : ℕ)^8465*12500000000000^6417 ≤ 5364961220729^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266604229 10000000000 5364961220729 12500000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2106138627/10000000000 : ℝ), (168490427/312500000 : ℝ), (5266604229/10000000000 : ℝ)] ![(512432047047/4000000000000 : ℝ), (44269509047657/100000000000000 : ℝ), (5364961220729/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2106138627/10000000000 : ℝ)|^8465 ≤ (512432047047/4000000000000 : ℝ)^6417
        have hw : |(-2106138627/10000000000 : ℝ)|=(2106138627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(168490427/312500000 : ℝ)|^8465 ≤ (44269509047657/100000000000000 : ℝ)^6417
        have hw : |(168490427/312500000 : ℝ)|=(168490427/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266604229/10000000000 : ℝ)|^8465 ≤ (5364961220729/12500000000000 : ℝ)^6417
        have hw : |(5266604229/10000000000 : ℝ)|=(5266604229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s5_1 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068882669/2000000000 : ℝ)*x 0 + (-2169568037/10000000000 : ℝ)*x 1 + (5266604489/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068882669/2000000000 : ℝ)^8465 ≤ (8751625406327/20000000000000 : ℝ)^6417 := by
    have hnat : (1068882669 : ℕ)^8465*20000000000000^6417 ≤ 8751625406327^6417*2000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068882669 2000000000 8751625406327 20000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2169568037/10000000000 : ℝ)^8465 ≤ (6661090196439/50000000000000 : ℝ)^6417 := by
    have hnat : (2169568037 : ℕ)^8465*50000000000000^6417 ≤ 6661090196439^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2169568037 10000000000 6661090196439 50000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266604489/10000000000 : ℝ)^8465 ≤ (2682480785057/6250000000000 : ℝ)^6417 := by
    have hnat : (5266604489 : ℕ)^8465*6250000000000^6417 ≤ 2682480785057^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266604489 10000000000 2682480785057 6250000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068882669/2000000000 : ℝ), (-2169568037/10000000000 : ℝ), (5266604489/10000000000 : ℝ)] ![(8751625406327/20000000000000 : ℝ), (6661090196439/50000000000000 : ℝ), (2682480785057/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068882669/2000000000 : ℝ)|^8465 ≤ (8751625406327/20000000000000 : ℝ)^6417
        have hw : |(1068882669/2000000000 : ℝ)|=(1068882669/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2169568037/10000000000 : ℝ)|^8465 ≤ (6661090196439/50000000000000 : ℝ)^6417
        have hw : |(-2169568037/10000000000 : ℝ)|=(2169568037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266604489/10000000000 : ℝ)|^8465 ≤ (2682480785057/6250000000000 : ℝ)^6417
        have hw : |(5266604489/10000000000 : ℝ)|=(5266604489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s5_2 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344412433/10000000000 : ℝ)*x 0 + (526660549/1000000000 : ℝ)*x 1 + (-86782717/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344412433/10000000000 : ℝ)^8465 ≤ (21879058590679/50000000000000 : ℝ)^6417 := by
    have hnat : (5344412433 : ℕ)^8465*50000000000000^6417 ≤ 21879058590679^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344412433 10000000000 21879058590679 50000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526660549/1000000000 : ℝ)^8465 ≤ (2682481457623/6250000000000 : ℝ)^6417 := by
    have hnat : (526660549 : ℕ)^8465*6250000000000^6417 ≤ 2682481457623^6417*1000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526660549 1000000000 2682481457623 6250000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (86782717/400000000 : ℝ)^8465 ≤ (13322179485653/100000000000000 : ℝ)^6417 := by
    have hnat : (86782717 : ℕ)^8465*100000000000000^6417 ≤ 13322179485653^6417*400000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86782717 400000000 13322179485653 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344412433/10000000000 : ℝ), (526660549/1000000000 : ℝ), (-86782717/400000000 : ℝ)] ![(21879058590679/50000000000000 : ℝ), (2682481457623/6250000000000 : ℝ), (13322179485653/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344412433/10000000000 : ℝ)|^8465 ≤ (21879058590679/50000000000000 : ℝ)^6417
        have hw : |(5344412433/10000000000 : ℝ)|=(5344412433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526660549/1000000000 : ℝ)|^8465 ≤ (2682481457623/6250000000000 : ℝ)^6417
        have hw : |(526660549/1000000000 : ℝ)|=(526660549/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-86782717/400000000 : ℝ)|^8465 ≤ (13322179485653/100000000000000 : ℝ)^6417
        have hw : |(-86782717/400000000 : ℝ)|=(86782717/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s5_3 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2173311441/5000000000 : ℝ)*x 0 + (2110410671/5000000000 : ℝ)*x 1 + (2238020801/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2173311441/5000000000 : ℝ)^8465 ≤ (4164638971189/12500000000000 : ℝ)^6417 := by
    have hnat : (2173311441 : ℕ)^8465*12500000000000^6417 ≤ 4164638971189^6417*5000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173311441 5000000000 4164638971189 12500000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2110410671/5000000000 : ℝ)^8465 ≤ (6410199778961/20000000000000 : ℝ)^6417 := by
    have hnat : (2110410671 : ℕ)^8465*20000000000000^6417 ≤ 6410199778961^6417*5000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2110410671 5000000000 6410199778961 20000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2238020801/5000000000 : ℝ)^8465 ≤ (34631889319791/100000000000000 : ℝ)^6417 := by
    have hnat : (2238020801 : ℕ)^8465*100000000000000^6417 ≤ 34631889319791^6417*5000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2238020801 5000000000 34631889319791 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2173311441/5000000000 : ℝ), (2110410671/5000000000 : ℝ), (2238020801/5000000000 : ℝ)] ![(4164638971189/12500000000000 : ℝ), (6410199778961/20000000000000 : ℝ), (34631889319791/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2173311441/5000000000 : ℝ)|^8465 ≤ (4164638971189/12500000000000 : ℝ)^6417
        have hw : |(2173311441/5000000000 : ℝ)|=(2173311441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2110410671/5000000000 : ℝ)|^8465 ≤ (6410199778961/20000000000000 : ℝ)^6417
        have hw : |(2110410671/5000000000 : ℝ)|=(2110410671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2238020801/5000000000 : ℝ)|^8465 ≤ (34631889319791/100000000000000 : ℝ)^6417
        have hw : |(2238020801/5000000000 : ℝ)|=(2238020801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s5_4 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1053071399/5000000000 : ℝ)*x 0 + (1316731563/2500000000 : ℝ)*x 1 + (1347842737/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1053071399/5000000000 : ℝ)^8465 ≤ (200169291309/1562500000000 : ℝ)^6417 := by
    have hnat : (1053071399 : ℕ)^8465*1562500000000^6417 ≤ 200169291309^6417*5000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053071399 5000000000 200169291309 1562500000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316731563/2500000000 : ℝ)^8465 ≤ (21461575822649/50000000000000 : ℝ)^6417 := by
    have hnat : (1316731563 : ℕ)^8465*50000000000000^6417 ≤ 21461575822649^6417*2500000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316731563 2500000000 21461575822649 50000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347842737/2500000000 : ℝ)^8465 ≤ (22133006848427/50000000000000 : ℝ)^6417 := by
    have hnat : (1347842737 : ℕ)^8465*50000000000000^6417 ≤ 22133006848427^6417*2500000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347842737 2500000000 22133006848427 50000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1053071399/5000000000 : ℝ), (1316731563/2500000000 : ℝ), (1347842737/2500000000 : ℝ)] ![(200169291309/1562500000000 : ℝ), (21461575822649/50000000000000 : ℝ), (22133006848427/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1053071399/5000000000 : ℝ)|^8465 ≤ (200169291309/1562500000000 : ℝ)^6417
        have hw : |(-1053071399/5000000000 : ℝ)|=(1053071399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316731563/2500000000 : ℝ)|^8465 ≤ (21461575822649/50000000000000 : ℝ)^6417
        have hw : |(1316731563/2500000000 : ℝ)|=(1316731563/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347842737/2500000000 : ℝ)|^8465 ≤ (22133006848427/50000000000000 : ℝ)^6417
        have hw : |(1347842737/2500000000 : ℝ)|=(1347842737/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s5_5 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656215979/5000000000 : ℝ)*x 0 + (-2044802713/10000000000 : ℝ)*x 1 + (5391370937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656215979/5000000000 : ℝ)^8465 ≤ (8682606921577/20000000000000 : ℝ)^6417 := by
    have hnat : (2656215979 : ℕ)^8465*20000000000000^6417 ≤ 8682606921577^6417*5000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656215979 5000000000 8682606921577 20000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2044802713/10000000000 : ℝ)^8465 ≤ (3080237951091/25000000000000 : ℝ)^6417 := by
    have hnat : (2044802713 : ℕ)^8465*25000000000000^6417 ≤ 3080237951091^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2044802713 10000000000 3080237951091 25000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391370937/10000000000 : ℝ)^8465 ≤ (44266013577713/100000000000000 : ℝ)^6417 := by
    have hnat : (5391370937 : ℕ)^8465*100000000000000^6417 ≤ 44266013577713^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391370937 10000000000 44266013577713 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656215979/5000000000 : ℝ), (-2044802713/10000000000 : ℝ), (5391370937/10000000000 : ℝ)] ![(8682606921577/20000000000000 : ℝ), (3080237951091/25000000000000 : ℝ), (44266013577713/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656215979/5000000000 : ℝ)|^8465 ≤ (8682606921577/20000000000000 : ℝ)^6417
        have hw : |(2656215979/5000000000 : ℝ)|=(2656215979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2044802713/10000000000 : ℝ)|^8465 ≤ (3080237951091/25000000000000 : ℝ)^6417
        have hw : |(-2044802713/10000000000 : ℝ)|=(2044802713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391370937/10000000000 : ℝ)|^8465 ≤ (44266013577713/100000000000000 : ℝ)^6417
        have hw : |(5391370937/10000000000 : ℝ)|=(5391370937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s5_6 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312431969/10000000000 : ℝ)*x 0 + (5391370933/10000000000 : ℝ)*x 1 + (-2044802703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312431969/10000000000 : ℝ)^8465 ≤ (21706517363233/50000000000000 : ℝ)^6417 := by
    have hnat : (5312431969 : ℕ)^8465*50000000000000^6417 ≤ 21706517363233^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312431969 10000000000 21706517363233 50000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391370933/10000000000 : ℝ)^8465 ≤ (4426601353439/10000000000000 : ℝ)^6417 := by
    have hnat : (5391370933 : ℕ)^8465*10000000000000^6417 ≤ 4426601353439^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391370933 10000000000 4426601353439 10000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2044802703/10000000000 : ℝ)^8465 ≤ (6160475862439/50000000000000 : ℝ)^6417 := by
    have hnat : (2044802703 : ℕ)^8465*50000000000000^6417 ≤ 6160475862439^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2044802703 10000000000 6160475862439 50000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312431969/10000000000 : ℝ), (5391370933/10000000000 : ℝ), (-2044802703/10000000000 : ℝ)] ![(21706517363233/50000000000000 : ℝ), (4426601353439/10000000000000 : ℝ), (6160475862439/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312431969/10000000000 : ℝ)|^8465 ≤ (21706517363233/50000000000000 : ℝ)^6417
        have hw : |(5312431969/10000000000 : ℝ)|=(5312431969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391370933/10000000000 : ℝ)|^8465 ≤ (4426601353439/10000000000000 : ℝ)^6417
        have hw : |(5391370933/10000000000 : ℝ)|=(5391370933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2044802703/10000000000 : ℝ)|^8465 ≤ (6160475862439/50000000000000 : ℝ)^6417
        have hw : |(-2044802703/10000000000 : ℝ)|=(2044802703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s5_7 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (543329083/1250000000 : ℝ)*x 0 + (4475386689/10000000000 : ℝ)*x 1 + (263842421/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (543329083/1250000000 : ℝ)^8465 ≤ (16658605339519/50000000000000 : ℝ)^6417 := by
    have hnat : (543329083 : ℕ)^8465*50000000000000^6417 ≤ 16658605339519^6417*1250000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543329083 1250000000 16658605339519 50000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4475386689/10000000000 : ℝ)^8465 ≤ (6925041020793/20000000000000 : ℝ)^6417 := by
    have hnat : (4475386689 : ℕ)^8465*20000000000000^6417 ≤ 6925041020793^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4475386689 10000000000 6925041020793 20000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263842421/625000000 : ℝ)^8465 ≤ (32057584202197/100000000000000 : ℝ)^6417 := by
    have hnat : (263842421 : ℕ)^8465*100000000000000^6417 ≤ 32057584202197^6417*625000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263842421 625000000 32057584202197 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(543329083/1250000000 : ℝ), (4475386689/10000000000 : ℝ), (263842421/625000000 : ℝ)] ![(16658605339519/50000000000000 : ℝ), (6925041020793/20000000000000 : ℝ), (32057584202197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(543329083/1250000000 : ℝ)|^8465 ≤ (16658605339519/50000000000000 : ℝ)^6417
        have hw : |(543329083/1250000000 : ℝ)|=(543329083/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4475386689/10000000000 : ℝ)|^8465 ≤ (6925041020793/20000000000000 : ℝ)^6417
        have hw : |(4475386689/10000000000 : ℝ)|=(4475386689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263842421/625000000 : ℝ)|^8465 ≤ (32057584202197/100000000000000 : ℝ)^6417
        have hw : |(263842421/625000000 : ℝ)|=(263842421/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s5_8 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-28648227/10000000000 : ℝ)*x 0 + (5910921681/10000000000 : ℝ)*x 1 + (2955455773/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (28648227/10000000000 : ℝ)^8465 ≤ (44210433131/100000000000000 : ℝ)^6417 := by
    have hnat : (28648227 : ℕ)^8465*100000000000000^6417 ≤ 44210433131^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28648227 10000000000 44210433131 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5910921681/10000000000 : ℝ)^8465 ≤ (9995590260197/20000000000000 : ℝ)^6417 := by
    have hnat : (5910921681 : ℕ)^8465*20000000000000^6417 ≤ 9995590260197^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5910921681 10000000000 9995590260197 20000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2955455773/5000000000 : ℝ)^8465 ≤ (6247229782309/12500000000000 : ℝ)^6417 := by
    have hnat : (2955455773 : ℕ)^8465*12500000000000^6417 ≤ 6247229782309^6417*5000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2955455773 5000000000 6247229782309 12500000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-28648227/10000000000 : ℝ), (5910921681/10000000000 : ℝ), (2955455773/5000000000 : ℝ)] ![(44210433131/100000000000000 : ℝ), (9995590260197/20000000000000 : ℝ), (6247229782309/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-28648227/10000000000 : ℝ)|^8465 ≤ (44210433131/100000000000000 : ℝ)^6417
        have hw : |(-28648227/10000000000 : ℝ)|=(28648227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5910921681/10000000000 : ℝ)|^8465 ≤ (9995590260197/20000000000000 : ℝ)^6417
        have hw : |(5910921681/10000000000 : ℝ)|=(5910921681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2955455773/5000000000 : ℝ)|^8465 ≤ (6247229782309/12500000000000 : ℝ)^6417
        have hw : |(2955455773/5000000000 : ℝ)|=(2955455773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1271_s5_9 (p : ℝ) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1385255807/10000000000 : ℝ)*x 0 + (1394787013/2500000000 : ℝ)*x 1 + (5579749077/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1385255807/10000000000 : ℝ)^8465 ≤ (147427104119/2000000000000 : ℝ)^6417 := by
    have hnat : (1385255807 : ℕ)^8465*2000000000000^6417 ≤ 147427104119^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1385255807 10000000000 147427104119 2000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1394787013/2500000000 : ℝ)^8465 ≤ (578887896733/1250000000000 : ℝ)^6417 := by
    have hnat : (1394787013 : ℕ)^8465*1250000000000^6417 ≤ 578887896733^6417*2500000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1394787013 2500000000 578887896733 1250000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5579749077/10000000000 : ℝ)^8465 ≤ (46317613035731/100000000000000 : ℝ)^6417 := by
    have hnat : (5579749077 : ℕ)^8465*100000000000000^6417 ≤ 46317613035731^6417*10000000000^8465 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5579749077 10000000000 46317613035731 100000000000000 8465 6417 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8465/2048 : ℝ)) 8465 6417 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1385255807/10000000000 : ℝ), (1394787013/2500000000 : ℝ), (5579749077/10000000000 : ℝ)] ![(147427104119/2000000000000 : ℝ), (578887896733/1250000000000 : ℝ), (46317613035731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1385255807/10000000000 : ℝ)|^8465 ≤ (147427104119/2000000000000 : ℝ)^6417
        have hw : |(1385255807/10000000000 : ℝ)|=(1385255807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1394787013/2500000000 : ℝ)|^8465 ≤ (578887896733/1250000000000 : ℝ)^6417
        have hw : |(1394787013/2500000000 : ℝ)|=(1394787013/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5579749077/10000000000 : ℝ)|^8465 ≤ (46317613035731/100000000000000 : ℝ)^6417
        have hw : |(5579749077/10000000000 : ℝ)|=(5579749077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1271_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152016389/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14239/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (57/500 : ℝ)*pair X i i ≤ pair X i h) :
    (11493/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14143/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14239/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (57/500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14239/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (57/500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14239/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (57/500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14239/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (57/500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14239/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (57/500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14239/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (57/500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (57/500 : ℝ) ^ (529/128 : ℝ) ≤ (6328992561556793/50000000000000000000 : ℝ) := by
    have hpowers : (57/500 : ℝ)^529 ≤ (6328992561556793/50000000000000000000 : ℝ)^128 := by
      have hnat : (57 : ℕ)^529*50000000000000000000^128 ≤ 6328992561556793^128*500^529 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        57 500 6328992561556793 50000000000000000000 529 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (57/500 : ℝ)) (X := (6328992561556793/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 529 128 (by norm_num) hpowers
    exact h
  have hpowhi : (14239/100000 : ℝ) ^ (529/128 : ℝ) ≤ (31731416155609349/100000000000000000000 : ℝ) := by
    have hpowers : (14239/100000 : ℝ)^529 ≤ (31731416155609349/100000000000000000000 : ℝ)^128 := by
      have hnat : (14239 : ℕ)^529*100000000000000000000^128 ≤ 31731416155609349^128*100000^529 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14239 100000 31731416155609349 100000000000000000000 529 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14239/100000 : ℝ)) (X := (31731416155609349/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 529 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006328992561556793/25000000000000000000 : ℝ) ≤ (2500153125392773/2500000000000000 : ℝ) ^ (529/128 : ℝ) := by
    have hpowers : (25006328992561556793/25000000000000000000 : ℝ)^128 ≤ (2500153125392773/2500000000000000 : ℝ)^529 := by
      have hnat : (25006328992561556793 : ℕ)^128*2500000000000000^529 ≤ 2500153125392773^529*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006328992561556793 25000000000000000000 2500153125392773 2500000000000000 128 529 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500153125392773/2500000000000000 : ℝ)) (X := (25006328992561556793/25000000000000000000 : ℝ)) (by norm_num) 529 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (20008877880255744587/20000000000000000000 : ℝ) ≤ (10001073891810911/10000000000000000 : ℝ) ^ (529/128 : ℝ) := by
    have hpowers : (20008877880255744587/20000000000000000000 : ℝ)^128 ≤ (10001073891810911/10000000000000000 : ℝ)^529 := by
      have hnat : (20008877880255744587 : ℕ)^128*10000000000000000^529 ≤ 10001073891810911^529*20000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20008877880255744587 20000000000000000000 10001073891810911 10000000000000000 128 529 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001073891810911/10000000000000000 : ℝ)) (X := (20008877880255744587/20000000000000000000 : ℝ)) (by norm_num) 529 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031731416155609349/50000000000000000000 : ℝ) ≤ (1000153528205073/1000000000000000 : ℝ) ^ (529/128 : ℝ) := by
    have hpowers : (50031731416155609349/50000000000000000000 : ℝ)^128 ≤ (1000153528205073/1000000000000000 : ℝ)^529 := by
      have hnat : (50031731416155609349 : ℕ)^128*1000000000000000^529 ≤ 1000153528205073^529*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031731416155609349 50000000000000000000 1000153528205073 1000000000000000 128 529 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000153528205073/1000000000000000 : ℝ)) (X := (50031731416155609349/50000000000000000000 : ℝ)) (by norm_num) 529 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6328992561556793/50000000000000000000 : ℝ) ≤ ((7095304798623114247/7097500000000000000 : ℝ)+2*(461390239819/283900000000000 : ℝ)*(57/500 : ℝ))^(529/128 : ℝ) := by
    rw [show (7095304798623114247/7097500000000000000 : ℝ)+2*(461390239819/283900000000000 : ℝ)*(57/500 : ℝ)=(2500153125392773/2500000000000000 : ℝ) by norm_num, show 1+2*(6328992561556793/50000000000000000000 : ℝ)=(25006328992561556793/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31731416155609349/100000000000000000000 : ℝ)+(6328992561556793/50000000000000000000 : ℝ) ≤ ((7095304798623114247/7097500000000000000 : ℝ)+(461390239819/283900000000000 : ℝ)*((14239/100000 : ℝ)+(57/500 : ℝ)))^(529/128 : ℝ) := by
    rw [show (7095304798623114247/7097500000000000000 : ℝ)+(461390239819/283900000000000 : ℝ)*((14239/100000 : ℝ)+(57/500 : ℝ))=(10001073891810911/10000000000000000 : ℝ) by norm_num, show 1+(31731416155609349/100000000000000000000 : ℝ)+(6328992561556793/50000000000000000000 : ℝ)=(20008877880255744587/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31731416155609349/100000000000000000000 : ℝ) ≤ ((7095304798623114247/7097500000000000000 : ℝ)+2*(461390239819/283900000000000 : ℝ)*(14239/100000 : ℝ))^(529/128 : ℝ) := by
    rw [show (7095304798623114247/7097500000000000000 : ℝ)+2*(461390239819/283900000000000 : ℝ)*(14239/100000 : ℝ)=(1000153528205073/1000000000000000 : ℝ) by norm_num, show 1+2*(31731416155609349/100000000000000000000 : ℝ)=(50031731416155609349/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7095304798623114247/7097500000000000000 : ℝ)*(X 1 0+X 2 0)+(461390239819/283900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (529/128 : ℝ)) (lo := (57/500 : ℝ)) (hi := (14239/100000 : ℝ)) (c := (7095304798623114247/7097500000000000000 : ℝ)) (alpha := (461390239819/283900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7095304798623114247/7097500000000000000 : ℝ)*(X 0 1+X 2 1)+(461390239819/283900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (529/128 : ℝ)) (lo := (57/500 : ℝ)) (hi := (14239/100000 : ℝ)) (c := (7095304798623114247/7097500000000000000 : ℝ)) (alpha := (461390239819/283900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7095304798623114247/7097500000000000000 : ℝ)*(X 0 2+X 1 2)+(461390239819/283900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (529/128 : ℝ)) (lo := (57/500 : ℝ)) (hi := (14239/100000 : ℝ)) (c := (7095304798623114247/7097500000000000000 : ℝ)) (alpha := (461390239819/283900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2106138627/10000000000 : ℝ)*X 0 0+(168490427/312500000 : ℝ)*X 0 1+(5266604229/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1068882669/2000000000 : ℝ)*X 1 0+(-2169568037/10000000000 : ℝ)*X 1 1+(5266604489/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344412433/10000000000 : ℝ)*X 2 0+(526660549/1000000000 : ℝ)*X 2 1+(-86782717/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2173311441/5000000000 : ℝ)*X 0 0+(2110410671/5000000000 : ℝ)*X 0 1+(2238020801/5000000000 : ℝ)*X 0 2+(2173311441/5000000000 : ℝ)*X 1 0+(2110410671/5000000000 : ℝ)*X 1 1+(2238020801/5000000000 : ℝ)*X 1 2+(2173311441/5000000000 : ℝ)*X 2 0+(2110410671/5000000000 : ℝ)*X 2 1+(2238020801/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1053071399/5000000000 : ℝ)*X 0 0+(1316731563/2500000000 : ℝ)*X 0 1+(1347842737/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656215979/5000000000 : ℝ)*X 1 0+(-2044802713/10000000000 : ℝ)*X 1 1+(5391370937/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312431969/10000000000 : ℝ)*X 2 0+(5391370933/10000000000 : ℝ)*X 2 1+(-2044802703/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((543329083/1250000000 : ℝ)*X 0 0+(4475386689/10000000000 : ℝ)*X 0 1+(263842421/625000000 : ℝ)*X 0 2+(543329083/1250000000 : ℝ)*X 1 0+(4475386689/10000000000 : ℝ)*X 1 1+(263842421/625000000 : ℝ)*X 1 2+(543329083/1250000000 : ℝ)*X 2 0+(4475386689/10000000000 : ℝ)*X 2 1+(263842421/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-28648227/10000000000 : ℝ)*X 0 0+(5910921681/10000000000 : ℝ)*X 0 1+(2955455773/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s5_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1385255807/10000000000 : ℝ)*X 0 0+(1394787013/2500000000 : ℝ)*X 0 1+(5579749077/10000000000 : ℝ)*X 0 2+(1385255807/10000000000 : ℝ)*X 1 0+(1394787013/2500000000 : ℝ)*X 1 1+(5579749077/10000000000 : ℝ)*X 1 2+(1385255807/10000000000 : ℝ)*X 2 0+(1394787013/2500000000 : ℝ)*X 2 1+(5579749077/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1271_s5_9 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (237485785832522872430180763/354875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (382562939/100000000000000 : ℝ)*(lower2) + (365162281/100000000000000 : ℝ)*(lower3) + (992139913/100000000000000 : ℝ)*(lower4) + (49179741/10000000000000 : ℝ)*(lower5) + (5956297087986943/100000000000000 : ℝ)*(major0) + (5956297087986943/100000000000000 : ℝ)*(major1) + (5956297087986943/100000000000000 : ℝ)*(major2) + (799435403267461/10000000000000 : ℝ)*(sp0) + (1998590687009109/25000000000000 : ℝ)*(sp1) + (7994400117373239/100000000000000 : ℝ)*(sp2) + (3918194036293641/100000000000000 : ℝ)*(sp3) + (37148400611/100000000000000 : ℝ)*(sp4) + (37369336803/100000000000000 : ℝ)*(sp5) + (8936298017/100000000000000 : ℝ)*(sp8) + (3918194036293641/100000000000000 : ℝ)*(f.failure) + (7994400117373239/100000000000000 : ℝ)*(f.sum) + (63060432511301/1774375000000000000000000000 : ℝ)*base66 + (8585048277958951921/709750000000000000000000000000000 : ℝ)*base67 + (606447212383298079/709750000000000000000000000000000 : ℝ)*base70 + (5322771431429798079/709750000000000000000000000000000 : ℝ)*base72 + (386182502891/1774375000000000000000000000 : ℝ)*base74 + (2900271497929548079/709750000000000000000000000000000 : ℝ)*base76 + (44490816181511548079/709750000000000000000000000000000 : ℝ)*base78 + (3805262084179201921/709750000000000000000000000000000 : ℝ)*base79 + (3485572488381/1774375000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (51517651/10000000000000000000000 : ℝ)*base90 + (51517651/10000000000000000000000 : ℝ)*base92 + (51517651/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (26458472971358792071719/1774375000000000000000000000 : ℝ) := by norm_num
    linear_combination (44557147/10000000000000 : ℝ)*(lower2) + (291265403/100000000000000 : ℝ)*(lower3) + (109183049/25000000000000 : ℝ)*(lower4) + (142343141/50000000000000 : ℝ)*(lower5) + (5987071455201897/100000000000000 : ℝ)*(major0) + (5987071455201897/100000000000000 : ℝ)*(major1) + (5987071455201897/100000000000000 : ℝ)*(major2) + (216570897/25000000000000 : ℝ)*(sp3) + (100446235369197/1250000000000 : ℝ)*(sp4) + (8035704265610067/100000000000000 : ℝ)*(sp5) + (8035704265610067/100000000000000 : ℝ)*(sp6) + (246152253351463/6250000000000 : ℝ)*(sp7) + (1359018577/25000000000000 : ℝ)*(sp8) + (1227838967/100000000000000 : ℝ)*(sp9) + (1969219073872981/50000000000000 : ℝ)*(f.failure) + (8035704265610067/100000000000000 : ℝ)*(f.sum) + (6005140216263/3548750000000000000000000000 : ℝ)*base66 + (3217647241711798441/709750000000000000000000000000000 : ℝ)*base68 + (21161041123619048441/709750000000000000000000000000000 : ℝ)*base70 + (18714284047788951559/709750000000000000000000000000000 : ℝ)*base71 + (13200611599119/1774375000000000000000000000 : ℝ)*base74 + (7630482196096298441/709750000000000000000000000000000 : ℝ)*base76 + (13801599852203201559/709750000000000000000000000000000 : ℝ)*base77 + (1938729630568951559/709750000000000000000000000000000 : ℝ)*base79 + (96749638732647/14195000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (33714391/5000000000000000000000 : ℝ)*base90 + (33714391/5000000000000000000000 : ℝ)*base92 + (33714391/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1271_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152016389/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14239/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (57/500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11493/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14143/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1271_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1271_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152016389/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8073/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9619/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11493/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14143/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1271_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1271_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1271_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (529/128 : ℝ) ≤ p) (hpb : p ≤ (8465/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152016389/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8073/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9619/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11493/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14143/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1271_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
