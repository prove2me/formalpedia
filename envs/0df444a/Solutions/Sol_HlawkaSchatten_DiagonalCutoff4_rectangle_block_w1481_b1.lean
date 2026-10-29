-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1481_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:13:21.191992+00:00
-- url     : https://prove2.me/submissions/3ca874fc-bb0d-4202-b7d8-dc34975adc29

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
theorem support_rectangle_w1481_s3_0 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1914084187/10000000000 : ℝ)*x 0 + (5441957393/10000000000 : ℝ)*x 1 + (2605862361/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1914084187/10000000000 : ℝ)^4459 ≤ (2923129725073/25000000000000 : ℝ)^3435 := by
    have hnat : (1914084187 : ℕ)^4459*25000000000000^3435 ≤ 2923129725073^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1914084187 10000000000 2923129725073 25000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5441957393/10000000000 : ℝ)^4459 ≤ (45392249444939/100000000000000 : ℝ)^3435 := by
    have hnat : (5441957393 : ℕ)^4459*100000000000000^3435 ≤ 45392249444939^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5441957393 10000000000 45392249444939 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2605862361/5000000000 : ℝ)^4459 ≤ (42915231643241/100000000000000 : ℝ)^3435 := by
    have hnat : (2605862361 : ℕ)^4459*100000000000000^3435 ≤ 42915231643241^3435*5000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2605862361 5000000000 42915231643241 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1914084187/10000000000 : ℝ), (5441957393/10000000000 : ℝ), (2605862361/5000000000 : ℝ)] ![(2923129725073/25000000000000 : ℝ), (45392249444939/100000000000000 : ℝ), (42915231643241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1914084187/10000000000 : ℝ)|^4459 ≤ (2923129725073/25000000000000 : ℝ)^3435
        have hw : |(-1914084187/10000000000 : ℝ)|=(1914084187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5441957393/10000000000 : ℝ)|^4459 ≤ (45392249444939/100000000000000 : ℝ)^3435
        have hw : |(5441957393/10000000000 : ℝ)|=(5441957393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2605862361/5000000000 : ℝ)|^4459 ≤ (42915231643241/100000000000000 : ℝ)^3435
        have hw : |(2605862361/5000000000 : ℝ)|=(2605862361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1481_s3_1 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354468033/10000000000 : ℝ)*x 0 + (-1016094547/5000000000 : ℝ)*x 1 + (325732803/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354468033/10000000000 : ℝ)^4459 ≤ (44447217186093/100000000000000 : ℝ)^3435 := by
    have hnat : (5354468033 : ℕ)^4459*100000000000000^3435 ≤ 44447217186093^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354468033 10000000000 44447217186093 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1016094547/5000000000 : ℝ)^4459 ≤ (12637549816553/100000000000000 : ℝ)^3435 := by
    have hnat : (1016094547 : ℕ)^4459*100000000000000^3435 ≤ 12637549816553^3435*5000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1016094547 5000000000 12637549816553 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (325732803/625000000 : ℝ)^4459 ≤ (21457616495033/50000000000000 : ℝ)^3435 := by
    have hnat : (325732803 : ℕ)^4459*50000000000000^3435 ≤ 21457616495033^3435*625000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      325732803 625000000 21457616495033 50000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354468033/10000000000 : ℝ), (-1016094547/5000000000 : ℝ), (325732803/625000000 : ℝ)] ![(44447217186093/100000000000000 : ℝ), (12637549816553/100000000000000 : ℝ), (21457616495033/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354468033/10000000000 : ℝ)|^4459 ≤ (44447217186093/100000000000000 : ℝ)^3435
        have hw : |(5354468033/10000000000 : ℝ)|=(5354468033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1016094547/5000000000 : ℝ)|^4459 ≤ (12637549816553/100000000000000 : ℝ)^3435
        have hw : |(-1016094547/5000000000 : ℝ)|=(1016094547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(325732803/625000000 : ℝ)|^4459 ≤ (21457616495033/50000000000000 : ℝ)^3435
        have hw : |(325732803/625000000 : ℝ)|=(325732803/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1481_s3_2 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338617007/2500000000 : ℝ)*x 0 + (1302931169/2500000000 : ℝ)*x 1 + (-127011833/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338617007/2500000000 : ℝ)^4459 ≤ (8889443426443/20000000000000 : ℝ)^3435 := by
    have hnat : (1338617007 : ℕ)^4459*20000000000000^3435 ≤ 8889443426443^3435*2500000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338617007 2500000000 8889443426443 20000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1302931169/2500000000 : ℝ)^4459 ≤ (42915231151543/100000000000000 : ℝ)^3435 := by
    have hnat : (1302931169 : ℕ)^4459*100000000000000^3435 ≤ 42915231151543^3435*2500000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1302931169 2500000000 42915231151543 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (127011833/625000000 : ℝ)^4459 ≤ (505502068221/4000000000000 : ℝ)^3435 := by
    have hnat : (127011833 : ℕ)^4459*4000000000000^3435 ≤ 505502068221^3435*625000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127011833 625000000 505502068221 4000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338617007/2500000000 : ℝ), (1302931169/2500000000 : ℝ), (-127011833/625000000 : ℝ)] ![(8889443426443/20000000000000 : ℝ), (42915231151543/100000000000000 : ℝ), (505502068221/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338617007/2500000000 : ℝ)|^4459 ≤ (8889443426443/20000000000000 : ℝ)^3435
        have hw : |(1338617007/2500000000 : ℝ)|=(1338617007/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1302931169/2500000000 : ℝ)|^4459 ≤ (42915231151543/100000000000000 : ℝ)^3435
        have hw : |(1302931169/2500000000 : ℝ)|=(1302931169/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-127011833/625000000 : ℝ)|^4459 ≤ (505502068221/4000000000000 : ℝ)^3435
        have hw : |(-127011833/625000000 : ℝ)|=(127011833/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1481_s3_3 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (535497963/1250000000 : ℝ)*x 0 + (8070539/20000000 : ℝ)*x 1 + (28412233/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535497963/1250000000 : ℝ)^4459 ≤ (33273524207171/100000000000000 : ℝ)^3435 := by
    have hnat : (535497963 : ℕ)^4459*100000000000000^3435 ≤ 33273524207171^3435*1250000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535497963 1250000000 33273524207171 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8070539/20000000 : ℝ)^4459 ≤ (15393951511149/50000000000000 : ℝ)^3435 := by
    have hnat : (8070539 : ℕ)^4459*50000000000000^3435 ≤ 15393951511149^3435*20000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8070539 20000000 15393951511149 50000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (28412233/62500000 : ℝ)^4459 ≤ (8984643188311/25000000000000 : ℝ)^3435 := by
    have hnat : (28412233 : ℕ)^4459*25000000000000^3435 ≤ 8984643188311^3435*62500000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28412233 62500000 8984643188311 25000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535497963/1250000000 : ℝ), (8070539/20000000 : ℝ), (28412233/62500000 : ℝ)] ![(33273524207171/100000000000000 : ℝ), (15393951511149/50000000000000 : ℝ), (8984643188311/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535497963/1250000000 : ℝ)|^4459 ≤ (33273524207171/100000000000000 : ℝ)^3435
        have hw : |(535497963/1250000000 : ℝ)|=(535497963/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8070539/20000000 : ℝ)|^4459 ≤ (15393951511149/50000000000000 : ℝ)^3435
        have hw : |(8070539/20000000 : ℝ)|=(8070539/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(28412233/62500000 : ℝ)|^4459 ≤ (8984643188311/25000000000000 : ℝ)^3435
        have hw : |(28412233/62500000 : ℝ)|=(28412233/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1481_s3_4 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1914118357/10000000000 : ℝ)*x 0 + (5212949561/10000000000 : ℝ)*x 1 + (680090391/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1914118357/10000000000 : ℝ)^4459 ≤ (5846394929749/50000000000000 : ℝ)^3435 := by
    have hnat : (1914118357 : ℕ)^4459*50000000000000^3435 ≤ 5846394929749^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1914118357 10000000000 5846394929749 50000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5212949561/10000000000 : ℝ)^4459 ≤ (42928324515837/100000000000000 : ℝ)^3435 := by
    have hnat : (5212949561 : ℕ)^4459*100000000000000^3435 ≤ 42928324515837^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5212949561 10000000000 42928324515837 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (680090391/1250000000 : ℝ)^4459 ≤ (45378885612249/100000000000000 : ℝ)^3435 := by
    have hnat : (680090391 : ℕ)^4459*100000000000000^3435 ≤ 45378885612249^3435*1250000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      680090391 1250000000 45378885612249 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1914118357/10000000000 : ℝ), (5212949561/10000000000 : ℝ), (680090391/1250000000 : ℝ)] ![(5846394929749/50000000000000 : ℝ), (42928324515837/100000000000000 : ℝ), (45378885612249/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1914118357/10000000000 : ℝ)|^4459 ≤ (5846394929749/50000000000000 : ℝ)^3435
        have hw : |(-1914118357/10000000000 : ℝ)|=(1914118357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5212949561/10000000000 : ℝ)|^4459 ≤ (42928324515837/100000000000000 : ℝ)^3435
        have hw : |(5212949561/10000000000 : ℝ)|=(5212949561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(680090391/1250000000 : ℝ)|^4459 ≤ (45378885612249/100000000000000 : ℝ)^3435
        have hw : |(680090391/1250000000 : ℝ)|=(680090391/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1481_s3_5 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058865307/2000000000 : ℝ)*x 0 + (-450797749/2500000000 : ℝ)*x 1 + (5440723137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058865307/2000000000 : ℝ)^4459 ≤ (43800247995591/100000000000000 : ℝ)^3435 := by
    have hnat : (1058865307 : ℕ)^4459*100000000000000^3435 ≤ 43800247995591^3435*2000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058865307 2000000000 43800247995591 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (450797749/2500000000 : ℝ)^4459 ≤ (5410433142669/50000000000000 : ℝ)^3435 := by
    have hnat : (450797749 : ℕ)^4459*50000000000000^3435 ≤ 5410433142669^3435*2500000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450797749 2500000000 5410433142669 50000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5440723137/10000000000 : ℝ)^4459 ≤ (11344721427423/25000000000000 : ℝ)^3435 := by
    have hnat : (5440723137 : ℕ)^4459*25000000000000^3435 ≤ 11344721427423^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5440723137 10000000000 11344721427423 25000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058865307/2000000000 : ℝ), (-450797749/2500000000 : ℝ), (5440723137/10000000000 : ℝ)] ![(43800247995591/100000000000000 : ℝ), (5410433142669/50000000000000 : ℝ), (11344721427423/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058865307/2000000000 : ℝ)|^4459 ≤ (43800247995591/100000000000000 : ℝ)^3435
        have hw : |(1058865307/2000000000 : ℝ)|=(1058865307/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-450797749/2500000000 : ℝ)|^4459 ≤ (5410433142669/50000000000000 : ℝ)^3435
        have hw : |(-450797749/2500000000 : ℝ)|=(450797749/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5440723137/10000000000 : ℝ)|^4459 ≤ (11344721427423/25000000000000 : ℝ)^3435
        have hw : |(5440723137/10000000000 : ℝ)|=(5440723137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1481_s3_6 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058865301/2000000000 : ℝ)*x 0 + (1360180791/2500000000 : ℝ)*x 1 + (-1803191/10000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058865301/2000000000 : ℝ)^4459 ≤ (43800247673411/100000000000000 : ℝ)^3435 := by
    have hnat : (1058865301 : ℕ)^4459*100000000000000^3435 ≤ 43800247673411^3435*2000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058865301 2000000000 43800247673411 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1360180791/2500000000 : ℝ)^4459 ≤ (45378886002021/100000000000000 : ℝ)^3435 := by
    have hnat : (1360180791 : ℕ)^4459*100000000000000^3435 ≤ 45378886002021^3435*2500000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1360180791 2500000000 45378886002021 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1803191/10000000 : ℝ)^4459 ≤ (5410433158249/50000000000000 : ℝ)^3435 := by
    have hnat : (1803191 : ℕ)^4459*50000000000000^3435 ≤ 5410433158249^3435*10000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1803191 10000000 5410433158249 50000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058865301/2000000000 : ℝ), (1360180791/2500000000 : ℝ), (-1803191/10000000 : ℝ)] ![(43800247673411/100000000000000 : ℝ), (45378886002021/100000000000000 : ℝ), (5410433158249/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058865301/2000000000 : ℝ)|^4459 ≤ (43800247673411/100000000000000 : ℝ)^3435
        have hw : |(1058865301/2000000000 : ℝ)|=(1058865301/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1360180791/2500000000 : ℝ)|^4459 ≤ (45378886002021/100000000000000 : ℝ)^3435
        have hw : |(1360180791/2500000000 : ℝ)|=(1360180791/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1803191/10000000 : ℝ)|^4459 ≤ (5410433158249/50000000000000 : ℝ)^3435
        have hw : |(-1803191/10000000 : ℝ)|=(1803191/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1481_s3_7 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (535507407/1250000000 : ℝ)*x 0 + (908648157/2000000000 : ℝ)*x 1 + (4038006791/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535507407/1250000000 : ℝ)^4459 ≤ (33274285950799/100000000000000 : ℝ)^3435 := by
    have hnat : (535507407 : ℕ)^4459*100000000000000^3435 ≤ 33274285950799^3435*1250000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535507407 1250000000 33274285950799 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (908648157/2000000000 : ℝ)^4459 ≤ (8977674413421/25000000000000 : ℝ)^3435 := by
    have hnat : (908648157 : ℕ)^4459*25000000000000^3435 ≤ 8977674413421^3435*2000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      908648157 2000000000 8977674413421 25000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4038006791/10000000000 : ℝ)^4459 ≤ (15407508185751/50000000000000 : ℝ)^3435 := by
    have hnat : (4038006791 : ℕ)^4459*50000000000000^3435 ≤ 15407508185751^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4038006791 10000000000 15407508185751 50000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535507407/1250000000 : ℝ), (908648157/2000000000 : ℝ), (4038006791/10000000000 : ℝ)] ![(33274285950799/100000000000000 : ℝ), (8977674413421/25000000000000 : ℝ), (15407508185751/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535507407/1250000000 : ℝ)|^4459 ≤ (33274285950799/100000000000000 : ℝ)^3435
        have hw : |(535507407/1250000000 : ℝ)|=(535507407/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(908648157/2000000000 : ℝ)|^4459 ≤ (8977674413421/25000000000000 : ℝ)^3435
        have hw : |(908648157/2000000000 : ℝ)|=(908648157/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4038006791/10000000000 : ℝ)|^4459 ≤ (15407508185751/50000000000000 : ℝ)^3435
        have hw : |(4038006791/10000000000 : ℝ)|=(4038006791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1481_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160907049/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16127/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10193/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10701/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15573/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16127/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10193/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16127/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10193/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16127/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10193/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16127/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10193/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16127/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10193/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16127/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10193/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10193/100000 : ℝ) ^ (4457/1024 : ℝ) ≤ (1206523626617867/25000000000000000000 : ℝ) := by
    have hpowers : (10193/100000 : ℝ)^4457 ≤ (1206523626617867/25000000000000000000 : ℝ)^1024 := by
      have hnat : (10193 : ℕ)^4457*25000000000000000000^1024 ≤ 1206523626617867^1024*100000^4457 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10193 100000 1206523626617867 25000000000000000000 4457 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10193/100000 : ℝ)) (X := (1206523626617867/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4457 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16127/100000 : ℝ) ^ (4457/1024 : ℝ) ≤ (3555052575770269/10000000000000000000 : ℝ) := by
    have hpowers : (16127/100000 : ℝ)^4457 ≤ (3555052575770269/10000000000000000000 : ℝ)^1024 := by
      have hnat : (16127 : ℕ)^4457*10000000000000000000^1024 ≤ 3555052575770269^1024*100000^4457 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16127 100000 3555052575770269 10000000000000000000 4457 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16127/100000 : ℝ)) (X := (3555052575770269/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4457 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501206523626617867/12500000000000000000 : ℝ) ≤ (10000221751719961/10000000000000000 : ℝ) ^ (4457/1024 : ℝ) := by
    have hpowers : (12501206523626617867/12500000000000000000 : ℝ)^1024 ≤ (10000221751719961/10000000000000000 : ℝ)^4457 := by
      have hnat : (12501206523626617867 : ℕ)^1024*10000000000000000^4457 ≤ 10000221751719961^4457*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501206523626617867 12500000000000000000 10000221751719961 10000000000000000 1024 4457 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000221751719961/10000000000000000 : ℝ)) (X := (12501206523626617867/12500000000000000000 : ℝ)) (by norm_num) 4457 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50020188310132087079/50000000000000000000 : ℝ) ≤ (10000927512484203/10000000000000000 : ℝ) ^ (4457/1024 : ℝ) := by
    have hpowers : (50020188310132087079/50000000000000000000 : ℝ)^1024 ≤ (10000927512484203/10000000000000000 : ℝ)^4457 := by
      have hnat : (50020188310132087079 : ℕ)^1024*10000000000000000^4457 ≤ 10000927512484203^4457*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020188310132087079 50000000000000000000 10000927512484203 10000000000000000 1024 4457 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000927512484203/10000000000000000 : ℝ)) (X := (50020188310132087079/50000000000000000000 : ℝ)) (by norm_num) 4457 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003555052575770269/5000000000000000000 : ℝ) ≤ (2000326654649689/2000000000000000 : ℝ) ^ (4457/1024 : ℝ) := by
    have hpowers : (5003555052575770269/5000000000000000000 : ℝ)^1024 ≤ (2000326654649689/2000000000000000 : ℝ)^4457 := by
      have hnat : (5003555052575770269 : ℕ)^1024*2000000000000000^4457 ≤ 2000326654649689^4457*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003555052575770269 5000000000000000000 2000326654649689 2000000000000000 1024 4457 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000326654649689/2000000000000000 : ℝ)) (X := (5003555052575770269/5000000000000000000 : ℝ)) (by norm_num) 4457 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1206523626617867/25000000000000000000 : ℝ) ≤ ((29663464117883205581/29670000000000000000 : ℝ)+2*(352880382121/296700000000000 : ℝ)*(10193/100000 : ℝ))^(4457/1024 : ℝ) := by
    rw [show (29663464117883205581/29670000000000000000 : ℝ)+2*(352880382121/296700000000000 : ℝ)*(10193/100000 : ℝ)=(10000221751719961/10000000000000000 : ℝ) by norm_num, show 1+2*(1206523626617867/25000000000000000000 : ℝ)=(12501206523626617867/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3555052575770269/10000000000000000000 : ℝ)+(1206523626617867/25000000000000000000 : ℝ) ≤ ((29663464117883205581/29670000000000000000 : ℝ)+(352880382121/296700000000000 : ℝ)*((16127/100000 : ℝ)+(10193/100000 : ℝ)))^(4457/1024 : ℝ) := by
    rw [show (29663464117883205581/29670000000000000000 : ℝ)+(352880382121/296700000000000 : ℝ)*((16127/100000 : ℝ)+(10193/100000 : ℝ))=(10000927512484203/10000000000000000 : ℝ) by norm_num, show 1+(3555052575770269/10000000000000000000 : ℝ)+(1206523626617867/25000000000000000000 : ℝ)=(50020188310132087079/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3555052575770269/10000000000000000000 : ℝ) ≤ ((29663464117883205581/29670000000000000000 : ℝ)+2*(352880382121/296700000000000 : ℝ)*(16127/100000 : ℝ))^(4457/1024 : ℝ) := by
    rw [show (29663464117883205581/29670000000000000000 : ℝ)+2*(352880382121/296700000000000 : ℝ)*(16127/100000 : ℝ)=(2000326654649689/2000000000000000 : ℝ) by norm_num, show 1+2*(3555052575770269/10000000000000000000 : ℝ)=(5003555052575770269/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (29663464117883205581/29670000000000000000 : ℝ)*(X 1 0+X 2 0)+(352880382121/296700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4457/1024 : ℝ)) (lo := (10193/100000 : ℝ)) (hi := (16127/100000 : ℝ)) (c := (29663464117883205581/29670000000000000000 : ℝ)) (alpha := (352880382121/296700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (29663464117883205581/29670000000000000000 : ℝ)*(X 0 1+X 2 1)+(352880382121/296700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4457/1024 : ℝ)) (lo := (10193/100000 : ℝ)) (hi := (16127/100000 : ℝ)) (c := (29663464117883205581/29670000000000000000 : ℝ)) (alpha := (352880382121/296700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (29663464117883205581/29670000000000000000 : ℝ)*(X 0 2+X 1 2)+(352880382121/296700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4457/1024 : ℝ)) (lo := (10193/100000 : ℝ)) (hi := (16127/100000 : ℝ)) (c := (29663464117883205581/29670000000000000000 : ℝ)) (alpha := (352880382121/296700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1914084187/10000000000 : ℝ)*X 0 0+(5441957393/10000000000 : ℝ)*X 0 1+(2605862361/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5354468033/10000000000 : ℝ)*X 1 0+(-1016094547/5000000000 : ℝ)*X 1 1+(325732803/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338617007/2500000000 : ℝ)*X 2 0+(1302931169/2500000000 : ℝ)*X 2 1+(-127011833/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((535497963/1250000000 : ℝ)*X 0 0+(8070539/20000000 : ℝ)*X 0 1+(28412233/62500000 : ℝ)*X 0 2+(535497963/1250000000 : ℝ)*X 1 0+(8070539/20000000 : ℝ)*X 1 1+(28412233/62500000 : ℝ)*X 1 2+(535497963/1250000000 : ℝ)*X 2 0+(8070539/20000000 : ℝ)*X 2 1+(28412233/62500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1914118357/10000000000 : ℝ)*X 0 0+(5212949561/10000000000 : ℝ)*X 0 1+(680090391/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1058865307/2000000000 : ℝ)*X 1 0+(-450797749/2500000000 : ℝ)*X 1 1+(5440723137/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1058865301/2000000000 : ℝ)*X 2 0+(1360180791/2500000000 : ℝ)*X 2 1+(-1803191/10000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((535507407/1250000000 : ℝ)*X 0 0+(908648157/2000000000 : ℝ)*X 0 1+(4038006791/10000000000 : ℝ)*X 0 2+(535507407/1250000000 : ℝ)*X 1 0+(908648157/2000000000 : ℝ)*X 1 1+(4038006791/10000000000 : ℝ)*X 1 2+(535507407/1250000000 : ℝ)*X 2 0+(908648157/2000000000 : ℝ)*X 2 1+(4038006791/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1642952582277539213019/618125000000000000000000000 : ℝ) := by norm_num
    linear_combination (712404499/100000000000000 : ℝ)*(base19) + (782499097/100000000000000 : ℝ)*(base23) + (108927561/100000000000000 : ℝ)*(upper3) + (45190251/100000000000000 : ℝ)*(lower4) + (3150807414834237/100000000000000 : ℝ)*(major0) + (3150807414834237/100000000000000 : ℝ)*(major1) + (3150807414834237/100000000000000 : ℝ)*(major2) + (108586211531457/2500000000000 : ℝ)*(sp0) + (542932534768957/12500000000000 : ℝ)*(sp1) + (86869185915537/2000000000000 : ℝ)*(sp2) + (1958148222518579/100000000000000 : ℝ)*(sp3) + (100234383/800000000000 : ℝ)*(sp4) + (912280207/100000000000000 : ℝ)*(sp6) + (552799501/10000000000000 : ℝ)*(sp7) + (489538437628397/25000000000000 : ℝ)*(f.failure) + (2171730495278077/50000000000000 : ℝ)*(f.sum) + (341934144907/2472500000000000000000000000 : ℝ)*base65 + (4898860506426341101/989000000000000000000000000000000 : ℝ)*base68 + (11863298543251341101/989000000000000000000000000000000 : ℝ)*base70 + (827655641722658899/989000000000000000000000000000000 : ℝ)*base71 + (12534830001711/4945000000000000000000000000 : ℝ)*base74 + (5801319102843341101/989000000000000000000000000000000 : ℝ)*base76 + (2532171737279658899/989000000000000000000000000000000 : ℝ)*base77 + (6998593265536658899/989000000000000000000000000000000 : ℝ)*base79 + (34417149991791/4945000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (5129547/2500000000000000000000 : ℝ)*base90 + (5129547/2500000000000000000000 : ℝ)*base92 + (5129547/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1990962571347855587302442241/247250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1461675881/100000000000000 : ℝ)*(base19) + (94455079/6250000000000 : ℝ)*(base23) + (193388421/100000000000000 : ℝ)*(upper3) + (400509/1250000000000 : ℝ)*(lower4) + (34407629/20000000000000 : ℝ)*(upper5) + (3184802517972139/100000000000000 : ℝ)*(major0) + (3184802517972139/100000000000000 : ℝ)*(major1) + (3184802517972139/100000000000000 : ℝ)*(major2) + (1041451829/5000000000000 : ℝ)*(sp1) + (22058287907/100000000000000 : ℝ)*(sp2) + (4390323848661073/100000000000000 : ℝ)*(sp4) + (1097575389487153/25000000000000 : ℝ)*(sp5) + (2195150139545951/50000000000000 : ℝ)*(sp6) + (1979280918868967/100000000000000 : ℝ)*(sp7) + (1979280918868967/100000000000000 : ℝ)*(f.failure) + (4390323848661073/100000000000000 : ℝ)*(f.sum) + (8996208228917/7417500000000000000000000000 : ℝ)*base65 + (5872499284411069253/989000000000000000000000000000000 : ℝ)*base67 + (7244842416534069253/989000000000000000000000000000000 : ℝ)*base69 + (1647968908115069253/989000000000000000000000000000000 : ℝ)*base71 + (25862330890307/7417500000000000000000000000 : ℝ)*base73 + (15406090849274069253/989000000000000000000000000000000 : ℝ)*base75 + (393656771078930747/989000000000000000000000000000000 : ℝ)*base78 + (15379388270588069253/989000000000000000000000000000000 : ℝ)*base79 + (15687474289/57949218750000000000000000 : ℝ)*base81 + (2351617/10000000000000000000000 : ℝ)*base90 + (2351617/10000000000000000000000 : ℝ)*base92 + (2351617/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1481_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160907049/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16127/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10193/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10701/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15573/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1481_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1481_s4_0 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-191470811/1000000000 : ℝ)*x 0 + (5437921253/10000000000 : ℝ)*x 1 + (2607674751/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (191470811/1000000000 : ℝ)^4459 ≤ (11697466674477/100000000000000 : ℝ)^3435 := by
    have hnat : (191470811 : ℕ)^4459*100000000000000^3435 ≤ 11697466674477^3435*1000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      191470811 1000000000 11697466674477 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5437921253/10000000000 : ℝ)^4459 ≤ (45348552054811/100000000000000 : ℝ)^3435 := by
    have hnat : (5437921253 : ℕ)^4459*100000000000000^3435 ≤ 45348552054811^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437921253 10000000000 45348552054811 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2607674751/5000000000 : ℝ)^4459 ≤ (5369247657247/12500000000000 : ℝ)^3435 := by
    have hnat : (2607674751 : ℕ)^4459*12500000000000^3435 ≤ 5369247657247^3435*5000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607674751 5000000000 5369247657247 12500000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-191470811/1000000000 : ℝ), (5437921253/10000000000 : ℝ), (2607674751/5000000000 : ℝ)] ![(11697466674477/100000000000000 : ℝ), (45348552054811/100000000000000 : ℝ), (5369247657247/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-191470811/1000000000 : ℝ)|^4459 ≤ (11697466674477/100000000000000 : ℝ)^3435
        have hw : |(-191470811/1000000000 : ℝ)|=(191470811/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5437921253/10000000000 : ℝ)|^4459 ≤ (45348552054811/100000000000000 : ℝ)^3435
        have hw : |(5437921253/10000000000 : ℝ)|=(5437921253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2607674751/5000000000 : ℝ)|^4459 ≤ (5369247657247/12500000000000 : ℝ)^3435
        have hw : |(2607674751/5000000000 : ℝ)|=(2607674751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1481_s4_1 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353419907/10000000000 : ℝ)*x 0 + (-25359847/125000000 : ℝ)*x 1 + (521534913/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353419907/10000000000 : ℝ)^4459 ≤ (44435923393749/100000000000000 : ℝ)^3435 := by
    have hnat : (5353419907 : ℕ)^4459*100000000000000^3435 ≤ 44435923393749^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353419907 10000000000 44435923393749 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (25359847/125000000 : ℝ)^4459 ≤ (12610099309333/100000000000000 : ℝ)^3435 := by
    have hnat : (25359847 : ℕ)^4459*100000000000000^3435 ≤ 12610099309333^3435*125000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25359847 125000000 12610099309333 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (521534913/1000000000 : ℝ)^4459 ≤ (42953977280811/100000000000000 : ℝ)^3435 := by
    have hnat : (521534913 : ℕ)^4459*100000000000000^3435 ≤ 42953977280811^3435*1000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521534913 1000000000 42953977280811 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353419907/10000000000 : ℝ), (-25359847/125000000 : ℝ), (521534913/1000000000 : ℝ)] ![(44435923393749/100000000000000 : ℝ), (12610099309333/100000000000000 : ℝ), (42953977280811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353419907/10000000000 : ℝ)|^4459 ≤ (44435923393749/100000000000000 : ℝ)^3435
        have hw : |(5353419907/10000000000 : ℝ)|=(5353419907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-25359847/125000000 : ℝ)|^4459 ≤ (12610099309333/100000000000000 : ℝ)^3435
        have hw : |(-25359847/125000000 : ℝ)|=(25359847/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(521534913/1000000000 : ℝ)|^4459 ≤ (42953977280811/100000000000000 : ℝ)^3435
        have hw : |(521534913/1000000000 : ℝ)|=(521534913/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1481_s4_2 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353419739/10000000000 : ℝ)*x 0 + (1043069891/2000000000 : ℝ)*x 1 + (-2028787553/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353419739/10000000000 : ℝ)^4459 ≤ (11108980395891/25000000000000 : ℝ)^3435 := by
    have hnat : (5353419739 : ℕ)^4459*25000000000000^3435 ≤ 11108980395891^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353419739 10000000000 11108980395891 25000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043069891/2000000000 : ℝ)^4459 ≤ (8590796151097/20000000000000 : ℝ)^3435 := by
    have hnat : (1043069891 : ℕ)^4459*20000000000000^3435 ≤ 8590796151097^3435*2000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043069891 2000000000 8590796151097 20000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2028787553/10000000000 : ℝ)^4459 ≤ (2522019527831/20000000000000 : ℝ)^3435 := by
    have hnat : (2028787553 : ℕ)^4459*20000000000000^3435 ≤ 2522019527831^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2028787553 10000000000 2522019527831 20000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353419739/10000000000 : ℝ), (1043069891/2000000000 : ℝ), (-2028787553/10000000000 : ℝ)] ![(11108980395891/25000000000000 : ℝ), (8590796151097/20000000000000 : ℝ), (2522019527831/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353419739/10000000000 : ℝ)|^4459 ≤ (11108980395891/25000000000000 : ℝ)^3435
        have hw : |(5353419739/10000000000 : ℝ)|=(5353419739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043069891/2000000000 : ℝ)|^4459 ≤ (8590796151097/20000000000000 : ℝ)^3435
        have hw : |(1043069891/2000000000 : ℝ)|=(1043069891/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2028787553/10000000000 : ℝ)|^4459 ≤ (2522019527831/20000000000000 : ℝ)^3435
        have hw : |(-2028787553/10000000000 : ℝ)|=(2028787553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1481_s4_3 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (856874237/2000000000 : ℝ)*x 0 + (808743979/2000000000 : ℝ)*x 1 + (226870809/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (856874237/2000000000 : ℝ)^4459 ≤ (415967887231/1250000000000 : ℝ)^3435 := by
    have hnat : (856874237 : ℕ)^4459*1250000000000^3435 ≤ 415967887231^3435*2000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      856874237 2000000000 415967887231 1250000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (808743979/2000000000 : ℝ)^4459 ≤ (3858952915349/12500000000000 : ℝ)^3435 := by
    have hnat : (808743979 : ℕ)^4459*12500000000000^3435 ≤ 3858952915349^3435*2000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      808743979 2000000000 3858952915349 12500000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (226870809/500000000 : ℝ)^4459 ≤ (7170189135471/20000000000000 : ℝ)^3435 := by
    have hnat : (226870809 : ℕ)^4459*20000000000000^3435 ≤ 7170189135471^3435*500000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226870809 500000000 7170189135471 20000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(856874237/2000000000 : ℝ), (808743979/2000000000 : ℝ), (226870809/500000000 : ℝ)] ![(415967887231/1250000000000 : ℝ), (3858952915349/12500000000000 : ℝ), (7170189135471/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(856874237/2000000000 : ℝ)|^4459 ≤ (415967887231/1250000000000 : ℝ)^3435
        have hw : |(856874237/2000000000 : ℝ)|=(856874237/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(808743979/2000000000 : ℝ)|^4459 ≤ (3858952915349/12500000000000 : ℝ)^3435
        have hw : |(808743979/2000000000 : ℝ)|=(808743979/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(226870809/500000000 : ℝ)|^4459 ≤ (7170189135471/20000000000000 : ℝ)^3435
        have hw : |(226870809/500000000 : ℝ)|=(226870809/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1481_s4_4 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1914738977/10000000000 : ℝ)*x 0 + (5216494207/10000000000 : ℝ)*x 1 + (2718384017/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1914738977/10000000000 : ℝ)^4459 ≤ (11697711465471/100000000000000 : ℝ)^3435 := by
    have hnat : (1914738977 : ℕ)^4459*100000000000000^3435 ≤ 11697711465471^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1914738977 10000000000 11697711465471 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216494207/10000000000 : ℝ)^4459 ≤ (21483110024561/50000000000000 : ℝ)^3435 := by
    have hnat : (5216494207 : ℕ)^4459*50000000000000^3435 ≤ 21483110024561^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216494207 10000000000 21483110024561 50000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2718384017/5000000000 : ℝ)^4459 ≤ (45336068470411/100000000000000 : ℝ)^3435 := by
    have hnat : (2718384017 : ℕ)^4459*100000000000000^3435 ≤ 45336068470411^3435*5000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718384017 5000000000 45336068470411 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1914738977/10000000000 : ℝ), (5216494207/10000000000 : ℝ), (2718384017/5000000000 : ℝ)] ![(11697711465471/100000000000000 : ℝ), (21483110024561/50000000000000 : ℝ), (45336068470411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1914738977/10000000000 : ℝ)|^4459 ≤ (11697711465471/100000000000000 : ℝ)^3435
        have hw : |(-1914738977/10000000000 : ℝ)|=(1914738977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216494207/10000000000 : ℝ)|^4459 ≤ (21483110024561/50000000000000 : ℝ)^3435
        have hw : |(5216494207/10000000000 : ℝ)|=(5216494207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2718384017/5000000000 : ℝ)|^4459 ≤ (45336068470411/100000000000000 : ℝ)^3435
        have hw : |(2718384017/5000000000 : ℝ)|=(2718384017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1481_s4_5 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295281869/10000000000 : ℝ)*x 0 + (-451842249/2500000000 : ℝ)*x 1 + (543676803/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295281869/10000000000 : ℝ)^4459 ≤ (2190525395209/5000000000000 : ℝ)^3435 := by
    have hnat : (5295281869 : ℕ)^4459*5000000000000^3435 ≤ 2190525395209^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295281869 10000000000 2190525395209 5000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (451842249/2500000000 : ℝ)^4459 ≤ (2713355914433/25000000000000 : ℝ)^3435 := by
    have hnat : (451842249 : ℕ)^4459*25000000000000^3435 ≤ 2713355914433^3435*2500000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451842249 2500000000 2713355914433 25000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (543676803/1000000000 : ℝ)^4459 ≤ (45336068427113/100000000000000 : ℝ)^3435 := by
    have hnat : (543676803 : ℕ)^4459*100000000000000^3435 ≤ 45336068427113^3435*1000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543676803 1000000000 45336068427113 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295281869/10000000000 : ℝ), (-451842249/2500000000 : ℝ), (543676803/1000000000 : ℝ)] ![(2190525395209/5000000000000 : ℝ), (2713355914433/25000000000000 : ℝ), (45336068427113/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295281869/10000000000 : ℝ)|^4459 ≤ (2190525395209/5000000000000 : ℝ)^3435
        have hw : |(5295281869/10000000000 : ℝ)|=(5295281869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-451842249/2500000000 : ℝ)|^4459 ≤ (2713355914433/25000000000000 : ℝ)^3435
        have hw : |(-451842249/2500000000 : ℝ)|=(451842249/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(543676803/1000000000 : ℝ)|^4459 ≤ (45336068427113/100000000000000 : ℝ)^3435
        have hw : |(543676803/1000000000 : ℝ)|=(543676803/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1481_s4_6 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295281867/10000000000 : ℝ)*x 0 + (543676803/1000000000 : ℝ)*x 1 + (-903684499/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295281867/10000000000 : ℝ)^4459 ≤ (43810507882701/100000000000000 : ℝ)^3435 := by
    have hnat : (5295281867 : ℕ)^4459*100000000000000^3435 ≤ 43810507882701^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295281867 10000000000 43810507882701 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (543676803/1000000000 : ℝ)^4459 ≤ (45336068427113/100000000000000 : ℝ)^3435 := by
    have hnat : (543676803 : ℕ)^4459*100000000000000^3435 ≤ 45336068427113^3435*1000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543676803 1000000000 45336068427113 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (903684499/5000000000 : ℝ)^4459 ≤ (10853423673323/100000000000000 : ℝ)^3435 := by
    have hnat : (903684499 : ℕ)^4459*100000000000000^3435 ≤ 10853423673323^3435*5000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903684499 5000000000 10853423673323 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295281867/10000000000 : ℝ), (543676803/1000000000 : ℝ), (-903684499/5000000000 : ℝ)] ![(43810507882701/100000000000000 : ℝ), (45336068427113/100000000000000 : ℝ), (10853423673323/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295281867/10000000000 : ℝ)|^4459 ≤ (43810507882701/100000000000000 : ℝ)^3435
        have hw : |(5295281867/10000000000 : ℝ)|=(5295281867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(543676803/1000000000 : ℝ)|^4459 ≤ (45336068427113/100000000000000 : ℝ)^3435
        have hw : |(543676803/1000000000 : ℝ)|=(543676803/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-903684499/5000000000 : ℝ)|^4459 ≤ (10853423673323/100000000000000 : ℝ)^3435
        have hw : |(-903684499/5000000000 : ℝ)|=(903684499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1481_s4_7 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4284439813/10000000000 : ℝ)*x 0 + (2267438229/5000000000 : ℝ)*x 1 + (252892379/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4284439813/10000000000 : ℝ)^4459 ≤ (3327812293023/10000000000000 : ℝ)^3435 := by
    have hnat : (4284439813 : ℕ)^4459*10000000000000^3435 ≤ 3327812293023^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4284439813 10000000000 3327812293023 10000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2267438229/5000000000 : ℝ)^4459 ≤ (8956224744859/25000000000000 : ℝ)^3435 := by
    have hnat : (2267438229 : ℕ)^4459*25000000000000^3435 ≤ 8956224744859^3435*5000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2267438229 5000000000 8956224744859 25000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (252892379/625000000 : ℝ)^4459 ≤ (7724244517847/25000000000000 : ℝ)^3435 := by
    have hnat : (252892379 : ℕ)^4459*25000000000000^3435 ≤ 7724244517847^3435*625000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      252892379 625000000 7724244517847 25000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4284439813/10000000000 : ℝ), (2267438229/5000000000 : ℝ), (252892379/625000000 : ℝ)] ![(3327812293023/10000000000000 : ℝ), (8956224744859/25000000000000 : ℝ), (7724244517847/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4284439813/10000000000 : ℝ)|^4459 ≤ (3327812293023/10000000000000 : ℝ)^3435
        have hw : |(4284439813/10000000000 : ℝ)|=(4284439813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2267438229/5000000000 : ℝ)|^4459 ≤ (8956224744859/25000000000000 : ℝ)^3435
        have hw : |(2267438229/5000000000 : ℝ)|=(2267438229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(252892379/625000000 : ℝ)|^4459 ≤ (7724244517847/25000000000000 : ℝ)^3435
        have hw : |(252892379/625000000 : ℝ)|=(252892379/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1481_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160907049/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15573/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10701/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5389/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15489/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15573/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10701/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15573/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10701/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15573/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10701/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15573/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10701/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15573/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10701/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15573/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10701/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10701/100000 : ℝ) ^ (4457/1024 : ℝ) ≤ (372744847446621/6250000000000000000 : ℝ) := by
    have hpowers : (10701/100000 : ℝ)^4457 ≤ (372744847446621/6250000000000000000 : ℝ)^1024 := by
      have hnat : (10701 : ℕ)^4457*6250000000000000000^1024 ≤ 372744847446621^1024*100000^4457 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10701 100000 372744847446621 6250000000000000000 4457 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10701/100000 : ℝ)) (X := (372744847446621/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4457 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15573/100000 : ℝ) ^ (4457/1024 : ℝ) ≤ (7633238376663703/25000000000000000000 : ℝ) := by
    have hpowers : (15573/100000 : ℝ)^4457 ≤ (7633238376663703/25000000000000000000 : ℝ)^1024 := by
      have hnat : (15573 : ℕ)^4457*25000000000000000000^1024 ≤ 7633238376663703^1024*100000^4457 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15573 100000 7633238376663703 25000000000000000000 4457 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15573/100000 : ℝ)) (X := (7633238376663703/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4457 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125372744847446621/3125000000000000000 : ℝ) ≤ (1000027403056139/1000000000000000 : ℝ) ^ (4457/1024 : ℝ) := by
    have hpowers : (3125372744847446621/3125000000000000000 : ℝ)^1024 ≤ (1000027403056139/1000000000000000 : ℝ)^4457 := by
      have hnat : (3125372744847446621 : ℕ)^1024*1000000000000000^4457 ≤ 1000027403056139^4457*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125372744847446621 3125000000000000000 1000027403056139 1000000000000000 1024 4457 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000027403056139/1000000000000000 : ℝ)) (X := (3125372744847446621/3125000000000000000 : ℝ)) (by norm_num) 4457 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25009124217766450187/25000000000000000000 : ℝ) ≤ (10000838401257393/10000000000000000 : ℝ) ^ (4457/1024 : ℝ) := by
    have hpowers : (25009124217766450187/25000000000000000000 : ℝ)^1024 ≤ (10000838401257393/10000000000000000 : ℝ)^4457 := by
      have hnat : (25009124217766450187 : ℕ)^1024*10000000000000000^4457 ≤ 10000838401257393^4457*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25009124217766450187 25000000000000000000 10000838401257393 10000000000000000 1024 4457 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000838401257393/10000000000000000 : ℝ)) (X := (25009124217766450187/25000000000000000000 : ℝ)) (by norm_num) 4457 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507633238376663703/12500000000000000000 : ℝ) ≤ (2500350692988349/2500000000000000 : ℝ) ^ (4457/1024 : ℝ) := by
    have hpowers : (12507633238376663703/12500000000000000000 : ℝ)^1024 ≤ (2500350692988349/2500000000000000 : ℝ)^4457 := by
      have hnat : (12507633238376663703 : ℕ)^1024*2500000000000000^4457 ≤ 2500350692988349^4457*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507633238376663703 12500000000000000000 2500350692988349 2500000000000000 1024 4457 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500350692988349/2500000000000000 : ℝ)) (X := (12507633238376663703/12500000000000000000 : ℝ)) (by norm_num) 4457 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(372744847446621/6250000000000000000 : ℝ) ≤ ((279938255260110551/280000000000000000 : ℝ)+2*(564370696003/487200000000000 : ℝ)*(10701/100000 : ℝ))^(4457/1024 : ℝ) := by
    rw [show (279938255260110551/280000000000000000 : ℝ)+2*(564370696003/487200000000000 : ℝ)*(10701/100000 : ℝ)=(1000027403056139/1000000000000000 : ℝ) by norm_num, show 1+2*(372744847446621/6250000000000000000 : ℝ)=(3125372744847446621/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7633238376663703/25000000000000000000 : ℝ)+(372744847446621/6250000000000000000 : ℝ) ≤ ((279938255260110551/280000000000000000 : ℝ)+(564370696003/487200000000000 : ℝ)*((15573/100000 : ℝ)+(10701/100000 : ℝ)))^(4457/1024 : ℝ) := by
    rw [show (279938255260110551/280000000000000000 : ℝ)+(564370696003/487200000000000 : ℝ)*((15573/100000 : ℝ)+(10701/100000 : ℝ))=(10000838401257393/10000000000000000 : ℝ) by norm_num, show 1+(7633238376663703/25000000000000000000 : ℝ)+(372744847446621/6250000000000000000 : ℝ)=(25009124217766450187/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7633238376663703/25000000000000000000 : ℝ) ≤ ((279938255260110551/280000000000000000 : ℝ)+2*(564370696003/487200000000000 : ℝ)*(15573/100000 : ℝ))^(4457/1024 : ℝ) := by
    rw [show (279938255260110551/280000000000000000 : ℝ)+2*(564370696003/487200000000000 : ℝ)*(15573/100000 : ℝ)=(2500350692988349/2500000000000000 : ℝ) by norm_num, show 1+2*(7633238376663703/25000000000000000000 : ℝ)=(12507633238376663703/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (279938255260110551/280000000000000000 : ℝ)*(X 1 0+X 2 0)+(564370696003/487200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4457/1024 : ℝ)) (lo := (10701/100000 : ℝ)) (hi := (15573/100000 : ℝ)) (c := (279938255260110551/280000000000000000 : ℝ)) (alpha := (564370696003/487200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (279938255260110551/280000000000000000 : ℝ)*(X 0 1+X 2 1)+(564370696003/487200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4457/1024 : ℝ)) (lo := (10701/100000 : ℝ)) (hi := (15573/100000 : ℝ)) (c := (279938255260110551/280000000000000000 : ℝ)) (alpha := (564370696003/487200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (279938255260110551/280000000000000000 : ℝ)*(X 0 2+X 1 2)+(564370696003/487200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4457/1024 : ℝ)) (lo := (10701/100000 : ℝ)) (hi := (15573/100000 : ℝ)) (c := (279938255260110551/280000000000000000 : ℝ)) (alpha := (564370696003/487200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-191470811/1000000000 : ℝ)*X 0 0+(5437921253/10000000000 : ℝ)*X 0 1+(2607674751/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5353419907/10000000000 : ℝ)*X 1 0+(-25359847/125000000 : ℝ)*X 1 1+(521534913/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353419739/10000000000 : ℝ)*X 2 0+(1043069891/2000000000 : ℝ)*X 2 1+(-2028787553/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((856874237/2000000000 : ℝ)*X 0 0+(808743979/2000000000 : ℝ)*X 0 1+(226870809/500000000 : ℝ)*X 0 2+(856874237/2000000000 : ℝ)*X 1 0+(808743979/2000000000 : ℝ)*X 1 1+(226870809/500000000 : ℝ)*X 1 2+(856874237/2000000000 : ℝ)*X 2 0+(808743979/2000000000 : ℝ)*X 2 1+(226870809/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1914738977/10000000000 : ℝ)*X 0 0+(5216494207/10000000000 : ℝ)*X 0 1+(2718384017/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5295281869/10000000000 : ℝ)*X 1 0+(-451842249/2500000000 : ℝ)*X 1 1+(543676803/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5295281867/10000000000 : ℝ)*X 2 0+(543676803/1000000000 : ℝ)*X 2 1+(-903684499/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4284439813/10000000000 : ℝ)*X 0 0+(2267438229/5000000000 : ℝ)*X 0 1+(252892379/625000000 : ℝ)*X 0 2+(4284439813/10000000000 : ℝ)*X 1 0+(2267438229/5000000000 : ℝ)*X 1 1+(252892379/625000000 : ℝ)*X 1 2+(4284439813/10000000000 : ℝ)*X 2 0+(2267438229/5000000000 : ℝ)*X 2 1+(252892379/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (276169871940015849335073283/29000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (52416207/3125000000000 : ℝ)*(base19) + (742759561/50000000000000 : ℝ)*(base23) + (27196297/100000000000000 : ℝ)*(lower2) + (40777003/50000000000000 : ℝ)*(upper3) + (213330913/100000000000000 : ℝ)*(upper5) + (3259270357559587/100000000000000 : ℝ)*(major0) + (3259270357559587/100000000000000 : ℝ)*(major1) + (3259270357559587/100000000000000 : ℝ)*(major2) + (1123238607420591/25000000000000 : ℝ)*(sp0) + (2246488882938977/50000000000000 : ℝ)*(sp1) + (898595591535491/20000000000000 : ℝ)*(sp2) + (2025549612240197/100000000000000 : ℝ)*(sp3) + (12506757107/50000000000000 : ℝ)*(sp4) + (11342245761/100000000000000 : ℝ)*(sp7) + (1012780477242979/50000000000000 : ℝ)*(f.failure) + (2246489721598289/50000000000000 : ℝ)*(f.sum) + (12162734093777/3480000000000000000000000000 : ℝ)*base66 + (1276118836301651717/348000000000000000000000000000000 : ℝ)*base67 + (1128136038401651717/348000000000000000000000000000000 : ℝ)*base69 + (173069440097651717/348000000000000000000000000000000 : ℝ)*base71 + (3767080253417/3480000000000000000000000000 : ℝ)*base74 + (18406343166348283/348000000000000000000000000000000 : ℝ)*base76 + (202213059581651717/348000000000000000000000000000000 : ℝ)*base77 + (328864007321651717/348000000000000000000000000000000 : ℝ)*base79 + (3227630614697/3480000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (56858971/5000000000000000000000 : ℝ)*base89 + (56858971/5000000000000000000000 : ℝ)*base91 + (56858971/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (136299741755387493576215121/14500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1574727197/100000000000000 : ℝ)*(base19) + (1702502703/100000000000000 : ℝ)*(base23) + (194934463/100000000000000 : ℝ)*(upper3) + (29469529/50000000000000 : ℝ)*(lower4) + (195923291/100000000000000 : ℝ)*(upper5) + (823309215041523/25000000000000 : ℝ)*(major0) + (823309215041523/25000000000000 : ℝ)*(major1) + (823309215041523/25000000000000 : ℝ)*(major2) + (11783866817/50000000000000 : ℝ)*(sp1) + (6306036371/25000000000000 : ℝ)*(sp2) + (4539803058725207/100000000000000 : ℝ)*(sp4) + (567472239533047/12500000000000 : ℝ)*(sp5) + (226988806603851/5000000000000 : ℝ)*(sp6) + (1023335174137117/50000000000000 : ℝ)*(sp7) + (1023335174137117/50000000000000 : ℝ)*(f.failure) + (4539803058725207/100000000000000 : ℝ)*(f.sum) + (1100679545919/290000000000000000000000000 : ℝ)*base65 + (15229933662859431/29000000000000000000000000000000 : ℝ)*base67 + (20894300865859431/29000000000000000000000000000000 : ℝ)*base69 + (160836903575859431/29000000000000000000000000000000 : ℝ)*base71 + (1229151914349/290000000000000000000000000 : ℝ)*base73 + (298983865667859431/29000000000000000000000000000000 : ℝ)*base75 + (17743530789859431/29000000000000000000000000000000 : ℝ)*base77 + (28761160503859431/29000000000000000000000000000000 : ℝ)*base79 + (875166451229/290000000000000000000000000 : ℝ)*base81 + (17837733/5000000000000000000000 : ℝ)*base89 + (17837733/5000000000000000000000 : ℝ)*base91 + (17837733/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1481_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160907049/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15573/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10701/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5389/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1481_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1481_s5_0 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1914793521/10000000000 : ℝ)*x 0 + (2718686089/5000000000 : ℝ)*x 1 + (5215842089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1914793521/10000000000 : ℝ)^4459 ≤ (5849072014991/50000000000000 : ℝ)^3435 := by
    have hnat : (1914793521 : ℕ)^4459*50000000000000^3435 ≤ 5849072014991^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1914793521 10000000000 5849072014991 50000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2718686089/5000000000 : ℝ)^4459 ≤ (11335652056217/25000000000000 : ℝ)^3435 := by
    have hnat : (2718686089 : ℕ)^4459*25000000000000^3435 ≤ 11335652056217^3435*5000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718686089 5000000000 11335652056217 25000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215842089/10000000000 : ℝ)^4459 ≤ (42959247730183/100000000000000 : ℝ)^3435 := by
    have hnat : (5215842089 : ℕ)^4459*100000000000000^3435 ≤ 42959247730183^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215842089 10000000000 42959247730183 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1914793521/10000000000 : ℝ), (2718686089/5000000000 : ℝ), (5215842089/10000000000 : ℝ)] ![(5849072014991/50000000000000 : ℝ), (11335652056217/25000000000000 : ℝ), (42959247730183/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1914793521/10000000000 : ℝ)|^4459 ≤ (5849072014991/50000000000000 : ℝ)^3435
        have hw : |(-1914793521/10000000000 : ℝ)|=(1914793521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2718686089/5000000000 : ℝ)|^4459 ≤ (11335652056217/25000000000000 : ℝ)^3435
        have hw : |(2718686089/5000000000 : ℝ)|=(2718686089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215842089/10000000000 : ℝ)|^4459 ≤ (42959247730183/100000000000000 : ℝ)^3435
        have hw : |(5215842089/10000000000 : ℝ)|=(5215842089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1481_s5_1 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (20911237/39062500 : ℝ)*x 0 + (-2028325649/10000000000 : ℝ)*x 1 + (5215842211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20911237/39062500 : ℝ)^4459 ≤ (44434380055743/100000000000000 : ℝ)^3435 := by
    have hnat : (20911237 : ℕ)^4459*100000000000000^3435 ≤ 44434380055743^3435*39062500^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20911237 39062500 44434380055743 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2028325649/10000000000 : ℝ)^4459 ≤ (3151592723721/25000000000000 : ℝ)^3435 := by
    have hnat : (2028325649 : ℕ)^4459*25000000000000^3435 ≤ 3151592723721^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2028325649 10000000000 3151592723721 25000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215842211/10000000000 : ℝ)^4459 ≤ (42959249034559/100000000000000 : ℝ)^3435 := by
    have hnat : (5215842211 : ℕ)^4459*100000000000000^3435 ≤ 42959249034559^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215842211 10000000000 42959249034559 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(20911237/39062500 : ℝ), (-2028325649/10000000000 : ℝ), (5215842211/10000000000 : ℝ)] ![(44434380055743/100000000000000 : ℝ), (3151592723721/25000000000000 : ℝ), (42959249034559/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(20911237/39062500 : ℝ)|^4459 ≤ (44434380055743/100000000000000 : ℝ)^3435
        have hw : |(20911237/39062500 : ℝ)|=(20911237/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2028325649/10000000000 : ℝ)|^4459 ≤ (3151592723721/25000000000000 : ℝ)^3435
        have hw : |(-2028325649/10000000000 : ℝ)|=(2028325649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215842211/10000000000 : ℝ)|^4459 ≤ (42959249034559/100000000000000 : ℝ)^3435
        have hw : |(5215842211/10000000000 : ℝ)|=(5215842211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1481_s5_2 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (669159559/1250000000 : ℝ)*x 0 + (5215842401/10000000000 : ℝ)*x 1 + (-405665133/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669159559/1250000000 : ℝ)^4459 ≤ (22217188950389/50000000000000 : ℝ)^3435 := by
    have hnat : (669159559 : ℕ)^4459*50000000000000^3435 ≤ 22217188950389^3435*1250000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669159559 1250000000 22217188950389 50000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5215842401/10000000000 : ℝ)^4459 ≤ (10739812766491/25000000000000 : ℝ)^3435 := by
    have hnat : (5215842401 : ℕ)^4459*25000000000000^3435 ≤ 10739812766491^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215842401 10000000000 10739812766491 25000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (405665133/2000000000 : ℝ)^4459 ≤ (12606371023971/100000000000000 : ℝ)^3435 := by
    have hnat : (405665133 : ℕ)^4459*100000000000000^3435 ≤ 12606371023971^3435*2000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      405665133 2000000000 12606371023971 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669159559/1250000000 : ℝ), (5215842401/10000000000 : ℝ), (-405665133/2000000000 : ℝ)] ![(22217188950389/50000000000000 : ℝ), (10739812766491/25000000000000 : ℝ), (12606371023971/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669159559/1250000000 : ℝ)|^4459 ≤ (22217188950389/50000000000000 : ℝ)^3435
        have hw : |(669159559/1250000000 : ℝ)|=(669159559/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5215842401/10000000000 : ℝ)|^4459 ≤ (10739812766491/25000000000000 : ℝ)^3435
        have hw : |(5215842401/10000000000 : ℝ)|=(5215842401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-405665133/2000000000 : ℝ)|^4459 ≤ (12606371023971/100000000000000 : ℝ)^3435
        have hw : |(-405665133/2000000000 : ℝ)|=(405665133/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1481_s5_3 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4284423023/10000000000 : ℝ)*x 0 + (2022435059/5000000000 : ℝ)*x 1 + (907250747/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4284423023/10000000000 : ℝ)^4459 ≤ (16638976821159/50000000000000 : ℝ)^3435 := by
    have hnat : (4284423023 : ℕ)^4459*50000000000000^3435 ≤ 16638976821159^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4284423023 10000000000 16638976821159 50000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2022435059/5000000000 : ℝ)^4459 ≤ (15441511461123/50000000000000 : ℝ)^3435 := by
    have hnat : (2022435059 : ℕ)^4459*50000000000000^3435 ≤ 15441511461123^3435*5000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2022435059 5000000000 15441511461123 50000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (907250747/2000000000 : ℝ)^4459 ≤ (17919511709071/50000000000000 : ℝ)^3435 := by
    have hnat : (907250747 : ℕ)^4459*50000000000000^3435 ≤ 17919511709071^3435*2000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      907250747 2000000000 17919511709071 50000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4284423023/10000000000 : ℝ), (2022435059/5000000000 : ℝ), (907250747/2000000000 : ℝ)] ![(16638976821159/50000000000000 : ℝ), (15441511461123/50000000000000 : ℝ), (17919511709071/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4284423023/10000000000 : ℝ)|^4459 ≤ (16638976821159/50000000000000 : ℝ)^3435
        have hw : |(4284423023/10000000000 : ℝ)|=(4284423023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2022435059/5000000000 : ℝ)|^4459 ≤ (15441511461123/50000000000000 : ℝ)^3435
        have hw : |(2022435059/5000000000 : ℝ)|=(2022435059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(907250747/2000000000 : ℝ)|^4459 ≤ (17919511709071/50000000000000 : ℝ)^3435
        have hw : |(907250747/2000000000 : ℝ)|=(907250747/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1481_s5_4 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-119676487/625000000 : ℝ)*x 0 + (65212207/125000000 : ℝ)*x 1 + (2718114719/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (119676487/625000000 : ℝ)^4459 ≤ (5849192048787/50000000000000 : ℝ)^3435 := by
    have hnat : (119676487 : ℕ)^4459*50000000000000^3435 ≤ 5849192048787^3435*625000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      119676487 625000000 5849192048787 50000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (65212207/125000000 : ℝ)^4459 ≤ (859427548817/2000000000000 : ℝ)^3435 := by
    have hnat : (65212207 : ℕ)^4459*2000000000000^3435 ≤ 859427548817^3435*125000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65212207 125000000 859427548817 2000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2718114719/5000000000 : ℝ)^4459 ≤ (22665119222193/50000000000000 : ℝ)^3435 := by
    have hnat : (2718114719 : ℕ)^4459*50000000000000^3435 ≤ 22665119222193^3435*5000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718114719 5000000000 22665119222193 50000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-119676487/625000000 : ℝ), (65212207/125000000 : ℝ), (2718114719/5000000000 : ℝ)] ![(5849192048787/50000000000000 : ℝ), (859427548817/2000000000000 : ℝ), (22665119222193/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-119676487/625000000 : ℝ)|^4459 ≤ (5849192048787/50000000000000 : ℝ)^3435
        have hw : |(-119676487/625000000 : ℝ)|=(119676487/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(65212207/125000000 : ℝ)|^4459 ≤ (859427548817/2000000000000 : ℝ)^3435
        have hw : |(65212207/125000000 : ℝ)|=(65212207/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2718114719/5000000000 : ℝ)|^4459 ≤ (22665119222193/50000000000000 : ℝ)^3435
        have hw : |(2718114719/5000000000 : ℝ)|=(2718114719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1481_s5_5 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323852817/2500000000 : ℝ)*x 0 + (-1807938577/10000000000 : ℝ)*x 1 + (2718114719/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323852817/2500000000 : ℝ)^4459 ≤ (21905948820299/50000000000000 : ℝ)^3435 := by
    have hnat : (1323852817 : ℕ)^4459*50000000000000^3435 ≤ 21905948820299^3435*2500000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323852817 2500000000 21905948820299 50000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1807938577/10000000000 : ℝ)^4459 ≤ (2171572779763/20000000000000 : ℝ)^3435 := by
    have hnat : (1807938577 : ℕ)^4459*20000000000000^3435 ≤ 2171572779763^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1807938577 10000000000 2171572779763 20000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2718114719/5000000000 : ℝ)^4459 ≤ (22665119222193/50000000000000 : ℝ)^3435 := by
    have hnat : (2718114719 : ℕ)^4459*50000000000000^3435 ≤ 22665119222193^3435*5000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718114719 5000000000 22665119222193 50000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323852817/2500000000 : ℝ), (-1807938577/10000000000 : ℝ), (2718114719/5000000000 : ℝ)] ![(21905948820299/50000000000000 : ℝ), (2171572779763/20000000000000 : ℝ), (22665119222193/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323852817/2500000000 : ℝ)|^4459 ≤ (21905948820299/50000000000000 : ℝ)^3435
        have hw : |(1323852817/2500000000 : ℝ)|=(1323852817/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1807938577/10000000000 : ℝ)|^4459 ≤ (2171572779763/20000000000000 : ℝ)^3435
        have hw : |(-1807938577/10000000000 : ℝ)|=(1807938577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2718114719/5000000000 : ℝ)|^4459 ≤ (22665119222193/50000000000000 : ℝ)^3435
        have hw : |(2718114719/5000000000 : ℝ)|=(2718114719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1481_s5_6 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (661926407/1250000000 : ℝ)*x 0 + (1087245889/2000000000 : ℝ)*x 1 + (-225992323/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661926407/1250000000 : ℝ)^4459 ≤ (43811897511719/100000000000000 : ℝ)^3435 := by
    have hnat : (661926407 : ℕ)^4459*100000000000000^3435 ≤ 43811897511719^3435*1250000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661926407 1250000000 43811897511719 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1087245889/2000000000 : ℝ)^4459 ≤ (11332559630039/25000000000000 : ℝ)^3435 := by
    have hnat : (1087245889 : ℕ)^4459*25000000000000^3435 ≤ 11332559630039^3435*2000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087245889 2000000000 11332559630039 25000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (225992323/1250000000 : ℝ)^4459 ≤ (10857863953387/100000000000000 : ℝ)^3435 := by
    have hnat : (225992323 : ℕ)^4459*100000000000000^3435 ≤ 10857863953387^3435*1250000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225992323 1250000000 10857863953387 100000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661926407/1250000000 : ℝ), (1087245889/2000000000 : ℝ), (-225992323/1250000000 : ℝ)] ![(43811897511719/100000000000000 : ℝ), (11332559630039/25000000000000 : ℝ), (10857863953387/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661926407/1250000000 : ℝ)|^4459 ≤ (43811897511719/100000000000000 : ℝ)^3435
        have hw : |(661926407/1250000000 : ℝ)|=(661926407/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1087245889/2000000000 : ℝ)|^4459 ≤ (11332559630039/25000000000000 : ℝ)^3435
        have hw : |(1087245889/2000000000 : ℝ)|=(1087245889/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-225992323/1250000000 : ℝ)|^4459 ≤ (10857863953387/100000000000000 : ℝ)^3435
        have hw : |(-225992323/1250000000 : ℝ)|=(225992323/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1481_s5_7 (p : ℝ) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2142245313/5000000000 : ℝ)*x 0 + (141679311/312500000 : ℝ)*x 1 + (4047404149/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2142245313/5000000000 : ℝ)^4459 ≤ (1039957351931/3125000000000 : ℝ)^3435 := by
    have hnat : (2142245313 : ℕ)^4459*3125000000000^3435 ≤ 1039957351931^3435*5000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2142245313 5000000000 1039957351931 3125000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (141679311/312500000 : ℝ)^4459 ≤ (2238326511439/6250000000000 : ℝ)^3435 := by
    have hnat : (141679311 : ℕ)^4459*6250000000000^3435 ≤ 2238326511439^3435*312500000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      141679311 312500000 2238326511439 6250000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4047404149/10000000000 : ℝ)^4459 ≤ (15454070269327/50000000000000 : ℝ)^3435 := by
    have hnat : (4047404149 : ℕ)^4459*50000000000000^3435 ≤ 15454070269327^3435*10000000000^4459 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4047404149 10000000000 15454070269327 50000000000000 4459 3435 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4459/1024 : ℝ)) 4459 3435 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2142245313/5000000000 : ℝ), (141679311/312500000 : ℝ), (4047404149/10000000000 : ℝ)] ![(1039957351931/3125000000000 : ℝ), (2238326511439/6250000000000 : ℝ), (15454070269327/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2142245313/5000000000 : ℝ)|^4459 ≤ (1039957351931/3125000000000 : ℝ)^3435
        have hw : |(2142245313/5000000000 : ℝ)|=(2142245313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(141679311/312500000 : ℝ)|^4459 ≤ (2238326511439/6250000000000 : ℝ)^3435
        have hw : |(141679311/312500000 : ℝ)|=(141679311/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4047404149/10000000000 : ℝ)|^4459 ≤ (15454070269327/50000000000000 : ℝ)^3435
        have hw : |(4047404149/10000000000 : ℝ)|=(4047404149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1481_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160907049/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5389/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10789/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15477/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15489/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5389/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15489/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5389/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15489/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5389/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15489/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5389/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15489/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5389/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15489/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5389/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5389/50000 : ℝ) ^ (4457/1024 : ℝ) ≤ (3076483839277847/50000000000000000000 : ℝ) := by
    have hpowers : (5389/50000 : ℝ)^4457 ≤ (3076483839277847/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5389 : ℕ)^4457*50000000000000000000^1024 ≤ 3076483839277847^1024*50000^4457 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5389 50000 3076483839277847 50000000000000000000 4457 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5389/50000 : ℝ)) (X := (3076483839277847/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4457 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15489/100000 : ℝ) ^ (4457/1024 : ℝ) ≤ (29822573713897061/100000000000000000000 : ℝ) := by
    have hpowers : (15489/100000 : ℝ)^4457 ≤ (29822573713897061/100000000000000000000 : ℝ)^1024 := by
      have hnat : (15489 : ℕ)^4457*100000000000000000000^1024 ≤ 29822573713897061^1024*100000^4457 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15489 100000 29822573713897061 100000000000000000000 4457 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15489/100000 : ℝ)) (X := (29822573713897061/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4457 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25003076483839277847/25000000000000000000 : ℝ) ≤ (10000282716639769/10000000000000000 : ℝ) ^ (4457/1024 : ℝ) := by
    have hpowers : (25003076483839277847/25000000000000000000 : ℝ)^1024 ≤ (10000282716639769/10000000000000000 : ℝ)^4457 := by
      have hnat : (25003076483839277847 : ℕ)^1024*10000000000000000^4457 ≤ 10000282716639769^4457*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003076483839277847 25000000000000000000 10000282716639769 10000000000000000 1024 4457 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000282716639769/10000000000000000 : ℝ)) (X := (25003076483839277847/25000000000000000000 : ℝ)) (by norm_num) 4457 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20007195108278490551/20000000000000000000 : ℝ) ≤ (500041321350021/500000000000000 : ℝ) ^ (4457/1024 : ℝ) := by
    have hpowers : (20007195108278490551/20000000000000000000 : ℝ)^1024 ≤ (500041321350021/500000000000000 : ℝ)^4457 := by
      have hnat : (20007195108278490551 : ℕ)^1024*500000000000000^4457 ≤ 500041321350021^4457*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20007195108278490551 20000000000000000000 500041321350021 500000000000000 1024 4457 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500041321350021/500000000000000 : ℝ)) (X := (20007195108278490551/20000000000000000000 : ℝ)) (by norm_num) 4457 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50029822573713897061/50000000000000000000 : ℝ) ≤ (10001370137361071/10000000000000000 : ℝ) ^ (4457/1024 : ℝ) := by
    have hpowers : (50029822573713897061/50000000000000000000 : ℝ)^1024 ≤ (10001370137361071/10000000000000000 : ℝ)^4457 := by
      have hnat : (50029822573713897061 : ℕ)^1024*10000000000000000^4457 ≤ 10001370137361071^4457*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50029822573713897061 50000000000000000000 10001370137361071 10000000000000000 1024 4457 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001370137361071/10000000000000000 : ℝ)) (X := (50029822573713897061/50000000000000000000 : ℝ)) (by norm_num) 4457 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3076483839277847/50000000000000000000 : ℝ) ≤ ((47099611657555758803/47110000000000000000 : ℝ)+2*(543710360651/471100000000000 : ℝ)*(5389/50000 : ℝ))^(4457/1024 : ℝ) := by
    rw [show (47099611657555758803/47110000000000000000 : ℝ)+2*(543710360651/471100000000000 : ℝ)*(5389/50000 : ℝ)=(10000282716639769/10000000000000000 : ℝ) by norm_num, show 1+2*(3076483839277847/50000000000000000000 : ℝ)=(25003076483839277847/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(29822573713897061/100000000000000000000 : ℝ)+(3076483839277847/50000000000000000000 : ℝ) ≤ ((47099611657555758803/47110000000000000000 : ℝ)+(543710360651/471100000000000 : ℝ)*((15489/100000 : ℝ)+(5389/50000 : ℝ)))^(4457/1024 : ℝ) := by
    rw [show (47099611657555758803/47110000000000000000 : ℝ)+(543710360651/471100000000000 : ℝ)*((15489/100000 : ℝ)+(5389/50000 : ℝ))=(500041321350021/500000000000000 : ℝ) by norm_num, show 1+(29822573713897061/100000000000000000000 : ℝ)+(3076483839277847/50000000000000000000 : ℝ)=(20007195108278490551/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(29822573713897061/100000000000000000000 : ℝ) ≤ ((47099611657555758803/47110000000000000000 : ℝ)+2*(543710360651/471100000000000 : ℝ)*(15489/100000 : ℝ))^(4457/1024 : ℝ) := by
    rw [show (47099611657555758803/47110000000000000000 : ℝ)+2*(543710360651/471100000000000 : ℝ)*(15489/100000 : ℝ)=(10001370137361071/10000000000000000 : ℝ) by norm_num, show 1+2*(29822573713897061/100000000000000000000 : ℝ)=(50029822573713897061/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (47099611657555758803/47110000000000000000 : ℝ)*(X 1 0+X 2 0)+(543710360651/471100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4457/1024 : ℝ)) (lo := (5389/50000 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (47099611657555758803/47110000000000000000 : ℝ)) (alpha := (543710360651/471100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (47099611657555758803/47110000000000000000 : ℝ)*(X 0 1+X 2 1)+(543710360651/471100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4457/1024 : ℝ)) (lo := (5389/50000 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (47099611657555758803/47110000000000000000 : ℝ)) (alpha := (543710360651/471100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (47099611657555758803/47110000000000000000 : ℝ)*(X 0 2+X 1 2)+(543710360651/471100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4457/1024 : ℝ)) (lo := (5389/50000 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (47099611657555758803/47110000000000000000 : ℝ)) (alpha := (543710360651/471100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1914793521/10000000000 : ℝ)*X 0 0+(2718686089/5000000000 : ℝ)*X 0 1+(5215842089/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((20911237/39062500 : ℝ)*X 1 0+(-2028325649/10000000000 : ℝ)*X 1 1+(5215842211/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((669159559/1250000000 : ℝ)*X 2 0+(5215842401/10000000000 : ℝ)*X 2 1+(-405665133/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4284423023/10000000000 : ℝ)*X 0 0+(2022435059/5000000000 : ℝ)*X 0 1+(907250747/2000000000 : ℝ)*X 0 2+(4284423023/10000000000 : ℝ)*X 1 0+(2022435059/5000000000 : ℝ)*X 1 1+(907250747/2000000000 : ℝ)*X 1 2+(4284423023/10000000000 : ℝ)*X 2 0+(2022435059/5000000000 : ℝ)*X 2 1+(907250747/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-119676487/625000000 : ℝ)*X 0 0+(65212207/125000000 : ℝ)*X 0 1+(2718114719/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1323852817/2500000000 : ℝ)*X 1 0+(-1807938577/10000000000 : ℝ)*X 1 1+(2718114719/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((661926407/1250000000 : ℝ)*X 2 0+(1087245889/2000000000 : ℝ)*X 2 1+(-225992323/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2142245313/5000000000 : ℝ)*X 0 0+(141679311/312500000 : ℝ)*X 0 1+(4047404149/10000000000 : ℝ)*X 0 2+(2142245313/5000000000 : ℝ)*X 1 0+(141679311/312500000 : ℝ)*X 1 1+(4047404149/10000000000 : ℝ)*X 1 2+(2142245313/5000000000 : ℝ)*X 2 0+(141679311/312500000 : ℝ)*X 2 1+(4047404149/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1481_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2757103196842854375273153279/588875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (529268933/50000000000000 : ℝ)*(base19) + (768781361/100000000000000 : ℝ)*(base23) + (31851399/20000000000000 : ℝ)*(upper3) + (1013011/1562500000000 : ℝ)*(upper4) + (381323/1250000000000 : ℝ)*(upper5) + (818647707019431/25000000000000 : ℝ)*(major0) + (818647707019431/25000000000000 : ℝ)*(major1) + (818647707019431/25000000000000 : ℝ)*(major2) + (4514080977081801/100000000000000 : ℝ)*(sp0) + (4514098169874387/100000000000000 : ℝ)*(sp1) + (4514098459630893/100000000000000 : ℝ)*(sp2) + (407015080704437/20000000000000 : ℝ)*(sp3) + (4562832613/25000000000000 : ℝ)*(sp4) + (3434077439/50000000000000 : ℝ)*(sp7) + (2035082271677063/100000000000000 : ℝ)*(f.failure) + (4514099228412253/100000000000000 : ℝ)*(f.sum) + (18779074954267/11777500000000000000000000000 : ℝ)*base65 + (8714126713122401093/1177750000000000000000000000000000 : ℝ)*base67 + (7471023373392098907/1177750000000000000000000000000000 : ℝ)*base70 + (8572203641799151093/1177750000000000000000000000000000 : ℝ)*base71 + (33508292944059/23555000000000000000000000000 : ℝ)*base73 + (5589428057820098907/1177750000000000000000000000000000 : ℝ)*base76 + (5800880026738848907/1177750000000000000000000000000000 : ℝ)*base78 + (4515723231088848907/1177750000000000000000000000000000 : ℝ)*base80 + (26695058209009/5888750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (88317087/10000000000000000000000 : ℝ)*base89 + (88317087/10000000000000000000000 : ℝ)*base91 + (88317087/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4449394383995645085416403747/1177750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (316479839/50000000000000 : ℝ)*(base19) + (335486907/50000000000000 : ℝ)*(base23) + (80795917/100000000000000 : ℝ)*(upper3) + (11263017/50000000000000 : ℝ)*(lower4) + (39423563/50000000000000 : ℝ)*(upper5) + (1654285988406761/50000000000000 : ℝ)*(major0) + (1654285988406761/50000000000000 : ℝ)*(major1) + (1654285988406761/50000000000000 : ℝ)*(major2) + (9441216737/100000000000000 : ℝ)*(sp1) + (4986512733/50000000000000 : ℝ)*(sp2) + (1140235765000679/25000000000000 : ℝ)*(sp4) + (2280466492913151/50000000000000 : ℝ)*(sp5) + (4560932416003437/100000000000000 : ℝ)*(sp6) + (411240153539019/20000000000000 : ℝ)*(sp7) + (411240153539019/20000000000000 : ℝ)*(f.failure) + (1140235765000679/25000000000000 : ℝ)*(f.sum) + (9734949961983/5888750000000000000000000000 : ℝ)*base65 + (11521849676688432917/2355500000000000000000000000000000 : ℝ)*base68 + (8931083191734932917/2355500000000000000000000000000000 : ℝ)*base70 + (13171941661173432917/2355500000000000000000000000000000 : ℝ)*base72 + (26101337315693/23555000000000000000000000000 : ℝ)*base74 + (19889364258947432917/2355500000000000000000000000000000 : ℝ)*base76 + (11380566537005432917/2355500000000000000000000000000000 : ℝ)*base78 + (17052208870078932917/2355500000000000000000000000000000 : ℝ)*base80 + (90197912124813/23555000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (13644931/2000000000000000000000 : ℝ)*base89 + (13644931/2000000000000000000000 : ℝ)*base91 + (13644931/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1481_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160907049/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5389/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10789/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15477/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1481_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1481_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160907049/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16127/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10193/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10789/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15477/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1481_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1481_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1481_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4457/1024 : ℝ) ≤ p) (hpb : p ≤ (4459/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160907049/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16127/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10193/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10789/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15477/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1481_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
