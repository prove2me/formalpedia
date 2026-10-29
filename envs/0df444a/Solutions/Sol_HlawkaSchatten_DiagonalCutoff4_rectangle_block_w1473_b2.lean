-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1473_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:11:37.303455+00:00
-- url     : https://prove2.me/submissions/adfbd5bd-8bd0-41ba-aea9-5320012b6ecb

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
theorem support_rectangle_w1473_s6_0 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-48180257/250000000 : ℝ)*x 0 + (5438353473/10000000000 : ℝ)*x 1 + (1303852707/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (48180257/250000000 : ℝ)^4443 ≤ (11769645528767/100000000000000 : ℝ)^3419 := by
    have hnat : (48180257 : ℕ)^4443*100000000000000^3419 ≤ 11769645528767^3419*250000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48180257 250000000 11769645528767 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5438353473/10000000000 : ℝ)^4443 ≤ (45314708695453/100000000000000 : ℝ)^3419 := by
    have hnat : (5438353473 : ℕ)^4443*100000000000000^3419 ≤ 45314708695453^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438353473 10000000000 45314708695453 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1303852707/2500000000 : ℝ)^4443 ≤ (42915645759999/100000000000000 : ℝ)^3419 := by
    have hnat : (1303852707 : ℕ)^4443*100000000000000^3419 ≤ 42915645759999^3419*2500000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303852707 2500000000 42915645759999 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-48180257/250000000 : ℝ), (5438353473/10000000000 : ℝ), (1303852707/2500000000 : ℝ)] ![(11769645528767/100000000000000 : ℝ), (45314708695453/100000000000000 : ℝ), (42915645759999/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-48180257/250000000 : ℝ)|^4443 ≤ (11769645528767/100000000000000 : ℝ)^3419
        have hw : |(-48180257/250000000 : ℝ)|=(48180257/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5438353473/10000000000 : ℝ)|^4443 ≤ (45314708695453/100000000000000 : ℝ)^3419
        have hw : |(5438353473/10000000000 : ℝ)|=(5438353473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1303852707/2500000000 : ℝ)|^4443 ≤ (42915645759999/100000000000000 : ℝ)^3419
        have hw : |(1303852707/2500000000 : ℝ)|=(1303852707/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_s6_1 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353666293/10000000000 : ℝ)*x 0 + (-1020742403/5000000000 : ℝ)*x 1 + (5215410903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353666293/10000000000 : ℝ)^4443 ≤ (8879972119731/20000000000000 : ℝ)^3419 := by
    have hnat : (5353666293 : ℕ)^4443*20000000000000^3419 ≤ 8879972119731^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353666293 10000000000 8879972119731 20000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1020742403/5000000000 : ℝ)^4443 ≤ (792780801541/6250000000000 : ℝ)^3419 := by
    have hnat : (1020742403 : ℕ)^4443*6250000000000^3419 ≤ 792780801541^3419*5000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1020742403 5000000000 792780801541 6250000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215410903/10000000000 : ℝ)^4443 ≤ (21457823280991/50000000000000 : ℝ)^3419 := by
    have hnat : (5215410903 : ℕ)^4443*50000000000000^3419 ≤ 21457823280991^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215410903 10000000000 21457823280991 50000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353666293/10000000000 : ℝ), (-1020742403/5000000000 : ℝ), (5215410903/10000000000 : ℝ)] ![(8879972119731/20000000000000 : ℝ), (792780801541/6250000000000 : ℝ), (21457823280991/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353666293/10000000000 : ℝ)|^4443 ≤ (8879972119731/20000000000000 : ℝ)^3419
        have hw : |(5353666293/10000000000 : ℝ)|=(5353666293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1020742403/5000000000 : ℝ)|^4443 ≤ (792780801541/6250000000000 : ℝ)^3419
        have hw : |(-1020742403/5000000000 : ℝ)|=(1020742403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215410903/10000000000 : ℝ)|^4443 ≤ (21457823280991/50000000000000 : ℝ)^3419
        have hw : |(5215410903/10000000000 : ℝ)|=(5215410903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_s6_2 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676833163/5000000000 : ℝ)*x 0 + (1043082157/2000000000 : ℝ)*x 1 + (-1020742459/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676833163/5000000000 : ℝ)^4443 ≤ (693747827411/1562500000000 : ℝ)^3419 := by
    have hnat : (2676833163 : ℕ)^4443*1562500000000^3419 ≤ 693747827411^3419*5000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676833163 5000000000 693747827411 1562500000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043082157/2000000000 : ℝ)^4443 ≤ (8583129060039/20000000000000 : ℝ)^3419 := by
    have hnat : (1043082157 : ℕ)^4443*20000000000000^3419 ≤ 8583129060039^3419*2000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043082157 2000000000 8583129060039 20000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1020742459/5000000000 : ℝ)^4443 ≤ (792780858061/6250000000000 : ℝ)^3419 := by
    have hnat : (1020742459 : ℕ)^4443*6250000000000^3419 ≤ 792780858061^3419*5000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1020742459 5000000000 792780858061 6250000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676833163/5000000000 : ℝ), (1043082157/2000000000 : ℝ), (-1020742459/5000000000 : ℝ)] ![(693747827411/1562500000000 : ℝ), (8583129060039/20000000000000 : ℝ), (792780858061/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676833163/5000000000 : ℝ)|^4443 ≤ (693747827411/1562500000000 : ℝ)^3419
        have hw : |(2676833163/5000000000 : ℝ)|=(2676833163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043082157/2000000000 : ℝ)|^4443 ≤ (8583129060039/20000000000000 : ℝ)^3419
        have hw : |(1043082157/2000000000 : ℝ)|=(1043082157/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1020742459/5000000000 : ℝ)|^4443 ≤ (792780858061/6250000000000 : ℝ)^3419
        have hw : |(-1020742459/5000000000 : ℝ)|=(1020742459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_s6_3 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2144143273/5000000000 : ℝ)*x 0 + (2024314389/5000000000 : ℝ)*x 1 + (227015441/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2144143273/5000000000 : ℝ)^4443 ≤ (16638791415089/50000000000000 : ℝ)^3419 := by
    have hnat : (2144143273 : ℕ)^4443*50000000000000^3419 ≤ 16638791415089^3419*5000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2144143273 5000000000 16638791415089 50000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2024314389/5000000000 : ℝ)^4443 ≤ (30881301821189/100000000000000 : ℝ)^3419 := by
    have hnat : (2024314389 : ℕ)^4443*100000000000000^3419 ≤ 30881301821189^3419*5000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2024314389 5000000000 30881301821189 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (227015441/500000000 : ℝ)^4443 ≤ (4480139416941/12500000000000 : ℝ)^3419 := by
    have hnat : (227015441 : ℕ)^4443*12500000000000^3419 ≤ 4480139416941^3419*500000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      227015441 500000000 4480139416941 12500000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2144143273/5000000000 : ℝ), (2024314389/5000000000 : ℝ), (227015441/500000000 : ℝ)] ![(16638791415089/50000000000000 : ℝ), (30881301821189/100000000000000 : ℝ), (4480139416941/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2144143273/5000000000 : ℝ)|^4443 ≤ (16638791415089/50000000000000 : ℝ)^3419
        have hw : |(2144143273/5000000000 : ℝ)|=(2144143273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2024314389/5000000000 : ℝ)|^4443 ≤ (30881301821189/100000000000000 : ℝ)^3419
        have hw : |(2024314389/5000000000 : ℝ)|=(2024314389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(227015441/500000000 : ℝ)|^4443 ≤ (4480139416941/12500000000000 : ℝ)^3419
        have hw : |(227015441/500000000 : ℝ)|=(227015441/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_s6_4 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1927240931/10000000000 : ℝ)*x 0 + (1043309963/2000000000 : ℝ)*x 1 + (2718603069/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1927240931/10000000000 : ℝ)^4443 ≤ (1176988878119/10000000000000 : ℝ)^3419 := by
    have hnat : (1927240931 : ℕ)^4443*10000000000000^3419 ≤ 1176988878119^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1927240931 10000000000 1176988878119 10000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043309963/2000000000 : ℝ)^4443 ≤ (21463912740069/50000000000000 : ℝ)^3419 := by
    have hnat : (1043309963 : ℕ)^4443*50000000000000^3419 ≤ 21463912740069^3419*2000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043309963 2000000000 21463912740069 50000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2718603069/5000000000 : ℝ)^4443 ≤ (9060457144763/20000000000000 : ℝ)^3419 := by
    have hnat : (2718603069 : ℕ)^4443*20000000000000^3419 ≤ 9060457144763^3419*5000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718603069 5000000000 9060457144763 20000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1927240931/10000000000 : ℝ), (1043309963/2000000000 : ℝ), (2718603069/5000000000 : ℝ)] ![(1176988878119/10000000000000 : ℝ), (21463912740069/50000000000000 : ℝ), (9060457144763/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1927240931/10000000000 : ℝ)|^4443 ≤ (1176988878119/10000000000000 : ℝ)^3419
        have hw : |(-1927240931/10000000000 : ℝ)|=(1927240931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043309963/2000000000 : ℝ)|^4443 ≤ (21463912740069/50000000000000 : ℝ)^3419
        have hw : |(1043309963/2000000000 : ℝ)|=(1043309963/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2718603069/5000000000 : ℝ)|^4443 ≤ (9060457144763/20000000000000 : ℝ)^3419
        have hw : |(2718603069/5000000000 : ℝ)|=(2718603069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_s6_5 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647756399/5000000000 : ℝ)*x 0 + (-1819689513/10000000000 : ℝ)*x 1 + (5437206139/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647756399/5000000000 : ℝ)^4443 ≤ (10943537137687/25000000000000 : ℝ)^3419 := by
    have hnat : (2647756399 : ℕ)^4443*25000000000000^3419 ≤ 10943537137687^3419*5000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647756399 5000000000 10943537137687 25000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1819689513/10000000000 : ℝ)^4443 ≤ (2184713139891/20000000000000 : ℝ)^3419 := by
    have hnat : (1819689513 : ℕ)^4443*20000000000000^3419 ≤ 2184713139891^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1819689513 10000000000 2184713139891 20000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5437206139/10000000000 : ℝ)^4443 ≤ (45302285734643/100000000000000 : ℝ)^3419 := by
    have hnat : (5437206139 : ℕ)^4443*100000000000000^3419 ≤ 45302285734643^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437206139 10000000000 45302285734643 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647756399/5000000000 : ℝ), (-1819689513/10000000000 : ℝ), (5437206139/10000000000 : ℝ)] ![(10943537137687/25000000000000 : ℝ), (2184713139891/20000000000000 : ℝ), (45302285734643/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647756399/5000000000 : ℝ)|^4443 ≤ (10943537137687/25000000000000 : ℝ)^3419
        have hw : |(2647756399/5000000000 : ℝ)|=(2647756399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1819689513/10000000000 : ℝ)|^4443 ≤ (2184713139891/20000000000000 : ℝ)^3419
        have hw : |(-1819689513/10000000000 : ℝ)|=(1819689513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5437206139/10000000000 : ℝ)|^4443 ≤ (45302285734643/100000000000000 : ℝ)^3419
        have hw : |(5437206139/10000000000 : ℝ)|=(5437206139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_s6_6 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323878201/2500000000 : ℝ)*x 0 + (1087441227/2000000000 : ℝ)*x 1 + (-181968951/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323878201/2500000000 : ℝ)^4443 ≤ (54717685769/125000000000 : ℝ)^3419 := by
    have hnat : (1323878201 : ℕ)^4443*125000000000^3419 ≤ 54717685769^3419*2500000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323878201 2500000000 54717685769 125000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1087441227/2000000000 : ℝ)^4443 ≤ (45302285691333/100000000000000 : ℝ)^3419 := by
    have hnat : (1087441227 : ℕ)^4443*100000000000000^3419 ≤ 45302285691333^3419*2000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087441227 2000000000 45302285691333 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (181968951/1000000000 : ℝ)^4443 ≤ (10923565676053/100000000000000 : ℝ)^3419 := by
    have hnat : (181968951 : ℕ)^4443*100000000000000^3419 ≤ 10923565676053^3419*1000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      181968951 1000000000 10923565676053 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323878201/2500000000 : ℝ), (1087441227/2000000000 : ℝ), (-181968951/1000000000 : ℝ)] ![(54717685769/125000000000 : ℝ), (45302285691333/100000000000000 : ℝ), (10923565676053/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323878201/2500000000 : ℝ)|^4443 ≤ (54717685769/125000000000 : ℝ)^3419
        have hw : |(1323878201/2500000000 : ℝ)|=(1323878201/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1087441227/2000000000 : ℝ)|^4443 ≤ (45302285691333/100000000000000 : ℝ)^3419
        have hw : |(1087441227/2000000000 : ℝ)|=(1087441227/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-181968951/1000000000 : ℝ)|^4443 ≤ (10923565676053/100000000000000 : ℝ)^3419
        have hw : |(-181968951/1000000000 : ℝ)|=(181968951/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_s6_7 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4288354179/10000000000 : ℝ)*x 0 + (4537796957/10000000000 : ℝ)*x 1 + (2025579553/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4288354179/10000000000 : ℝ)^4443 ≤ (33278264862357/100000000000000 : ℝ)^3419 := by
    have hnat : (4288354179 : ℕ)^4443*100000000000000^3419 ≤ 33278264862357^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4288354179 10000000000 33278264862357 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4537796957/10000000000 : ℝ)^4443 ≤ (286522801189/800000000000 : ℝ)^3419 := by
    have hnat : (4537796957 : ℕ)^4443*800000000000^3419 ≤ 286522801189^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4537796957 10000000000 286522801189 800000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2025579553/5000000000 : ℝ)^4443 ≤ (30906384985019/100000000000000 : ℝ)^3419 := by
    have hnat : (2025579553 : ℕ)^4443*100000000000000^3419 ≤ 30906384985019^3419*5000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2025579553 5000000000 30906384985019 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4288354179/10000000000 : ℝ), (4537796957/10000000000 : ℝ), (2025579553/5000000000 : ℝ)] ![(33278264862357/100000000000000 : ℝ), (286522801189/800000000000 : ℝ), (30906384985019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4288354179/10000000000 : ℝ)|^4443 ≤ (33278264862357/100000000000000 : ℝ)^3419
        have hw : |(4288354179/10000000000 : ℝ)|=(4288354179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4537796957/10000000000 : ℝ)|^4443 ≤ (286522801189/800000000000 : ℝ)^3419
        have hw : |(4537796957/10000000000 : ℝ)|=(4537796957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2025579553/5000000000 : ℝ)|^4443 ≤ (30906384985019/100000000000000 : ℝ)^3419
        have hw : |(2025579553/5000000000 : ℝ)|=(2025579553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1473_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160270543/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (619/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5377/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2689/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7737/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (619/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5377/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (619/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5377/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (619/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5377/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (619/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5377/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (619/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5377/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (619/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5377/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5377/50000 : ℝ) ^ (4441/1024 : ℝ) ≤ (630960909519109/10000000000000000000 : ℝ) := by
    have hpowers : (5377/50000 : ℝ)^4441 ≤ (630960909519109/10000000000000000000 : ℝ)^1024 := by
      have hnat : (5377 : ℕ)^4441*10000000000000000000^1024 ≤ 630960909519109^1024*50000^4441 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5377 50000 630960909519109 10000000000000000000 4441 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5377/50000 : ℝ)) (X := (630960909519109/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4441 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (619/4000 : ℝ) ^ (4441/1024 : ℝ) ≤ (30584247782809039/100000000000000000000 : ℝ) := by
    have hpowers : (619/4000 : ℝ)^4441 ≤ (30584247782809039/100000000000000000000 : ℝ)^1024 := by
      have hnat : (619 : ℕ)^4441*100000000000000000000^1024 ≤ 30584247782809039^1024*4000^4441 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        619 4000 30584247782809039 100000000000000000000 4441 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (619/4000 : ℝ)) (X := (30584247782809039/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4441 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000630960909519109/5000000000000000000 : ℝ) ≤ (10000290958165713/10000000000000000 : ℝ) ^ (4441/1024 : ℝ) := by
    have hpowers : (5000630960909519109/5000000000000000000 : ℝ)^1024 ≤ (10000290958165713/10000000000000000 : ℝ)^4441 := by
      have hnat : (5000630960909519109 : ℕ)^1024*10000000000000000^4441 ≤ 10000290958165713^4441*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000630960909519109 5000000000000000000 10000290958165713 10000000000000000 1024 4441 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000290958165713/10000000000000000 : ℝ)) (X := (5000630960909519109/5000000000000000000 : ℝ)) (by norm_num) 4441 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100036893856878000129/100000000000000000000 : ℝ) ≤ (10000850573033519/10000000000000000 : ℝ) ^ (4441/1024 : ℝ) := by
    have hpowers : (100036893856878000129/100000000000000000000 : ℝ)^1024 ≤ (10000850573033519/10000000000000000 : ℝ)^4441 := by
      have hnat : (100036893856878000129 : ℕ)^1024*10000000000000000^4441 ≤ 10000850573033519^4441*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100036893856878000129 100000000000000000000 10000850573033519 10000000000000000 1024 4441 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000850573033519/10000000000000000 : ℝ)) (X := (100036893856878000129/100000000000000000000 : ℝ)) (by norm_num) 4441 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50030584247782809039/50000000000000000000 : ℝ) ≤ (400056407516053/400000000000000 : ℝ) ^ (4441/1024 : ℝ) := by
    have hpowers : (50030584247782809039/50000000000000000000 : ℝ)^1024 ≤ (400056407516053/400000000000000 : ℝ)^4441 := by
      have hnat : (50030584247782809039 : ℕ)^1024*400000000000000^4441 ≤ 400056407516053^4441*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030584247782809039 50000000000000000000 400056407516053 400000000000000 1024 4441 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400056407516053/400000000000000 : ℝ)) (X := (50030584247782809039/50000000000000000000 : ℝ)) (by norm_num) 4441 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(630960909519109/10000000000000000000 : ℝ) ≤ ((377594699335388477/377680000000000000 : ℝ)+2*(279807433903/236050000000000 : ℝ)*(5377/50000 : ℝ))^(4441/1024 : ℝ) := by
    rw [show (377594699335388477/377680000000000000 : ℝ)+2*(279807433903/236050000000000 : ℝ)*(5377/50000 : ℝ)=(10000290958165713/10000000000000000 : ℝ) by norm_num, show 1+2*(630960909519109/10000000000000000000 : ℝ)=(5000630960909519109/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30584247782809039/100000000000000000000 : ℝ)+(630960909519109/10000000000000000000 : ℝ) ≤ ((377594699335388477/377680000000000000 : ℝ)+(279807433903/236050000000000 : ℝ)*((619/4000 : ℝ)+(5377/50000 : ℝ)))^(4441/1024 : ℝ) := by
    rw [show (377594699335388477/377680000000000000 : ℝ)+(279807433903/236050000000000 : ℝ)*((619/4000 : ℝ)+(5377/50000 : ℝ))=(10000850573033519/10000000000000000 : ℝ) by norm_num, show 1+(30584247782809039/100000000000000000000 : ℝ)+(630960909519109/10000000000000000000 : ℝ)=(100036893856878000129/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30584247782809039/100000000000000000000 : ℝ) ≤ ((377594699335388477/377680000000000000 : ℝ)+2*(279807433903/236050000000000 : ℝ)*(619/4000 : ℝ))^(4441/1024 : ℝ) := by
    rw [show (377594699335388477/377680000000000000 : ℝ)+2*(279807433903/236050000000000 : ℝ)*(619/4000 : ℝ)=(400056407516053/400000000000000 : ℝ) by norm_num, show 1+2*(30584247782809039/100000000000000000000 : ℝ)=(50030584247782809039/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (377594699335388477/377680000000000000 : ℝ)*(X 1 0+X 2 0)+(279807433903/236050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4441/1024 : ℝ)) (lo := (5377/50000 : ℝ)) (hi := (619/4000 : ℝ)) (c := (377594699335388477/377680000000000000 : ℝ)) (alpha := (279807433903/236050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (377594699335388477/377680000000000000 : ℝ)*(X 0 1+X 2 1)+(279807433903/236050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4441/1024 : ℝ)) (lo := (5377/50000 : ℝ)) (hi := (619/4000 : ℝ)) (c := (377594699335388477/377680000000000000 : ℝ)) (alpha := (279807433903/236050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (377594699335388477/377680000000000000 : ℝ)*(X 0 2+X 1 2)+(279807433903/236050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4441/1024 : ℝ)) (lo := (5377/50000 : ℝ)) (hi := (619/4000 : ℝ)) (c := (377594699335388477/377680000000000000 : ℝ)) (alpha := (279807433903/236050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-48180257/250000000 : ℝ)*X 0 0+(5438353473/10000000000 : ℝ)*X 0 1+(1303852707/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5353666293/10000000000 : ℝ)*X 1 0+(-1020742403/5000000000 : ℝ)*X 1 1+(5215410903/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676833163/5000000000 : ℝ)*X 2 0+(1043082157/2000000000 : ℝ)*X 2 1+(-1020742459/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2144143273/5000000000 : ℝ)*X 0 0+(2024314389/5000000000 : ℝ)*X 0 1+(227015441/500000000 : ℝ)*X 0 2+(2144143273/5000000000 : ℝ)*X 1 0+(2024314389/5000000000 : ℝ)*X 1 1+(227015441/500000000 : ℝ)*X 1 2+(2144143273/5000000000 : ℝ)*X 2 0+(2024314389/5000000000 : ℝ)*X 2 1+(227015441/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1927240931/10000000000 : ℝ)*X 0 0+(1043309963/2000000000 : ℝ)*X 0 1+(2718603069/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2647756399/5000000000 : ℝ)*X 1 0+(-1819689513/10000000000 : ℝ)*X 1 1+(5437206139/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1323878201/2500000000 : ℝ)*X 2 0+(1087441227/2000000000 : ℝ)*X 2 1+(-181968951/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4288354179/10000000000 : ℝ)*X 0 0+(4537796957/10000000000 : ℝ)*X 0 1+(2025579553/5000000000 : ℝ)*X 0 2+(4288354179/10000000000 : ℝ)*X 1 0+(4537796957/10000000000 : ℝ)*X 1 1+(2025579553/5000000000 : ℝ)*X 1 2+(4288354179/10000000000 : ℝ)*X 2 0+(4537796957/10000000000 : ℝ)*X 2 1+(2025579553/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (108635923678153717201881501/18884000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (946940437/100000000000000 : ℝ)*(base19) + (916377637/100000000000000 : ℝ)*(base23) + (3116441/10000000000000 : ℝ)*(lower2) + (97945533/50000000000000 : ℝ)*(upper3) + (53120081/100000000000000 : ℝ)*(upper5) + (3259672146699829/100000000000000 : ℝ)*(major0) + (3259672146699829/100000000000000 : ℝ)*(major1) + (3259672146699829/100000000000000 : ℝ)*(major2) + (17521386454139/390625000000 : ℝ)*(sp0) + (2242743548753619/50000000000000 : ℝ)*(sp1) + (2242743564035019/50000000000000 : ℝ)*(sp2) + (1016924300480617/50000000000000 : ℝ)*(sp3) + (13112188091/100000000000000 : ℝ)*(sp4) + (7456230653/100000000000000 : ℝ)*(sp7) + (127116003574493/6250000000000 : ℝ)*(f.failure) + (1121372011111919/25000000000000 : ℝ)*(f.sum) + (705428630719/5901250000000000000000000000 : ℝ)*base66 + (320458338190449633/37768000000000000000000000000000 : ℝ)*base67 + (125136033628865633/37768000000000000000000000000000 : ℝ)*base69 + (7292426647929633/37768000000000000000000000000000 : ℝ)*base71 + (79669292537449/23605000000000000000000000000 : ℝ)*base73 + (301284998152606367/37768000000000000000000000000000 : ℝ)*base76 + (272417821500342367/37768000000000000000000000000000 : ℝ)*base78 + (181269229908905633/37768000000000000000000000000000 : ℝ)*base79 + (3179680799647/737656250000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (2809699/625000000000000000000 : ℝ)*base89 + (2809699/625000000000000000000 : ℝ)*base91 + (2809699/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (214888361717377319618163513/18884000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1886569241/100000000000000 : ℝ)*(base19) + (257146223/12500000000000 : ℝ)*(base23) + (39230229/6250000000000 : ℝ)*(lower1) + (233572181/100000000000000 : ℝ)*(upper3) + (74422911/100000000000000 : ℝ)*(lower4) + (9330709/4000000000000 : ℝ)*(upper5) + (3293404087141777/100000000000000 : ℝ)*(major0) + (3293404087141777/100000000000000 : ℝ)*(major1) + (3293404087141777/100000000000000 : ℝ)*(major2) + (2269799891/100000000000000 : ℝ)*(sp2) + (4531904863031479/100000000000000 : ℝ)*(sp4) + (2265951488231119/50000000000000 : ℝ)*(sp5) + (1132975134015451/25000000000000 : ℝ)*(sp6) + (1027451465969569/50000000000000 : ℝ)*(sp7) + (1027451465969569/50000000000000 : ℝ)*(f.failure) + (4531904863031479/100000000000000 : ℝ)*(f.sum) + (37227795293303/23605000000000000000000000000 : ℝ)*base66 + (200568975089254771/37768000000000000000000000000000 : ℝ)*base68 + (269277057901473229/37768000000000000000000000000000 : ℝ)*base69 + (901140573901345229/37768000000000000000000000000000 : ℝ)*base71 + (2031009163601/11802500000000000000000000000 : ℝ)*base73 + (40808569208833229/37768000000000000000000000000000 : ℝ)*base75 + (78175619928398771/37768000000000000000000000000000 : ℝ)*base78 + (228303071707625229/37768000000000000000000000000000 : ℝ)*base79 + (41468705059503/5901250000000000000000000000 : ℝ)*base81 + (4894033/5000000000000000000000 : ℝ)*base90 + (4894033/5000000000000000000000 : ℝ)*base92 + (4894033/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1473_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160270543/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (619/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5377/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2689/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7737/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1473_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1473_s7_0 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334603799/625000000 : ℝ)*x 0 + (1043084883/2000000000 : ℝ)*x 1 + (-408294853/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334603799/625000000 : ℝ)^4443 ≤ (44399801226853/100000000000000 : ℝ)^3419 := by
    have hnat : (334603799 : ℕ)^4443*100000000000000^3419 ≤ 44399801226853^3419*625000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334603799 625000000 44399801226853 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043084883/2000000000 : ℝ)^4443 ≤ (42915791047443/100000000000000 : ℝ)^3419 := by
    have hnat : (1043084883 : ℕ)^4443*100000000000000^3419 ≤ 42915791047443^3419*2000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043084883 2000000000 42915791047443 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (408294853/2000000000 : ℝ)^4443 ≤ (6342203856833/50000000000000 : ℝ)^3419 := by
    have hnat : (408294853 : ℕ)^4443*50000000000000^3419 ≤ 6342203856833^3419*2000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      408294853 2000000000 6342203856833 50000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334603799/625000000 : ℝ), (1043084883/2000000000 : ℝ), (-408294853/2000000000 : ℝ)] ![(44399801226853/100000000000000 : ℝ), (42915791047443/100000000000000 : ℝ), (6342203856833/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334603799/625000000 : ℝ)|^4443 ≤ (44399801226853/100000000000000 : ℝ)^3419
        have hw : |(334603799/625000000 : ℝ)|=(334603799/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043084883/2000000000 : ℝ)|^4443 ≤ (42915791047443/100000000000000 : ℝ)^3419
        have hw : |(1043084883/2000000000 : ℝ)|=(1043084883/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-408294853/2000000000 : ℝ)|^4443 ≤ (6342203856833/50000000000000 : ℝ)^3419
        have hw : |(-408294853/2000000000 : ℝ)|=(408294853/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_s7_1 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (107207299/250000000 : ℝ)*x 0 + (202432293/500000000 : ℝ)*x 1 + (4540286991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107207299/250000000 : ℝ)^4443 ≤ (33277637426517/100000000000000 : ℝ)^3419 := by
    have hnat : (107207299 : ℕ)^4443*100000000000000^3419 ≤ 33277637426517^3419*250000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107207299 250000000 33277637426517 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (202432293/500000000 : ℝ)^4443 ≤ (30881471139469/100000000000000 : ℝ)^3419 := by
    have hnat : (202432293 : ℕ)^4443*100000000000000^3419 ≤ 30881471139469^3419*500000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      202432293 500000000 30881471139469 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4540286991/10000000000 : ℝ)^4443 ≤ (35840891408321/100000000000000 : ℝ)^3419 := by
    have hnat : (4540286991 : ℕ)^4443*100000000000000^3419 ≤ 35840891408321^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4540286991 10000000000 35840891408321 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(107207299/250000000 : ℝ), (202432293/500000000 : ℝ), (4540286991/10000000000 : ℝ)] ![(33277637426517/100000000000000 : ℝ), (30881471139469/100000000000000 : ℝ), (35840891408321/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(107207299/250000000 : ℝ)|^4443 ≤ (33277637426517/100000000000000 : ℝ)^3419
        have hw : |(107207299/250000000 : ℝ)|=(107207299/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(202432293/500000000 : ℝ)|^4443 ≤ (30881471139469/100000000000000 : ℝ)^3419
        have hw : |(202432293/500000000 : ℝ)|=(202432293/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4540286991/10000000000 : ℝ)|^4443 ≤ (35840891408321/100000000000000 : ℝ)^3419
        have hw : |(4540286991/10000000000 : ℝ)|=(4540286991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_s7_2 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1927238911/10000000000 : ℝ)*x 0 + (5216560789/10000000000 : ℝ)*x 1 + (271859839/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1927238911/10000000000 : ℝ)^4443 ≤ (11769872750033/100000000000000 : ℝ)^3419 := by
    have hnat : (1927238911 : ℕ)^4443*100000000000000^3419 ≤ 11769872750033^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1927238911 10000000000 11769872750033 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216560789/10000000000 : ℝ)^4443 ≤ (21463971417061/50000000000000 : ℝ)^3419 := by
    have hnat : (5216560789 : ℕ)^4443*50000000000000^3419 ≤ 21463971417061^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216560789 10000000000 21463971417061 50000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (271859839/500000000 : ℝ)^4443 ≤ (45302184401651/100000000000000 : ℝ)^3419 := by
    have hnat : (271859839 : ℕ)^4443*100000000000000^3419 ≤ 45302184401651^3419*500000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271859839 500000000 45302184401651 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1927238911/10000000000 : ℝ), (5216560789/10000000000 : ℝ), (271859839/500000000 : ℝ)] ![(11769872750033/100000000000000 : ℝ), (21463971417061/50000000000000 : ℝ), (45302184401651/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1927238911/10000000000 : ℝ)|^4443 ≤ (11769872750033/100000000000000 : ℝ)^3419
        have hw : |(-1927238911/10000000000 : ℝ)|=(1927238911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216560789/10000000000 : ℝ)|^4443 ≤ (21463971417061/50000000000000 : ℝ)^3419
        have hw : |(5216560789/10000000000 : ℝ)|=(5216560789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(271859839/500000000 : ℝ)|^4443 ≤ (45302184401651/100000000000000 : ℝ)^3419
        have hw : |(271859839/500000000 : ℝ)|=(271859839/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_s7_3 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (165484829/312500000 : ℝ)*x 0 + (-454924197/2500000000 : ℝ)*x 1 + (5437199181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165484829/312500000 : ℝ)^4443 ≤ (10943541783621/25000000000000 : ℝ)^3419 := by
    have hnat : (165484829 : ℕ)^4443*25000000000000^3419 ≤ 10943541783621^3419*312500000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165484829 312500000 10943541783621 25000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (454924197/2500000000 : ℝ)^4443 ≤ (10923622450989/100000000000000 : ℝ)^3419 := by
    have hnat : (454924197 : ℕ)^4443*100000000000000^3419 ≤ 10923622450989^3419*2500000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      454924197 2500000000 10923622450989 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5437199181/10000000000 : ℝ)^4443 ≤ (11325552599517/25000000000000 : ℝ)^3419 := by
    have hnat : (5437199181 : ℕ)^4443*25000000000000^3419 ≤ 11325552599517^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437199181 10000000000 11325552599517 25000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165484829/312500000 : ℝ), (-454924197/2500000000 : ℝ), (5437199181/10000000000 : ℝ)] ![(10943541783621/25000000000000 : ℝ), (10923622450989/100000000000000 : ℝ), (11325552599517/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165484829/312500000 : ℝ)|^4443 ≤ (10943541783621/25000000000000 : ℝ)^3419
        have hw : |(165484829/312500000 : ℝ)|=(165484829/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-454924197/2500000000 : ℝ)|^4443 ≤ (10923622450989/100000000000000 : ℝ)^3419
        have hw : |(-454924197/2500000000 : ℝ)|=(454924197/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5437199181/10000000000 : ℝ)|^4443 ≤ (11325552599517/25000000000000 : ℝ)^3419
        have hw : |(5437199181/10000000000 : ℝ)|=(5437199181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_s7_4 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323878839/2500000000 : ℝ)*x 0 + (54371989/100000000 : ℝ)*x 1 + (-909848019/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323878839/2500000000 : ℝ)^4443 ≤ (43774176028897/100000000000000 : ℝ)^3419 := by
    have hnat : (1323878839 : ℕ)^4443*100000000000000^3419 ≤ 43774176028897^3419*2500000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323878839 2500000000 43774176028897 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (54371989/100000000 : ℝ)^4443 ≤ (11325551838897/25000000000000 : ℝ)^3419 := by
    have hnat : (54371989 : ℕ)^4443*25000000000000^3419 ≤ 11325551838897^3419*100000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54371989 100000000 11325551838897 25000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (909848019/5000000000 : ℝ)^4443 ≤ (1365452075039/12500000000000 : ℝ)^3419 := by
    have hnat : (909848019 : ℕ)^4443*12500000000000^3419 ≤ 1365452075039^3419*5000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      909848019 5000000000 1365452075039 12500000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323878839/2500000000 : ℝ), (54371989/100000000 : ℝ), (-909848019/5000000000 : ℝ)] ![(43774176028897/100000000000000 : ℝ), (11325551838897/25000000000000 : ℝ), (1365452075039/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323878839/2500000000 : ℝ)|^4443 ≤ (43774176028897/100000000000000 : ℝ)^3419
        have hw : |(1323878839/2500000000 : ℝ)|=(1323878839/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(54371989/100000000 : ℝ)|^4443 ≤ (11325551838897/25000000000000 : ℝ)^3419
        have hw : |(54371989/100000000 : ℝ)|=(54371989/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-909848019/5000000000 : ℝ)|^4443 ≤ (1365452075039/12500000000000 : ℝ)^3419
        have hw : |(-909848019/5000000000 : ℝ)|=(909848019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_s7_5 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4288356961/10000000000 : ℝ)*x 0 + (2268887049/5000000000 : ℝ)*x 1 + (1012794981/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4288356961/10000000000 : ℝ)^4443 ≤ (16639146458489/50000000000000 : ℝ)^3419 := by
    have hnat : (4288356961 : ℕ)^4443*50000000000000^3419 ≤ 16639146458489^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4288356961 10000000000 16639146458489 50000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2268887049/5000000000 : ℝ)^4443 ≤ (35815115694297/100000000000000 : ℝ)^3419 := by
    have hnat : (2268887049 : ℕ)^4443*100000000000000^3419 ≤ 35815115694297^3419*5000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2268887049 5000000000 35815115694297 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1012794981/2500000000 : ℝ)^4443 ≤ (30906591373503/100000000000000 : ℝ)^3419 := by
    have hnat : (1012794981 : ℕ)^4443*100000000000000^3419 ≤ 30906591373503^3419*2500000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1012794981 2500000000 30906591373503 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4288356961/10000000000 : ℝ), (2268887049/5000000000 : ℝ), (1012794981/2500000000 : ℝ)] ![(16639146458489/50000000000000 : ℝ), (35815115694297/100000000000000 : ℝ), (30906591373503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4288356961/10000000000 : ℝ)|^4443 ≤ (16639146458489/50000000000000 : ℝ)^3419
        have hw : |(4288356961/10000000000 : ℝ)|=(4288356961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2268887049/5000000000 : ℝ)|^4443 ≤ (35815115694297/100000000000000 : ℝ)^3419
        have hw : |(2268887049/5000000000 : ℝ)|=(2268887049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1012794981/2500000000 : ℝ)|^4443 ≤ (30906591373503/100000000000000 : ℝ)^3419
        have hw : |(1012794981/2500000000 : ℝ)|=(1012794981/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1473_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160270543/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7737/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2689/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2689/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15473/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7737/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2689/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7737/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2689/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7737/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2689/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7737/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2689/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7737/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2689/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7737/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2689/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
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
  have hpowlo : (2689/25000 : ℝ) ^ (4441/1024 : ℝ) ≤ (789337475113333/12500000000000000000 : ℝ) := by
    have hpowers : (2689/25000 : ℝ)^4441 ≤ (789337475113333/12500000000000000000 : ℝ)^1024 := by
      have hnat : (2689 : ℕ)^4441*12500000000000000000^1024 ≤ 789337475113333^1024*25000^4441 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2689 25000 789337475113333 12500000000000000000 4441 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2689/25000 : ℝ)) (X := (789337475113333/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4441 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7737/50000 : ℝ) ^ (4441/1024 : ℝ) ≤ (15287838690947891/50000000000000000000 : ℝ) := by
    have hpowers : (7737/50000 : ℝ)^4441 ≤ (15287838690947891/50000000000000000000 : ℝ)^1024 := by
      have hnat : (7737 : ℕ)^4441*50000000000000000000^1024 ≤ 15287838690947891^1024*50000^4441 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7737 50000 15287838690947891 50000000000000000000 4441 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7737/50000 : ℝ)) (X := (15287838690947891/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4441 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250789337475113333/6250000000000000000 : ℝ) ≤ (2500072798226143/2500000000000000 : ℝ) ^ (4441/1024 : ℝ) := by
    have hpowers : (6250789337475113333/6250000000000000000 : ℝ)^1024 ≤ (2500072798226143/2500000000000000 : ℝ)^4441 := by
      have hnat : (6250789337475113333 : ℕ)^1024*2500000000000000^4441 ≤ 2500072798226143^4441*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250789337475113333 6250000000000000000 2500072798226143 2500000000000000 1024 4441 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500072798226143/2500000000000000 : ℝ)) (X := (6250789337475113333/6250000000000000000 : ℝ)) (by norm_num) 4441 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50018445188591401223/50000000000000000000 : ℝ) ≤ (10000850492821927/10000000000000000 : ℝ) ^ (4441/1024 : ℝ) := by
    have hpowers : (50018445188591401223/50000000000000000000 : ℝ)^1024 ≤ (10000850492821927/10000000000000000 : ℝ)^4441 := by
      have hnat : (50018445188591401223 : ℕ)^1024*10000000000000000^4441 ≤ 10000850492821927^4441*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018445188591401223 50000000000000000000 10000850492821927 10000000000000000 1024 4441 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000850492821927/10000000000000000 : ℝ)) (X := (50018445188591401223/50000000000000000000 : ℝ)) (by norm_num) 4441 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015287838690947891/25000000000000000000 : ℝ) ≤ (5000704896369641/5000000000000000 : ℝ) ^ (4441/1024 : ℝ) := by
    have hpowers : (25015287838690947891/25000000000000000000 : ℝ)^1024 ≤ (5000704896369641/5000000000000000 : ℝ)^4441 := by
      have hnat : (25015287838690947891 : ℕ)^1024*5000000000000000^4441 ≤ 5000704896369641^4441*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015287838690947891 25000000000000000000 5000704896369641 5000000000000000 1024 4441 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000704896369641/5000000000000000 : ℝ)) (X := (25015287838690947891/25000000000000000000 : ℝ)) (by norm_num) 4441 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(789337475113333/12500000000000000000 : ℝ) ≤ ((2948083886768851871/2948750000000000000 : ℝ)+2*(111859983471/94360000000000 : ℝ)*(2689/25000 : ℝ))^(4441/1024 : ℝ) := by
    rw [show (2948083886768851871/2948750000000000000 : ℝ)+2*(111859983471/94360000000000 : ℝ)*(2689/25000 : ℝ)=(2500072798226143/2500000000000000 : ℝ) by norm_num, show 1+2*(789337475113333/12500000000000000000 : ℝ)=(6250789337475113333/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15287838690947891/50000000000000000000 : ℝ)+(789337475113333/12500000000000000000 : ℝ) ≤ ((2948083886768851871/2948750000000000000 : ℝ)+(111859983471/94360000000000 : ℝ)*((7737/50000 : ℝ)+(2689/25000 : ℝ)))^(4441/1024 : ℝ) := by
    rw [show (2948083886768851871/2948750000000000000 : ℝ)+(111859983471/94360000000000 : ℝ)*((7737/50000 : ℝ)+(2689/25000 : ℝ))=(10000850492821927/10000000000000000 : ℝ) by norm_num, show 1+(15287838690947891/50000000000000000000 : ℝ)+(789337475113333/12500000000000000000 : ℝ)=(50018445188591401223/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15287838690947891/50000000000000000000 : ℝ) ≤ ((2948083886768851871/2948750000000000000 : ℝ)+2*(111859983471/94360000000000 : ℝ)*(7737/50000 : ℝ))^(4441/1024 : ℝ) := by
    rw [show (2948083886768851871/2948750000000000000 : ℝ)+2*(111859983471/94360000000000 : ℝ)*(7737/50000 : ℝ)=(5000704896369641/5000000000000000 : ℝ) by norm_num, show 1+2*(15287838690947891/50000000000000000000 : ℝ)=(25015287838690947891/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2948083886768851871/2948750000000000000 : ℝ)*(X 1 0+X 2 0)+(111859983471/94360000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4441/1024 : ℝ)) (lo := (2689/25000 : ℝ)) (hi := (7737/50000 : ℝ)) (c := (2948083886768851871/2948750000000000000 : ℝ)) (alpha := (111859983471/94360000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2948083886768851871/2948750000000000000 : ℝ)*(X 0 1+X 2 1)+(111859983471/94360000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4441/1024 : ℝ)) (lo := (2689/25000 : ℝ)) (hi := (7737/50000 : ℝ)) (c := (2948083886768851871/2948750000000000000 : ℝ)) (alpha := (111859983471/94360000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2948083886768851871/2948750000000000000 : ℝ)*(X 0 2+X 1 2)+(111859983471/94360000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4441/1024 : ℝ)) (lo := (2689/25000 : ℝ)) (hi := (7737/50000 : ℝ)) (c := (2948083886768851871/2948750000000000000 : ℝ)) (alpha := (111859983471/94360000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((334603799/625000000 : ℝ)*X 2 0+(1043084883/2000000000 : ℝ)*X 2 1+(-408294853/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_s7_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((107207299/250000000 : ℝ)*X 0 0+(202432293/500000000 : ℝ)*X 0 1+(4540286991/10000000000 : ℝ)*X 0 2+(107207299/250000000 : ℝ)*X 1 0+(202432293/500000000 : ℝ)*X 1 1+(4540286991/10000000000 : ℝ)*X 1 2+(107207299/250000000 : ℝ)*X 2 0+(202432293/500000000 : ℝ)*X 2 1+(4540286991/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_s7_1 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((-1927238911/10000000000 : ℝ)*X 0 0+(5216560789/10000000000 : ℝ)*X 0 1+(271859839/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_s7_2 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((165484829/312500000 : ℝ)*X 1 0+(-454924197/2500000000 : ℝ)*X 1 1+(5437199181/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_s7_3 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((1323878839/2500000000 : ℝ)*X 2 0+(54371989/100000000 : ℝ)*X 2 1+(-909848019/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_s7_4 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4288356961/10000000000 : ℝ)*X 0 0+(2268887049/5000000000 : ℝ)*X 0 1+(1012794981/2500000000 : ℝ)*X 0 2+(4288356961/10000000000 : ℝ)*X 1 0+(2268887049/5000000000 : ℝ)*X 1 1+(1012794981/2500000000 : ℝ)*X 1 2+(4288356961/10000000000 : ℝ)*X 2 0+(2268887049/5000000000 : ℝ)*X 2 1+(1012794981/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_s7_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (189138899027734856842810011/73718750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (47703079/5000000000000 : ℝ)*(base15) + (284733897/50000000000000 : ℝ)*(lower1) + (117710371/25000000000000 : ℝ)*(lower2) + (466473447/100000000000000 : ℝ)*(lower4) + (40674219/100000000000000 : ℝ)*(lower5) + (1646852849671649/50000000000000 : ℝ)*(major0) + (1646852849671649/50000000000000 : ℝ)*(major1) + (1646852849671649/50000000000000 : ℝ)*(major2) + (13402396853/100000000000000 : ℝ)*(sp0) + (1003771559/50000000000000 : ℝ)*(sp1) + (4532320191807059/100000000000000 : ℝ)*(sp2) + (4532319237745479/100000000000000 : ℝ)*(sp3) + (906461357882041/20000000000000 : ℝ)*(sp4) + (2055089113813661/100000000000000 : ℝ)*(sp5) + (1027545560678389/50000000000000 : ℝ)*(f.failure) + (4532320191807059/100000000000000 : ℝ)*(f.sum) + (4246411478289/2359000000000000000000000000 : ℝ)*base66 + (1437357168092663471/147437500000000000000000000000000 : ℝ)*base68 + (1231392275515600971/147437500000000000000000000000000 : ℝ)*base70 + (603810504644913471/147437500000000000000000000000000 : ℝ)*base72 + (422648791427/94360000000000000000000000 : ℝ)*base74 + (1103001146750663471/147437500000000000000000000000000 : ℝ)*base76 + (937152216731163471/147437500000000000000000000000000 : ℝ)*base78 + (242719899148663471/147437500000000000000000000000000 : ℝ)*base80 + (17180303024287/1179500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (46604773/5000000000000000000000 : ℝ)*base90 + (46604773/5000000000000000000000 : ℝ)*base92 + (46604773/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1473_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160270543/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7737/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2689/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2689/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15473/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1473_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1473_box_0 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1706336357/10000000000 : ℝ)*x 0 + (2703530441/5000000000 : ℝ)*x 1 + (2703529959/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1706336357/10000000000 : ℝ)^4443 ≤ (5023840884891/50000000000000 : ℝ)^3419 := by
    have hnat : (1706336357 : ℕ)^4443*50000000000000^3419 ≤ 5023840884891^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1706336357 10000000000 5023840884891 50000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2703530441/5000000000 : ℝ)^4443 ≤ (44976164314961/100000000000000 : ℝ)^3419 := by
    have hnat : (2703530441 : ℕ)^4443*100000000000000^3419 ≤ 44976164314961^3419*5000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703530441 5000000000 44976164314961 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703529959/5000000000 : ℝ)^4443 ≤ (44976153894777/100000000000000 : ℝ)^3419 := by
    have hnat : (2703529959 : ℕ)^4443*100000000000000^3419 ≤ 44976153894777^3419*5000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703529959 5000000000 44976153894777 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1706336357/10000000000 : ℝ), (2703530441/5000000000 : ℝ), (2703529959/5000000000 : ℝ)] ![(5023840884891/50000000000000 : ℝ), (44976164314961/100000000000000 : ℝ), (44976153894777/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1706336357/10000000000 : ℝ)|^4443 ≤ (5023840884891/50000000000000 : ℝ)^3419
        have hw : |(-1706336357/10000000000 : ℝ)|=(1706336357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2703530441/5000000000 : ℝ)|^4443 ≤ (44976164314961/100000000000000 : ℝ)^3419
        have hw : |(2703530441/5000000000 : ℝ)|=(2703530441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703529959/5000000000 : ℝ)|^4443 ≤ (44976153894777/100000000000000 : ℝ)^3419
        have hw : |(2703529959/5000000000 : ℝ)|=(2703529959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_box_1 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (42160617/80000000 : ℝ)*x 0 + (-948010711/5000000000 : ℝ)*x 1 + (5407060343/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42160617/80000000 : ℝ)^4443 ≤ (5437639275587/12500000000000 : ℝ)^3419 := by
    have hnat : (42160617 : ℕ)^4443*12500000000000^3419 ≤ 5437639275587^3419*80000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42160617 80000000 5437639275587 12500000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (948010711/5000000000 : ℝ)^4443 ≤ (11522727293263/100000000000000 : ℝ)^3419 := by
    have hnat : (948010711 : ℕ)^4443*100000000000000^3419 ≤ 11522727293263^3419*5000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      948010711 5000000000 11522727293263 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407060343/10000000000 : ℝ)^4443 ≤ (22488079244369/50000000000000 : ℝ)^3419 := by
    have hnat : (5407060343 : ℕ)^4443*50000000000000^3419 ≤ 22488079244369^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407060343 10000000000 22488079244369 50000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42160617/80000000 : ℝ), (-948010711/5000000000 : ℝ), (5407060343/10000000000 : ℝ)] ![(5437639275587/12500000000000 : ℝ), (11522727293263/100000000000000 : ℝ), (22488079244369/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42160617/80000000 : ℝ)|^4443 ≤ (5437639275587/12500000000000 : ℝ)^3419
        have hw : |(42160617/80000000 : ℝ)|=(42160617/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-948010711/5000000000 : ℝ)|^4443 ≤ (11522727293263/100000000000000 : ℝ)^3419
        have hw : |(-948010711/5000000000 : ℝ)|=(948010711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407060343/10000000000 : ℝ)|^4443 ≤ (22488079244369/50000000000000 : ℝ)^3419
        have hw : |(5407060343/10000000000 : ℝ)|=(5407060343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_box_2 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (32937987/62500000 : ℝ)*x 0 + (2703529763/5000000000 : ℝ)*x 1 + (-94801073/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (32937987/62500000 : ℝ)^4443 ≤ (21750561366157/50000000000000 : ℝ)^3419 := by
    have hnat : (32937987 : ℕ)^4443*50000000000000^3419 ≤ 21750561366157^3419*62500000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32937987 62500000 21750561366157 50000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2703529763/5000000000 : ℝ)^4443 ≤ (11244037414381/25000000000000 : ℝ)^3419 := by
    have hnat : (2703529763 : ℕ)^4443*25000000000000^3419 ≤ 11244037414381^3419*5000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703529763 5000000000 11244037414381 25000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (94801073/500000000 : ℝ)^4443 ≤ (1440340949171/12500000000000 : ℝ)^3419 := by
    have hnat : (94801073 : ℕ)^4443*12500000000000^3419 ≤ 1440340949171^3419*500000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94801073 500000000 1440340949171 12500000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(32937987/62500000 : ℝ), (2703529763/5000000000 : ℝ), (-94801073/500000000 : ℝ)] ![(21750561366157/50000000000000 : ℝ), (11244037414381/25000000000000 : ℝ), (1440340949171/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(32937987/62500000 : ℝ)|^4443 ≤ (21750561366157/50000000000000 : ℝ)^3419
        have hw : |(32937987/62500000 : ℝ)|=(32937987/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2703529763/5000000000 : ℝ)|^4443 ≤ (11244037414381/25000000000000 : ℝ)^3419
        have hw : |(2703529763/5000000000 : ℝ)|=(2703529763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-94801073/500000000 : ℝ)|^4443 ≤ (1440340949171/12500000000000 : ℝ)^3419
        have hw : |(-94801073/500000000 : ℝ)|=(94801073/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_box_3 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1123311793/2500000000 : ℝ)*x 0 + (4193054729/10000000000 : ℝ)*x 1 + (4193055433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1123311793/2500000000 : ℝ)^4443 ≤ (17679548154363/50000000000000 : ℝ)^3419 := by
    have hnat : (1123311793 : ℕ)^4443*50000000000000^3419 ≤ 17679548154363^3419*2500000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123311793 2500000000 17679548154363 50000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4193054729/10000000000 : ℝ)^4443 ≤ (126251751219/390625000000 : ℝ)^3419 := by
    have hnat : (4193054729 : ℕ)^4443*390625000000^3419 ≤ 126251751219^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4193054729 10000000000 126251751219 390625000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4193055433/10000000000 : ℝ)^4443 ≤ (32320455363811/100000000000000 : ℝ)^3419 := by
    have hnat : (4193055433 : ℕ)^4443*100000000000000^3419 ≤ 32320455363811^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4193055433 10000000000 32320455363811 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1123311793/2500000000 : ℝ), (4193054729/10000000000 : ℝ), (4193055433/10000000000 : ℝ)] ![(17679548154363/50000000000000 : ℝ), (126251751219/390625000000 : ℝ), (32320455363811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1123311793/2500000000 : ℝ)|^4443 ≤ (17679548154363/50000000000000 : ℝ)^3419
        have hw : |(1123311793/2500000000 : ℝ)|=(1123311793/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4193054729/10000000000 : ℝ)|^4443 ≤ (126251751219/390625000000 : ℝ)^3419
        have hw : |(4193054729/10000000000 : ℝ)|=(4193054729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4193055433/10000000000 : ℝ)|^4443 ≤ (32320455363811/100000000000000 : ℝ)^3419
        have hw : |(4193055433/10000000000 : ℝ)|=(4193055433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_box_4 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2153557263/10000000000 : ℝ)*x 0 + (655266829/1250000000 : ℝ)*x 1 + (524213509/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2153557263/10000000000 : ℝ)^4443 ≤ (6798371992981/50000000000000 : ℝ)^3419 := by
    have hnat : (2153557263 : ℕ)^4443*50000000000000^3419 ≤ 6798371992981^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2153557263 10000000000 6798371992981 50000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655266829/1250000000 : ℝ)^4443 ≤ (21600812773529/50000000000000 : ℝ)^3419 := by
    have hnat : (655266829 : ℕ)^4443*50000000000000^3419 ≤ 21600812773529^3419*1250000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655266829 1250000000 21600812773529 50000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524213509/1000000000 : ℝ)^4443 ≤ (43201630452009/100000000000000 : ℝ)^3419 := by
    have hnat : (524213509 : ℕ)^4443*100000000000000^3419 ≤ 43201630452009^3419*1000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524213509 1000000000 43201630452009 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2153557263/10000000000 : ℝ), (655266829/1250000000 : ℝ), (524213509/1000000000 : ℝ)] ![(6798371992981/50000000000000 : ℝ), (21600812773529/50000000000000 : ℝ), (43201630452009/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2153557263/10000000000 : ℝ)|^4443 ≤ (6798371992981/50000000000000 : ℝ)^3419
        have hw : |(-2153557263/10000000000 : ℝ)|=(2153557263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655266829/1250000000 : ℝ)|^4443 ≤ (21600812773529/50000000000000 : ℝ)^3419
        have hw : |(655266829/1250000000 : ℝ)|=(655266829/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(524213509/1000000000 : ℝ)|^4443 ≤ (43201630452009/100000000000000 : ℝ)^3419
        have hw : |(524213509/1000000000 : ℝ)|=(524213509/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_box_5 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1346313439/2500000000 : ℝ)*x 0 + (-98170783/500000000 : ℝ)*x 1 + (81908361/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1346313439/2500000000 : ℝ)^4443 ≤ (2237029330747/5000000000000 : ℝ)^3419 := by
    have hnat : (1346313439 : ℕ)^4443*5000000000000^3419 ≤ 2237029330747^3419*2500000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346313439 2500000000 2237029330747 5000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (98170783/500000000 : ℝ)^4443 ≤ (75361142263/625000000000 : ℝ)^3419 := by
    have hnat : (98170783 : ℕ)^4443*625000000000^3419 ≤ 75361142263^3419*500000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      98170783 500000000 75361142263 625000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (81908361/156250000 : ℝ)^4443 ≤ (21600815300971/50000000000000 : ℝ)^3419 := by
    have hnat : (81908361 : ℕ)^4443*50000000000000^3419 ≤ 21600815300971^3419*156250000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81908361 156250000 21600815300971 50000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1346313439/2500000000 : ℝ), (-98170783/500000000 : ℝ), (81908361/156250000 : ℝ)] ![(2237029330747/5000000000000 : ℝ), (75361142263/625000000000 : ℝ), (21600815300971/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1346313439/2500000000 : ℝ)|^4443 ≤ (2237029330747/5000000000000 : ℝ)^3419
        have hw : |(1346313439/2500000000 : ℝ)|=(1346313439/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-98170783/500000000 : ℝ)|^4443 ≤ (75361142263/625000000000 : ℝ)^3419
        have hw : |(-98170783/500000000 : ℝ)|=(98170783/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(81908361/156250000 : ℝ)|^4443 ≤ (21600815300971/50000000000000 : ℝ)^3419
        have hw : |(81908361/156250000 : ℝ)|=(81908361/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_box_6 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (538525427/1000000000 : ℝ)*x 0 + (655266851/1250000000 : ℝ)*x 1 + (-1963415363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (538525427/1000000000 : ℝ)^4443 ≤ (4474059216421/10000000000000 : ℝ)^3419 := by
    have hnat : (538525427 : ℕ)^4443*10000000000000^3419 ≤ 4474059216421^3419*1000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538525427 1000000000 4474059216421 10000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655266851/1250000000 : ℝ)^4443 ≤ (4320162743193/10000000000000 : ℝ)^3419 := by
    have hnat : (655266851 : ℕ)^4443*10000000000000^3419 ≤ 4320162743193^3419*1250000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655266851 1250000000 4320162743193 10000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1963415363/10000000000 : ℝ)^4443 ≤ (12057780391859/100000000000000 : ℝ)^3419 := by
    have hnat : (1963415363 : ℕ)^4443*100000000000000^3419 ≤ 12057780391859^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1963415363 10000000000 12057780391859 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(538525427/1000000000 : ℝ), (655266851/1250000000 : ℝ), (-1963415363/10000000000 : ℝ)] ![(4474059216421/10000000000000 : ℝ), (4320162743193/10000000000000 : ℝ), (12057780391859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(538525427/1000000000 : ℝ)|^4443 ≤ (4474059216421/10000000000000 : ℝ)^3419
        have hw : |(538525427/1000000000 : ℝ)|=(538525427/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655266851/1250000000 : ℝ)|^4443 ≤ (4320162743193/10000000000000 : ℝ)^3419
        have hw : |(655266851/1250000000 : ℝ)|=(655266851/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1963415363/10000000000 : ℝ)|^4443 ≤ (12057780391859/100000000000000 : ℝ)^3419
        have hw : |(-1963415363/10000000000 : ℝ)|=(1963415363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_box_7 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (163244173/400000000 : ℝ)*x 0 + (109974667/250000000 : ℝ)*x 1 + (137468343/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (163244173/400000000 : ℝ)^4443 ≤ (15601794015563/50000000000000 : ℝ)^3419 := by
    have hnat : (163244173 : ℕ)^4443*50000000000000^3419 ≤ 15601794015563^3419*400000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163244173 400000000 15601794015563 50000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (109974667/250000000 : ℝ)^4443 ≤ (4299775559053/12500000000000 : ℝ)^3419 := by
    have hnat : (109974667 : ℕ)^4443*12500000000000^3419 ≤ 4299775559053^3419*250000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109974667 250000000 4299775559053 12500000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (137468343/312500000 : ℝ)^4443 ≤ (6879641496049/20000000000000 : ℝ)^3419 := by
    have hnat : (137468343 : ℕ)^4443*20000000000000^3419 ≤ 6879641496049^3419*312500000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137468343 312500000 6879641496049 20000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(163244173/400000000 : ℝ), (109974667/250000000 : ℝ), (137468343/312500000 : ℝ)] ![(15601794015563/50000000000000 : ℝ), (4299775559053/12500000000000 : ℝ), (6879641496049/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(163244173/400000000 : ℝ)|^4443 ≤ (15601794015563/50000000000000 : ℝ)^3419
        have hw : |(163244173/400000000 : ℝ)|=(163244173/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(109974667/250000000 : ℝ)|^4443 ≤ (4299775559053/12500000000000 : ℝ)^3419
        have hw : |(109974667/250000000 : ℝ)|=(109974667/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(137468343/312500000 : ℝ)|^4443 ≤ (6879641496049/20000000000000 : ℝ)^3419
        have hw : |(137468343/312500000 : ℝ)|=(137468343/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_box_8 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2059277383/10000000000 : ℝ)*x 0 + (5127039369/10000000000 : ℝ)*x 1 + (5427624633/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2059277383/10000000000 : ℝ)^4443 ≤ (200442848673/1562500000000 : ℝ)^3419 := by
    have hnat : (2059277383 : ℕ)^4443*1562500000000^3419 ≤ 200442848673^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2059277383 10000000000 200442848673 1562500000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5127039369/10000000000 : ℝ)^4443 ≤ (41973086706759/100000000000000 : ℝ)^3419 := by
    have hnat : (5127039369 : ℕ)^4443*100000000000000^3419 ≤ 41973086706759^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5127039369 10000000000 41973086706759 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5427624633/10000000000 : ℝ)^4443 ≤ (22599285479183/50000000000000 : ℝ)^3419 := by
    have hnat : (5427624633 : ℕ)^4443*50000000000000^3419 ≤ 22599285479183^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427624633 10000000000 22599285479183 50000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2059277383/10000000000 : ℝ), (5127039369/10000000000 : ℝ), (5427624633/10000000000 : ℝ)] ![(200442848673/1562500000000 : ℝ), (41973086706759/100000000000000 : ℝ), (22599285479183/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2059277383/10000000000 : ℝ)|^4443 ≤ (200442848673/1562500000000 : ℝ)^3419
        have hw : |(-2059277383/10000000000 : ℝ)|=(2059277383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5127039369/10000000000 : ℝ)|^4443 ≤ (41973086706759/100000000000000 : ℝ)^3419
        have hw : |(5127039369/10000000000 : ℝ)|=(5127039369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5427624633/10000000000 : ℝ)|^4443 ≤ (22599285479183/50000000000000 : ℝ)^3419
        have hw : |(5427624633/10000000000 : ℝ)|=(5427624633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_box_9 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1051141617/2000000000 : ℝ)*x 0 + (-1887361309/10000000000 : ℝ)*x 1 + (1356906189/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051141617/2000000000 : ℝ)^4443 ≤ (43347046751551/100000000000000 : ℝ)^3419 := by
    have hnat : (1051141617 : ℕ)^4443*100000000000000^3419 ≤ 43347046751551^3419*2000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051141617 2000000000 43347046751551 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1887361309/10000000000 : ℝ)^4443 ≤ (2863595235207/25000000000000 : ℝ)^3419 := by
    have hnat : (1887361309 : ℕ)^4443*25000000000000^3419 ≤ 2863595235207^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1887361309 10000000000 2863595235207 25000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1356906189/2500000000 : ℝ)^4443 ≤ (2824910768089/6250000000000 : ℝ)^3419 := by
    have hnat : (1356906189 : ℕ)^4443*6250000000000^3419 ≤ 2824910768089^3419*2500000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356906189 2500000000 2824910768089 6250000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1051141617/2000000000 : ℝ), (-1887361309/10000000000 : ℝ), (1356906189/2500000000 : ℝ)] ![(43347046751551/100000000000000 : ℝ), (2863595235207/25000000000000 : ℝ), (2824910768089/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1051141617/2000000000 : ℝ)|^4443 ≤ (43347046751551/100000000000000 : ℝ)^3419
        have hw : |(1051141617/2000000000 : ℝ)|=(1051141617/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1887361309/10000000000 : ℝ)|^4443 ≤ (2863595235207/25000000000000 : ℝ)^3419
        have hw : |(-1887361309/10000000000 : ℝ)|=(1887361309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1356906189/2500000000 : ℝ)|^4443 ≤ (2824910768089/6250000000000 : ℝ)^3419
        have hw : |(1356906189/2500000000 : ℝ)|=(1356906189/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_box_10 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5255708663/10000000000 : ℝ)*x 0 + (1356906049/2500000000 : ℝ)*x 1 + (-471840323/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5255708663/10000000000 : ℝ)^4443 ≤ (43347052946437/100000000000000 : ℝ)^3419 := by
    have hnat : (5255708663 : ℕ)^4443*100000000000000^3419 ≤ 43347052946437^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255708663 10000000000 43347052946437 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1356906049/2500000000 : ℝ)^4443 ≤ (1129964155733/2500000000000 : ℝ)^3419 := by
    have hnat : (1356906049 : ℕ)^4443*2500000000000^3419 ≤ 1129964155733^3419*2500000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356906049 2500000000 1129964155733 2500000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (471840323/2500000000 : ℝ)^4443 ≤ (2290876161351/20000000000000 : ℝ)^3419 := by
    have hnat : (471840323 : ℕ)^4443*20000000000000^3419 ≤ 2290876161351^3419*2500000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      471840323 2500000000 2290876161351 20000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5255708663/10000000000 : ℝ), (1356906049/2500000000 : ℝ), (-471840323/2500000000 : ℝ)] ![(43347052946437/100000000000000 : ℝ), (1129964155733/2500000000000 : ℝ), (2290876161351/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5255708663/10000000000 : ℝ)|^4443 ≤ (43347052946437/100000000000000 : ℝ)^3419
        have hw : |(5255708663/10000000000 : ℝ)|=(5255708663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1356906049/2500000000 : ℝ)|^4443 ≤ (1129964155733/2500000000000 : ℝ)^3419
        have hw : |(1356906049/2500000000 : ℝ)|=(1356906049/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-471840323/2500000000 : ℝ)|^4443 ≤ (2290876161351/20000000000000 : ℝ)^3419
        have hw : |(-471840323/2500000000 : ℝ)|=(471840323/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_box_11 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4543480491/10000000000 : ℝ)*x 0 + (833469237/2000000000 : ℝ)*x 1 + (2083673297/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4543480491/10000000000 : ℝ)^4443 ≤ (17936827268391/50000000000000 : ℝ)^3419 := by
    have hnat : (4543480491 : ℕ)^4443*50000000000000^3419 ≤ 17936827268391^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4543480491 10000000000 17936827268391 50000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (833469237/2000000000 : ℝ)^4443 ≤ (32063170679121/100000000000000 : ℝ)^3419 := by
    have hnat : (833469237 : ℕ)^4443*100000000000000^3419 ≤ 32063170679121^3419*2000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      833469237 2000000000 32063170679121 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2083673297/5000000000 : ℝ)^4443 ≤ (16031587384203/50000000000000 : ℝ)^3419 := by
    have hnat : (2083673297 : ℕ)^4443*50000000000000^3419 ≤ 16031587384203^3419*5000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2083673297 5000000000 16031587384203 50000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4543480491/10000000000 : ℝ), (833469237/2000000000 : ℝ), (2083673297/5000000000 : ℝ)] ![(17936827268391/50000000000000 : ℝ), (32063170679121/100000000000000 : ℝ), (16031587384203/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4543480491/10000000000 : ℝ)|^4443 ≤ (17936827268391/50000000000000 : ℝ)^3419
        have hw : |(4543480491/10000000000 : ℝ)|=(4543480491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(833469237/2000000000 : ℝ)|^4443 ≤ (32063170679121/100000000000000 : ℝ)^3419
        have hw : |(833469237/2000000000 : ℝ)|=(833469237/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2083673297/5000000000 : ℝ)|^4443 ≤ (16031587384203/50000000000000 : ℝ)^3419
        have hw : |(2083673297/5000000000 : ℝ)|=(2083673297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_box_12 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-450197487/2500000000 : ℝ)*x 0 + (5518311663/10000000000 : ℝ)*x 1 + (1306788069/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (450197487/2500000000 : ℝ)^4443 ≤ (107763620747/1000000000000 : ℝ)^3419 := by
    have hnat : (450197487 : ℕ)^4443*1000000000000^3419 ≤ 107763620747^3419*2500000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450197487 2500000000 107763620747 1000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5518311663/10000000000 : ℝ)^4443 ≤ (11545599290971/25000000000000 : ℝ)^3419 := by
    have hnat : (5518311663 : ℕ)^4443*25000000000000^3419 ≤ 11545599290971^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5518311663 10000000000 11545599290971 25000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1306788069/2500000000 : ℝ)^4443 ≤ (10760310187333/25000000000000 : ℝ)^3419 := by
    have hnat : (1306788069 : ℕ)^4443*25000000000000^3419 ≤ 10760310187333^3419*2500000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1306788069 2500000000 10760310187333 25000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-450197487/2500000000 : ℝ), (5518311663/10000000000 : ℝ), (1306788069/2500000000 : ℝ)] ![(107763620747/1000000000000 : ℝ), (11545599290971/25000000000000 : ℝ), (10760310187333/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-450197487/2500000000 : ℝ)|^4443 ≤ (107763620747/1000000000000 : ℝ)^3419
        have hw : |(-450197487/2500000000 : ℝ)|=(450197487/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5518311663/10000000000 : ℝ)|^4443 ≤ (11545599290971/25000000000000 : ℝ)^3419
        have hw : |(5518311663/10000000000 : ℝ)|=(5518311663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1306788069/2500000000 : ℝ)|^4443 ≤ (10760310187333/25000000000000 : ℝ)^3419
        have hw : |(1306788069/2500000000 : ℝ)|=(1306788069/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_box_13 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2697857891/5000000000 : ℝ)*x 0 + (-984676553/5000000000 : ℝ)*x 1 + (1306788091/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2697857891/5000000000 : ℝ)^4443 ≤ (44853570051549/100000000000000 : ℝ)^3419 := by
    have hnat : (2697857891 : ℕ)^4443*100000000000000^3419 ≤ 44853570051549^3419*5000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697857891 5000000000 44853570051549 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (984676553/5000000000 : ℝ)^4443 ≤ (60525941227/500000000000 : ℝ)^3419 := by
    have hnat : (984676553 : ℕ)^4443*500000000000^3419 ≤ 60525941227^3419*5000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      984676553 5000000000 60525941227 500000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1306788091/2500000000 : ℝ)^4443 ≤ (538015521137/1250000000000 : ℝ)^3419 := by
    have hnat : (1306788091 : ℕ)^4443*1250000000000^3419 ≤ 538015521137^3419*2500000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1306788091 2500000000 538015521137 1250000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2697857891/5000000000 : ℝ), (-984676553/5000000000 : ℝ), (1306788091/2500000000 : ℝ)] ![(44853570051549/100000000000000 : ℝ), (60525941227/500000000000 : ℝ), (538015521137/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2697857891/5000000000 : ℝ)|^4443 ≤ (44853570051549/100000000000000 : ℝ)^3419
        have hw : |(2697857891/5000000000 : ℝ)|=(2697857891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-984676553/5000000000 : ℝ)|^4443 ≤ (60525941227/500000000000 : ℝ)^3419
        have hw : |(-984676553/5000000000 : ℝ)|=(984676553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1306788091/2500000000 : ℝ)|^4443 ≤ (538015521137/1250000000000 : ℝ)^3419
        have hw : |(1306788091/2500000000 : ℝ)|=(1306788091/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_box_14 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2697857799/5000000000 : ℝ)*x 0 + (1306788063/2500000000 : ℝ)*x 1 + (-61542297/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2697857799/5000000000 : ℝ)^4443 ≤ (8970713612777/20000000000000 : ℝ)^3419 := by
    have hnat : (2697857799 : ℕ)^4443*20000000000000^3419 ≤ 8970713612777^3419*5000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697857799 5000000000 8970713612777 20000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1306788063/2500000000 : ℝ)^4443 ≤ (10760310123131/25000000000000 : ℝ)^3419 := by
    have hnat : (1306788063 : ℕ)^4443*25000000000000^3419 ≤ 10760310123131^3419*2500000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1306788063 2500000000 10760310123131 25000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (61542297/312500000 : ℝ)^4443 ≤ (12105191424529/100000000000000 : ℝ)^3419 := by
    have hnat : (61542297 : ℕ)^4443*100000000000000^3419 ≤ 12105191424529^3419*312500000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      61542297 312500000 12105191424529 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2697857799/5000000000 : ℝ), (1306788063/2500000000 : ℝ), (-61542297/312500000 : ℝ)] ![(8970713612777/20000000000000 : ℝ), (10760310123131/25000000000000 : ℝ), (12105191424529/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2697857799/5000000000 : ℝ)|^4443 ≤ (8970713612777/20000000000000 : ℝ)^3419
        have hw : |(2697857799/5000000000 : ℝ)|=(2697857799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1306788063/2500000000 : ℝ)|^4443 ≤ (10760310123131/25000000000000 : ℝ)^3419
        have hw : |(1306788063/2500000000 : ℝ)|=(1306788063/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-61542297/312500000 : ℝ)|^4443 ≤ (12105191424529/100000000000000 : ℝ)^3419
        have hw : |(-61542297/312500000 : ℝ)|=(61542297/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1473_box_15 (p : ℝ) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2021401449/5000000000 : ℝ)*x 0 + (4417673479/10000000000 : ℝ)*x 1 + (883534853/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2021401449/5000000000 : ℝ)^4443 ≤ (15411783836509/50000000000000 : ℝ)^3419 := by
    have hnat : (2021401449 : ℕ)^4443*50000000000000^3419 ≤ 15411783836509^3419*5000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2021401449 5000000000 15411783836509 50000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4417673479/10000000000 : ℝ)^4443 ≤ (34588212156529/100000000000000 : ℝ)^3419 := by
    have hnat : (4417673479 : ℕ)^4443*100000000000000^3419 ≤ 34588212156529^3419*10000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4417673479 10000000000 34588212156529 100000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (883534853/2000000000 : ℝ)^4443 ≤ (17294110076831/50000000000000 : ℝ)^3419 := by
    have hnat : (883534853 : ℕ)^4443*50000000000000^3419 ≤ 17294110076831^3419*2000000000^4443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      883534853 2000000000 17294110076831 50000000000000 4443 3419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4443/1024 : ℝ)) 4443 3419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2021401449/5000000000 : ℝ), (4417673479/10000000000 : ℝ), (883534853/2000000000 : ℝ)] ![(15411783836509/50000000000000 : ℝ), (34588212156529/100000000000000 : ℝ), (17294110076831/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2021401449/5000000000 : ℝ)|^4443 ≤ (15411783836509/50000000000000 : ℝ)^3419
        have hw : |(2021401449/5000000000 : ℝ)|=(2021401449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4417673479/10000000000 : ℝ)|^4443 ≤ (34588212156529/100000000000000 : ℝ)^3419
        have hw : |(4417673479/10000000000 : ℝ)|=(4417673479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(883534853/2000000000 : ℝ)|^4443 ≤ (17294110076831/50000000000000 : ℝ)^3419
        have hw : |(883534853/2000000000 : ℝ)|=(883534853/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1473_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160270543/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15473/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2689/25000 : ℝ)*pair X i i ≤ pair X i h) :
    -(12739/20000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(11689/20000 : ℝ) ∧ (79889/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (85747/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15473/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2689/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15473/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2689/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15473/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2689/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15473/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2689/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15473/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2689/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15473/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2689/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2689/25000 : ℝ) ^ (4441/1024 : ℝ) ≤ (789337475113333/12500000000000000000 : ℝ) := by
    have hpowers : (2689/25000 : ℝ)^4441 ≤ (789337475113333/12500000000000000000 : ℝ)^1024 := by
      have hnat : (2689 : ℕ)^4441*12500000000000000000^1024 ≤ 789337475113333^1024*25000^4441 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2689 25000 789337475113333 12500000000000000000 4441 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2689/25000 : ℝ)) (X := (789337475113333/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4441 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15473/100000 : ℝ) ^ (4441/1024 : ℝ) ≤ (3056710882896029/10000000000000000000 : ℝ) := by
    have hpowers : (15473/100000 : ℝ)^4441 ≤ (3056710882896029/10000000000000000000 : ℝ)^1024 := by
      have hnat : (15473 : ℕ)^4441*10000000000000000000^1024 ≤ 3056710882896029^1024*100000^4441 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15473 100000 3056710882896029 10000000000000000000 4441 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15473/100000 : ℝ)) (X := (3056710882896029/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4441 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250789337475113333/6250000000000000000 : ℝ) ≤ (2500072798226143/2500000000000000 : ℝ) ^ (4441/1024 : ℝ) := by
    have hpowers : (6250789337475113333/6250000000000000000 : ℝ)^1024 ≤ (2500072798226143/2500000000000000 : ℝ)^4441 := by
      have hnat : (6250789337475113333 : ℕ)^1024*2500000000000000^4441 ≤ 2500072798226143^4441*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250789337475113333 6250000000000000000 2500072798226143 2500000000000000 1024 4441 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500072798226143/2500000000000000 : ℝ)) (X := (6250789337475113333/6250000000000000000 : ℝ)) (by norm_num) 4441 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50018440904314933477/50000000000000000000 : ℝ) ≤ (2500212573826351/2500000000000000 : ℝ) ^ (4441/1024 : ℝ) := by
    have hpowers : (50018440904314933477/50000000000000000000 : ℝ)^1024 ≤ (2500212573826351/2500000000000000 : ℝ)^4441 := by
      have hnat : (50018440904314933477 : ℕ)^1024*2500000000000000^4441 ≤ 2500212573826351^4441*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018440904314933477 50000000000000000000 2500212573826351 2500000000000000 1024 4441 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500212573826351/2500000000000000 : ℝ)) (X := (50018440904314933477/50000000000000000000 : ℝ)) (by norm_num) 4441 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003056710882896029/5000000000000000000 : ℝ) ≤ (2500352349426559/2500000000000000 : ℝ) ^ (4441/1024 : ℝ) := by
    have hpowers : (5003056710882896029/5000000000000000000 : ℝ)^1024 ≤ (2500352349426559/2500000000000000 : ℝ)^4441 := by
      have hnat : (5003056710882896029 : ℕ)^1024*2500000000000000^4441 ≤ 2500352349426559^4441*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003056710882896029 5000000000000000000 2500352349426559 2500000000000000 1024 4441 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500352349426559/2500000000000000 : ℝ)) (X := (5003056710882896029/5000000000000000000 : ℝ)) (by norm_num) 4441 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(789337475113333/12500000000000000000 : ℝ) ≤ ((2357967307304208407/2358500000000000000 : ℝ)+2*(8735975013/7370312500000 : ℝ)*(2689/25000 : ℝ))^(4441/1024 : ℝ) := by
    rw [show (2357967307304208407/2358500000000000000 : ℝ)+2*(8735975013/7370312500000 : ℝ)*(2689/25000 : ℝ)=(2500072798226143/2500000000000000 : ℝ) by norm_num, show 1+2*(789337475113333/12500000000000000000 : ℝ)=(6250789337475113333/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3056710882896029/10000000000000000000 : ℝ)+(789337475113333/12500000000000000000 : ℝ) ≤ ((2357967307304208407/2358500000000000000 : ℝ)+(8735975013/7370312500000 : ℝ)*((15473/100000 : ℝ)+(2689/25000 : ℝ)))^(4441/1024 : ℝ) := by
    rw [show (2357967307304208407/2358500000000000000 : ℝ)+(8735975013/7370312500000 : ℝ)*((15473/100000 : ℝ)+(2689/25000 : ℝ))=(2500212573826351/2500000000000000 : ℝ) by norm_num, show 1+(3056710882896029/10000000000000000000 : ℝ)+(789337475113333/12500000000000000000 : ℝ)=(50018440904314933477/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3056710882896029/10000000000000000000 : ℝ) ≤ ((2357967307304208407/2358500000000000000 : ℝ)+2*(8735975013/7370312500000 : ℝ)*(15473/100000 : ℝ))^(4441/1024 : ℝ) := by
    rw [show (2357967307304208407/2358500000000000000 : ℝ)+2*(8735975013/7370312500000 : ℝ)*(15473/100000 : ℝ)=(2500352349426559/2500000000000000 : ℝ) by norm_num, show 1+2*(3056710882896029/10000000000000000000 : ℝ)=(5003056710882896029/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2357967307304208407/2358500000000000000 : ℝ)*(X 1 0+X 2 0)+(8735975013/7370312500000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4441/1024 : ℝ)) (lo := (2689/25000 : ℝ)) (hi := (15473/100000 : ℝ)) (c := (2357967307304208407/2358500000000000000 : ℝ)) (alpha := (8735975013/7370312500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2357967307304208407/2358500000000000000 : ℝ)*(X 0 1+X 2 1)+(8735975013/7370312500000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4441/1024 : ℝ)) (lo := (2689/25000 : ℝ)) (hi := (15473/100000 : ℝ)) (c := (2357967307304208407/2358500000000000000 : ℝ)) (alpha := (8735975013/7370312500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2357967307304208407/2358500000000000000 : ℝ)*(X 0 2+X 1 2)+(8735975013/7370312500000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4441/1024 : ℝ)) (lo := (2689/25000 : ℝ)) (hi := (15473/100000 : ℝ)) (c := (2357967307304208407/2358500000000000000 : ℝ)) (alpha := (8735975013/7370312500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1706336357/10000000000 : ℝ)*X 0 0+(2703530441/5000000000 : ℝ)*X 0 1+(2703529959/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((42160617/80000000 : ℝ)*X 1 0+(-948010711/5000000000 : ℝ)*X 1 1+(5407060343/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((32937987/62500000 : ℝ)*X 2 0+(2703529763/5000000000 : ℝ)*X 2 1+(-94801073/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1123311793/2500000000 : ℝ)*X 0 0+(4193054729/10000000000 : ℝ)*X 0 1+(4193055433/10000000000 : ℝ)*X 0 2+(1123311793/2500000000 : ℝ)*X 1 0+(4193054729/10000000000 : ℝ)*X 1 1+(4193055433/10000000000 : ℝ)*X 1 2+(1123311793/2500000000 : ℝ)*X 2 0+(4193054729/10000000000 : ℝ)*X 2 1+(4193055433/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2153557263/10000000000 : ℝ)*X 0 0+(655266829/1250000000 : ℝ)*X 0 1+(524213509/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1346313439/2500000000 : ℝ)*X 1 0+(-98170783/500000000 : ℝ)*X 1 1+(81908361/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((538525427/1000000000 : ℝ)*X 2 0+(655266851/1250000000 : ℝ)*X 2 1+(-1963415363/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((163244173/400000000 : ℝ)*X 0 0+(109974667/250000000 : ℝ)*X 0 1+(137468343/312500000 : ℝ)*X 0 2+(163244173/400000000 : ℝ)*X 1 0+(109974667/250000000 : ℝ)*X 1 1+(137468343/312500000 : ℝ)*X 1 2+(163244173/400000000 : ℝ)*X 2 0+(109974667/250000000 : ℝ)*X 2 1+(137468343/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2059277383/10000000000 : ℝ)*X 0 0+(5127039369/10000000000 : ℝ)*X 0 1+(5427624633/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1051141617/2000000000 : ℝ)*X 1 0+(-1887361309/10000000000 : ℝ)*X 1 1+(1356906189/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5255708663/10000000000 : ℝ)*X 2 0+(1356906049/2500000000 : ℝ)*X 2 1+(-471840323/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4543480491/10000000000 : ℝ)*X 0 0+(833469237/2000000000 : ℝ)*X 0 1+(2083673297/5000000000 : ℝ)*X 0 2+(4543480491/10000000000 : ℝ)*X 1 0+(833469237/2000000000 : ℝ)*X 1 1+(2083673297/5000000000 : ℝ)*X 1 2+(4543480491/10000000000 : ℝ)*X 2 0+(833469237/2000000000 : ℝ)*X 2 1+(2083673297/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-450197487/2500000000 : ℝ)*X 0 0+(5518311663/10000000000 : ℝ)*X 0 1+(1306788069/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2697857891/5000000000 : ℝ)*X 1 0+(-984676553/5000000000 : ℝ)*X 1 1+(1306788091/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2697857799/5000000000 : ℝ)*X 2 0+(1306788063/2500000000 : ℝ)*X 2 1+(-61542297/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2021401449/5000000000 : ℝ)*X 0 0+(4417673479/10000000000 : ℝ)*X 0 1+(883534853/2000000000 : ℝ)*X 0 2+(2021401449/5000000000 : ℝ)*X 1 0+(4417673479/10000000000 : ℝ)*X 1 1+(883534853/2000000000 : ℝ)*X 1 2+(2021401449/5000000000 : ℝ)*X 2 0+(4417673479/10000000000 : ℝ)*X 2 1+(883534853/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1473_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-12739/20000 : ℝ) ≤ (-75109568308573265195755242627549/117925000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13531383/100000000000000 : ℝ)*(lower1) + (23106421/25000000000000 : ℝ)*(lower2) + (6873833/5000000000000 : ℝ)*(lower3) + (13178401/100000000000000 : ℝ)*(upper5) + (2165189199086369/100000000000000 : ℝ)*(major0) + (2165189199086369/100000000000000 : ℝ)*(major1) + (2165189199086369/100000000000000 : ℝ)*(major2) + (3000650363125521/100000000000000 : ℝ)*(sp4) + (3000564833918701/100000000000000 : ℝ)*(sp5) + (300062391033267/10000000000000 : ℝ)*(sp6) + (135087156577673/10000000000000 : ℝ)*(sp7) + (4276460341/5000000000000 : ℝ)*(sp13) + (26452792851/100000000000000 : ℝ)*(sp14) + (43677827747/50000000000000 : ℝ)*(sp15) + (42217466294757/3125000000000 : ℝ)*(f.failure) + (3000650363125521/100000000000000 : ℝ)*(f.sum) + (30892113193807/23585000000000000000000000000 : ℝ)*base66 + (1258786253630644183/235850000000000000000000000000000 : ℝ)*base67 + (1199135311725944183/235850000000000000000000000000000 : ℝ)*base69 + (476245444234644183/235850000000000000000000000000000 : ℝ)*base71 + (46526011962549/11792500000000000000000000000 : ℝ)*base73 + (426689704283955817/235850000000000000000000000000000 : ℝ)*base76 + (388537873847055817/235850000000000000000000000000000 : ℝ)*base78 + (394729839871644183/235850000000000000000000000000000 : ℝ)*base79 + (46924882291137/5896250000000000000000000000 : ℝ)*base81 + (681949/312500000000000000000 : ℝ)*base90 + (681949/312500000000000000000 : ℝ)*base92 + (681949/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (11689/20000 : ℝ) ≤ (13784877524285949675455643064569/23585000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (165006871/100000000000000 : ℝ)*(upper0) + (10058163/100000000000000 : ℝ)*(upper3) + (63991971/50000000000000 : ℝ)*(upper4) + (447759029228011/20000000000000 : ℝ)*(major0) + (447759029228011/20000000000000 : ℝ)*(major1) + (447759029228011/20000000000000 : ℝ)*(major2) + (765303985681367/25000000000000 : ℝ)*(sp0) + (23915752598151/781250000000 : ℝ)*(sp1) + (95662312183971/3125000000000 : ℝ)*(sp2) + (69844232094587/5000000000000 : ℝ)*(sp3) + (3214247201/50000000000000 : ℝ)*(sp5) + (85089959/25000000000000 : ℝ)*(sp7) + (6818332261/100000000000000 : ℝ)*(sp8) + (28771170657/100000000000000 : ℝ)*(sp10) + (174610622781447/12500000000000 : ℝ)*(f.failure) + (306122276105773/10000000000000 : ℝ)*(f.sum) + (2029982022891/943400000000000000000000000 : ℝ)*base65 + (294167598682598477/47170000000000000000000000000000 : ℝ)*base67 + (543383351768038477/47170000000000000000000000000000 : ℝ)*base69 + (46071822033791523/47170000000000000000000000000000 : ℝ)*base72 + (2479672741971/1179250000000000000000000000 : ℝ)*base73 + (92176382677711523/47170000000000000000000000000000 : ℝ)*base76 + (105588882766978477/47170000000000000000000000000000 : ℝ)*base77 + (674238054854568477/47170000000000000000000000000000 : ℝ)*base79 + (982398943193/294812500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (6484279/1250000000000000000000 : ℝ)*base90 + (6484279/1250000000000000000000 : ℝ)*base92 + (6484279/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (79889/100000 : ℝ) ≤ (47106097965156843055939743277971/58962500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (64916237/100000000000000 : ℝ)*(upper0) + (35955203/50000000000000 : ℝ)*(lower3) + (7783939/10000000000000 : ℝ)*(upper4) + (1218511719714083/50000000000000 : ℝ)*(major0) + (1218511719714083/50000000000000 : ℝ)*(major1) + (1218511719714083/50000000000000 : ℝ)*(major2) + (3186083773/4000000000000 : ℝ)*(sp1) + (4576952689/100000000000000 : ℝ)*(sp3) + (150952843/10000000000000 : ℝ)*(sp4) + (1663422576450791/50000000000000 : ℝ)*(sp8) + (831692039020527/25000000000000 : ℝ)*(sp9) + (3326847808176433/100000000000000 : ℝ)*(sp10) + (380140988216599/25000000000000 : ℝ)*(sp11) + (1145746421/100000000000000 : ℝ)*(sp12) + (760284264909543/50000000000000 : ℝ)*(f.failure) + (3326847808176433/100000000000000 : ℝ)*(f.sum) + (21142958469089/2948125000000000000000000000 : ℝ)*base65 + (1880811573282825781/117925000000000000000000000000000 : ℝ)*base67 + (1147771650450900781/117925000000000000000000000000000 : ℝ)*base69 + (1314265490244350781/117925000000000000000000000000000 : ℝ)*base71 + (16123186024003/23585000000000000000000000000 : ℝ)*base74 + (1081752893334475781/117925000000000000000000000000000 : ℝ)*base75 + (879560888932900781/117925000000000000000000000000000 : ℝ)*base77 + (683283761138850781/117925000000000000000000000000000 : ℝ)*base79 + (3282384380987/23585000000000000000000000000 : ℝ)*base81 + (2491849/5000000000000000000000 : ℝ)*base89 + (2491849/5000000000000000000000 : ℝ)*base91 + (2491849/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-85747/100000 : ℝ) ≤ (-50557299138895078454644132650519/58962500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14197719/100000000000000 : ℝ)*(lower0) + (21822111/50000000000000 : ℝ)*(lower1) + (1595703/10000000000000 : ℝ)*(lower2) + (13420189/100000000000000 : ℝ)*(lower3) + (45410561/25000000000000 : ℝ)*(lower4) + (1237584086278561/50000000000000 : ℝ)*(major0) + (1237584086278561/50000000000000 : ℝ)*(major1) + (1237584086278561/50000000000000 : ℝ)*(major2) + (9796988363/10000000000000 : ℝ)*(sp6) + (31249966597/100000000000000 : ℝ)*(sp7) + (1717274606421849/50000000000000 : ℝ)*(sp12) + (1717274606421849/50000000000000 : ℝ)*(sp13) + (858612810740017/25000000000000 : ℝ)*(sp14) + (1544337494424019/100000000000000 : ℝ)*(sp15) + (193046093048827/12500000000000 : ℝ)*(f.failure) + (1717274606421849/50000000000000 : ℝ)*(f.sum) + (119316815942551/23585000000000000000000000000 : ℝ)*base66 + (1185767010878552673/117925000000000000000000000000000 : ℝ)*base68 + (245736531150447327/117925000000000000000000000000000 : ℝ)*base69 + (421968093430952673/117925000000000000000000000000000 : ℝ)*base72 + (24709640113799/23585000000000000000000000000 : ℝ)*base73 + (159622339525247327/117925000000000000000000000000000 : ℝ)*base75 + (193370354515352673/117925000000000000000000000000000 : ℝ)*base78 + (366803405084402673/117925000000000000000000000000000 : ℝ)*base80 + (103857794629679/23585000000000000000000000000 : ℝ)*base81 + (3803061/1250000000000000000000 : ℝ)*base89 + (3803061/1250000000000000000000 : ℝ)*base91 + (3803061/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1473_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160270543/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15473/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2689/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12739/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(11689/20000 : ℝ) else (79889/100000 : ℝ) ≤ X j i ∧ X j i ≤ (85747/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1473_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1473_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160270543/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (619/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5377/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12739/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(11689/20000 : ℝ) else (79889/100000 : ℝ) ≤ X j i ∧ X j i ≤ (85747/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1473_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1473_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1473_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4441/1024 : ℝ) ≤ p) (hpb : p ≤ (4443/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160270543/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (619/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5377/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12739/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(11689/20000 : ℝ) else (79889/100000 : ℝ) ≤ X j i ∧ X j i ≤ (85747/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1473_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
