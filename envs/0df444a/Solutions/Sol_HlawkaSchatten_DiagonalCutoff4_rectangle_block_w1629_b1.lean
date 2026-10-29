-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1629_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:59:52.586167+00:00
-- url     : https://prove2.me/submissions/2e7cb78a-aaed-49f6-acb0-f58ea1c48aaa

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
theorem support_rectangle_w1629_s3_0 (p : ℝ) (hpa : (4831/1024 : ℝ) ≤ p) (hpb : p ≤ (4835/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1657535867/10000000000 : ℝ)*x 0 + (5453999309/10000000000 : ℝ)*x 1 + (2591104401/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1657535867/10000000000 : ℝ)^4835 ≤ (10226707647501/100000000000000 : ℝ)^3811 := by
    have hnat : (1657535867 : ℕ)^4835*100000000000000^3811 ≤ 10226707647501^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1657535867 10000000000 10226707647501 100000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5453999309/10000000000 : ℝ)^4835 ≤ (23170825640429/50000000000000 : ℝ)^3811 := by
    have hnat : (5453999309 : ℕ)^4835*50000000000000^3811 ≤ 23170825640429^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5453999309 10000000000 23170825640429 50000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2591104401/5000000000 : ℝ)^4835 ≤ (21715820528483/50000000000000 : ℝ)^3811 := by
    have hnat : (2591104401 : ℕ)^4835*50000000000000^3811 ≤ 21715820528483^3811*5000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591104401 5000000000 21715820528483 50000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4835/1024 : ℝ)) 4835 3811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1657535867/10000000000 : ℝ), (5453999309/10000000000 : ℝ), (2591104401/5000000000 : ℝ)] ![(10226707647501/100000000000000 : ℝ), (23170825640429/50000000000000 : ℝ), (21715820528483/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1657535867/10000000000 : ℝ)|^4835 ≤ (10226707647501/100000000000000 : ℝ)^3811
        have hw : |(-1657535867/10000000000 : ℝ)|=(1657535867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5453999309/10000000000 : ℝ)|^4835 ≤ (23170825640429/50000000000000 : ℝ)^3811
        have hw : |(5453999309/10000000000 : ℝ)|=(5453999309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2591104401/5000000000 : ℝ)|^4835 ≤ (21715820528483/50000000000000 : ℝ)^3811
        have hw : |(2591104401/5000000000 : ℝ)|=(2591104401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1629_s3_1 (p : ℝ) (hpa : (4831/1024 : ℝ) ≤ p) (hpb : p ≤ (4835/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350916319/10000000000 : ℝ)*x 0 + (-449394303/2500000000 : ℝ)*x 1 + (647776101/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350916319/10000000000 : ℝ)^4835 ≤ (45233263705749/100000000000000 : ℝ)^3811 := by
    have hnat : (5350916319 : ℕ)^4835*100000000000000^3811 ≤ 45233263705749^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350916319 10000000000 45233263705749 100000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (449394303/2500000000 : ℝ)^4835 ≤ (2267019029749/20000000000000 : ℝ)^3811 := by
    have hnat : (449394303 : ℕ)^4835*20000000000000^3811 ≤ 2267019029749^3811*2500000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449394303 2500000000 2267019029749 20000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (647776101/1250000000 : ℝ)^4835 ≤ (43431641120763/100000000000000 : ℝ)^3811 := by
    have hnat : (647776101 : ℕ)^4835*100000000000000^3811 ≤ 43431641120763^3811*1250000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647776101 1250000000 43431641120763 100000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4835/1024 : ℝ)) 4835 3811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350916319/10000000000 : ℝ), (-449394303/2500000000 : ℝ), (647776101/1250000000 : ℝ)] ![(45233263705749/100000000000000 : ℝ), (2267019029749/20000000000000 : ℝ), (43431641120763/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350916319/10000000000 : ℝ)|^4835 ≤ (45233263705749/100000000000000 : ℝ)^3811
        have hw : |(5350916319/10000000000 : ℝ)|=(5350916319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-449394303/2500000000 : ℝ)|^4835 ≤ (2267019029749/20000000000000 : ℝ)^3811
        have hw : |(-449394303/2500000000 : ℝ)|=(449394303/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(647776101/1250000000 : ℝ)|^4835 ≤ (43431641120763/100000000000000 : ℝ)^3811
        have hw : |(647776101/1250000000 : ℝ)|=(647776101/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1629_s3_2 (p : ℝ) (hpa : (4831/1024 : ℝ) ≤ p) (hpb : p ≤ (4835/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350916309/10000000000 : ℝ)*x 0 + (1295552203/2500000000 : ℝ)*x 1 + (-898788611/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350916309/10000000000 : ℝ)^4835 ≤ (45233263598501/100000000000000 : ℝ)^3811 := by
    have hnat : (5350916309 : ℕ)^4835*100000000000000^3811 ≤ 45233263598501^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350916309 10000000000 45233263598501 100000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1295552203/2500000000 : ℝ)^4835 ≤ (21715820581647/50000000000000 : ℝ)^3811 := by
    have hnat : (1295552203 : ℕ)^4835*50000000000000^3811 ≤ 21715820581647^3811*2500000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295552203 2500000000 21715820581647 50000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (898788611/5000000000 : ℝ)^4835 ≤ (5667547614373/50000000000000 : ℝ)^3811 := by
    have hnat : (898788611 : ℕ)^4835*50000000000000^3811 ≤ 5667547614373^3811*5000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898788611 5000000000 5667547614373 50000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4835/1024 : ℝ)) 4835 3811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350916309/10000000000 : ℝ), (1295552203/2500000000 : ℝ), (-898788611/5000000000 : ℝ)] ![(45233263598501/100000000000000 : ℝ), (21715820581647/50000000000000 : ℝ), (5667547614373/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350916309/10000000000 : ℝ)|^4835 ≤ (45233263598501/100000000000000 : ℝ)^3811
        have hw : |(5350916309/10000000000 : ℝ)|=(5350916309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1295552203/2500000000 : ℝ)|^4835 ≤ (21715820581647/50000000000000 : ℝ)^3811
        have hw : |(1295552203/2500000000 : ℝ)|=(1295552203/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-898788611/5000000000 : ℝ)|^4835 ≤ (5667547614373/50000000000000 : ℝ)^3811
        have hw : |(-898788611/5000000000 : ℝ)|=(898788611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1629_s3_3 (p : ℝ) (hpa : (4831/1024 : ℝ) ≤ p) (hpb : p ≤ (4835/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2098553599/5000000000 : ℝ)*x 0 + (3865240273/10000000000 : ℝ)*x 1 + (4549861561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2098553599/5000000000 : ℝ)^4835 ≤ (33238261210941/100000000000000 : ℝ)^3811 := by
    have hnat : (2098553599 : ℕ)^4835*100000000000000^3811 ≤ 33238261210941^3811*5000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2098553599 5000000000 33238261210941 100000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3865240273/10000000000 : ℝ)^4835 ≤ (5988009997077/20000000000000 : ℝ)^3811 := by
    have hnat : (3865240273 : ℕ)^4835*20000000000000^3811 ≤ 5988009997077^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3865240273 10000000000 5988009997077 20000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4549861561/10000000000 : ℝ)^4835 ≤ (36821688791413/100000000000000 : ℝ)^3811 := by
    have hnat : (4549861561 : ℕ)^4835*100000000000000^3811 ≤ 36821688791413^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4549861561 10000000000 36821688791413 100000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4835/1024 : ℝ)) 4835 3811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2098553599/5000000000 : ℝ), (3865240273/10000000000 : ℝ), (4549861561/10000000000 : ℝ)] ![(33238261210941/100000000000000 : ℝ), (5988009997077/20000000000000 : ℝ), (36821688791413/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2098553599/5000000000 : ℝ)|^4835 ≤ (33238261210941/100000000000000 : ℝ)^3811
        have hw : |(2098553599/5000000000 : ℝ)|=(2098553599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3865240273/10000000000 : ℝ)|^4835 ≤ (5988009997077/20000000000000 : ℝ)^3811
        have hw : |(3865240273/10000000000 : ℝ)|=(3865240273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4549861561/10000000000 : ℝ)|^4835 ≤ (36821688791413/100000000000000 : ℝ)^3811
        have hw : |(4549861561/10000000000 : ℝ)|=(4549861561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1629_s3_4 (p : ℝ) (hpa : (4831/1024 : ℝ) ≤ p) (hpb : p ≤ (4835/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1657603687/10000000000 : ℝ)*x 0 + (5184249991/10000000000 : ℝ)*x 1 + (5451936507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1657603687/10000000000 : ℝ)^4835 ≤ (2045447704093/20000000000000 : ℝ)^3811 := by
    have hnat : (1657603687 : ℕ)^4835*20000000000000^3811 ≤ 2045447704093^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1657603687 10000000000 2045447704093 20000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5184249991/10000000000 : ℝ)^4835 ≤ (43453345820547/100000000000000 : ℝ)^3811 := by
    have hnat : (5184249991 : ℕ)^4835*100000000000000^3811 ≤ 43453345820547^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184249991 10000000000 43453345820547 100000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5451936507/10000000000 : ℝ)^4835 ≤ (2315970782567/5000000000000 : ℝ)^3811 := by
    have hnat : (5451936507 : ℕ)^4835*5000000000000^3811 ≤ 2315970782567^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5451936507 10000000000 2315970782567 5000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4835/1024 : ℝ)) 4835 3811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1657603687/10000000000 : ℝ), (5184249991/10000000000 : ℝ), (5451936507/10000000000 : ℝ)] ![(2045447704093/20000000000000 : ℝ), (43453345820547/100000000000000 : ℝ), (2315970782567/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1657603687/10000000000 : ℝ)|^4835 ≤ (2045447704093/20000000000000 : ℝ)^3811
        have hw : |(-1657603687/10000000000 : ℝ)|=(1657603687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5184249991/10000000000 : ℝ)|^4835 ≤ (43453345820547/100000000000000 : ℝ)^3811
        have hw : |(5184249991/10000000000 : ℝ)|=(5184249991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5451936507/10000000000 : ℝ)|^4835 ≤ (2315970782567/5000000000000 : ℝ)^3811
        have hw : |(5451936507/10000000000 : ℝ)|=(5451936507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1629_s3_5 (p : ℝ) (hpa : (4831/1024 : ℝ) ≤ p) (hpb : p ≤ (4835/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1319627319/2500000000 : ℝ)*x 0 + (-38196237/250000000 : ℝ)*x 1 + (2725968269/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1319627319/2500000000 : ℝ)^4835 ≤ (22229066237933/50000000000000 : ℝ)^3811 := by
    have hnat : (1319627319 : ℕ)^4835*50000000000000^3811 ≤ 22229066237933^3811*2500000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319627319 2500000000 22229066237933 50000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (38196237/250000000 : ℝ)^4835 ≤ (4611225764659/50000000000000 : ℝ)^3811 := by
    have hnat : (38196237 : ℕ)^4835*50000000000000^3811 ≤ 4611225764659^3811*250000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38196237 250000000 4611225764659 50000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2725968269/5000000000 : ℝ)^4835 ≤ (23159707992741/50000000000000 : ℝ)^3811 := by
    have hnat : (2725968269 : ℕ)^4835*50000000000000^3811 ≤ 23159707992741^3811*5000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2725968269 5000000000 23159707992741 50000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4835/1024 : ℝ)) 4835 3811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1319627319/2500000000 : ℝ), (-38196237/250000000 : ℝ), (2725968269/5000000000 : ℝ)] ![(22229066237933/50000000000000 : ℝ), (4611225764659/50000000000000 : ℝ), (23159707992741/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1319627319/2500000000 : ℝ)|^4835 ≤ (22229066237933/50000000000000 : ℝ)^3811
        have hw : |(1319627319/2500000000 : ℝ)|=(1319627319/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-38196237/250000000 : ℝ)|^4835 ≤ (4611225764659/50000000000000 : ℝ)^3811
        have hw : |(-38196237/250000000 : ℝ)|=(38196237/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2725968269/5000000000 : ℝ)|^4835 ≤ (23159707992741/50000000000000 : ℝ)^3811
        have hw : |(2725968269/5000000000 : ℝ)|=(2725968269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1629_s3_6 (p : ℝ) (hpa : (4831/1024 : ℝ) ≤ p) (hpb : p ≤ (4835/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5278509203/10000000000 : ℝ)*x 0 + (5451936631/10000000000 : ℝ)*x 1 + (-1527849451/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5278509203/10000000000 : ℝ)^4835 ≤ (2222906584791/5000000000000 : ℝ)^3811 := by
    have hnat : (5278509203 : ℕ)^4835*5000000000000^3811 ≤ 2222906584791^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5278509203 10000000000 2222906584791 5000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5451936631/10000000000 : ℝ)^4835 ≤ (46319416987909/100000000000000 : ℝ)^3811 := by
    have hnat : (5451936631 : ℕ)^4835*100000000000000^3811 ≤ 46319416987909^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5451936631 10000000000 46319416987909 100000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1527849451/10000000000 : ℝ)^4835 ≤ (288201603351/3125000000000 : ℝ)^3811 := by
    have hnat : (1527849451 : ℕ)^4835*3125000000000^3811 ≤ 288201603351^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1527849451 10000000000 288201603351 3125000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4835/1024 : ℝ)) 4835 3811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5278509203/10000000000 : ℝ), (5451936631/10000000000 : ℝ), (-1527849451/10000000000 : ℝ)] ![(2222906584791/5000000000000 : ℝ), (46319416987909/100000000000000 : ℝ), (288201603351/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5278509203/10000000000 : ℝ)|^4835 ≤ (2222906584791/5000000000000 : ℝ)^3811
        have hw : |(5278509203/10000000000 : ℝ)|=(5278509203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5451936631/10000000000 : ℝ)|^4835 ≤ (46319416987909/100000000000000 : ℝ)^3811
        have hw : |(5451936631/10000000000 : ℝ)|=(5451936631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1527849451/10000000000 : ℝ)|^4835 ≤ (288201603351/3125000000000 : ℝ)^3811
        have hw : |(-1527849451/10000000000 : ℝ)|=(1527849451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1629_s3_7 (p : ℝ) (hpa : (4831/1024 : ℝ) ≤ p) (hpb : p ≤ (4835/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2098638853/5000000000 : ℝ)*x 0 + (4544719859/10000000000 : ℝ)*x 1 + (3870436199/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2098638853/5000000000 : ℝ)^4835 ≤ (16619987175549/50000000000000 : ℝ)^3811 := by
    have hnat : (2098638853 : ℕ)^4835*50000000000000^3811 ≤ 16619987175549^3811*5000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2098638853 5000000000 16619987175549 50000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4544719859/10000000000 : ℝ)^4835 ≤ (36768904585397/100000000000000 : ℝ)^3811 := by
    have hnat : (4544719859 : ℕ)^4835*100000000000000^3811 ≤ 36768904585397^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4544719859 10000000000 36768904585397 100000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3870436199/10000000000 : ℝ)^4835 ≤ (7497780262549/25000000000000 : ℝ)^3811 := by
    have hnat : (3870436199 : ℕ)^4835*25000000000000^3811 ≤ 7497780262549^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3870436199 10000000000 7497780262549 25000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4835/1024 : ℝ)) 4835 3811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2098638853/5000000000 : ℝ), (4544719859/10000000000 : ℝ), (3870436199/10000000000 : ℝ)] ![(16619987175549/50000000000000 : ℝ), (36768904585397/100000000000000 : ℝ), (7497780262549/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2098638853/5000000000 : ℝ)|^4835 ≤ (16619987175549/50000000000000 : ℝ)^3811
        have hw : |(2098638853/5000000000 : ℝ)|=(2098638853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4544719859/10000000000 : ℝ)|^4835 ≤ (36768904585397/100000000000000 : ℝ)^3811
        have hw : |(4544719859/10000000000 : ℝ)|=(4544719859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3870436199/10000000000 : ℝ)|^4835 ≤ (7497780262549/25000000000000 : ℝ)^3811
        have hw : |(3870436199/10000000000 : ℝ)|=(3870436199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1629_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4831/1024 : ℝ) ≤ p) (hpb : p ≤ (4835/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (175946507/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16419/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5227/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5273/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4079/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16419/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5227/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16419/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5227/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16419/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5227/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16419/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5227/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16419/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5227/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16419/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5227/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5227/50000 : ℝ) ^ (4831/1024 : ℝ) ≤ (1180774629390857/50000000000000000000 : ℝ) := by
    have hpowers : (5227/50000 : ℝ)^4831 ≤ (1180774629390857/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5227 : ℕ)^4831*50000000000000000000^1024 ≤ 1180774629390857^1024*50000^4831 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5227 50000 1180774629390857 50000000000000000000 4831 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5227/50000 : ℝ)) (X := (1180774629390857/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4831 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16419/100000 : ℝ) ^ (4831/1024 : ℝ) ≤ (3973868692939199/20000000000000000000 : ℝ) := by
    have hpowers : (16419/100000 : ℝ)^4831 ≤ (3973868692939199/20000000000000000000 : ℝ)^1024 := by
      have hnat : (16419 : ℕ)^4831*20000000000000000000^1024 ≤ 3973868692939199^1024*100000^4831 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16419 100000 3973868692939199 20000000000000000000 4831 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16419/100000 : ℝ)) (X := (3973868692939199/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4831 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25001180774629390857/25000000000000000000 : ℝ) ≤ (5000050055504853/5000000000000000 : ℝ) ^ (4831/1024 : ℝ) := by
    have hpowers : (25001180774629390857/25000000000000000000 : ℝ)^1024 ≤ (5000050055504853/5000000000000000 : ℝ)^4831 := by
      have hnat : (25001180774629390857 : ℕ)^1024*5000000000000000^4831 ≤ 5000050055504853^4831*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001180774629390857 25000000000000000000 5000050055504853 5000000000000000 1024 4831 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000050055504853/5000000000000000 : ℝ)) (X := (25001180774629390857/25000000000000000000 : ℝ)) (by norm_num) 4831 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100022230892723477709/100000000000000000000 : ℝ) ≤ (125005889681327/125000000000000 : ℝ) ^ (4831/1024 : ℝ) := by
    have hpowers : (100022230892723477709/100000000000000000000 : ℝ)^1024 ≤ (125005889681327/125000000000000 : ℝ)^4831 := by
      have hnat : (100022230892723477709 : ℕ)^1024*125000000000000^4831 ≤ 125005889681327^4831*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100022230892723477709 100000000000000000000 125005889681327 125000000000000 1024 4831 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125005889681327/125000000000000 : ℝ)) (X := (100022230892723477709/100000000000000000000 : ℝ)) (by norm_num) 4831 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10003973868692939199/10000000000000000000 : ℝ) ≤ (5000421119001307/5000000000000000 : ℝ) ^ (4831/1024 : ℝ) := by
    have hpowers : (10003973868692939199/10000000000000000000 : ℝ)^1024 ≤ (5000421119001307/5000000000000000 : ℝ)^4831 := by
      have hnat : (10003973868692939199 : ℕ)^1024*5000000000000000^4831 ≤ 5000421119001307^4831*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10003973868692939199 10000000000000000000 5000421119001307 5000000000000000 1024 4831 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000421119001307/5000000000000000 : ℝ)) (X := (10003973868692939199/10000000000000000000 : ℝ)) (by norm_num) 4831 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1180774629390857/50000000000000000000 : ℝ) ≤ ((29821419483294518029/29825000000000000000 : ℝ)+2*(185531748227/298250000000000 : ℝ)*(5227/50000 : ℝ))^(4831/1024 : ℝ) := by
    rw [show (29821419483294518029/29825000000000000000 : ℝ)+2*(185531748227/298250000000000 : ℝ)*(5227/50000 : ℝ)=(5000050055504853/5000000000000000 : ℝ) by norm_num, show 1+2*(1180774629390857/50000000000000000000 : ℝ)=(25001180774629390857/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3973868692939199/20000000000000000000 : ℝ)+(1180774629390857/50000000000000000000 : ℝ) ≤ ((29821419483294518029/29825000000000000000 : ℝ)+(185531748227/298250000000000 : ℝ)*((16419/100000 : ℝ)+(5227/50000 : ℝ)))^(4831/1024 : ℝ) := by
    rw [show (29821419483294518029/29825000000000000000 : ℝ)+(185531748227/298250000000000 : ℝ)*((16419/100000 : ℝ)+(5227/50000 : ℝ))=(125005889681327/125000000000000 : ℝ) by norm_num, show 1+(3973868692939199/20000000000000000000 : ℝ)+(1180774629390857/50000000000000000000 : ℝ)=(100022230892723477709/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3973868692939199/20000000000000000000 : ℝ) ≤ ((29821419483294518029/29825000000000000000 : ℝ)+2*(185531748227/298250000000000 : ℝ)*(16419/100000 : ℝ))^(4831/1024 : ℝ) := by
    rw [show (29821419483294518029/29825000000000000000 : ℝ)+2*(185531748227/298250000000000 : ℝ)*(16419/100000 : ℝ)=(5000421119001307/5000000000000000 : ℝ) by norm_num, show 1+2*(3973868692939199/20000000000000000000 : ℝ)=(10003973868692939199/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (29821419483294518029/29825000000000000000 : ℝ)*(X 1 0+X 2 0)+(185531748227/298250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4831/1024 : ℝ)) (lo := (5227/50000 : ℝ)) (hi := (16419/100000 : ℝ)) (c := (29821419483294518029/29825000000000000000 : ℝ)) (alpha := (185531748227/298250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (29821419483294518029/29825000000000000000 : ℝ)*(X 0 1+X 2 1)+(185531748227/298250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4831/1024 : ℝ)) (lo := (5227/50000 : ℝ)) (hi := (16419/100000 : ℝ)) (c := (29821419483294518029/29825000000000000000 : ℝ)) (alpha := (185531748227/298250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (29821419483294518029/29825000000000000000 : ℝ)*(X 0 2+X 1 2)+(185531748227/298250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4831/1024 : ℝ)) (lo := (5227/50000 : ℝ)) (hi := (16419/100000 : ℝ)) (c := (29821419483294518029/29825000000000000000 : ℝ)) (alpha := (185531748227/298250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1657535867/10000000000 : ℝ)*X 0 0+(5453999309/10000000000 : ℝ)*X 0 1+(2591104401/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1629_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350916319/10000000000 : ℝ)*X 1 0+(-449394303/2500000000 : ℝ)*X 1 1+(647776101/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1629_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350916309/10000000000 : ℝ)*X 2 0+(1295552203/2500000000 : ℝ)*X 2 1+(-898788611/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1629_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2098553599/5000000000 : ℝ)*X 0 0+(3865240273/10000000000 : ℝ)*X 0 1+(4549861561/10000000000 : ℝ)*X 0 2+(2098553599/5000000000 : ℝ)*X 1 0+(3865240273/10000000000 : ℝ)*X 1 1+(4549861561/10000000000 : ℝ)*X 1 2+(2098553599/5000000000 : ℝ)*X 2 0+(3865240273/10000000000 : ℝ)*X 2 1+(4549861561/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1629_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1657603687/10000000000 : ℝ)*X 0 0+(5184249991/10000000000 : ℝ)*X 0 1+(5451936507/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1629_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1319627319/2500000000 : ℝ)*X 1 0+(-38196237/250000000 : ℝ)*X 1 1+(2725968269/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1629_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5278509203/10000000000 : ℝ)*X 2 0+(5451936631/10000000000 : ℝ)*X 2 1+(-1527849451/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1629_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2098638853/5000000000 : ℝ)*X 0 0+(4544719859/10000000000 : ℝ)*X 0 1+(3870436199/10000000000 : ℝ)*X 0 2+(2098638853/5000000000 : ℝ)*X 1 0+(4544719859/10000000000 : ℝ)*X 1 1+(3870436199/10000000000 : ℝ)*X 1 2+(2098638853/5000000000 : ℝ)*X 2 0+(4544719859/10000000000 : ℝ)*X 2 1+(3870436199/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1629_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18588292604111489016264667011/1491250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2015365803/100000000000000 : ℝ)*(base19) + (1877022979/100000000000000 : ℝ)*(base23) + (14069347/20000000000000 : ℝ)*(lower2) + (78100219/25000000000000 : ℝ)*(upper3) + (209061077/100000000000000 : ℝ)*(upper5) + (2570018188745373/100000000000000 : ℝ)*(major0) + (2570018188745373/100000000000000 : ℝ)*(major1) + (1285009094372687/50000000000000 : ℝ)*(major2) + (1839664950629303/50000000000000 : ℝ)*(sp0) + (1839676191741873/50000000000000 : ℝ)*(sp1) + (367935252182657/10000000000000 : ℝ)*(sp2) + (730335468087829/50000000000000 : ℝ)*(sp3) + (765549717/3125000000000 : ℝ)*(sp4) + (10626968629/100000000000000 : ℝ)*(sp7) + (45646298848259/3125000000000 : ℝ)*(f.failure) + (73587087976991/2000000000000 : ℝ)*(f.sum) + (74037580215469/29825000000000000000000000000 : ℝ)*base65 + (7386546270268870183/2982500000000000000000000000000000 : ℝ)*base68 + (2490814733328973923/1491250000000000000000000000000000 : ℝ)*base69 + (9532700136238629817/2982500000000000000000000000000000 : ℝ)*base71 + (6073380988791/1864062500000000000000000000 : ℝ)*base74 + (14110049942623973923/1491250000000000000000000000000000 : ℝ)*base75 + (11482957378645929817/2982500000000000000000000000000000 : ℝ)*base77 + (31123580935343429817/2982500000000000000000000000000000 : ℝ)*base79 + (92066077078083/29825000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (3456313/312500000000000000000 : ℝ)*base89 + (3456313/312500000000000000000 : ℝ)*base91 + (331313/312500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3906248469722136670988970759/372812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1711320329/100000000000000 : ℝ)*(base19) + (845484209/50000000000000 : ℝ)*(base23) + (246840641/100000000000000 : ℝ)*(upper3) + (345411/3125000000000 : ℝ)*(lower4) + (236391541/100000000000000 : ℝ)*(upper5) + (1304692027481957/50000000000000 : ℝ)*(major0) + (1304692027481957/50000000000000 : ℝ)*(major1) + (1304692027481957/50000000000000 : ℝ)*(major2) + (2013361453/10000000000000 : ℝ)*(sp1) + (20889705193/100000000000000 : ℝ)*(sp2) + (233482026740883/6250000000000 : ℝ)*(sp4) + (933922645729817/25000000000000 : ℝ)*(sp5) + (933922461795129/25000000000000 : ℝ)*(sp6) + (74152766640713/5000000000000 : ℝ)*(sp7) + (74152766640713/5000000000000 : ℝ)*(f.failure) + (233482026740883/6250000000000 : ℝ)*(f.sum) + (14523089043711/7456250000000000000000000000 : ℝ)*base66 + (10010094858022397247/1491250000000000000000000000000000 : ℝ)*base68 + (6935653998602397247/1491250000000000000000000000000000 : ℝ)*base70 + (12262971581934897247/1491250000000000000000000000000000 : ℝ)*base72 + (2809609683807/3728125000000000000000000000 : ℝ)*base73 + (13878701215267602753/1491250000000000000000000000000000 : ℝ)*base75 + (935938159398647247/1491250000000000000000000000000000 : ℝ)*base78 + (5929034921212397247/1491250000000000000000000000000000 : ℝ)*base80 + (33237627811447/14912500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (6339491/500000000000000000000 : ℝ)*base89 + (6339491/500000000000000000000 : ℝ)*base91 + (6339491/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1629_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4831/1024 : ℝ) ≤ p) (hpb : p ≤ (4835/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (175946507/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16419/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5227/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5273/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4079/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1629_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1629_s4_0 (p : ℝ) (hpa : (4831/1024 : ℝ) ≤ p) (hpb : p ≤ (4835/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-414402717/2500000000 : ℝ)*x 0 + (2726812171/5000000000 : ℝ)*x 1 + (1036506747/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (414402717/2500000000 : ℝ)^4835 ≤ (5113647365673/50000000000000 : ℝ)^3811 := by
    have hnat : (414402717 : ℕ)^4835*50000000000000^3811 ≤ 5113647365673^3811*2500000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      414402717 2500000000 5113647365673 50000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2726812171/5000000000 : ℝ)^4835 ≤ (9267521843731/20000000000000 : ℝ)^3811 := by
    have hnat : (2726812171 : ℕ)^4835*20000000000000^3811 ≤ 9267521843731^3811*5000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2726812171 5000000000 9267521843731 20000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1036506747/2000000000 : ℝ)^4835 ≤ (43435096043349/100000000000000 : ℝ)^3811 := by
    have hnat : (1036506747 : ℕ)^4835*100000000000000^3811 ≤ 43435096043349^3811*2000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036506747 2000000000 43435096043349 100000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4835/1024 : ℝ)) 4835 3811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-414402717/2500000000 : ℝ), (2726812171/5000000000 : ℝ), (1036506747/2000000000 : ℝ)] ![(5113647365673/50000000000000 : ℝ), (9267521843731/20000000000000 : ℝ), (43435096043349/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-414402717/2500000000 : ℝ)|^4835 ≤ (5113647365673/50000000000000 : ℝ)^3811
        have hw : |(-414402717/2500000000 : ℝ)|=(414402717/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2726812171/5000000000 : ℝ)|^4835 ≤ (9267521843731/20000000000000 : ℝ)^3811
        have hw : |(2726812171/5000000000 : ℝ)|=(2726812171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1036506747/2000000000 : ℝ)|^4835 ≤ (43435096043349/100000000000000 : ℝ)^3811
        have hw : |(1036506747/2000000000 : ℝ)|=(1036506747/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1629_s4_1 (p : ℝ) (hpa : (4831/1024 : ℝ) ≤ p) (hpb : p ≤ (4835/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350815171/10000000000 : ℝ)*x 0 + (-1797280979/10000000000 : ℝ)*x 1 + (5182533707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350815171/10000000000 : ℝ)^4835 ≤ (45232178921197/100000000000000 : ℝ)^3811 := by
    have hnat : (5350815171 : ℕ)^4835*100000000000000^3811 ≤ 45232178921197^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350815171 10000000000 45232178921197 100000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1797280979/10000000000 : ℝ)^4835 ≤ (2266545061813/20000000000000 : ℝ)^3811 := by
    have hnat : (1797280979 : ℕ)^4835*20000000000000^3811 ≤ 2266545061813^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1797280979 10000000000 2266545061813 20000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5182533707/10000000000 : ℝ)^4835 ≤ (69496153193/160000000000 : ℝ)^3811 := by
    have hnat : (5182533707 : ℕ)^4835*160000000000^3811 ≤ 69496153193^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182533707 10000000000 69496153193 160000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4835/1024 : ℝ)) 4835 3811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350815171/10000000000 : ℝ), (-1797280979/10000000000 : ℝ), (5182533707/10000000000 : ℝ)] ![(45232178921197/100000000000000 : ℝ), (2266545061813/20000000000000 : ℝ), (69496153193/160000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350815171/10000000000 : ℝ)|^4835 ≤ (45232178921197/100000000000000 : ℝ)^3811
        have hw : |(5350815171/10000000000 : ℝ)|=(5350815171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1797280979/10000000000 : ℝ)|^4835 ≤ (2266545061813/20000000000000 : ℝ)^3811
        have hw : |(-1797280979/10000000000 : ℝ)|=(1797280979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5182533707/10000000000 : ℝ)|^4835 ≤ (69496153193/160000000000 : ℝ)^3811
        have hw : |(5182533707/10000000000 : ℝ)|=(5182533707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1629_s4_2 (p : ℝ) (hpa : (4831/1024 : ℝ) ≤ p) (hpb : p ≤ (4835/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070163031/2000000000 : ℝ)*x 0 + (5182533729/10000000000 : ℝ)*x 1 + (-449320243/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070163031/2000000000 : ℝ)^4835 ≤ (22616089374801/50000000000000 : ℝ)^3811 := by
    have hnat : (1070163031 : ℕ)^4835*50000000000000^3811 ≤ 22616089374801^3811*2000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070163031 2000000000 22616089374801 50000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5182533729/10000000000 : ℝ)^4835 ≤ (43435095979551/100000000000000 : ℝ)^3811 := by
    have hnat : (5182533729 : ℕ)^4835*100000000000000^3811 ≤ 43435095979551^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182533729 10000000000 43435095979551 100000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (449320243/2500000000 : ℝ)^4835 ≤ (11332725253067/100000000000000 : ℝ)^3811 := by
    have hnat : (449320243 : ℕ)^4835*100000000000000^3811 ≤ 11332725253067^3811*2500000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449320243 2500000000 11332725253067 100000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4835/1024 : ℝ)) 4835 3811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070163031/2000000000 : ℝ), (5182533729/10000000000 : ℝ), (-449320243/2500000000 : ℝ)] ![(22616089374801/50000000000000 : ℝ), (43435095979551/100000000000000 : ℝ), (11332725253067/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070163031/2000000000 : ℝ)|^4835 ≤ (22616089374801/50000000000000 : ℝ)^3811
        have hw : |(1070163031/2000000000 : ℝ)|=(1070163031/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5182533729/10000000000 : ℝ)|^4835 ≤ (43435095979551/100000000000000 : ℝ)^3811
        have hw : |(5182533729/10000000000 : ℝ)|=(5182533729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-449320243/2500000000 : ℝ)|^4835 ≤ (11332725253067/100000000000000 : ℝ)^3811
        have hw : |(-449320243/2500000000 : ℝ)|=(449320243/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1629_s4_3 (p : ℝ) (hpa : (4831/1024 : ℝ) ≤ p) (hpb : p ≤ (4835/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4197155839/10000000000 : ℝ)*x 0 + (773223337/2000000000 : ℝ)*x 1 + (181959003/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4197155839/10000000000 : ℝ)^4835 ≤ (8309687479591/25000000000000 : ℝ)^3811 := by
    have hnat : (4197155839 : ℕ)^4835*25000000000000^3811 ≤ 8309687479591^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4197155839 10000000000 8309687479591 25000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (773223337/2000000000 : ℝ)^4835 ≤ (7487165749577/25000000000000 : ℝ)^3811 := by
    have hnat : (773223337 : ℕ)^4835*25000000000000^3811 ≤ 7487165749577^3811*2000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      773223337 2000000000 7487165749577 25000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (181959003/400000000 : ℝ)^4835 ≤ (36812587069491/100000000000000 : ℝ)^3811 := by
    have hnat : (181959003 : ℕ)^4835*100000000000000^3811 ≤ 36812587069491^3811*400000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      181959003 400000000 36812587069491 100000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4835/1024 : ℝ)) 4835 3811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4197155839/10000000000 : ℝ), (773223337/2000000000 : ℝ), (181959003/400000000 : ℝ)] ![(8309687479591/25000000000000 : ℝ), (7487165749577/25000000000000 : ℝ), (36812587069491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4197155839/10000000000 : ℝ)|^4835 ≤ (8309687479591/25000000000000 : ℝ)^3811
        have hw : |(4197155839/10000000000 : ℝ)|=(4197155839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(773223337/2000000000 : ℝ)|^4835 ≤ (7487165749577/25000000000000 : ℝ)^3811
        have hw : |(773223337/2000000000 : ℝ)|=(773223337/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(181959003/400000000 : ℝ)|^4835 ≤ (36812587069491/100000000000000 : ℝ)^3811
        have hw : |(181959003/400000000 : ℝ)|=(181959003/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1629_s4_4 (p : ℝ) (hpa : (4831/1024 : ℝ) ≤ p) (hpb : p ≤ (4835/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1657678123/10000000000 : ℝ)*x 0 + (1036912899/2000000000 : ℝ)*x 1 + (2725786083/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1657678123/10000000000 : ℝ)^4835 ≤ (204556423761/2000000000000 : ℝ)^3811 := by
    have hnat : (1657678123 : ℕ)^4835*2000000000000^3811 ≤ 204556423761^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1657678123 10000000000 204556423761 2000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036912899/2000000000 : ℝ)^4835 ≤ (4345669026917/10000000000000 : ℝ)^3811 := by
    have hnat : (1036912899 : ℕ)^4835*10000000000000^3811 ≤ 4345669026917^3811*2000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036912899 2000000000 4345669026917 10000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2725786083/5000000000 : ℝ)^4835 ≤ (11578872133317/25000000000000 : ℝ)^3811 := by
    have hnat : (2725786083 : ℕ)^4835*25000000000000^3811 ≤ 11578872133317^3811*5000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2725786083 5000000000 11578872133317 25000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4835/1024 : ℝ)) 4835 3811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1657678123/10000000000 : ℝ), (1036912899/2000000000 : ℝ), (2725786083/5000000000 : ℝ)] ![(204556423761/2000000000000 : ℝ), (4345669026917/10000000000000 : ℝ), (11578872133317/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1657678123/10000000000 : ℝ)|^4835 ≤ (204556423761/2000000000000 : ℝ)^3811
        have hw : |(-1657678123/10000000000 : ℝ)|=(1657678123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1036912899/2000000000 : ℝ)|^4835 ≤ (4345669026917/10000000000000 : ℝ)^3811
        have hw : |(1036912899/2000000000 : ℝ)|=(1036912899/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2725786083/5000000000 : ℝ)|^4835 ≤ (11578872133317/25000000000000 : ℝ)^3811
        have hw : |(2725786083/5000000000 : ℝ)|=(2725786083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1629_s4_5 (p : ℝ) (hpa : (4831/1024 : ℝ) ≤ p) (hpb : p ≤ (4835/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2639297541/5000000000 : ℝ)*x 0 + (-1528242549/10000000000 : ℝ)*x 1 + (170361631/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2639297541/5000000000 : ℝ)^4835 ≤ (44459049363387/100000000000000 : ℝ)^3811 := by
    have hnat : (2639297541 : ℕ)^4835*100000000000000^3811 ≤ 44459049363387^3811*5000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639297541 5000000000 44459049363387 100000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1528242549/10000000000 : ℝ)^4835 ≤ (1845092362211/20000000000000 : ℝ)^3811 := by
    have hnat : (1528242549 : ℕ)^4835*20000000000000^3811 ≤ 1845092362211^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1528242549 10000000000 1845092362211 20000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (170361631/312500000 : ℝ)^4835 ≤ (46315488813511/100000000000000 : ℝ)^3811 := by
    have hnat : (170361631 : ℕ)^4835*100000000000000^3811 ≤ 46315488813511^3811*312500000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170361631 312500000 46315488813511 100000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4835/1024 : ℝ)) 4835 3811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2639297541/5000000000 : ℝ), (-1528242549/10000000000 : ℝ), (170361631/312500000 : ℝ)] ![(44459049363387/100000000000000 : ℝ), (1845092362211/20000000000000 : ℝ), (46315488813511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2639297541/5000000000 : ℝ)|^4835 ≤ (44459049363387/100000000000000 : ℝ)^3811
        have hw : |(2639297541/5000000000 : ℝ)|=(2639297541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1528242549/10000000000 : ℝ)|^4835 ≤ (1845092362211/20000000000000 : ℝ)^3811
        have hw : |(-1528242549/10000000000 : ℝ)|=(1528242549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(170361631/312500000 : ℝ)|^4835 ≤ (46315488813511/100000000000000 : ℝ)^3811
        have hw : |(170361631/312500000 : ℝ)|=(170361631/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1629_s4_6 (p : ℝ) (hpa : (4831/1024 : ℝ) ≤ p) (hpb : p ≤ (4835/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2639297523/5000000000 : ℝ)*x 0 + (5451572271/10000000000 : ℝ)*x 1 + (-191030311/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2639297523/5000000000 : ℝ)^4835 ≤ (8891809795741/20000000000000 : ℝ)^3811 := by
    have hnat : (2639297523 : ℕ)^4835*20000000000000^3811 ≤ 8891809795741^3811*5000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639297523 5000000000 8891809795741 20000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5451572271/10000000000 : ℝ)^4835 ≤ (2315774483251/5000000000000 : ℝ)^3811 := by
    have hnat : (5451572271 : ℕ)^4835*5000000000000^3811 ≤ 2315774483251^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5451572271 10000000000 2315774483251 5000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (191030311/1250000000 : ℝ)^4835 ≤ (2306365335969/25000000000000 : ℝ)^3811 := by
    have hnat : (191030311 : ℕ)^4835*25000000000000^3811 ≤ 2306365335969^3811*1250000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      191030311 1250000000 2306365335969 25000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4835/1024 : ℝ)) 4835 3811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2639297523/5000000000 : ℝ), (5451572271/10000000000 : ℝ), (-191030311/1250000000 : ℝ)] ![(8891809795741/20000000000000 : ℝ), (2315774483251/5000000000000 : ℝ), (2306365335969/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2639297523/5000000000 : ℝ)|^4835 ≤ (8891809795741/20000000000000 : ℝ)^3811
        have hw : |(2639297523/5000000000 : ℝ)|=(2639297523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5451572271/10000000000 : ℝ)|^4835 ≤ (2315774483251/5000000000000 : ℝ)^3811
        have hw : |(5451572271/10000000000 : ℝ)|=(5451572271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-191030311/1250000000 : ℝ)|^4835 ≤ (2306365335969/25000000000000 : ℝ)^3811
        have hw : |(-191030311/1250000000 : ℝ)|=(191030311/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1629_s4_7 (p : ℝ) (hpa : (4831/1024 : ℝ) ≤ p) (hpb : p ≤ (4835/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (839465003/2000000000 : ℝ)*x 0 + (4543859821/10000000000 : ℝ)*x 1 + (3871285763/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (839465003/2000000000 : ℝ)^4835 ≤ (4155056210097/12500000000000 : ℝ)^3811 := by
    have hnat : (839465003 : ℕ)^4835*12500000000000^3811 ≤ 4155056210097^3811*2000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      839465003 2000000000 4155056210097 12500000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4543859821/10000000000 : ℝ)^4835 ≤ (7352015417179/20000000000000 : ℝ)^3811 := by
    have hnat : (4543859821 : ℕ)^4835*20000000000000^3811 ≤ 7352015417179^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4543859821 10000000000 7352015417179 20000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3871285763/10000000000 : ℝ)^4835 ≤ (29999473218243/100000000000000 : ℝ)^3811 := by
    have hnat : (3871285763 : ℕ)^4835*100000000000000^3811 ≤ 29999473218243^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3871285763 10000000000 29999473218243 100000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4835/1024 : ℝ)) 4835 3811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(839465003/2000000000 : ℝ), (4543859821/10000000000 : ℝ), (3871285763/10000000000 : ℝ)] ![(4155056210097/12500000000000 : ℝ), (7352015417179/20000000000000 : ℝ), (29999473218243/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(839465003/2000000000 : ℝ)|^4835 ≤ (4155056210097/12500000000000 : ℝ)^3811
        have hw : |(839465003/2000000000 : ℝ)|=(839465003/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4543859821/10000000000 : ℝ)|^4835 ≤ (7352015417179/20000000000000 : ℝ)^3811
        have hw : |(4543859821/10000000000 : ℝ)|=(4543859821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3871285763/10000000000 : ℝ)|^4835 ≤ (29999473218243/100000000000000 : ℝ)^3811
        have hw : |(3871285763/10000000000 : ℝ)|=(3871285763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1629_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4831/1024 : ℝ) ≤ p) (hpb : p ≤ (4835/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (175946507/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4079/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5273/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10553/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4077/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4079/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5273/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4079/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5273/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4079/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5273/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4079/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5273/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4079/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5273/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4079/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5273/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5273/50000 : ℝ) ^ (4831/1024 : ℝ) ≤ (1230607112107069/50000000000000000000 : ℝ) := by
    have hpowers : (5273/50000 : ℝ)^4831 ≤ (1230607112107069/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5273 : ℕ)^4831*50000000000000000000^1024 ≤ 1230607112107069^1024*50000^4831 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5273 50000 1230607112107069 50000000000000000000 4831 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5273/50000 : ℝ)) (X := (1230607112107069/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4831 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4079/25000 : ℝ) ^ (4831/1024 : ℝ) ≤ (2411014520695479/12500000000000000000 : ℝ) := by
    have hpowers : (4079/25000 : ℝ)^4831 ≤ (2411014520695479/12500000000000000000 : ℝ)^1024 := by
      have hnat : (4079 : ℕ)^4831*12500000000000000000^1024 ≤ 2411014520695479^1024*25000^4831 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4079 25000 2411014520695479 12500000000000000000 4831 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4079/25000 : ℝ)) (X := (2411014520695479/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4831 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25001230607112107069/25000000000000000000 : ℝ) ≤ (1000010433593399/1000000000000000 : ℝ) ^ (4831/1024 : ℝ) := by
    have hpowers : (25001230607112107069/25000000000000000000 : ℝ)^1024 ≤ (1000010433593399/1000000000000000 : ℝ)^4831 := by
      have hnat : (25001230607112107069 : ℕ)^1024*1000000000000000^4831 ≤ 1000010433593399^4831*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001230607112107069 25000000000000000000 1000010433593399 1000000000000000 1024 4831 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000010433593399/1000000000000000 : ℝ)) (X := (25001230607112107069/25000000000000000000 : ℝ)) (by norm_num) 4831 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10002174933038977797/10000000000000000000 : ℝ) ≤ (1250057621108463/1250000000000000 : ℝ) ^ (4831/1024 : ℝ) := by
    have hpowers : (10002174933038977797/10000000000000000000 : ℝ)^1024 ≤ (1250057621108463/1250000000000000 : ℝ)^4831 := by
      have hnat : (10002174933038977797 : ℕ)^1024*1250000000000000^4831 ≤ 1250057621108463^4831*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002174933038977797 10000000000000000000 1250057621108463 1250000000000000 1024 4831 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250057621108463/1250000000000000 : ℝ)) (X := (10002174933038977797/10000000000000000000 : ℝ)) (by norm_num) 4831 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6252411014520695479/6250000000000000000 : ℝ) ≤ (5000408800900709/5000000000000000 : ℝ) ^ (4831/1024 : ℝ) := by
    have hpowers : (6252411014520695479/6250000000000000000 : ℝ)^1024 ≤ (5000408800900709/5000000000000000 : ℝ)^4831 := by
      have hnat : (6252411014520695479 : ℕ)^1024*5000000000000000^4831 ≤ 5000408800900709^4831*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252411014520695479 6250000000000000000 5000408800900709 5000000000000000 1024 4831 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000408800900709/5000000000000000 : ℝ)) (X := (6252411014520695479/6250000000000000000 : ℝ)) (by norm_num) 4831 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1230607112107069/50000000000000000000 : ℝ) ≤ ((14423269979125306653/14425000000000000000 : ℝ)+2*(178316466857/288500000000000 : ℝ)*(5273/50000 : ℝ))^(4831/1024 : ℝ) := by
    rw [show (14423269979125306653/14425000000000000000 : ℝ)+2*(178316466857/288500000000000 : ℝ)*(5273/50000 : ℝ)=(1000010433593399/1000000000000000 : ℝ) by norm_num, show 1+2*(1230607112107069/50000000000000000000 : ℝ)=(25001230607112107069/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2411014520695479/12500000000000000000 : ℝ)+(1230607112107069/50000000000000000000 : ℝ) ≤ ((14423269979125306653/14425000000000000000 : ℝ)+(178316466857/288500000000000 : ℝ)*((4079/25000 : ℝ)+(5273/50000 : ℝ)))^(4831/1024 : ℝ) := by
    rw [show (14423269979125306653/14425000000000000000 : ℝ)+(178316466857/288500000000000 : ℝ)*((4079/25000 : ℝ)+(5273/50000 : ℝ))=(1250057621108463/1250000000000000 : ℝ) by norm_num, show 1+(2411014520695479/12500000000000000000 : ℝ)+(1230607112107069/50000000000000000000 : ℝ)=(10002174933038977797/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2411014520695479/12500000000000000000 : ℝ) ≤ ((14423269979125306653/14425000000000000000 : ℝ)+2*(178316466857/288500000000000 : ℝ)*(4079/25000 : ℝ))^(4831/1024 : ℝ) := by
    rw [show (14423269979125306653/14425000000000000000 : ℝ)+2*(178316466857/288500000000000 : ℝ)*(4079/25000 : ℝ)=(5000408800900709/5000000000000000 : ℝ) by norm_num, show 1+2*(2411014520695479/12500000000000000000 : ℝ)=(6252411014520695479/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14423269979125306653/14425000000000000000 : ℝ)*(X 1 0+X 2 0)+(178316466857/288500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4831/1024 : ℝ)) (lo := (5273/50000 : ℝ)) (hi := (4079/25000 : ℝ)) (c := (14423269979125306653/14425000000000000000 : ℝ)) (alpha := (178316466857/288500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14423269979125306653/14425000000000000000 : ℝ)*(X 0 1+X 2 1)+(178316466857/288500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4831/1024 : ℝ)) (lo := (5273/50000 : ℝ)) (hi := (4079/25000 : ℝ)) (c := (14423269979125306653/14425000000000000000 : ℝ)) (alpha := (178316466857/288500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14423269979125306653/14425000000000000000 : ℝ)*(X 0 2+X 1 2)+(178316466857/288500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4831/1024 : ℝ)) (lo := (5273/50000 : ℝ)) (hi := (4079/25000 : ℝ)) (c := (14423269979125306653/14425000000000000000 : ℝ)) (alpha := (178316466857/288500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-414402717/2500000000 : ℝ)*X 0 0+(2726812171/5000000000 : ℝ)*X 0 1+(1036506747/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1629_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350815171/10000000000 : ℝ)*X 1 0+(-1797280979/10000000000 : ℝ)*X 1 1+(5182533707/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1629_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1070163031/2000000000 : ℝ)*X 2 0+(5182533729/10000000000 : ℝ)*X 2 1+(-449320243/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1629_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4197155839/10000000000 : ℝ)*X 0 0+(773223337/2000000000 : ℝ)*X 0 1+(181959003/400000000 : ℝ)*X 0 2+(4197155839/10000000000 : ℝ)*X 1 0+(773223337/2000000000 : ℝ)*X 1 1+(181959003/400000000 : ℝ)*X 1 2+(4197155839/10000000000 : ℝ)*X 2 0+(773223337/2000000000 : ℝ)*X 2 1+(181959003/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1629_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1657678123/10000000000 : ℝ)*X 0 0+(1036912899/2000000000 : ℝ)*X 0 1+(2725786083/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1629_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2639297541/5000000000 : ℝ)*X 1 0+(-1528242549/10000000000 : ℝ)*X 1 1+(170361631/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1629_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2639297523/5000000000 : ℝ)*X 2 0+(5451572271/10000000000 : ℝ)*X 2 1+(-191030311/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1629_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((839465003/2000000000 : ℝ)*X 0 0+(4543859821/10000000000 : ℝ)*X 0 1+(3871285763/10000000000 : ℝ)*X 0 2+(839465003/2000000000 : ℝ)*X 1 0+(4543859821/10000000000 : ℝ)*X 1 1+(3871285763/10000000000 : ℝ)*X 1 2+(839465003/2000000000 : ℝ)*X 2 0+(4543859821/10000000000 : ℝ)*X 2 1+(3871285763/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1629_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4500821575951088854739819247/360625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2028604381/100000000000000 : ℝ)*(base19) + (1885217461/100000000000000 : ℝ)*(base23) + (70821529/100000000000000 : ℝ)*(lower2) + (153258771/50000000000000 : ℝ)*(upper3) + (107443373/50000000000000 : ℝ)*(upper5) + (1288326617171567/50000000000000 : ℝ)*(major0) + (1288326617171567/50000000000000 : ℝ)*(major1) + (1288326617171567/50000000000000 : ℝ)*(major2) + (3688828883401707/100000000000000 : ℝ)*(sp0) + (184442570123979/5000000000000 : ℝ)*(sp1) + (7377703091733/200000000000 : ℝ)*(sp2) + (366110491332779/25000000000000 : ℝ)*(sp3) + (4909536451/20000000000000 : ℝ)*(sp4) + (106562507/1000000000000 : ℝ)*(sp7) + (183056577697727/12500000000000 : ℝ)*(f.failure) + (1844426715541981/50000000000000 : ℝ)*(f.sum) + (85165450240063/14425000000000000000000000000 : ℝ)*base65 + (988489844279735251/721250000000000000000000000000000 : ℝ)*base67 + (9090715358085264749/721250000000000000000000000000000 : ℝ)*base70 + (1846725540498485251/721250000000000000000000000000000 : ℝ)*base71 + (4549780527669/7212500000000000000000000000 : ℝ)*base73 + (57061333141514749/721250000000000000000000000000000 : ℝ)*base76 + (7526497655948485251/721250000000000000000000000000000 : ℝ)*base77 + (5383000834858485251/721250000000000000000000000000000 : ℝ)*base79 + (11259972302581/7212500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (7510411/1250000000000000000000 : ℝ)*base90 + (7510411/1250000000000000000000 : ℝ)*base92 + (7510411/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1566656622295805604090915249/180312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (667029833/50000000000000 : ℝ)*(base19) + (341638473/25000000000000 : ℝ)*(base23) + (394396423/100000000000000 : ℝ)*(lower1) + (111064247/50000000000000 : ℝ)*(upper3) + (14996301/100000000000000 : ℝ)*(lower4) + (10453457/6250000000000 : ℝ)*(upper5) + (1308003586799811/50000000000000 : ℝ)*(major0) + (1308003586799811/50000000000000 : ℝ)*(major1) + (1308003586799811/50000000000000 : ℝ)*(major2) + (2165432197/100000000000000 : ℝ)*(sp2) + (3745194445071951/100000000000000 : ℝ)*(sp4) + (749038622202457/20000000000000 : ℝ)*(sp5) + (3745190913085863/100000000000000 : ℝ)*(sp6) + (1486819612508489/100000000000000 : ℝ)*(sp7) + (1486819612508489/100000000000000 : ℝ)*(f.failure) + (3745194445071951/100000000000000 : ℝ)*(f.sum) + (10683572951551/3606250000000000000000000000 : ℝ)*base65 + (17348256912848707417/721250000000000000000000000000000 : ℝ)*base68 + (2810422946527457417/721250000000000000000000000000000 : ℝ)*base70 + (36724518789482457417/721250000000000000000000000000000 : ℝ)*base72 + (33311899560177/7212500000000000000000000000 : ℝ)*base73 + (20314681970025042583/721250000000000000000000000000000 : ℝ)*base75 + (2244728248171207417/721250000000000000000000000000000 : ℝ)*base78 + (14256256533544957417/721250000000000000000000000000000 : ℝ)*base80 + (42133971256521/14425000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (52602077/10000000000000000000000 : ℝ)*base90 + (52602077/10000000000000000000000 : ℝ)*base92 + (52602077/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1629_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4831/1024 : ℝ) ≤ p) (hpb : p ≤ (4835/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (175946507/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4079/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5273/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10553/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4077/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1629_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1629_s5_0 (p : ℝ) (hpa : (4831/1024 : ℝ) ≤ p) (hpb : p ≤ (4835/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-207202089/1250000000 : ℝ)*x 0 + (1363398943/2500000000 : ℝ)*x 1 + (1295639599/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (207202089/1250000000 : ℝ)^4835 ≤ (10227340476609/100000000000000 : ℝ)^3811 := by
    have hnat : (207202089 : ℕ)^4835*100000000000000^3811 ≤ 10227340476609^3811*1250000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207202089 1250000000 10227340476609 100000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1363398943/2500000000 : ℝ)^4835 ≤ (46337301243369/100000000000000 : ℝ)^3811 := by
    have hnat : (1363398943 : ℕ)^4835*100000000000000^3811 ≤ 46337301243369^3811*2500000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1363398943 2500000000 46337301243369 100000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1295639599/2500000000 : ℝ)^4835 ≤ (868707165283/2000000000000 : ℝ)^3811 := by
    have hnat : (1295639599 : ℕ)^4835*2000000000000^3811 ≤ 868707165283^3811*2500000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295639599 2500000000 868707165283 2000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4835/1024 : ℝ)) 4835 3811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-207202089/1250000000 : ℝ), (1363398943/2500000000 : ℝ), (1295639599/2500000000 : ℝ)] ![(10227340476609/100000000000000 : ℝ), (46337301243369/100000000000000 : ℝ), (868707165283/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-207202089/1250000000 : ℝ)|^4835 ≤ (10227340476609/100000000000000 : ℝ)^3811
        have hw : |(-207202089/1250000000 : ℝ)|=(207202089/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1363398943/2500000000 : ℝ)|^4835 ≤ (46337301243369/100000000000000 : ℝ)^3811
        have hw : |(1363398943/2500000000 : ℝ)|=(1363398943/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1295639599/2500000000 : ℝ)|^4835 ≤ (868707165283/2000000000000 : ℝ)^3811
        have hw : |(1295639599/2500000000 : ℝ)|=(1295639599/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1629_s5_1 (p : ℝ) (hpa : (4831/1024 : ℝ) ≤ p) (hpb : p ≤ (4835/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675403813/5000000000 : ℝ)*x 0 + (-1797258649/10000000000 : ℝ)*x 1 + (2591279059/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675403813/5000000000 : ℝ)^4835 ≤ (45232098003363/100000000000000 : ℝ)^3811 := by
    have hnat : (2675403813 : ℕ)^4835*100000000000000^3811 ≤ 45232098003363^3811*5000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675403813 5000000000 45232098003363 100000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1797258649/10000000000 : ℝ)^4835 ≤ (708284167197/6250000000000 : ℝ)^3811 := by
    have hnat : (1797258649 : ℕ)^4835*6250000000000^3811 ≤ 708284167197^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1797258649 10000000000 708284167197 6250000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2591279059/5000000000 : ℝ)^4835 ≤ (4343535530817/10000000000000 : ℝ)^3811 := by
    have hnat : (2591279059 : ℕ)^4835*10000000000000^3811 ≤ 4343535530817^3811*5000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591279059 5000000000 4343535530817 10000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4835/1024 : ℝ)) 4835 3811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675403813/5000000000 : ℝ), (-1797258649/10000000000 : ℝ), (2591279059/5000000000 : ℝ)] ![(45232098003363/100000000000000 : ℝ), (708284167197/6250000000000 : ℝ), (4343535530817/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675403813/5000000000 : ℝ)|^4835 ≤ (45232098003363/100000000000000 : ℝ)^3811
        have hw : |(2675403813/5000000000 : ℝ)|=(2675403813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1797258649/10000000000 : ℝ)|^4835 ≤ (708284167197/6250000000000 : ℝ)^3811
        have hw : |(-1797258649/10000000000 : ℝ)|=(1797258649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2591279059/5000000000 : ℝ)|^4835 ≤ (4343535530817/10000000000000 : ℝ)^3811
        have hw : |(2591279059/5000000000 : ℝ)|=(2591279059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1629_s5_2 (p : ℝ) (hpa : (4831/1024 : ℝ) ≤ p) (hpb : p ≤ (4835/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350807253/10000000000 : ℝ)*x 0 + (1295639611/2500000000 : ℝ)*x 1 + (-449314679/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350807253/10000000000 : ℝ)^4835 ≤ (11308023500763/25000000000000 : ℝ)^3811 := by
    have hnat : (5350807253 : ℕ)^4835*25000000000000^3811 ≤ 11308023500763^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350807253 10000000000 11308023500763 25000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1295639611/2500000000 : ℝ)^4835 ≤ (8687071754907/20000000000000 : ℝ)^3811 := by
    have hnat : (1295639611 : ℕ)^4835*20000000000000^3811 ≤ 8687071754907^3811*2500000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295639611 2500000000 8687071754907 20000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (449314679/2500000000 : ℝ)^4835 ≤ (11332547211133/100000000000000 : ℝ)^3811 := by
    have hnat : (449314679 : ℕ)^4835*100000000000000^3811 ≤ 11332547211133^3811*2500000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449314679 2500000000 11332547211133 100000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4835/1024 : ℝ)) 4835 3811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350807253/10000000000 : ℝ), (1295639611/2500000000 : ℝ), (-449314679/2500000000 : ℝ)] ![(11308023500763/25000000000000 : ℝ), (8687071754907/20000000000000 : ℝ), (11332547211133/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350807253/10000000000 : ℝ)|^4835 ≤ (11308023500763/25000000000000 : ℝ)^3811
        have hw : |(5350807253/10000000000 : ℝ)|=(5350807253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1295639611/2500000000 : ℝ)|^4835 ≤ (8687071754907/20000000000000 : ℝ)^3811
        have hw : |(1295639611/2500000000 : ℝ)|=(1295639611/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-449314679/2500000000 : ℝ)|^4835 ≤ (11332547211133/100000000000000 : ℝ)^3811
        have hw : |(-449314679/2500000000 : ℝ)|=(449314679/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1629_s5_3 (p : ℝ) (hpa : (4831/1024 : ℝ) ≤ p) (hpb : p ≤ (4835/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4197159443/10000000000 : ℝ)*x 0 + (3866182807/10000000000 : ℝ)*x 1 + (4548908253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4197159443/10000000000 : ℝ)^4835 ≤ (664775722573/2000000000000 : ℝ)^3811 := by
    have hnat : (4197159443 : ℕ)^4835*2000000000000^3811 ≤ 664775722573^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4197159443 10000000000 664775722573 2000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3866182807/10000000000 : ℝ)^4835 ≤ (29949312839131/100000000000000 : ℝ)^3811 := by
    have hnat : (3866182807 : ℕ)^4835*100000000000000^3811 ≤ 29949312839131^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3866182807 10000000000 29949312839131 100000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4548908253/10000000000 : ℝ)^4835 ≤ (7362380202901/20000000000000 : ℝ)^3811 := by
    have hnat : (4548908253 : ℕ)^4835*20000000000000^3811 ≤ 7362380202901^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4548908253 10000000000 7362380202901 20000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4835/1024 : ℝ)) 4835 3811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4197159443/10000000000 : ℝ), (3866182807/10000000000 : ℝ), (4548908253/10000000000 : ℝ)] ![(664775722573/2000000000000 : ℝ), (29949312839131/100000000000000 : ℝ), (7362380202901/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4197159443/10000000000 : ℝ)|^4835 ≤ (664775722573/2000000000000 : ℝ)^3811
        have hw : |(4197159443/10000000000 : ℝ)|=(4197159443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3866182807/10000000000 : ℝ)|^4835 ≤ (29949312839131/100000000000000 : ℝ)^3811
        have hw : |(3866182807/10000000000 : ℝ)|=(3866182807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4548908253/10000000000 : ℝ)|^4835 ≤ (7362380202901/20000000000000 : ℝ)^3811
        have hw : |(4548908253/10000000000 : ℝ)|=(4548908253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1629_s5_4 (p : ℝ) (hpa : (4831/1024 : ℝ) ≤ p) (hpb : p ≤ (4835/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-828841879/5000000000 : ℝ)*x 0 + (648073549/1250000000 : ℝ)*x 1 + (5451544497/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (828841879/5000000000 : ℝ)^4835 ≤ (10227865297797/100000000000000 : ℝ)^3811 := by
    have hnat : (828841879 : ℕ)^4835*100000000000000^3811 ≤ 10227865297797^3811*5000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      828841879 5000000000 10227865297797 100000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (648073549/1250000000 : ℝ)^4835 ≤ (43456944393091/100000000000000 : ℝ)^3811 := by
    have hnat : (648073549 : ℕ)^4835*100000000000000^3811 ≤ 43456944393091^3811*1250000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      648073549 1250000000 43456944393091 100000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5451544497/10000000000 : ℝ)^4835 ≤ (46315190300623/100000000000000 : ℝ)^3811 := by
    have hnat : (5451544497 : ℕ)^4835*100000000000000^3811 ≤ 46315190300623^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5451544497 10000000000 46315190300623 100000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4835/1024 : ℝ)) 4835 3811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-828841879/5000000000 : ℝ), (648073549/1250000000 : ℝ), (5451544497/10000000000 : ℝ)] ![(10227865297797/100000000000000 : ℝ), (43456944393091/100000000000000 : ℝ), (46315190300623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-828841879/5000000000 : ℝ)|^4835 ≤ (10227865297797/100000000000000 : ℝ)^3811
        have hw : |(-828841879/5000000000 : ℝ)|=(828841879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(648073549/1250000000 : ℝ)|^4835 ≤ (43456944393091/100000000000000 : ℝ)^3811
        have hw : |(648073549/1250000000 : ℝ)|=(648073549/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5451544497/10000000000 : ℝ)|^4835 ≤ (46315190300623/100000000000000 : ℝ)^3811
        have hw : |(5451544497/10000000000 : ℝ)|=(5451544497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1629_s5_5 (p : ℝ) (hpa : (4831/1024 : ℝ) ≤ p) (hpb : p ≤ (4835/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5278601499/10000000000 : ℝ)*x 0 + (-1528272387/10000000000 : ℝ)*x 1 + (5451544629/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5278601499/10000000000 : ℝ)^4835 ≤ (22229558966481/50000000000000 : ℝ)^3811 := by
    have hnat : (5278601499 : ℕ)^4835*50000000000000^3811 ≤ 22229558966481^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5278601499 10000000000 22229558966481 50000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1528272387/10000000000 : ℝ)^4835 ≤ (184513806621/2000000000000 : ℝ)^3811 := by
    have hnat : (1528272387 : ℕ)^4835*2000000000000^3811 ≤ 184513806621^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1528272387 10000000000 184513806621 2000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5451544629/10000000000 : ℝ)^4835 ≤ (9263038344679/20000000000000 : ℝ)^3811 := by
    have hnat : (5451544629 : ℕ)^4835*20000000000000^3811 ≤ 9263038344679^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5451544629 10000000000 9263038344679 20000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4835/1024 : ℝ)) 4835 3811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5278601499/10000000000 : ℝ), (-1528272387/10000000000 : ℝ), (5451544629/10000000000 : ℝ)] ![(22229558966481/50000000000000 : ℝ), (184513806621/2000000000000 : ℝ), (9263038344679/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5278601499/10000000000 : ℝ)|^4835 ≤ (22229558966481/50000000000000 : ℝ)^3811
        have hw : |(5278601499/10000000000 : ℝ)|=(5278601499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1528272387/10000000000 : ℝ)|^4835 ≤ (184513806621/2000000000000 : ℝ)^3811
        have hw : |(-1528272387/10000000000 : ℝ)|=(1528272387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5451544629/10000000000 : ℝ)|^4835 ≤ (9263038344679/20000000000000 : ℝ)^3811
        have hw : |(5451544629/10000000000 : ℝ)|=(5451544629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1629_s5_6 (p : ℝ) (hpa : (4831/1024 : ℝ) ≤ p) (hpb : p ≤ (4835/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5278601601/10000000000 : ℝ)*x 0 + (681443071/1250000000 : ℝ)*x 1 + (-152827233/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5278601601/10000000000 : ℝ)^4835 ≤ (8891823804579/20000000000000 : ℝ)^3811 := by
    have hnat : (5278601601 : ℕ)^4835*20000000000000^3811 ≤ 8891823804579^3811*10000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5278601601 10000000000 8891823804579 20000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (681443071/1250000000 : ℝ)^4835 ≤ (23157595532951/50000000000000 : ℝ)^3811 := by
    have hnat : (681443071 : ℕ)^4835*50000000000000^3811 ≤ 23157595532951^3811*1250000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      681443071 1250000000 23157595532951 50000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (152827233/1000000000 : ℝ)^4835 ≤ (1153211236813/12500000000000 : ℝ)^3811 := by
    have hnat : (152827233 : ℕ)^4835*12500000000000^3811 ≤ 1153211236813^3811*1000000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      152827233 1000000000 1153211236813 12500000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4835/1024 : ℝ)) 4835 3811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5278601601/10000000000 : ℝ), (681443071/1250000000 : ℝ), (-152827233/1000000000 : ℝ)] ![(8891823804579/20000000000000 : ℝ), (23157595532951/50000000000000 : ℝ), (1153211236813/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5278601601/10000000000 : ℝ)|^4835 ≤ (8891823804579/20000000000000 : ℝ)^3811
        have hw : |(5278601601/10000000000 : ℝ)|=(5278601601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(681443071/1250000000 : ℝ)|^4835 ≤ (23157595532951/50000000000000 : ℝ)^3811
        have hw : |(681443071/1250000000 : ℝ)|=(681443071/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-152827233/1000000000 : ℝ)|^4835 ≤ (1153211236813/12500000000000 : ℝ)^3811
        have hw : |(-152827233/1000000000 : ℝ)|=(152827233/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1629_s5_7 (p : ℝ) (hpa : (4831/1024 : ℝ) ≤ p) (hpb : p ≤ (4835/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (524666089/1250000000 : ℝ)*x 0 + (56797433/125000000 : ℝ)*x 1 + (241959377/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (524666089/1250000000 : ℝ)^4835 ≤ (16620243412929/50000000000000 : ℝ)^3811 := by
    have hnat : (524666089 : ℕ)^4835*50000000000000^3811 ≤ 16620243412929^3811*1250000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524666089 1250000000 16620243412929 50000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (56797433/125000000 : ℝ)^4835 ≤ (36759408081147/100000000000000 : ℝ)^3811 := by
    have hnat : (56797433 : ℕ)^4835*100000000000000^3811 ≤ 36759408081147^3811*125000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56797433 125000000 36759408081147 100000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (241959377/625000000 : ℝ)^4835 ≤ (7500026268679/25000000000000 : ℝ)^3811 := by
    have hnat : (241959377 : ℕ)^4835*25000000000000^3811 ≤ 7500026268679^3811*625000000^4835 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      241959377 625000000 7500026268679 25000000000000 4835 3811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4835/1024 : ℝ)) 4835 3811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(524666089/1250000000 : ℝ), (56797433/125000000 : ℝ), (241959377/625000000 : ℝ)] ![(16620243412929/50000000000000 : ℝ), (36759408081147/100000000000000 : ℝ), (7500026268679/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(524666089/1250000000 : ℝ)|^4835 ≤ (16620243412929/50000000000000 : ℝ)^3811
        have hw : |(524666089/1250000000 : ℝ)|=(524666089/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(56797433/125000000 : ℝ)|^4835 ≤ (36759408081147/100000000000000 : ℝ)^3811
        have hw : |(56797433/125000000 : ℝ)|=(56797433/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(241959377/625000000 : ℝ)|^4835 ≤ (7500026268679/25000000000000 : ℝ)^3811
        have hw : |(241959377/625000000 : ℝ)|=(241959377/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1629_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4831/1024 : ℝ) ≤ p) (hpb : p ≤ (4835/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (175946507/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4077/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10553/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5277/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16307/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4077/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10553/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4077/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10553/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4077/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10553/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4077/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10553/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4077/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10553/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4077/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10553/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10553/100000 : ℝ) ^ (4831/1024 : ℝ) ≤ (2468930941990863/100000000000000000000 : ℝ) := by
    have hpowers : (10553/100000 : ℝ)^4831 ≤ (2468930941990863/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10553 : ℕ)^4831*100000000000000000000^1024 ≤ 2468930941990863^1024*100000^4831 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10553 100000 2468930941990863 100000000000000000000 4831 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10553/100000 : ℝ)) (X := (2468930941990863/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4831 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4077/25000 : ℝ) ^ (4831/1024 : ℝ) ≤ (769741580960363/4000000000000000000 : ℝ) := by
    have hpowers : (4077/25000 : ℝ)^4831 ≤ (769741580960363/4000000000000000000 : ℝ)^1024 := by
      have hnat : (4077 : ℕ)^4831*4000000000000000000^1024 ≤ 769741580960363^1024*25000^4831 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4077 25000 769741580960363 4000000000000000000 4831 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4077/25000 : ℝ)) (X := (769741580960363/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4831 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002468930941990863/50000000000000000000 : ℝ) ≤ (5000052331527583/5000000000000000 : ℝ) ^ (4831/1024 : ℝ) := by
    have hpowers : (50002468930941990863/50000000000000000000 : ℝ)^1024 ≤ (5000052331527583/5000000000000000 : ℝ)^4831 := by
      have hnat : (50002468930941990863 : ℕ)^1024*5000000000000000^4831 ≤ 5000052331527583^4831*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002468930941990863 50000000000000000000 5000052331527583 5000000000000000 1024 4831 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000052331527583/5000000000000000 : ℝ)) (X := (50002468930941990863/50000000000000000000 : ℝ)) (by norm_num) 4831 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50010856235232999969/50000000000000000000 : ℝ) ≤ (10000460187702323/10000000000000000 : ℝ) ^ (4831/1024 : ℝ) := by
    have hpowers : (50010856235232999969/50000000000000000000 : ℝ)^1024 ≤ (10000460187702323/10000000000000000 : ℝ)^4831 := by
      have hnat : (50010856235232999969 : ℕ)^1024*10000000000000000^4831 ≤ 10000460187702323^4831*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010856235232999969 50000000000000000000 10000460187702323 10000000000000000 1024 4831 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000460187702323/10000000000000000 : ℝ)) (X := (50010856235232999969/50000000000000000000 : ℝ)) (by norm_num) 4831 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2000769741580960363/2000000000000000000 : ℝ) ≤ (250020392808737/250000000000000 : ℝ) ^ (4831/1024 : ℝ) := by
    have hpowers : (2000769741580960363/2000000000000000000 : ℝ)^1024 ≤ (250020392808737/250000000000000 : ℝ)^4831 := by
      have hnat : (2000769741580960363 : ℕ)^1024*250000000000000^4831 ≤ 250020392808737^4831*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000769741580960363 2000000000000000000 250020392808737 250000000000000 1024 4831 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250020392808737/250000000000000 : ℝ)) (X := (2000769741580960363/2000000000000000000 : ℝ)) (by norm_num) 4831 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2468930941990863/100000000000000000000 : ℝ) ≤ ((3596443664542474043/3596875000000000000 : ℝ)+2*(355524647157/575500000000000 : ℝ)*(10553/100000 : ℝ))^(4831/1024 : ℝ) := by
    rw [show (3596443664542474043/3596875000000000000 : ℝ)+2*(355524647157/575500000000000 : ℝ)*(10553/100000 : ℝ)=(5000052331527583/5000000000000000 : ℝ) by norm_num, show 1+2*(2468930941990863/100000000000000000000 : ℝ)=(50002468930941990863/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(769741580960363/4000000000000000000 : ℝ)+(2468930941990863/100000000000000000000 : ℝ) ≤ ((3596443664542474043/3596875000000000000 : ℝ)+(355524647157/575500000000000 : ℝ)*((4077/25000 : ℝ)+(10553/100000 : ℝ)))^(4831/1024 : ℝ) := by
    rw [show (3596443664542474043/3596875000000000000 : ℝ)+(355524647157/575500000000000 : ℝ)*((4077/25000 : ℝ)+(10553/100000 : ℝ))=(10000460187702323/10000000000000000 : ℝ) by norm_num, show 1+(769741580960363/4000000000000000000 : ℝ)+(2468930941990863/100000000000000000000 : ℝ)=(50010856235232999969/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(769741580960363/4000000000000000000 : ℝ) ≤ ((3596443664542474043/3596875000000000000 : ℝ)+2*(355524647157/575500000000000 : ℝ)*(4077/25000 : ℝ))^(4831/1024 : ℝ) := by
    rw [show (3596443664542474043/3596875000000000000 : ℝ)+2*(355524647157/575500000000000 : ℝ)*(4077/25000 : ℝ)=(250020392808737/250000000000000 : ℝ) by norm_num, show 1+2*(769741580960363/4000000000000000000 : ℝ)=(2000769741580960363/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3596443664542474043/3596875000000000000 : ℝ)*(X 1 0+X 2 0)+(355524647157/575500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4831/1024 : ℝ)) (lo := (10553/100000 : ℝ)) (hi := (4077/25000 : ℝ)) (c := (3596443664542474043/3596875000000000000 : ℝ)) (alpha := (355524647157/575500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3596443664542474043/3596875000000000000 : ℝ)*(X 0 1+X 2 1)+(355524647157/575500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4831/1024 : ℝ)) (lo := (10553/100000 : ℝ)) (hi := (4077/25000 : ℝ)) (c := (3596443664542474043/3596875000000000000 : ℝ)) (alpha := (355524647157/575500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3596443664542474043/3596875000000000000 : ℝ)*(X 0 2+X 1 2)+(355524647157/575500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4831/1024 : ℝ)) (lo := (10553/100000 : ℝ)) (hi := (4077/25000 : ℝ)) (c := (3596443664542474043/3596875000000000000 : ℝ)) (alpha := (355524647157/575500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-207202089/1250000000 : ℝ)*X 0 0+(1363398943/2500000000 : ℝ)*X 0 1+(1295639599/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1629_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675403813/5000000000 : ℝ)*X 1 0+(-1797258649/10000000000 : ℝ)*X 1 1+(2591279059/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1629_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350807253/10000000000 : ℝ)*X 2 0+(1295639611/2500000000 : ℝ)*X 2 1+(-449314679/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1629_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4197159443/10000000000 : ℝ)*X 0 0+(3866182807/10000000000 : ℝ)*X 0 1+(4548908253/10000000000 : ℝ)*X 0 2+(4197159443/10000000000 : ℝ)*X 1 0+(3866182807/10000000000 : ℝ)*X 1 1+(4548908253/10000000000 : ℝ)*X 1 2+(4197159443/10000000000 : ℝ)*X 2 0+(3866182807/10000000000 : ℝ)*X 2 1+(4548908253/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1629_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-828841879/5000000000 : ℝ)*X 0 0+(648073549/1250000000 : ℝ)*X 0 1+(5451544497/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1629_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5278601499/10000000000 : ℝ)*X 1 0+(-1528272387/10000000000 : ℝ)*X 1 1+(5451544629/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1629_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5278601601/10000000000 : ℝ)*X 2 0+(681443071/1250000000 : ℝ)*X 2 1+(-152827233/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1629_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((524666089/1250000000 : ℝ)*X 0 0+(56797433/125000000 : ℝ)*X 0 1+(241959377/625000000 : ℝ)*X 0 2+(524666089/1250000000 : ℝ)*X 1 0+(56797433/125000000 : ℝ)*X 1 1+(241959377/625000000 : ℝ)*X 1 2+(524666089/1250000000 : ℝ)*X 2 0+(56797433/125000000 : ℝ)*X 2 1+(241959377/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1629_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1330691872491122255402277699/179843750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1319590043/100000000000000 : ℝ)*(base19) + (993190187/100000000000000 : ℝ)*(base23) + (18514957/50000000000000 : ℝ)*(lower2) + (21713677/10000000000000 : ℝ)*(upper3) + (78011751/100000000000000 : ℝ)*(upper5) + (2577143252680709/100000000000000 : ℝ)*(major0) + (2577143252680709/100000000000000 : ℝ)*(major1) + (257714325268071/10000000000000 : ℝ)*(major2) + (1844771692611331/50000000000000 : ℝ)*(sp0) + (1844776906696597/50000000000000 : ℝ)*(sp1) + (73791082795861/2000000000000 : ℝ)*(sp2) + (91545244837973/6250000000000 : ℝ)*(sp3) + (469910423/4000000000000 : ℝ)*(sp4) + (7208332091/100000000000000 : ℝ)*(sp7) + (73236556286983/5000000000000 : ℝ)*(f.failure) + (3689555132983237/100000000000000 : ℝ)*(f.sum) + (194803445909683/57550000000000000000000000000 : ℝ)*base65 + (123740684158523987/359687500000000000000000000000000 : ℝ)*base67 + (69644855742086357/8992187500000000000000000000000 : ℝ)*base69 + (1843567481102273987/359687500000000000000000000000000 : ℝ)*base71 + (93593847024717/57550000000000000000000000000 : ℝ)*base74 + (126731708629250839/17984375000000000000000000000000 : ℝ)*base75 + (234515567336917737/359687500000000000000000000000000 : ℝ)*base77 + (521596744928707263/359687500000000000000000000000000 : ℝ)*base80 + (51744749411087/28775000000000000000000000000 : ℝ)*base82 + (3418381/500000000000000000000 : ℝ)*base89 + (3418381/500000000000000000000 : ℝ)*base91 + (1581619/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7457449471452169584678999/1798437500000000000000000000000 : ℝ) := by norm_num
    linear_combination (97731663/20000000000000 : ℝ)*(base19) + (383918757/50000000000000 : ℝ)*(base23) + (145499179/100000000000000 : ℝ)*(lower1) + (25242217/20000000000000 : ℝ)*(upper3) + (38091011/50000000000000 : ℝ)*(lower4) + (4789539/20000000000000 : ℝ)*(upper5) + (52330355637813/2000000000000 : ℝ)*(major0) + (52330355637813/2000000000000 : ℝ)*(major1) + (52330355637813/2000000000000 : ℝ)*(major2) + (285444447/6250000000000 : ℝ)*(sp2) + (117060175203127/3125000000000 : ℝ)*(sp4) + (3745925117841749/100000000000000 : ℝ)*(sp5) + (1872960135775699/50000000000000 : ℝ)*(sp6) + (743554909530159/50000000000000 : ℝ)*(sp7) + (743554909530159/50000000000000 : ℝ)*(f.failure) + (117060175203127/3125000000000 : ℝ)*(f.sum) + (181060792111/575500000000000000000000000 : ℝ)*base66 + (150860333889255791/7193750000000000000000000000000 : ℝ)*base68 + (10780168562144209/7193750000000000000000000000000 : ℝ)*base69 + (408760329408187959/7193750000000000000000000000000 : ℝ)*base71 + (219368422837/46040000000000000000000000 : ℝ)*base74 + (546761125989499541/7193750000000000000000000000000 : ℝ)*base76 + (22461767655981709/7193750000000000000000000000000 : ℝ)*base77 + (46088596422844209/7193750000000000000000000000000 : ℝ)*base79 + (991204860661/575500000000000000000000000 : ℝ)*base82 + (12795387/5000000000000000000000 : ℝ)*base90 + (12795387/5000000000000000000000 : ℝ)*base92 + (12795387/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1629_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4831/1024 : ℝ) ≤ p) (hpb : p ≤ (4835/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (175946507/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4077/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10553/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5277/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16307/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1629_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1629_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4831/1024 : ℝ) ≤ p) (hpb : p ≤ (4835/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (175946507/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16419/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5227/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5277/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16307/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1629_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1629_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1629_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4831/1024 : ℝ) ≤ p) (hpb : p ≤ (4835/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (175946507/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16419/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5227/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5277/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16307/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1629_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
