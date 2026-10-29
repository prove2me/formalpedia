-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1716_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:54:50.051228+00:00
-- url     : https://prove2.me/submissions/42bda6b3-2b4d-4ec3-ba7c-23111a78682e

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
theorem support_rectangle_w1716_s0_0 (p : ℝ) (hpa : (5343/1024 : ℝ) ≤ p) (hpb : p ≤ (5351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1319112307/10000000000 : ℝ)*x 0 + (56860099/100000000 : ℝ)*x 1 + (4966446241/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1319112307/10000000000 : ℝ)^5351 ≤ (8167578410597/100000000000000 : ℝ)^4327 := by
    have hnat : (1319112307 : ℕ)^5351*100000000000000^4327 ≤ 8167578410597^4327*10000000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319112307 10000000000 8167578410597 100000000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (56860099/100000000 : ℝ)^5351 ≤ (49748725287807/100000000000000 : ℝ)^4327 := by
    have hnat : (56860099 : ℕ)^5351*100000000000000^4327 ≤ 49748725287807^4327*100000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56860099 100000000 49748725287807 100000000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4966446241/10000000000 : ℝ)^5351 ≤ (42083696281723/100000000000000 : ℝ)^4327 := by
    have hnat : (4966446241 : ℕ)^5351*100000000000000^4327 ≤ 42083696281723^4327*10000000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4966446241 10000000000 42083696281723 100000000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5351/1024 : ℝ)) 5351 4327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1319112307/10000000000 : ℝ), (56860099/100000000 : ℝ), (4966446241/10000000000 : ℝ)] ![(8167578410597/100000000000000 : ℝ), (49748725287807/100000000000000 : ℝ), (42083696281723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1319112307/10000000000 : ℝ)|^5351 ≤ (8167578410597/100000000000000 : ℝ)^4327
        have hw : |(-1319112307/10000000000 : ℝ)|=(1319112307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(56860099/100000000 : ℝ)|^5351 ≤ (49748725287807/100000000000000 : ℝ)^4327
        have hw : |(56860099/100000000 : ℝ)|=(56860099/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4966446241/10000000000 : ℝ)|^5351 ≤ (42083696281723/100000000000000 : ℝ)^4327
        have hw : |(4966446241/10000000000 : ℝ)|=(4966446241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1716_s0_1 (p : ℝ) (hpa : (5343/1024 : ℝ) ≤ p) (hpb : p ≤ (5351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5400114891/10000000000 : ℝ)*x 0 + (-341600787/2000000000 : ℝ)*x 1 + (1241611497/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5400114891/10000000000 : ℝ)^5351 ≤ (23337010337351/50000000000000 : ℝ)^4327 := by
    have hnat : (5400114891 : ℕ)^5351*50000000000000^4327 ≤ 23337010337351^4327*10000000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400114891 10000000000 23337010337351 50000000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (341600787/2000000000 : ℝ)^5351 ≤ (702642854581/6250000000000 : ℝ)^4327 := by
    have hnat : (341600787 : ℕ)^5351*6250000000000^4327 ≤ 702642854581^4327*2000000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341600787 2000000000 702642854581 6250000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1241611497/2500000000 : ℝ)^5351 ≤ (21041846815279/50000000000000 : ℝ)^4327 := by
    have hnat : (1241611497 : ℕ)^5351*50000000000000^4327 ≤ 21041846815279^4327*2500000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1241611497 2500000000 21041846815279 50000000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5351/1024 : ℝ)) 5351 4327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5400114891/10000000000 : ℝ), (-341600787/2000000000 : ℝ), (1241611497/2500000000 : ℝ)] ![(23337010337351/50000000000000 : ℝ), (702642854581/6250000000000 : ℝ), (21041846815279/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5400114891/10000000000 : ℝ)|^5351 ≤ (23337010337351/50000000000000 : ℝ)^4327
        have hw : |(5400114891/10000000000 : ℝ)|=(5400114891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-341600787/2000000000 : ℝ)|^5351 ≤ (702642854581/6250000000000 : ℝ)^4327
        have hw : |(-341600787/2000000000 : ℝ)|=(341600787/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1241611497/2500000000 : ℝ)|^5351 ≤ (21041846815279/50000000000000 : ℝ)^4327
        have hw : |(1241611497/2500000000 : ℝ)|=(1241611497/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1716_s0_2 (p : ℝ) (hpa : (5343/1024 : ℝ) ≤ p) (hpb : p ≤ (5351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5400114799/10000000000 : ℝ)*x 0 + (4966446311/10000000000 : ℝ)*x 1 + (-1708003641/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5400114799/10000000000 : ℝ)^5351 ≤ (5834252461419/12500000000000 : ℝ)^4327 := by
    have hnat : (5400114799 : ℕ)^5351*12500000000000^4327 ≤ 5834252461419^4327*10000000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400114799 10000000000 5834252461419 12500000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4966446311/10000000000 : ℝ)^5351 ≤ (42083697015247/100000000000000 : ℝ)^4327 := by
    have hnat : (4966446311 : ℕ)^5351*100000000000000^4327 ≤ 42083697015247^4327*10000000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4966446311 10000000000 42083697015247 100000000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1708003641/10000000000 : ℝ)^5351 ≤ (2248456656039/20000000000000 : ℝ)^4327 := by
    have hnat : (1708003641 : ℕ)^5351*20000000000000^4327 ≤ 2248456656039^4327*10000000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1708003641 10000000000 2248456656039 20000000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5351/1024 : ℝ)) 5351 4327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5400114799/10000000000 : ℝ), (4966446311/10000000000 : ℝ), (-1708003641/10000000000 : ℝ)] ![(5834252461419/12500000000000 : ℝ), (42083697015247/100000000000000 : ℝ), (2248456656039/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5400114799/10000000000 : ℝ)|^5351 ≤ (5834252461419/12500000000000 : ℝ)^4327
        have hw : |(5400114799/10000000000 : ℝ)|=(5400114799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4966446311/10000000000 : ℝ)|^5351 ≤ (42083697015247/100000000000000 : ℝ)^4327
        have hw : |(4966446311/10000000000 : ℝ)|=(4966446311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1708003641/10000000000 : ℝ)|^5351 ≤ (2248456656039/20000000000000 : ℝ)^4327
        have hw : |(-1708003641/10000000000 : ℝ)|=(1708003641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1716_s0_3 (p : ℝ) (hpa : (5343/1024 : ℝ) ≤ p) (hpb : p ≤ (5351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4034563919/10000000000 : ℝ)*x 0 + (306273593/1000000000 : ℝ)*x 1 + (1294373651/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4034563919/10000000000 : ℝ)^5351 ≤ (1627334990353/5000000000000 : ℝ)^4327 := by
    have hnat : (4034563919 : ℕ)^5351*5000000000000^4327 ≤ 1627334990353^4327*10000000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4034563919 10000000000 1627334990353 5000000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (306273593/1000000000 : ℝ)^5351 ≤ (23147044380999/100000000000000 : ℝ)^4327 := by
    have hnat : (306273593 : ℕ)^5351*100000000000000^4327 ≤ 23147044380999^4327*1000000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      306273593 1000000000 23147044380999 100000000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1294373651/2500000000 : ℝ)^5351 ≤ (1107656394927/2500000000000 : ℝ)^4327 := by
    have hnat : (1294373651 : ℕ)^5351*2500000000000^4327 ≤ 1107656394927^4327*2500000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294373651 2500000000 1107656394927 2500000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5351/1024 : ℝ)) 5351 4327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4034563919/10000000000 : ℝ), (306273593/1000000000 : ℝ), (1294373651/2500000000 : ℝ)] ![(1627334990353/5000000000000 : ℝ), (23147044380999/100000000000000 : ℝ), (1107656394927/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4034563919/10000000000 : ℝ)|^5351 ≤ (1627334990353/5000000000000 : ℝ)^4327
        have hw : |(4034563919/10000000000 : ℝ)|=(4034563919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(306273593/1000000000 : ℝ)|^5351 ≤ (23147044380999/100000000000000 : ℝ)^4327
        have hw : |(306273593/1000000000 : ℝ)|=(306273593/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1294373651/2500000000 : ℝ)|^5351 ≤ (1107656394927/2500000000000 : ℝ)^4327
        have hw : |(1294373651/2500000000 : ℝ)|=(1294373651/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1716_s0_4 (p : ℝ) (hpa : (5343/1024 : ℝ) ≤ p) (hpb : p ≤ (5351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-330172453/2500000000 : ℝ)*x 0 + (2492006521/5000000000 : ℝ)*x 1 + (1133573237/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330172453/2500000000 : ℝ)^5351 ≤ (8179659101493/100000000000000 : ℝ)^4327 := by
    have hnat : (330172453 : ℕ)^5351*100000000000000^4327 ≤ 8179659101493^4327*2500000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330172453 2500000000 8179659101493 100000000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2492006521/5000000000 : ℝ)^5351 ≤ (2641740888679/6250000000000 : ℝ)^4327 := by
    have hnat : (2492006521 : ℕ)^5351*6250000000000^4327 ≤ 2641740888679^4327*5000000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2492006521 5000000000 2641740888679 6250000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1133573237/2000000000 : ℝ)^5351 ≤ (24776243335411/50000000000000 : ℝ)^4327 := by
    have hnat : (1133573237 : ℕ)^5351*50000000000000^4327 ≤ 24776243335411^4327*2000000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1133573237 2000000000 24776243335411 50000000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5351/1024 : ℝ)) 5351 4327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-330172453/2500000000 : ℝ), (2492006521/5000000000 : ℝ), (1133573237/2000000000 : ℝ)] ![(8179659101493/100000000000000 : ℝ), (2641740888679/6250000000000 : ℝ), (24776243335411/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-330172453/2500000000 : ℝ)|^5351 ≤ (8179659101493/100000000000000 : ℝ)^4327
        have hw : |(-330172453/2500000000 : ℝ)|=(330172453/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2492006521/5000000000 : ℝ)|^5351 ≤ (2641740888679/6250000000000 : ℝ)^4327
        have hw : |(2492006521/5000000000 : ℝ)|=(2492006521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1133573237/2000000000 : ℝ)|^5351 ≤ (24776243335411/50000000000000 : ℝ)^4327
        have hw : |(1133573237/2000000000 : ℝ)|=(1133573237/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1716_s0_5 (p : ℝ) (hpa : (5343/1024 : ℝ) ≤ p) (hpb : p ≤ (5351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5205360973/10000000000 : ℝ)*x 0 + (-201316901/2000000000 : ℝ)*x 1 + (708483319/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5205360973/10000000000 : ℝ)^5351 ≤ (44601342713383/100000000000000 : ℝ)^4327 := by
    have hnat : (5205360973 : ℕ)^5351*100000000000000^4327 ≤ 44601342713383^4327*10000000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5205360973 10000000000 44601342713383 100000000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (201316901/2000000000 : ℝ)^5351 ≤ (5846166631819/100000000000000 : ℝ)^4327 := by
    have hnat : (201316901 : ℕ)^5351*100000000000000^4327 ≤ 5846166631819^4327*2000000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201316901 2000000000 5846166631819 100000000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (708483319/1250000000 : ℝ)^5351 ≤ (9910498127743/20000000000000 : ℝ)^4327 := by
    have hnat : (708483319 : ℕ)^5351*20000000000000^4327 ≤ 9910498127743^4327*1250000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      708483319 1250000000 9910498127743 20000000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5351/1024 : ℝ)) 5351 4327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5205360973/10000000000 : ℝ), (-201316901/2000000000 : ℝ), (708483319/1250000000 : ℝ)] ![(44601342713383/100000000000000 : ℝ), (5846166631819/100000000000000 : ℝ), (9910498127743/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5205360973/10000000000 : ℝ)|^5351 ≤ (44601342713383/100000000000000 : ℝ)^4327
        have hw : |(5205360973/10000000000 : ℝ)|=(5205360973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-201316901/2000000000 : ℝ)|^5351 ≤ (5846166631819/100000000000000 : ℝ)^4327
        have hw : |(-201316901/2000000000 : ℝ)|=(201316901/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(708483319/1250000000 : ℝ)|^5351 ≤ (9910498127743/20000000000000 : ℝ)^4327
        have hw : |(708483319/1250000000 : ℝ)|=(708483319/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1716_s0_6 (p : ℝ) (hpa : (5343/1024 : ℝ) ≤ p) (hpb : p ≤ (5351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2602680943/5000000000 : ℝ)*x 0 + (5667865737/10000000000 : ℝ)*x 1 + (-201316877/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2602680943/5000000000 : ℝ)^5351 ≤ (22300676193801/50000000000000 : ℝ)^4327 := by
    have hnat : (2602680943 : ℕ)^5351*50000000000000^4327 ≤ 22300676193801^4327*5000000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2602680943 5000000000 22300676193801 50000000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5667865737/10000000000 : ℝ)^5351 ≤ (49552481827181/100000000000000 : ℝ)^4327 := by
    have hnat : (5667865737 : ℕ)^5351*100000000000000^4327 ≤ 49552481827181^4327*10000000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5667865737 10000000000 49552481827181 100000000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (201316877/2000000000 : ℝ)^5351 ≤ (1461541442483/25000000000000 : ℝ)^4327 := by
    have hnat : (201316877 : ℕ)^5351*25000000000000^4327 ≤ 1461541442483^4327*2000000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201316877 2000000000 1461541442483 25000000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5351/1024 : ℝ)) 5351 4327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2602680943/5000000000 : ℝ), (5667865737/10000000000 : ℝ), (-201316877/2000000000 : ℝ)] ![(22300676193801/50000000000000 : ℝ), (49552481827181/100000000000000 : ℝ), (1461541442483/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2602680943/5000000000 : ℝ)|^5351 ≤ (22300676193801/50000000000000 : ℝ)^4327
        have hw : |(2602680943/5000000000 : ℝ)|=(2602680943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5667865737/10000000000 : ℝ)|^5351 ≤ (49552481827181/100000000000000 : ℝ)^4327
        have hw : |(5667865737/10000000000 : ℝ)|=(5667865737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-201316877/2000000000 : ℝ)|^5351 ≤ (1461541442483/25000000000000 : ℝ)^4327
        have hw : |(-201316877/2000000000 : ℝ)|=(201316877/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1716_s0_7 (p : ℝ) (hpa : (5343/1024 : ℝ) ≤ p) (hpb : p ≤ (5351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4039204449/10000000000 : ℝ)*x 0 + (512586693/1000000000 : ℝ)*x 1 + (3116061191/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4039204449/10000000000 : ℝ)^5351 ≤ (2037062515213/6250000000000 : ℝ)^4327 := by
    have hnat : (4039204449 : ℕ)^5351*6250000000000^4327 ≤ 2037062515213^4327*10000000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4039204449 10000000000 2037062515213 6250000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (512586693/1000000000 : ℝ)^5351 ≤ (21880272858789/50000000000000 : ℝ)^4327 := by
    have hnat : (512586693 : ℕ)^5351*50000000000000^4327 ≤ 21880272858789^4327*1000000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      512586693 1000000000 21880272858789 50000000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3116061191/10000000000 : ℝ)^5351 ≤ (5911613504337/25000000000000 : ℝ)^4327 := by
    have hnat : (3116061191 : ℕ)^5351*25000000000000^4327 ≤ 5911613504337^4327*10000000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3116061191 10000000000 5911613504337 25000000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5351/1024 : ℝ)) 5351 4327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4039204449/10000000000 : ℝ), (512586693/1000000000 : ℝ), (3116061191/10000000000 : ℝ)] ![(2037062515213/6250000000000 : ℝ), (21880272858789/50000000000000 : ℝ), (5911613504337/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4039204449/10000000000 : ℝ)|^5351 ≤ (2037062515213/6250000000000 : ℝ)^4327
        have hw : |(4039204449/10000000000 : ℝ)|=(4039204449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(512586693/1000000000 : ℝ)|^5351 ≤ (21880272858789/50000000000000 : ℝ)^4327
        have hw : |(512586693/1000000000 : ℝ)|=(512586693/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3116061191/10000000000 : ℝ)|^5351 ≤ (5911613504337/25000000000000 : ℝ)^4327
        have hw : |(3116061191/10000000000 : ℝ)|=(3116061191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1716_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5343/1024 : ℝ) ≤ p) (hpb : p ≤ (5351/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (196947307/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (3111/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (21701/100000 : ℝ)*pair X 0 0 := by
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
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (5343/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5343 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5343*1^1024 ≤ 0^1024*1^5343 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5343 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5343 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5343/1024 : ℝ) ≤ (838762862232521473/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5343 ≤ (838762862232521473/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5343*100000000000000000000^1024 ≤ 838762862232521473^1024*5^5343 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 838762862232521473 100000000000000000000 5343 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (838762862232521473/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5343 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5343/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5343 := by
      have hnat : (1 : ℕ)^1024*1^5343 ≤ 1^5343*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5343 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5343 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100838762862232521473/100000000000000000000 : ℝ) ≤ (2504005222289717/2500000000000000 : ℝ) ^ (5343/1024 : ℝ) := by
    have hpowers : (100838762862232521473/100000000000000000000 : ℝ)^1024 ≤ (2504005222289717/2500000000000000 : ℝ)^5343 := by
      have hnat : (100838762862232521473 : ℕ)^1024*2500000000000000^5343 ≤ 2504005222289717^5343*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100838762862232521473 100000000000000000000 2504005222289717 2500000000000000 1024 5343 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2504005222289717/2500000000000000 : ℝ)) (X := (100838762862232521473/100000000000000000000 : ℝ)) (by norm_num) 5343 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50838762862232521473/50000000000000000000 : ℝ) ≤ (1254005222289717/1250000000000000 : ℝ) ^ (5343/1024 : ℝ) := by
    have hpowers : (50838762862232521473/50000000000000000000 : ℝ)^1024 ≤ (1254005222289717/1250000000000000 : ℝ)^5343 := by
      have hnat : (50838762862232521473 : ℕ)^1024*1250000000000000^5343 ≤ 1254005222289717^5343*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50838762862232521473 50000000000000000000 1254005222289717 1250000000000000 1024 5343 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1254005222289717/1250000000000000 : ℝ)) (X := (50838762862232521473/50000000000000000000 : ℝ)) (by norm_num) 5343 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(4005222289717/1000000000000000 : ℝ)*(0 : ℝ))^(5343/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(4005222289717/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(838762862232521473/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(4005222289717/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5343/1024 : ℝ) := by
    rw [show (1 : ℝ)+(4005222289717/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2504005222289717/2500000000000000 : ℝ) by norm_num, show 1+(838762862232521473/100000000000000000000 : ℝ)+(0 : ℝ)=(100838762862232521473/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(838762862232521473/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(4005222289717/1000000000000000 : ℝ)*(2/5 : ℝ))^(5343/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(4005222289717/1000000000000000 : ℝ)*(2/5 : ℝ)=(1254005222289717/1250000000000000 : ℝ) by norm_num, show 1+2*(838762862232521473/100000000000000000000 : ℝ)=(50838762862232521473/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(4005222289717/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5343/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (4005222289717/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(4005222289717/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5343/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (4005222289717/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(4005222289717/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5343/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (4005222289717/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1319112307/10000000000 : ℝ)*X 0 0+(56860099/100000000 : ℝ)*X 0 1+(4966446241/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1716_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5400114891/10000000000 : ℝ)*X 1 0+(-341600787/2000000000 : ℝ)*X 1 1+(1241611497/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1716_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5400114799/10000000000 : ℝ)*X 2 0+(4966446311/10000000000 : ℝ)*X 2 1+(-1708003641/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1716_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4034563919/10000000000 : ℝ)*X 0 0+(306273593/1000000000 : ℝ)*X 0 1+(1294373651/2500000000 : ℝ)*X 0 2+(4034563919/10000000000 : ℝ)*X 1 0+(306273593/1000000000 : ℝ)*X 1 1+(1294373651/2500000000 : ℝ)*X 1 2+(4034563919/10000000000 : ℝ)*X 2 0+(306273593/1000000000 : ℝ)*X 2 1+(1294373651/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1716_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-330172453/2500000000 : ℝ)*X 0 0+(2492006521/5000000000 : ℝ)*X 0 1+(1133573237/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1716_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5205360973/10000000000 : ℝ)*X 1 0+(-201316901/2000000000 : ℝ)*X 1 1+(708483319/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1716_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2602680943/5000000000 : ℝ)*X 2 0+(5667865737/10000000000 : ℝ)*X 2 1+(-201316877/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1716_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4039204449/10000000000 : ℝ)*X 0 0+(512586693/1000000000 : ℝ)*X 0 1+(3116061191/10000000000 : ℝ)*X 0 2+(4039204449/10000000000 : ℝ)*X 1 0+(512586693/1000000000 : ℝ)*X 1 1+(3116061191/10000000000 : ℝ)*X 1 2+(4039204449/10000000000 : ℝ)*X 2 0+(512586693/1000000000 : ℝ)*X 2 1+(3116061191/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1716_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (309038571199819659/40000000000000000000000 : ℝ) := by norm_num
    linear_combination (46879859/50000000000000 : ℝ)*(base1) + (672542911/50000000000000 : ℝ)*(base19) + (1321409251/100000000000000 : ℝ)*(base23) + (16780119/12500000000000 : ℝ)*(upper3) + (250549859/100000000000000 : ℝ)*(upper5) + (931307057251311/100000000000000 : ℝ)*(major0) + (931307057251311/100000000000000 : ℝ)*(major1) + (931307057251311/100000000000000 : ℝ)*(major2) + (27794723914401/2000000000000 : ℝ)*(sp0) + (55589653221317/4000000000000 : ℝ)*(sp1) + (173717669276187/12500000000000 : ℝ)*(sp2) + (472869283953253/100000000000000 : ℝ)*(sp3) + (3286829207/50000000000000 : ℝ)*(sp4) + (450909689/25000000000000 : ℝ)*(sp7) + (236435590675863/50000000000000 : ℝ)*(f.failure) + (1389742675618747/100000000000000 : ℝ)*(f.sum) + (14996801581013/50000000000000000000000000000 : ℝ)*base66 + (56276744268987/100000000000000000000000000000 : ℝ)*base67 + (255748935268987/100000000000000000000000000000 : ℝ)*base69 + (214827292531013/100000000000000000000000000000 : ℝ)*base72 + (101893745318987/50000000000000000000000000000 : ℝ)*base73 + (564850290731013/100000000000000000000000000000 : ℝ)*base76 + (118591805431013/100000000000000000000000000000 : ℝ)*base78 + (421007142531013/100000000000000000000000000000 : ℝ)*base80 + (121747206468987/50000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (22249059/5000000000000000000000 : ℝ)*base90 + (22249059/5000000000000000000000 : ℝ)*base92 + (22249059/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (133959960953324932472937/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (133618423/100000000000000 : ℝ)*(base1) + (374280961/50000000000000 : ℝ)*(base19) + (1057321107/100000000000000 : ℝ)*(base23) + (515385681/100000000000000 : ℝ)*(base32) + (221347021/100000000000000 : ℝ)*(upper3) + (489964984461887/50000000000000 : ℝ)*(major0) + (489964984461887/50000000000000 : ℝ)*(major1) + (489964984461887/50000000000000 : ℝ)*(major2) + (1152992621/100000000000000 : ℝ)*(sp1) + (2550276581/100000000000000 : ℝ)*(sp2) + (1462300248283481/100000000000000 : ℝ)*(sp4) + (731149106555257/50000000000000 : ℝ)*(sp5) + (146229650706737/10000000000000 : ℝ)*(sp6) + (24877940847591/5000000000000 : ℝ)*(sp7) + (124389866488981/25000000000000 : ℝ)*(f.failure) + (731150057332529/50000000000000 : ℝ)*(f.sum) + (9574031684021/25000000000000000000000000000 : ℝ)*base66 + (45453668415979/50000000000000000000000000000 : ℝ)*base67 + (180263121734021/50000000000000000000000000000 : ℝ)*base70 + (224094572134021/50000000000000000000000000000 : ℝ)*base72 + (28318173640979/25000000000000000000000000000 : ℝ)*base73 + (285477263715979/50000000000000000000000000000 : ℝ)*base75 + (6429202434021/50000000000000000000000000000 : ℝ)*base78 + (209230590534021/50000000000000000000000000000 : ℝ)*base80 + (69841960209021/25000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (3124167/2500000000000000000000 : ℝ)*base89 + (3124167/2500000000000000000000 : ℝ)*base91 + (3124167/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1716_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5343/1024 : ℝ) ≤ p) (hpb : p ≤ (5351/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (196947307/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3111/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (21701/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1716_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1716_s1_0 (p : ℝ) (hpa : (5343/1024 : ℝ) ≤ p) (hpb : p ≤ (5351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-693754343/5000000000 : ℝ)*x 0 + (5479298771/10000000000 : ℝ)*x 1 + (5128059039/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (693754343/5000000000 : ℝ)^5351 ≤ (8694462300713/100000000000000 : ℝ)^4327 := by
    have hnat : (693754343 : ℕ)^5351*100000000000000^4327 ≤ 8694462300713^4327*5000000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      693754343 5000000000 8694462300713 100000000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5479298771/10000000000 : ℝ)^5351 ≤ (47521847469599/100000000000000 : ℝ)^4327 := by
    have hnat : (5479298771 : ℕ)^5351*100000000000000^4327 ≤ 47521847469599^4327*10000000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5479298771 10000000000 47521847469599 100000000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5128059039/10000000000 : ℝ)^5351 ≤ (21891845102751/50000000000000 : ℝ)^4327 := by
    have hnat : (5128059039 : ℕ)^5351*50000000000000^4327 ≤ 21891845102751^4327*10000000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5128059039 10000000000 21891845102751 50000000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5351/1024 : ℝ)) 5351 4327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-693754343/5000000000 : ℝ), (5479298771/10000000000 : ℝ), (5128059039/10000000000 : ℝ)] ![(8694462300713/100000000000000 : ℝ), (47521847469599/100000000000000 : ℝ), (21891845102751/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-693754343/5000000000 : ℝ)|^5351 ≤ (8694462300713/100000000000000 : ℝ)^4327
        have hw : |(-693754343/5000000000 : ℝ)|=(693754343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5479298771/10000000000 : ℝ)|^5351 ≤ (47521847469599/100000000000000 : ℝ)^4327
        have hw : |(5479298771/10000000000 : ℝ)|=(5479298771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5128059039/10000000000 : ℝ)|^5351 ≤ (21891845102751/50000000000000 : ℝ)^4327
        have hw : |(5128059039/10000000000 : ℝ)|=(5128059039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1716_s1_1 (p : ℝ) (hpa : (5343/1024 : ℝ) ≤ p) (hpb : p ≤ (5351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345056963/10000000000 : ℝ)*x 0 + (-785009379/5000000000 : ℝ)*x 1 + (2564029011/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345056963/10000000000 : ℝ)^5351 ≤ (23043120538611/50000000000000 : ℝ)^4327 := by
    have hnat : (5345056963 : ℕ)^5351*50000000000000^4327 ≤ 23043120538611^4327*10000000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345056963 10000000000 23043120538611 50000000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (785009379/5000000000 : ℝ)^5351 ≤ (10130079432859/100000000000000 : ℝ)^4327 := by
    have hnat : (785009379 : ℕ)^5351*100000000000000^4327 ≤ 10130079432859^4327*5000000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      785009379 5000000000 10130079432859 100000000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2564029011/5000000000 : ℝ)^5351 ≤ (2189183973369/5000000000000 : ℝ)^4327 := by
    have hnat : (2564029011 : ℕ)^5351*5000000000000^4327 ≤ 2189183973369^4327*5000000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2564029011 5000000000 2189183973369 5000000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5351/1024 : ℝ)) 5351 4327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345056963/10000000000 : ℝ), (-785009379/5000000000 : ℝ), (2564029011/5000000000 : ℝ)] ![(23043120538611/50000000000000 : ℝ), (10130079432859/100000000000000 : ℝ), (2189183973369/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345056963/10000000000 : ℝ)|^5351 ≤ (23043120538611/50000000000000 : ℝ)^4327
        have hw : |(5345056963/10000000000 : ℝ)|=(5345056963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-785009379/5000000000 : ℝ)|^5351 ≤ (10130079432859/100000000000000 : ℝ)^4327
        have hw : |(-785009379/5000000000 : ℝ)|=(785009379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2564029011/5000000000 : ℝ)|^5351 ≤ (2189183973369/5000000000000 : ℝ)^4327
        have hw : |(2564029011/5000000000 : ℝ)|=(2564029011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1716_s1_2 (p : ℝ) (hpa : (5343/1024 : ℝ) ≤ p) (hpb : p ≤ (5351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345055673/10000000000 : ℝ)*x 0 + (256402953/500000000 : ℝ)*x 1 + (-1570019109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345055673/10000000000 : ℝ)^5351 ≤ (9217245464469/20000000000000 : ℝ)^4327 := by
    have hnat : (5345055673 : ℕ)^5351*20000000000000^4327 ≤ 9217245464469^4327*10000000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345055673 10000000000 9217245464469 20000000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (256402953/500000000 : ℝ)^5351 ≤ (21891845213617/50000000000000 : ℝ)^4327 := by
    have hnat : (256402953 : ℕ)^5351*50000000000000^4327 ≤ 21891845213617^4327*500000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256402953 500000000 21891845213617 50000000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1570019109/10000000000 : ℝ)^5351 ≤ (5065041116769/50000000000000 : ℝ)^4327 := by
    have hnat : (1570019109 : ℕ)^5351*50000000000000^4327 ≤ 5065041116769^4327*10000000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1570019109 10000000000 5065041116769 50000000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5351/1024 : ℝ)) 5351 4327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345055673/10000000000 : ℝ), (256402953/500000000 : ℝ), (-1570019109/10000000000 : ℝ)] ![(9217245464469/20000000000000 : ℝ), (21891845213617/50000000000000 : ℝ), (5065041116769/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345055673/10000000000 : ℝ)|^5351 ≤ (9217245464469/20000000000000 : ℝ)^4327
        have hw : |(5345055673/10000000000 : ℝ)|=(5345055673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(256402953/500000000 : ℝ)|^5351 ≤ (21891845213617/50000000000000 : ℝ)^4327
        have hw : |(256402953/500000000 : ℝ)|=(256402953/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1570019109/10000000000 : ℝ)|^5351 ≤ (5065041116769/50000000000000 : ℝ)^4327
        have hw : |(-1570019109/10000000000 : ℝ)|=(1570019109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1716_s1_3 (p : ℝ) (hpa : (5343/1024 : ℝ) ≤ p) (hpb : p ≤ (5351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (511827183/1250000000 : ℝ)*x 0 + (1799364439/5000000000 : ℝ)*x 1 + (578875069/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (511827183/1250000000 : ℝ)^5351 ≤ (33146847893007/100000000000000 : ℝ)^4327 := by
    have hnat : (511827183 : ℕ)^5351*100000000000000^4327 ≤ 33146847893007^4327*1250000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      511827183 1250000000 33146847893007 100000000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1799364439/5000000000 : ℝ)^5351 ≤ (14127985475949/50000000000000 : ℝ)^4327 := by
    have hnat : (1799364439 : ℕ)^5351*50000000000000^4327 ≤ 14127985475949^4327*5000000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1799364439 5000000000 14127985475949 50000000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (578875069/1250000000 : ℝ)^5351 ≤ (38597181148919/100000000000000 : ℝ)^4327 := by
    have hnat : (578875069 : ℕ)^5351*100000000000000^4327 ≤ 38597181148919^4327*1250000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      578875069 1250000000 38597181148919 100000000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5351/1024 : ℝ)) 5351 4327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(511827183/1250000000 : ℝ), (1799364439/5000000000 : ℝ), (578875069/1250000000 : ℝ)] ![(33146847893007/100000000000000 : ℝ), (14127985475949/50000000000000 : ℝ), (38597181148919/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(511827183/1250000000 : ℝ)|^5351 ≤ (33146847893007/100000000000000 : ℝ)^4327
        have hw : |(511827183/1250000000 : ℝ)|=(511827183/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1799364439/5000000000 : ℝ)|^5351 ≤ (14127985475949/50000000000000 : ℝ)^4327
        have hw : |(1799364439/5000000000 : ℝ)|=(1799364439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(578875069/1250000000 : ℝ)|^5351 ≤ (38597181148919/100000000000000 : ℝ)^4327
        have hw : |(578875069/1250000000 : ℝ)|=(578875069/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1716_s1_4 (p : ℝ) (hpa : (5343/1024 : ℝ) ≤ p) (hpb : p ≤ (5351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1387692463/10000000000 : ℝ)*x 0 + (5132252951/10000000000 : ℝ)*x 1 + (5475036527/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1387692463/10000000000 : ℝ)^5351 ≤ (8695886441871/100000000000000 : ℝ)^4327 := by
    have hnat : (1387692463 : ℕ)^5351*100000000000000^4327 ≤ 8695886441871^4327*10000000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1387692463 10000000000 8695886441871 100000000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5132252951/10000000000 : ℝ)^5351 ≤ (10956994109399/25000000000000 : ℝ)^4327 := by
    have hnat : (5132252951 : ℕ)^5351*25000000000000^4327 ≤ 10956994109399^4327*10000000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5132252951 10000000000 10956994109399 25000000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5475036527/10000000000 : ℝ)^5351 ≤ (23738068550999/50000000000000 : ℝ)^4327 := by
    have hnat : (5475036527 : ℕ)^5351*50000000000000^4327 ≤ 23738068550999^4327*10000000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5475036527 10000000000 23738068550999 50000000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5351/1024 : ℝ)) 5351 4327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1387692463/10000000000 : ℝ), (5132252951/10000000000 : ℝ), (5475036527/10000000000 : ℝ)] ![(8695886441871/100000000000000 : ℝ), (10956994109399/25000000000000 : ℝ), (23738068550999/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1387692463/10000000000 : ℝ)|^5351 ≤ (8695886441871/100000000000000 : ℝ)^4327
        have hw : |(-1387692463/10000000000 : ℝ)|=(1387692463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5132252951/10000000000 : ℝ)|^5351 ≤ (10956994109399/25000000000000 : ℝ)^4327
        have hw : |(5132252951/10000000000 : ℝ)|=(5132252951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5475036527/10000000000 : ℝ)|^5351 ≤ (23738068550999/50000000000000 : ℝ)^4327
        have hw : |(5475036527/10000000000 : ℝ)|=(5475036527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1716_s1_5 (p : ℝ) (hpa : (5343/1024 : ℝ) ≤ p) (hpb : p ≤ (5351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (328187571/625000000 : ℝ)*x 0 + (-1223040779/10000000000 : ℝ)*x 1 + (109500721/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (328187571/625000000 : ℝ)^5351 ≤ (9017090009417/20000000000000 : ℝ)^4327 := by
    have hnat : (328187571 : ℕ)^5351*20000000000000^4327 ≤ 9017090009417^4327*625000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328187571 625000000 9017090009417 20000000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1223040779/10000000000 : ℝ)^5351 ≤ (185960448883/2500000000000 : ℝ)^4327 := by
    have hnat : (1223040779 : ℕ)^5351*2500000000000^4327 ≤ 185960448883^4327*10000000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1223040779 10000000000 185960448883 2500000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (109500721/200000000 : ℝ)^5351 ≤ (47476131986891/100000000000000 : ℝ)^4327 := by
    have hnat : (109500721 : ℕ)^5351*100000000000000^4327 ≤ 47476131986891^4327*200000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109500721 200000000 47476131986891 100000000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5351/1024 : ℝ)) 5351 4327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(328187571/625000000 : ℝ), (-1223040779/10000000000 : ℝ), (109500721/200000000 : ℝ)] ![(9017090009417/20000000000000 : ℝ), (185960448883/2500000000000 : ℝ), (47476131986891/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(328187571/625000000 : ℝ)|^5351 ≤ (9017090009417/20000000000000 : ℝ)^4327
        have hw : |(328187571/625000000 : ℝ)|=(328187571/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1223040779/10000000000 : ℝ)|^5351 ≤ (185960448883/2500000000000 : ℝ)^4327
        have hw : |(-1223040779/10000000000 : ℝ)|=(1223040779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(109500721/200000000 : ℝ)|^5351 ≤ (47476131986891/100000000000000 : ℝ)^4327
        have hw : |(109500721/200000000 : ℝ)|=(109500721/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1716_s1_6 (p : ℝ) (hpa : (5343/1024 : ℝ) ≤ p) (hpb : p ≤ (5351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (328187589/625000000 : ℝ)*x 0 + (273751783/500000000 : ℝ)*x 1 + (-1223040927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (328187589/625000000 : ℝ)^5351 ≤ (45085453105067/100000000000000 : ℝ)^4327 := by
    have hnat : (328187589 : ℕ)^5351*100000000000000^4327 ≤ 45085453105067^4327*625000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328187589 625000000 45085453105067 100000000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (273751783/500000000 : ℝ)^5351 ≤ (47476127804727/100000000000000 : ℝ)^4327 := by
    have hnat : (273751783 : ℕ)^5351*100000000000000^4327 ≤ 47476127804727^4327*500000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273751783 500000000 47476127804727 100000000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1223040927/10000000000 : ℝ)^5351 ≤ (7438419068459/100000000000000 : ℝ)^4327 := by
    have hnat : (1223040927 : ℕ)^5351*100000000000000^4327 ≤ 7438419068459^4327*10000000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1223040927 10000000000 7438419068459 100000000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5351/1024 : ℝ)) 5351 4327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(328187589/625000000 : ℝ), (273751783/500000000 : ℝ), (-1223040927/10000000000 : ℝ)] ![(45085453105067/100000000000000 : ℝ), (47476127804727/100000000000000 : ℝ), (7438419068459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(328187589/625000000 : ℝ)|^5351 ≤ (45085453105067/100000000000000 : ℝ)^4327
        have hw : |(328187589/625000000 : ℝ)|=(328187589/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(273751783/500000000 : ℝ)|^5351 ≤ (47476127804727/100000000000000 : ℝ)^4327
        have hw : |(273751783/500000000 : ℝ)|=(273751783/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1223040927/10000000000 : ℝ)|^5351 ≤ (7438419068459/100000000000000 : ℝ)^4327
        have hw : |(-1223040927/10000000000 : ℝ)|=(1223040927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1716_s1_7 (p : ℝ) (hpa : (5343/1024 : ℝ) ≤ p) (hpb : p ≤ (5351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4095153003/10000000000 : ℝ)*x 0 + (4618673819/10000000000 : ℝ)*x 1 + (112851633/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4095153003/10000000000 : ℝ)^5351 ≤ (1326088370027/4000000000000 : ℝ)^4327 := by
    have hnat : (4095153003 : ℕ)^5351*4000000000000^4327 ≤ 1326088370027^4327*10000000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4095153003 10000000000 1326088370027 4000000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4618673819/10000000000 : ℝ)^5351 ≤ (38470170568587/100000000000000 : ℝ)^4327 := by
    have hnat : (4618673819 : ℕ)^5351*100000000000000^4327 ≤ 38470170568587^4327*10000000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4618673819 10000000000 38470170568587 100000000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (112851633/312500000 : ℝ)^5351 ≤ (5675524032021/20000000000000 : ℝ)^4327 := by
    have hnat : (112851633 : ℕ)^5351*20000000000000^4327 ≤ 5675524032021^4327*312500000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112851633 312500000 5675524032021 20000000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5351/1024 : ℝ)) 5351 4327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4095153003/10000000000 : ℝ), (4618673819/10000000000 : ℝ), (112851633/312500000 : ℝ)] ![(1326088370027/4000000000000 : ℝ), (38470170568587/100000000000000 : ℝ), (5675524032021/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4095153003/10000000000 : ℝ)|^5351 ≤ (1326088370027/4000000000000 : ℝ)^4327
        have hw : |(4095153003/10000000000 : ℝ)|=(4095153003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4618673819/10000000000 : ℝ)|^5351 ≤ (38470170568587/100000000000000 : ℝ)^4327
        have hw : |(4618673819/10000000000 : ℝ)|=(4618673819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(112851633/312500000 : ℝ)|^5351 ≤ (5675524032021/20000000000000 : ℝ)^4327
        have hw : |(112851633/312500000 : ℝ)|=(112851633/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1716_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5343/1024 : ℝ) ≤ p) (hpb : p ≤ (5351/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (196947307/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (21701/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3111/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (4909/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (693/4000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (21701/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3111/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (21701/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3111/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (21701/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3111/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (21701/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3111/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (21701/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3111/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (21701/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3111/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3111/50000 : ℝ) ^ (5343/1024 : ℝ) ≤ (5093309010483/10000000000000000000 : ℝ) := by
    have hpowers : (3111/50000 : ℝ)^5343 ≤ (5093309010483/10000000000000000000 : ℝ)^1024 := by
      have hnat : (3111 : ℕ)^5343*10000000000000000000^1024 ≤ 5093309010483^1024*50000^5343 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3111 50000 5093309010483 10000000000000000000 5343 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3111/50000 : ℝ)) (X := (5093309010483/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5343 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (21701/100000 : ℝ) ^ (5343/1024 : ℝ) ≤ (6901311719019001/20000000000000000000 : ℝ) := by
    have hpowers : (21701/100000 : ℝ)^5343 ≤ (6901311719019001/20000000000000000000 : ℝ)^1024 := by
      have hnat : (21701 : ℕ)^5343*20000000000000000000^1024 ≤ 6901311719019001^1024*100000^5343 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21701 100000 6901311719019001 20000000000000000000 5343 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (21701/100000 : ℝ)) (X := (6901311719019001/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5343 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000005093309010483/5000000000000000000 : ℝ) ≤ (10000001952291327/10000000000000000 : ℝ) ^ (5343/1024 : ℝ) := by
    have hpowers : (5000005093309010483/5000000000000000000 : ℝ)^1024 ≤ (10000001952291327/10000000000000000 : ℝ)^5343 := by
      have hnat : (5000005093309010483 : ℕ)^1024*10000000000000000^5343 ≤ 10000001952291327^5343*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000005093309010483 5000000000000000000 10000001952291327 10000000000000000 1024 5343 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000001952291327/10000000000000000 : ℝ)) (X := (5000005093309010483/5000000000000000000 : ℝ)) (by norm_num) 5343 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20006911498337039967/20000000000000000000 : ℝ) ≤ (312520694091539/312500000000000 : ℝ) ^ (5343/1024 : ℝ) := by
    have hpowers : (20006911498337039967/20000000000000000000 : ℝ)^1024 ≤ (312520694091539/312500000000000 : ℝ)^5343 := by
      have hnat : (20006911498337039967 : ℕ)^1024*312500000000000^5343 ≤ 312520694091539^5343*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20006911498337039967 20000000000000000000 312520694091539 312500000000000 1024 5343 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312520694091539/312500000000000 : ℝ)) (X := (20006911498337039967/20000000000000000000 : ℝ)) (by norm_num) 5343 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006901311719019001/10000000000000000000 : ℝ) ≤ (10001322469567169/10000000000000000 : ℝ) ^ (5343/1024 : ℝ) := by
    have hpowers : (10006901311719019001/10000000000000000000 : ℝ)^1024 ≤ (10001322469567169/10000000000000000 : ℝ)^5343 := by
      have hnat : (10006901311719019001 : ℕ)^1024*10000000000000000^5343 ≤ 10001322469567169^5343*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006901311719019001 10000000000000000000 10001322469567169 10000000000000000 1024 5343 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001322469567169/10000000000000000 : ℝ)) (X := (10006901311719019001/10000000000000000000 : ℝ)) (by norm_num) 5343 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5093309010483/10000000000000000000 : ℝ) ≤ ((154781813961027161709/154790000000000000000 : ℝ)+2*(660258637921/1547900000000000 : ℝ)*(3111/50000 : ℝ))^(5343/1024 : ℝ) := by
    rw [show (154781813961027161709/154790000000000000000 : ℝ)+2*(660258637921/1547900000000000 : ℝ)*(3111/50000 : ℝ)=(10000001952291327/10000000000000000 : ℝ) by norm_num, show 1+2*(5093309010483/10000000000000000000 : ℝ)=(5000005093309010483/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6901311719019001/20000000000000000000 : ℝ)+(5093309010483/10000000000000000000 : ℝ) ≤ ((154781813961027161709/154790000000000000000 : ℝ)+(660258637921/1547900000000000 : ℝ)*((21701/100000 : ℝ)+(3111/50000 : ℝ)))^(5343/1024 : ℝ) := by
    rw [show (154781813961027161709/154790000000000000000 : ℝ)+(660258637921/1547900000000000 : ℝ)*((21701/100000 : ℝ)+(3111/50000 : ℝ))=(312520694091539/312500000000000 : ℝ) by norm_num, show 1+(6901311719019001/20000000000000000000 : ℝ)+(5093309010483/10000000000000000000 : ℝ)=(20006911498337039967/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6901311719019001/20000000000000000000 : ℝ) ≤ ((154781813961027161709/154790000000000000000 : ℝ)+2*(660258637921/1547900000000000 : ℝ)*(21701/100000 : ℝ))^(5343/1024 : ℝ) := by
    rw [show (154781813961027161709/154790000000000000000 : ℝ)+2*(660258637921/1547900000000000 : ℝ)*(21701/100000 : ℝ)=(10001322469567169/10000000000000000 : ℝ) by norm_num, show 1+2*(6901311719019001/20000000000000000000 : ℝ)=(10006901311719019001/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (154781813961027161709/154790000000000000000 : ℝ)*(X 1 0+X 2 0)+(660258637921/1547900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5343/1024 : ℝ)) (lo := (3111/50000 : ℝ)) (hi := (21701/100000 : ℝ)) (c := (154781813961027161709/154790000000000000000 : ℝ)) (alpha := (660258637921/1547900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (154781813961027161709/154790000000000000000 : ℝ)*(X 0 1+X 2 1)+(660258637921/1547900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5343/1024 : ℝ)) (lo := (3111/50000 : ℝ)) (hi := (21701/100000 : ℝ)) (c := (154781813961027161709/154790000000000000000 : ℝ)) (alpha := (660258637921/1547900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (154781813961027161709/154790000000000000000 : ℝ)*(X 0 2+X 1 2)+(660258637921/1547900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5343/1024 : ℝ)) (lo := (3111/50000 : ℝ)) (hi := (21701/100000 : ℝ)) (c := (154781813961027161709/154790000000000000000 : ℝ)) (alpha := (660258637921/1547900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-693754343/5000000000 : ℝ)*X 0 0+(5479298771/10000000000 : ℝ)*X 0 1+(5128059039/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1716_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345056963/10000000000 : ℝ)*X 1 0+(-785009379/5000000000 : ℝ)*X 1 1+(2564029011/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1716_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345055673/10000000000 : ℝ)*X 2 0+(256402953/500000000 : ℝ)*X 2 1+(-1570019109/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1716_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((511827183/1250000000 : ℝ)*X 0 0+(1799364439/5000000000 : ℝ)*X 0 1+(578875069/1250000000 : ℝ)*X 0 2+(511827183/1250000000 : ℝ)*X 1 0+(1799364439/5000000000 : ℝ)*X 1 1+(578875069/1250000000 : ℝ)*X 1 2+(511827183/1250000000 : ℝ)*X 2 0+(1799364439/5000000000 : ℝ)*X 2 1+(578875069/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1716_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1387692463/10000000000 : ℝ)*X 0 0+(5132252951/10000000000 : ℝ)*X 0 1+(5475036527/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1716_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((328187571/625000000 : ℝ)*X 1 0+(-1223040779/10000000000 : ℝ)*X 1 1+(109500721/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1716_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((328187589/625000000 : ℝ)*X 2 0+(273751783/500000000 : ℝ)*X 2 1+(-1223040927/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1716_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4095153003/10000000000 : ℝ)*X 0 0+(4618673819/10000000000 : ℝ)*X 0 1+(112851633/312500000 : ℝ)*X 0 2+(4095153003/10000000000 : ℝ)*X 1 0+(4618673819/10000000000 : ℝ)*X 1 1+(112851633/312500000 : ℝ)*X 1 2+(4095153003/10000000000 : ℝ)*X 2 0+(4618673819/10000000000 : ℝ)*X 2 1+(112851633/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1716_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1180606932330301980519357/77395000000000000000000000000 : ℝ) := by norm_num
    linear_combination (350664403/20000000000000 : ℝ)*(base19) + (532199691/50000000000000 : ℝ)*(base23) + (159000741/100000000000000 : ℝ)*(lower2) + (316922553/100000000000000 : ℝ)*(upper3) + (39510223/25000000000000 : ℝ)*(lower4) + (953955724830923/50000000000000 : ℝ)*(major0) + (953955724830923/50000000000000 : ℝ)*(major1) + (953955724830923/50000000000000 : ℝ)*(major2) + (711768291304519/25000000000000 : ℝ)*(sp0) + (711769637943507/25000000000000 : ℝ)*(sp1) + (1423539620348331/50000000000000 : ℝ)*(sp2) + (968739093726619/100000000000000 : ℝ)*(sp3) + (7139877967/100000000000000 : ℝ)*(sp4) + (748006047/25000000000000 : ℝ)*(sp7) + (121092760718851/12500000000000 : ℝ)*(f.failure) + (711770076274011/25000000000000 : ℝ)*(f.sum) + (209199207378419/77395000000000000000000000000 : ℝ)*base66 + (2619904148533472593/7739500000000000000000000000000000 : ℝ)*base68 + (50795812892547527407/7739500000000000000000000000000000 : ℝ)*base69 + (27853486463025027407/7739500000000000000000000000000000 : ℝ)*base71 + (10202846315329/19348750000000000000000000000 : ℝ)*base73 + (20370576521249027407/7739500000000000000000000000000000 : ℝ)*base75 + (59845160673573972593/7739500000000000000000000000000000 : ℝ)*base78 + (69113373431459972593/7739500000000000000000000000000000 : ℝ)*base80 + (61121593683907/9674375000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (13584257/1250000000000000000000 : ℝ)*base89 + (13584257/1250000000000000000000 : ℝ)*base91 + (13584257/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11497886039698398650008270503/1934875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (806474241/50000000000000 : ℝ)*(base19) + (2106878381/100000000000000 : ℝ)*(base23) + (2715243/1562500000000 : ℝ)*(upper2) + (97963581/50000000000000 : ℝ)*(upper3) + (73777959/25000000000000 : ℝ)*(upper5) + (488740616190311/25000000000000 : ℝ)*(major0) + (488740616190311/25000000000000 : ℝ)*(major1) + (488740616190311/25000000000000 : ℝ)*(major2) + (11377416671/100000000000000 : ℝ)*(sp1) + (11544440087/100000000000000 : ℝ)*(sp2) + (2917292491609863/100000000000000 : ℝ)*(sp4) + (291727950124471/10000000000000 : ℝ)*(sp5) + (583455768058279/20000000000000 : ℝ)*(sp6) + (248158059957789/25000000000000 : ℝ)*(sp7) + (248158059957789/25000000000000 : ℝ)*(f.failure) + (2917292491609863/100000000000000 : ℝ)*(f.sum) + (291545898745619/77395000000000000000000000000 : ℝ)*base65 + (25556037195388351499/3869750000000000000000000000000000 : ℝ)*base67 + (9852923172496648501/3869750000000000000000000000000000 : ℝ)*base70 + (1309399271060648501/3869750000000000000000000000000000 : ℝ)*base72 + (83083998151151/19348750000000000000000000000 : ℝ)*base73 + (7478083217048601499/3869750000000000000000000000000000 : ℝ)*base75 + (4715455918003851499/3869750000000000000000000000000000 : ℝ)*base77 + (21449349341350101499/3869750000000000000000000000000000 : ℝ)*base79 + (45000493961509/19348750000000000000000000000 : ℝ)*base82 + (22775777/2500000000000000000000 : ℝ)*base90 + (22775777/2500000000000000000000 : ℝ)*base92 + (22775777/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1716_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5343/1024 : ℝ) ≤ p) (hpb : p ≤ (5351/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (196947307/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (21701/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3111/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4909/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (693/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1716_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1716_s2_0 (p : ℝ) (hpa : (5343/1024 : ℝ) ≤ p) (hpb : p ≤ (5351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1390580129/10000000000 : ℝ)*x 0 + (5466649211/10000000000 : ℝ)*x 1 + (513864761/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1390580129/10000000000 : ℝ)^5351 ≤ (348730786367/4000000000000 : ℝ)^4327 := by
    have hnat : (1390580129 : ℕ)^5351*4000000000000^4327 ≤ 348730786367^4327*10000000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1390580129 10000000000 348730786367 4000000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5466649211/10000000000 : ℝ)^5351 ≤ (4738621205887/10000000000000 : ℝ)^4327 := by
    have hnat : (5466649211 : ℕ)^5351*10000000000000^4327 ≤ 4738621205887^4327*10000000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5466649211 10000000000 4738621205887 10000000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (513864761/1000000000 : ℝ)^5351 ≤ (43895518266529/100000000000000 : ℝ)^4327 := by
    have hnat : (513864761 : ℕ)^5351*100000000000000^4327 ≤ 43895518266529^4327*1000000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513864761 1000000000 43895518266529 100000000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5351/1024 : ℝ)) 5351 4327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1390580129/10000000000 : ℝ), (5466649211/10000000000 : ℝ), (513864761/1000000000 : ℝ)] ![(348730786367/4000000000000 : ℝ), (4738621205887/10000000000000 : ℝ), (43895518266529/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1390580129/10000000000 : ℝ)|^5351 ≤ (348730786367/4000000000000 : ℝ)^4327
        have hw : |(-1390580129/10000000000 : ℝ)|=(1390580129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5466649211/10000000000 : ℝ)|^5351 ≤ (4738621205887/10000000000000 : ℝ)^4327
        have hw : |(5466649211/10000000000 : ℝ)|=(5466649211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(513864761/1000000000 : ℝ)|^5351 ≤ (43895518266529/100000000000000 : ℝ)^4327
        have hw : |(513864761/1000000000 : ℝ)|=(513864761/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1716_s2_1 (p : ℝ) (hpa : (5343/1024 : ℝ) ≤ p) (hpb : p ≤ (5351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5341619793/10000000000 : ℝ)*x 0 + (-780294229/5000000000 : ℝ)*x 1 + (5138647613/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5341619793/10000000000 : ℝ)^5351 ≤ (4604959436943/10000000000000 : ℝ)^4327 := by
    have hnat : (5341619793 : ℕ)^5351*10000000000000^4327 ≤ 4604959436943^4327*10000000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5341619793 10000000000 4604959436943 10000000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (780294229/5000000000 : ℝ)^5351 ≤ (628430457097/6250000000000 : ℝ)^4327 := by
    have hnat : (780294229 : ℕ)^5351*6250000000000^4327 ≤ 628430457097^4327*5000000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      780294229 5000000000 628430457097 6250000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5138647613/10000000000 : ℝ)^5351 ≤ (2194775914911/5000000000000 : ℝ)^4327 := by
    have hnat : (5138647613 : ℕ)^5351*5000000000000^4327 ≤ 2194775914911^4327*10000000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5138647613 10000000000 2194775914911 5000000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5351/1024 : ℝ)) 5351 4327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5341619793/10000000000 : ℝ), (-780294229/5000000000 : ℝ), (5138647613/10000000000 : ℝ)] ![(4604959436943/10000000000000 : ℝ), (628430457097/6250000000000 : ℝ), (2194775914911/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5341619793/10000000000 : ℝ)|^5351 ≤ (4604959436943/10000000000000 : ℝ)^4327
        have hw : |(5341619793/10000000000 : ℝ)|=(5341619793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-780294229/5000000000 : ℝ)|^5351 ≤ (628430457097/6250000000000 : ℝ)^4327
        have hw : |(-780294229/5000000000 : ℝ)|=(780294229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5138647613/10000000000 : ℝ)|^5351 ≤ (2194775914911/5000000000000 : ℝ)^4327
        have hw : |(5138647613/10000000000 : ℝ)|=(5138647613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1716_s2_2 (p : ℝ) (hpa : (5343/1024 : ℝ) ≤ p) (hpb : p ≤ (5351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534161979/1000000000 : ℝ)*x 0 + (5138647611/10000000000 : ℝ)*x 1 + (-312117693/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534161979/1000000000 : ℝ)^5351 ≤ (23024797168723/50000000000000 : ℝ)^4327 := by
    have hnat : (534161979 : ℕ)^5351*50000000000000^4327 ≤ 23024797168723^4327*1000000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534161979 1000000000 23024797168723 50000000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5138647611/10000000000 : ℝ)^5351 ≤ (43895518277093/100000000000000 : ℝ)^4327 := by
    have hnat : (5138647611 : ℕ)^5351*100000000000000^4327 ≤ 43895518277093^4327*10000000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5138647611 10000000000 43895518277093 100000000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (312117693/2000000000 : ℝ)^5351 ≤ (10054887369327/100000000000000 : ℝ)^4327 := by
    have hnat : (312117693 : ℕ)^5351*100000000000000^4327 ≤ 10054887369327^4327*2000000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      312117693 2000000000 10054887369327 100000000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5351/1024 : ℝ)) 5351 4327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534161979/1000000000 : ℝ), (5138647611/10000000000 : ℝ), (-312117693/2000000000 : ℝ)] ![(23024797168723/50000000000000 : ℝ), (43895518277093/100000000000000 : ℝ), (10054887369327/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534161979/1000000000 : ℝ)|^5351 ≤ (23024797168723/50000000000000 : ℝ)^4327
        have hw : |(534161979/1000000000 : ℝ)|=(534161979/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5138647611/10000000000 : ℝ)|^5351 ≤ (43895518277093/100000000000000 : ℝ)^4327
        have hw : |(5138647611/10000000000 : ℝ)|=(5138647611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-312117693/2000000000 : ℝ)|^5351 ≤ (10054887369327/100000000000000 : ℝ)^4327
        have hw : |(-312117693/2000000000 : ℝ)|=(312117693/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1716_s2_3 (p : ℝ) (hpa : (5343/1024 : ℝ) ≤ p) (hpb : p ≤ (5351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4097001341/10000000000 : ℝ)*x 0 + (227041727/625000000 : ℝ)*x 1 + (114916167/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4097001341/10000000000 : ℝ)^5351 ≤ (33170714501727/100000000000000 : ℝ)^4327 := by
    have hnat : (4097001341 : ℕ)^5351*100000000000000^4327 ≤ 33170714501727^4327*10000000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4097001341 10000000000 33170714501727 100000000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (227041727/625000000 : ℝ)^5351 ≤ (14292937735061/50000000000000 : ℝ)^4327 := by
    have hnat : (227041727 : ℕ)^5351*50000000000000^4327 ≤ 14292937735061^4327*625000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      227041727 625000000 14292937735061 50000000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (114916167/250000000 : ℝ)^5351 ≤ (3824341000903/10000000000000 : ℝ)^4327 := by
    have hnat : (114916167 : ℕ)^5351*10000000000000^4327 ≤ 3824341000903^4327*250000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114916167 250000000 3824341000903 10000000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5351/1024 : ℝ)) 5351 4327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4097001341/10000000000 : ℝ), (227041727/625000000 : ℝ), (114916167/250000000 : ℝ)] ![(33170714501727/100000000000000 : ℝ), (14292937735061/50000000000000 : ℝ), (3824341000903/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4097001341/10000000000 : ℝ)|^5351 ≤ (33170714501727/100000000000000 : ℝ)^4327
        have hw : |(4097001341/10000000000 : ℝ)|=(4097001341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(227041727/625000000 : ℝ)|^5351 ≤ (14292937735061/50000000000000 : ℝ)^4327
        have hw : |(227041727/625000000 : ℝ)|=(227041727/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(114916167/250000000 : ℝ)|^5351 ≤ (3824341000903/10000000000000 : ℝ)^4327
        have hw : |(114916167/250000000 : ℝ)|=(114916167/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1716_s2_4 (p : ℝ) (hpa : (5343/1024 : ℝ) ≤ p) (hpb : p ≤ (5351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-695364219/5000000000 : ℝ)*x 0 + (160697119/312500000 : ℝ)*x 1 + (5462934347/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (695364219/5000000000 : ℝ)^5351 ≤ (272481860831/3125000000000 : ℝ)^4327 := by
    have hnat : (695364219 : ℕ)^5351*3125000000000^4327 ≤ 272481860831^4327*5000000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      695364219 5000000000 272481860831 3125000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (160697119/312500000 : ℝ)^5351 ≤ (43934187055869/100000000000000 : ℝ)^4327 := by
    have hnat : (160697119 : ℕ)^5351*100000000000000^4327 ≤ 43934187055869^4327*312500000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      160697119 312500000 43934187055869 100000000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5462934347/10000000000 : ℝ)^5351 ≤ (2959149586327/6250000000000 : ℝ)^4327 := by
    have hnat : (5462934347 : ℕ)^5351*6250000000000^4327 ≤ 2959149586327^4327*10000000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5462934347 10000000000 2959149586327 6250000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5351/1024 : ℝ)) 5351 4327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-695364219/5000000000 : ℝ), (160697119/312500000 : ℝ), (5462934347/10000000000 : ℝ)] ![(272481860831/3125000000000 : ℝ), (43934187055869/100000000000000 : ℝ), (2959149586327/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-695364219/5000000000 : ℝ)|^5351 ≤ (272481860831/3125000000000 : ℝ)^4327
        have hw : |(-695364219/5000000000 : ℝ)|=(695364219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(160697119/312500000 : ℝ)|^5351 ≤ (43934187055869/100000000000000 : ℝ)^4327
        have hw : |(160697119/312500000 : ℝ)|=(160697119/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5462934347/10000000000 : ℝ)|^5351 ≤ (2959149586327/6250000000000 : ℝ)^4327
        have hw : |(5462934347/10000000000 : ℝ)|=(5462934347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1716_s2_5 (p : ℝ) (hpa : (5343/1024 : ℝ) ≤ p) (hpb : p ≤ (5351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2626907179/5000000000 : ℝ)*x 0 + (-309075431/2500000000 : ℝ)*x 1 + (2731467173/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2626907179/5000000000 : ℝ)^5351 ≤ (45115322706307/100000000000000 : ℝ)^4327 := by
    have hnat : (2626907179 : ℕ)^5351*100000000000000^4327 ≤ 45115322706307^4327*5000000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626907179 5000000000 45115322706307 100000000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (309075431/2500000000 : ℝ)^5351 ≤ (3769141956483/50000000000000 : ℝ)^4327 := by
    have hnat : (309075431 : ℕ)^5351*50000000000000^4327 ≤ 3769141956483^4327*2500000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      309075431 2500000000 3769141956483 50000000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2731467173/5000000000 : ℝ)^5351 ≤ (23673196685257/50000000000000 : ℝ)^4327 := by
    have hnat : (2731467173 : ℕ)^5351*50000000000000^4327 ≤ 23673196685257^4327*5000000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2731467173 5000000000 23673196685257 50000000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5351/1024 : ℝ)) 5351 4327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2626907179/5000000000 : ℝ), (-309075431/2500000000 : ℝ), (2731467173/5000000000 : ℝ)] ![(45115322706307/100000000000000 : ℝ), (3769141956483/50000000000000 : ℝ), (23673196685257/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2626907179/5000000000 : ℝ)|^5351 ≤ (45115322706307/100000000000000 : ℝ)^4327
        have hw : |(2626907179/5000000000 : ℝ)|=(2626907179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-309075431/2500000000 : ℝ)|^5351 ≤ (3769141956483/50000000000000 : ℝ)^4327
        have hw : |(-309075431/2500000000 : ℝ)|=(309075431/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2731467173/5000000000 : ℝ)|^5351 ≤ (23673196685257/50000000000000 : ℝ)^4327
        have hw : |(2731467173/5000000000 : ℝ)|=(2731467173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1716_s2_6 (p : ℝ) (hpa : (5343/1024 : ℝ) ≤ p) (hpb : p ≤ (5351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1313453589/2500000000 : ℝ)*x 0 + (1365733587/2500000000 : ℝ)*x 1 + (-1236301723/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1313453589/2500000000 : ℝ)^5351 ≤ (11278830671267/25000000000000 : ℝ)^4327 := by
    have hnat : (1313453589 : ℕ)^5351*25000000000000^4327 ≤ 11278830671267^4327*2500000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313453589 2500000000 11278830671267 25000000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1365733587/2500000000 : ℝ)^5351 ≤ (946927867839/2000000000000 : ℝ)^4327 := by
    have hnat : (1365733587 : ℕ)^5351*2000000000000^4327 ≤ 946927867839^4327*2500000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1365733587 2500000000 946927867839 2000000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1236301723/10000000000 : ℝ)^5351 ≤ (3769141952713/50000000000000 : ℝ)^4327 := by
    have hnat : (1236301723 : ℕ)^5351*50000000000000^4327 ≤ 3769141952713^4327*10000000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1236301723 10000000000 3769141952713 50000000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5351/1024 : ℝ)) 5351 4327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1313453589/2500000000 : ℝ), (1365733587/2500000000 : ℝ), (-1236301723/10000000000 : ℝ)] ![(11278830671267/25000000000000 : ℝ), (946927867839/2000000000000 : ℝ), (3769141952713/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1313453589/2500000000 : ℝ)|^5351 ≤ (11278830671267/25000000000000 : ℝ)^4327
        have hw : |(1313453589/2500000000 : ℝ)|=(1313453589/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1365733587/2500000000 : ℝ)|^5351 ≤ (946927867839/2000000000000 : ℝ)^4327
        have hw : |(1365733587/2500000000 : ℝ)|=(1365733587/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1236301723/10000000000 : ℝ)|^5351 ≤ (3769141952713/50000000000000 : ℝ)^4327
        have hw : |(-1236301723/10000000000 : ℝ)|=(1236301723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1716_s2_7 (p : ℝ) (hpa : (5343/1024 : ℝ) ≤ p) (hpb : p ≤ (5351/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2048718611/5000000000 : ℝ)*x 0 + (1146472387/2500000000 : ℝ)*x 1 + (182179271/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2048718611/5000000000 : ℝ)^5351 ≤ (16587539378683/50000000000000 : ℝ)^4327 := by
    have hnat : (2048718611 : ℕ)^5351*50000000000000^4327 ≤ 16587539378683^4327*5000000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2048718611 5000000000 16587539378683 50000000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1146472387/2500000000 : ℝ)^5351 ≤ (9533190749197/25000000000000 : ℝ)^4327 := by
    have hnat : (1146472387 : ℕ)^5351*25000000000000^4327 ≤ 9533190749197^4327*2500000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1146472387 2500000000 9533190749197 25000000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (182179271/500000000 : ℝ)^5351 ≤ (28692158235661/100000000000000 : ℝ)^4327 := by
    have hnat : (182179271 : ℕ)^5351*100000000000000^4327 ≤ 28692158235661^4327*500000000^5351 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      182179271 500000000 28692158235661 100000000000000 5351 4327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5351/1024 : ℝ)) 5351 4327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2048718611/5000000000 : ℝ), (1146472387/2500000000 : ℝ), (182179271/500000000 : ℝ)] ![(16587539378683/50000000000000 : ℝ), (9533190749197/25000000000000 : ℝ), (28692158235661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2048718611/5000000000 : ℝ)|^5351 ≤ (16587539378683/50000000000000 : ℝ)^4327
        have hw : |(2048718611/5000000000 : ℝ)|=(2048718611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1146472387/2500000000 : ℝ)|^5351 ≤ (9533190749197/25000000000000 : ℝ)^4327
        have hw : |(1146472387/2500000000 : ℝ)|=(1146472387/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(182179271/500000000 : ℝ)|^5351 ≤ (28692158235661/100000000000000 : ℝ)^4327
        have hw : |(182179271/500000000 : ℝ)|=(182179271/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1716_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5343/1024 : ℝ) ≤ p) (hpb : p ≤ (5351/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (196947307/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (693/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4909/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10049/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17059/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (693/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4909/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (693/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4909/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (693/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4909/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (693/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4909/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (693/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4909/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (693/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4909/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4909/50000 : ℝ) ^ (5343/1024 : ℝ) ≤ (275153177837471/50000000000000000000 : ℝ) := by
    have hpowers : (4909/50000 : ℝ)^5343 ≤ (275153177837471/50000000000000000000 : ℝ)^1024 := by
      have hnat : (4909 : ℕ)^5343*50000000000000000000^1024 ≤ 275153177837471^1024*50000^5343 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4909 50000 275153177837471 50000000000000000000 5343 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4909/50000 : ℝ)) (X := (275153177837471/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5343 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (693/4000 : ℝ) ^ (5343/1024 : ℝ) ≤ (10655392981255061/100000000000000000000 : ℝ) := by
    have hpowers : (693/4000 : ℝ)^5343 ≤ (10655392981255061/100000000000000000000 : ℝ)^1024 := by
      have hnat : (693 : ℕ)^5343*100000000000000000000^1024 ≤ 10655392981255061^1024*4000^5343 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        693 4000 10655392981255061 100000000000000000000 5343 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (693/4000 : ℝ)) (X := (10655392981255061/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5343 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000275153177837471/25000000000000000000 : ℝ) ≤ (50000105467191/50000000000000 : ℝ) ^ (5343/1024 : ℝ) := by
    have hpowers : (25000275153177837471/25000000000000000000 : ℝ)^1024 ≤ (50000105467191/50000000000000 : ℝ)^5343 := by
      have hnat : (25000275153177837471 : ℕ)^1024*50000000000000^5343 ≤ 50000105467191^5343*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000275153177837471 25000000000000000000 50000105467191 50000000000000 1024 5343 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (50000105467191/50000000000000 : ℝ)) (X := (25000275153177837471/25000000000000000000 : ℝ)) (by norm_num) 5343 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100011205699336930003/100000000000000000000 : ℝ) ≤ (10000214750448517/10000000000000000 : ℝ) ^ (5343/1024 : ℝ) := by
    have hpowers : (100011205699336930003/100000000000000000000 : ℝ)^1024 ≤ (10000214750448517/10000000000000000 : ℝ)^5343 := by
      have hnat : (100011205699336930003 : ℕ)^1024*10000000000000000^5343 ≤ 10000214750448517^5343*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100011205699336930003 100000000000000000000 10000214750448517 10000000000000000 1024 5343 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000214750448517/10000000000000000 : ℝ)) (X := (100011205699336930003/100000000000000000000 : ℝ)) (by norm_num) 5343 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50010655392981255061/50000000000000000000 : ℝ) ≤ (5000204203729417/5000000000000000 : ℝ) ^ (5343/1024 : ℝ) := by
    have hpowers : (50010655392981255061/50000000000000000000 : ℝ)^1024 ≤ (5000204203729417/5000000000000000 : ℝ)^5343 := by
      have hnat : (50010655392981255061 : ℕ)^1024*5000000000000000^5343 ≤ 5000204203729417^5343*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010655392981255061 50000000000000000000 5000204203729417 5000000000000000 1024 5343 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000204203729417/5000000000000000 : ℝ)) (X := (50010655392981255061/50000000000000000000 : ℝ)) (by norm_num) 5343 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(275153177837471/50000000000000000000 : ℝ) ≤ ((18766588924846495697/18767500000000000000 : ℝ)+2*(193657010317/750700000000000 : ℝ)*(4909/50000 : ℝ))^(5343/1024 : ℝ) := by
    rw [show (18766588924846495697/18767500000000000000 : ℝ)+2*(193657010317/750700000000000 : ℝ)*(4909/50000 : ℝ)=(50000105467191/50000000000000 : ℝ) by norm_num, show 1+2*(275153177837471/50000000000000000000 : ℝ)=(25000275153177837471/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10655392981255061/100000000000000000000 : ℝ)+(275153177837471/50000000000000000000 : ℝ) ≤ ((18766588924846495697/18767500000000000000 : ℝ)+(193657010317/750700000000000 : ℝ)*((693/4000 : ℝ)+(4909/50000 : ℝ)))^(5343/1024 : ℝ) := by
    rw [show (18766588924846495697/18767500000000000000 : ℝ)+(193657010317/750700000000000 : ℝ)*((693/4000 : ℝ)+(4909/50000 : ℝ))=(10000214750448517/10000000000000000 : ℝ) by norm_num, show 1+(10655392981255061/100000000000000000000 : ℝ)+(275153177837471/50000000000000000000 : ℝ)=(100011205699336930003/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10655392981255061/100000000000000000000 : ℝ) ≤ ((18766588924846495697/18767500000000000000 : ℝ)+2*(193657010317/750700000000000 : ℝ)*(693/4000 : ℝ))^(5343/1024 : ℝ) := by
    rw [show (18766588924846495697/18767500000000000000 : ℝ)+2*(193657010317/750700000000000 : ℝ)*(693/4000 : ℝ)=(5000204203729417/5000000000000000 : ℝ) by norm_num, show 1+2*(10655392981255061/100000000000000000000 : ℝ)=(50010655392981255061/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18766588924846495697/18767500000000000000 : ℝ)*(X 1 0+X 2 0)+(193657010317/750700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5343/1024 : ℝ)) (lo := (4909/50000 : ℝ)) (hi := (693/4000 : ℝ)) (c := (18766588924846495697/18767500000000000000 : ℝ)) (alpha := (193657010317/750700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18766588924846495697/18767500000000000000 : ℝ)*(X 0 1+X 2 1)+(193657010317/750700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5343/1024 : ℝ)) (lo := (4909/50000 : ℝ)) (hi := (693/4000 : ℝ)) (c := (18766588924846495697/18767500000000000000 : ℝ)) (alpha := (193657010317/750700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18766588924846495697/18767500000000000000 : ℝ)*(X 0 2+X 1 2)+(193657010317/750700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5343/1024 : ℝ)) (lo := (4909/50000 : ℝ)) (hi := (693/4000 : ℝ)) (c := (18766588924846495697/18767500000000000000 : ℝ)) (alpha := (193657010317/750700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1390580129/10000000000 : ℝ)*X 0 0+(5466649211/10000000000 : ℝ)*X 0 1+(513864761/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1716_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5341619793/10000000000 : ℝ)*X 1 0+(-780294229/5000000000 : ℝ)*X 1 1+(5138647613/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1716_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534161979/1000000000 : ℝ)*X 2 0+(5138647611/10000000000 : ℝ)*X 2 1+(-312117693/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1716_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4097001341/10000000000 : ℝ)*X 0 0+(227041727/625000000 : ℝ)*X 0 1+(114916167/250000000 : ℝ)*X 0 2+(4097001341/10000000000 : ℝ)*X 1 0+(227041727/625000000 : ℝ)*X 1 1+(114916167/250000000 : ℝ)*X 1 2+(4097001341/10000000000 : ℝ)*X 2 0+(227041727/625000000 : ℝ)*X 2 1+(114916167/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1716_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-695364219/5000000000 : ℝ)*X 0 0+(160697119/312500000 : ℝ)*X 0 1+(5462934347/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1716_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2626907179/5000000000 : ℝ)*X 1 0+(-309075431/2500000000 : ℝ)*X 1 1+(2731467173/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1716_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1313453589/2500000000 : ℝ)*X 2 0+(1365733587/2500000000 : ℝ)*X 2 1+(-1236301723/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1716_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2048718611/5000000000 : ℝ)*X 0 0+(1146472387/2500000000 : ℝ)*X 0 1+(182179271/500000000 : ℝ)*X 0 2+(2048718611/5000000000 : ℝ)*X 1 0+(1146472387/2500000000 : ℝ)*X 1 1+(182179271/500000000 : ℝ)*X 1 2+(2048718611/5000000000 : ℝ)*X 2 0+(1146472387/2500000000 : ℝ)*X 2 1+(182179271/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1716_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4932641239656599460307225449/469187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1536051791/100000000000000 : ℝ)*(base19) + (288799633/20000000000000 : ℝ)*(base23) + (12064227/25000000000000 : ℝ)*(lower2) + (16027009/6250000000000 : ℝ)*(upper3) + (187339497/100000000000000 : ℝ)*(upper5) + (1021543536701813/50000000000000 : ℝ)*(major0) + (1021543536701813/50000000000000 : ℝ)*(major1) + (1021543536701813/50000000000000 : ℝ)*(major2) + (152439056843983/5000000000000 : ℝ)*(sp0) + (121951789930727/4000000000000 : ℝ)*(sp1) + (3048794840321801/100000000000000 : ℝ)*(sp2) + (1037371892522453/100000000000000 : ℝ)*(sp3) + (7573720153/50000000000000 : ℝ)*(sp4) + (5619526303/100000000000000 : ℝ)*(sp7) + (259344378012189/25000000000000 : ℝ)*(f.failure) + (1524398142159983/50000000000000 : ℝ)*(f.sum) + (59447390358043/37535000000000000000000000000 : ℝ)*base66 + (5964406716472376339/938375000000000000000000000000000 : ℝ)*base68 + (5861871638177126339/938375000000000000000000000000000 : ℝ)*base70 + (2593451862555126339/938375000000000000000000000000000 : ℝ)*base72 + (7827872259237/2345937500000000000000000000 : ℝ)*base73 + (4784066774671001339/938375000000000000000000000000000 : ℝ)*base76 + (8353248298880751339/938375000000000000000000000000000 : ℝ)*base78 + (2287112059200001339/938375000000000000000000000000000 : ℝ)*base80 + (136311850497717/37535000000000000000000000000 : ℝ)*base81 + (13274977/2500000000000000000000 : ℝ)*base90 + (13274977/2500000000000000000000 : ℝ)*base92 + (13274977/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (531337685628585091288384587/58648437500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1240305931/100000000000000 : ℝ)*(base19) + (1333959367/100000000000000 : ℝ)*(base23) + (48435823/25000000000000 : ℝ)*(upper3) + (21215199/50000000000000 : ℝ)*(lower4) + (94573741/50000000000000 : ℝ)*(upper5) + (261257591646513/12500000000000 : ℝ)*(major0) + (261257591646513/12500000000000 : ℝ)*(major1) + (261257591646513/12500000000000 : ℝ)*(major2) + (11368943761/100000000000000 : ℝ)*(sp1) + (3052848133/25000000000000 : ℝ)*(sp2) + (3118892775396033/100000000000000 : ℝ)*(sp4) + (1559440083073171/50000000000000 : ℝ)*(sp5) + (1559439615022067/50000000000000 : ℝ)*(sp6) + (530614194478959/50000000000000 : ℝ)*(sp7) + (530614194478959/50000000000000 : ℝ)*(f.failure) + (3118892775396033/100000000000000 : ℝ)*(f.sum) + (101474331267501/18767500000000000000000000000 : ℝ)*base66 + (1539420855581670439/234593750000000000000000000000000 : ℝ)*base68 + (2535701635659201689/234593750000000000000000000000000 : ℝ)*base70 + (4173649905779764189/234593750000000000000000000000000 : ℝ)*base72 + (16084075060081/18767500000000000000000000000 : ℝ)*base74 + (3184285175366014189/234593750000000000000000000000000 : ℝ)*base76 + (2700860038749295439/234593750000000000000000000000000 : ℝ)*base78 + (118118204336045439/234593750000000000000000000000000 : ℝ)*base80 + (74494773001731/18767500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (43213413/5000000000000000000000 : ℝ)*base89 + (43213413/5000000000000000000000 : ℝ)*base91 + (43213413/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1716_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5343/1024 : ℝ) ≤ p) (hpb : p ≤ (5351/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (196947307/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (693/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4909/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10049/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17059/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1716_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1716_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5343/1024 : ℝ) ≤ p) (hpb : p ≤ (5351/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (196947307/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10049/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17059/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1716_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1716_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1716_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5343/1024 : ℝ) ≤ p) (hpb : p ≤ (5351/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (196947307/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10049/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17059/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1716_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
