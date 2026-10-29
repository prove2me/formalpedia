-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1514_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:55:48.75359+00:00
-- url     : https://prove2.me/submissions/84f8e4e2-c78a-4540-93ec-d07c0242c8e0

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
theorem support_rectangle_w1514_s6_0 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-186506723/1000000000 : ℝ)*x 0 + (2716486301/5000000000 : ℝ)*x 1 + (5217737311/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (186506723/1000000000 : ℝ)^4525 ≤ (11412518209357/100000000000000 : ℝ)^3501 := by
    have hnat : (186506723 : ℕ)^4525*100000000000000^3501 ≤ 11412518209357^3501*1000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      186506723 1000000000 11412518209357 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2716486301/5000000000 : ℝ)^4525 ≤ (710164944341/1562500000000 : ℝ)^3501 := by
    have hnat : (2716486301 : ℕ)^4525*1562500000000^3501 ≤ 710164944341^3501*5000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716486301 5000000000 710164944341 1562500000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5217737311/10000000000 : ℝ)^4525 ≤ (43136925341339/100000000000000 : ℝ)^3501 := by
    have hnat : (5217737311 : ℕ)^4525*100000000000000^3501 ≤ 43136925341339^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217737311 10000000000 43136925341339 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-186506723/1000000000 : ℝ), (2716486301/5000000000 : ℝ), (5217737311/10000000000 : ℝ)] ![(11412518209357/100000000000000 : ℝ), (710164944341/1562500000000 : ℝ), (43136925341339/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-186506723/1000000000 : ℝ)|^4525 ≤ (11412518209357/100000000000000 : ℝ)^3501
        have hw : |(-186506723/1000000000 : ℝ)|=(186506723/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2716486301/5000000000 : ℝ)|^4525 ≤ (710164944341/1562500000000 : ℝ)^3501
        have hw : |(2716486301/5000000000 : ℝ)|=(2716486301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5217737311/10000000000 : ℝ)|^4525 ≤ (43136925341339/100000000000000 : ℝ)^3501
        have hw : |(5217737311/10000000000 : ℝ)|=(5217737311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1514_s6_1 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334467429/625000000 : ℝ)*x 0 + (-395059019/2000000000 : ℝ)*x 1 + (1304434491/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334467429/625000000 : ℝ)^4525 ≤ (22285670534269/50000000000000 : ℝ)^3501 := by
    have hnat : (334467429 : ℕ)^4525*50000000000000^3501 ≤ 22285670534269^3501*625000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334467429 625000000 22285670534269 50000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (395059019/2000000000 : ℝ)^4525 ≤ (12291726593079/100000000000000 : ℝ)^3501 := by
    have hnat : (395059019 : ℕ)^4525*100000000000000^3501 ≤ 12291726593079^3501*2000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      395059019 2000000000 12291726593079 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1304434491/2500000000 : ℝ)^4525 ≤ (10784233079737/25000000000000 : ℝ)^3501 := by
    have hnat : (1304434491 : ℕ)^4525*25000000000000^3501 ≤ 10784233079737^3501*2500000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304434491 2500000000 10784233079737 25000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334467429/625000000 : ℝ), (-395059019/2000000000 : ℝ), (1304434491/2500000000 : ℝ)] ![(22285670534269/50000000000000 : ℝ), (12291726593079/100000000000000 : ℝ), (10784233079737/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334467429/625000000 : ℝ)|^4525 ≤ (22285670534269/50000000000000 : ℝ)^3501
        have hw : |(334467429/625000000 : ℝ)|=(334467429/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-395059019/2000000000 : ℝ)|^4525 ≤ (12291726593079/100000000000000 : ℝ)^3501
        have hw : |(-395059019/2000000000 : ℝ)|=(395059019/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1304434491/2500000000 : ℝ)|^4525 ≤ (10784233079737/25000000000000 : ℝ)^3501
        have hw : |(1304434491/2500000000 : ℝ)|=(1304434491/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1514_s6_2 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351478677/10000000000 : ℝ)*x 0 + (1043547651/2000000000 : ℝ)*x 1 + (-987647479/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351478677/10000000000 : ℝ)^4525 ≤ (4457133905551/10000000000000 : ℝ)^3501 := by
    have hnat : (5351478677 : ℕ)^4525*10000000000000^3501 ≤ 4457133905551^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351478677 10000000000 4457133905551 10000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043547651/2000000000 : ℝ)^4525 ≤ (43136935428419/100000000000000 : ℝ)^3501 := by
    have hnat : (1043547651 : ℕ)^4525*100000000000000^3501 ≤ 43136935428419^3501*2000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043547651 2000000000 43136935428419 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (987647479/5000000000 : ℝ)^4525 ≤ (2458345098243/20000000000000 : ℝ)^3501 := by
    have hnat : (987647479 : ℕ)^4525*20000000000000^3501 ≤ 2458345098243^3501*5000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      987647479 5000000000 2458345098243 20000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351478677/10000000000 : ℝ), (1043547651/2000000000 : ℝ), (-987647479/5000000000 : ℝ)] ![(4457133905551/10000000000000 : ℝ), (43136935428419/100000000000000 : ℝ), (2458345098243/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351478677/10000000000 : ℝ)|^4525 ≤ (4457133905551/10000000000000 : ℝ)^3501
        have hw : |(5351478677/10000000000 : ℝ)|=(5351478677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043547651/2000000000 : ℝ)|^4525 ≤ (43136935428419/100000000000000 : ℝ)^3501
        have hw : |(1043547651/2000000000 : ℝ)|=(1043547651/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-987647479/5000000000 : ℝ)|^4525 ≤ (2458345098243/20000000000000 : ℝ)^3501
        have hw : |(-987647479/5000000000 : ℝ)|=(987647479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1514_s6_3 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (533605291/1250000000 : ℝ)*x 0 + (2015197739/5000000000 : ℝ)*x 1 + (4519145287/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (533605291/1250000000 : ℝ)^4525 ≤ (16639884779187/50000000000000 : ℝ)^3501 := by
    have hnat : (533605291 : ℕ)^4525*50000000000000^3501 ≤ 16639884779187^3501*1250000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533605291 1250000000 16639884779187 50000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2015197739/5000000000 : ℝ)^4525 ≤ (3089702363759/10000000000000 : ℝ)^3501 := by
    have hnat : (2015197739 : ℕ)^4525*10000000000000^3501 ≤ 3089702363759^3501*5000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2015197739 5000000000 3089702363759 10000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4519145287/10000000000 : ℝ)^4525 ≤ (223895042441/625000000000 : ℝ)^3501 := by
    have hnat : (4519145287 : ℕ)^4525*625000000000^3501 ≤ 223895042441^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4519145287 10000000000 223895042441 625000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(533605291/1250000000 : ℝ), (2015197739/5000000000 : ℝ), (4519145287/10000000000 : ℝ)] ![(16639884779187/50000000000000 : ℝ), (3089702363759/10000000000000 : ℝ), (223895042441/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(533605291/1250000000 : ℝ)|^4525 ≤ (16639884779187/50000000000000 : ℝ)^3501
        have hw : |(533605291/1250000000 : ℝ)|=(533605291/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2015197739/5000000000 : ℝ)|^4525 ≤ (3089702363759/10000000000000 : ℝ)^3501
        have hw : |(2015197739/5000000000 : ℝ)|=(2015197739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4519145287/10000000000 : ℝ)|^4525 ≤ (223895042441/625000000000 : ℝ)^3501
        have hw : |(4519145287/10000000000 : ℝ)|=(4519145287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1514_s6_4 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1865096007/10000000000 : ℝ)*x 0 + (1304711557/2500000000 : ℝ)*x 1 + (5431855601/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1865096007/10000000000 : ℝ)^4525 ≤ (11412745802913/100000000000000 : ℝ)^3501 := by
    have hnat : (1865096007 : ℕ)^4525*100000000000000^3501 ≤ 11412745802913^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1865096007 10000000000 11412745802913 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1304711557/2500000000 : ℝ)^4525 ≤ (43148775004023/100000000000000 : ℝ)^3501 := by
    have hnat : (1304711557 : ℕ)^4525*100000000000000^3501 ≤ 43148775004023^3501*2500000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304711557 2500000000 43148775004023 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5431855601/10000000000 : ℝ)^4525 ≤ (22719239585443/50000000000000 : ℝ)^3501 := by
    have hnat : (5431855601 : ℕ)^4525*50000000000000^3501 ≤ 22719239585443^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431855601 10000000000 22719239585443 50000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1865096007/10000000000 : ℝ), (1304711557/2500000000 : ℝ), (5431855601/10000000000 : ℝ)] ![(11412745802913/100000000000000 : ℝ), (43148775004023/100000000000000 : ℝ), (22719239585443/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1865096007/10000000000 : ℝ)|^4525 ≤ (11412745802913/100000000000000 : ℝ)^3501
        have hw : |(-1865096007/10000000000 : ℝ)|=(1865096007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1304711557/2500000000 : ℝ)|^4525 ≤ (43148775004023/100000000000000 : ℝ)^3501
        have hw : |(1304711557/2500000000 : ℝ)|=(1304711557/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5431855601/10000000000 : ℝ)|^4525 ≤ (22719239585443/50000000000000 : ℝ)^3501
        have hw : |(5431855601/10000000000 : ℝ)|=(5431855601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1514_s6_5 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (661870013/1250000000 : ℝ)*x 0 + (-880588653/5000000000 : ℝ)*x 1 + (5431855841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661870013/1250000000 : ℝ)^4525 ≤ (21981933318093/50000000000000 : ℝ)^3501 := by
    have hnat : (661870013 : ℕ)^4525*50000000000000^3501 ≤ 21981933318093^3501*1250000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661870013 1250000000 21981933318093 50000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (880588653/5000000000 : ℝ)^4525 ≤ (10597651583399/100000000000000 : ℝ)^3501 := by
    have hnat : (880588653 : ℕ)^4525*100000000000000^3501 ≤ 10597651583399^3501*5000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      880588653 5000000000 10597651583399 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5431855841/10000000000 : ℝ)^4525 ≤ (22719240882871/50000000000000 : ℝ)^3501 := by
    have hnat : (5431855841 : ℕ)^4525*50000000000000^3501 ≤ 22719240882871^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431855841 10000000000 22719240882871 50000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661870013/1250000000 : ℝ), (-880588653/5000000000 : ℝ), (5431855841/10000000000 : ℝ)] ![(21981933318093/50000000000000 : ℝ), (10597651583399/100000000000000 : ℝ), (22719240882871/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661870013/1250000000 : ℝ)|^4525 ≤ (21981933318093/50000000000000 : ℝ)^3501
        have hw : |(661870013/1250000000 : ℝ)|=(661870013/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-880588653/5000000000 : ℝ)|^4525 ≤ (10597651583399/100000000000000 : ℝ)^3501
        have hw : |(-880588653/5000000000 : ℝ)|=(880588653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5431855841/10000000000 : ℝ)|^4525 ≤ (22719240882871/50000000000000 : ℝ)^3501
        have hw : |(5431855841/10000000000 : ℝ)|=(5431855841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1514_s6_6 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294960339/10000000000 : ℝ)*x 0 + (2715927891/5000000000 : ℝ)*x 1 + (-1761177063/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294960339/10000000000 : ℝ)^4525 ≤ (10990967289521/25000000000000 : ℝ)^3501 := by
    have hnat : (5294960339 : ℕ)^4525*25000000000000^3501 ≤ 10990967289521^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294960339 10000000000 10990967289521 25000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2715927891/5000000000 : ℝ)^4525 ≤ (283990507049/625000000000 : ℝ)^3501 := by
    have hnat : (2715927891 : ℕ)^4525*625000000000^3501 ≤ 283990507049^3501*5000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2715927891 5000000000 283990507049 625000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1761177063/10000000000 : ℝ)^4525 ≤ (10597649693497/100000000000000 : ℝ)^3501 := by
    have hnat : (1761177063 : ℕ)^4525*100000000000000^3501 ≤ 10597649693497^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1761177063 10000000000 10597649693497 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294960339/10000000000 : ℝ), (2715927891/5000000000 : ℝ), (-1761177063/10000000000 : ℝ)] ![(10990967289521/25000000000000 : ℝ), (283990507049/625000000000 : ℝ), (10597649693497/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294960339/10000000000 : ℝ)|^4525 ≤ (10990967289521/25000000000000 : ℝ)^3501
        have hw : |(5294960339/10000000000 : ℝ)|=(5294960339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2715927891/5000000000 : ℝ)|^4525 ≤ (283990507049/625000000000 : ℝ)^3501
        have hw : |(2715927891/5000000000 : ℝ)|=(2715927891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1761177063/10000000000 : ℝ)|^4525 ≤ (10597649693497/100000000000000 : ℝ)^3501
        have hw : |(-1761177063/10000000000 : ℝ)|=(1761177063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1514_s6_7 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (533613459/1250000000 : ℝ)*x 0 + (4516628941/10000000000 : ℝ)*x 1 + (2016465297/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (533613459/1250000000 : ℝ)^4525 ≤ (16640213989447/50000000000000 : ℝ)^3501 := by
    have hnat : (533613459 : ℕ)^4525*50000000000000^3501 ≤ 16640213989447^3501*1250000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533613459 1250000000 16640213989447 50000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4516628941/10000000000 : ℝ)^4525 ≤ (17898713789977/50000000000000 : ℝ)^3501 := by
    have hnat : (4516628941 : ℕ)^4525*50000000000000^3501 ≤ 17898713789977^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4516628941 10000000000 17898713789977 50000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2016465297/5000000000 : ℝ)^4525 ≤ (247377155393/800000000000 : ℝ)^3501 := by
    have hnat : (2016465297 : ℕ)^4525*800000000000^3501 ≤ 247377155393^3501*5000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2016465297 5000000000 247377155393 800000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(533613459/1250000000 : ℝ), (4516628941/10000000000 : ℝ), (2016465297/5000000000 : ℝ)] ![(16640213989447/50000000000000 : ℝ), (17898713789977/50000000000000 : ℝ), (247377155393/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(533613459/1250000000 : ℝ)|^4525 ≤ (16640213989447/50000000000000 : ℝ)^3501
        have hw : |(533613459/1250000000 : ℝ)|=(533613459/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4516628941/10000000000 : ℝ)|^4525 ≤ (17898713789977/50000000000000 : ℝ)^3501
        have hw : |(4516628941/10000000000 : ℝ)|=(4516628941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2016465297/5000000000 : ℝ)|^4525 ≤ (247377155393/800000000000 : ℝ)^3501
        have hw : |(2016465297/5000000000 : ℝ)|=(2016465297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1514_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163539063/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10923/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2731/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7741/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15483/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10923/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15483/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10923/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15483/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10923/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15483/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10923/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15483/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10923/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15483/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10923/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10923/100000 : ℝ) ^ (4523/1024 : ℝ) ≤ (2827052269390331/50000000000000000000 : ℝ) := by
    have hpowers : (10923/100000 : ℝ)^4523 ≤ (2827052269390331/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10923 : ℕ)^4523*50000000000000000000^1024 ≤ 2827052269390331^1024*100000^4523 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10923 100000 2827052269390331 50000000000000000000 4523 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10923/100000 : ℝ)) (X := (2827052269390331/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4523 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15483/100000 : ℝ) ^ (4523/1024 : ℝ) ≤ (5279908088920501/20000000000000000000 : ℝ) := by
    have hpowers : (15483/100000 : ℝ)^4523 ≤ (5279908088920501/20000000000000000000 : ℝ)^1024 := by
      have hnat : (15483 : ℕ)^4523*20000000000000000000^1024 ≤ 5279908088920501^1024*100000^4523 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15483 100000 5279908088920501 20000000000000000000 4523 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15483/100000 : ℝ)) (X := (5279908088920501/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4523 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002827052269390331/25000000000000000000 : ℝ) ≤ (2500064001213987/2500000000000000 : ℝ) ^ (4523/1024 : ℝ) := by
    have hpowers : (25002827052269390331/25000000000000000000 : ℝ)^1024 ≤ (2500064001213987/2500000000000000 : ℝ)^4523 := by
      have hnat : (25002827052269390331 : ℕ)^1024*2500000000000000^4523 ≤ 2500064001213987^4523*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002827052269390331 25000000000000000000 2500064001213987 2500000000000000 1024 4523 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500064001213987/2500000000000000 : ℝ)) (X := (25002827052269390331/25000000000000000000 : ℝ)) (by norm_num) 4523 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100032053644983383167/100000000000000000000 : ℝ) ≤ (2500181399865817/2500000000000000 : ℝ) ^ (4523/1024 : ℝ) := by
    have hpowers : (100032053644983383167/100000000000000000000 : ℝ)^1024 ≤ (2500181399865817/2500000000000000 : ℝ)^4523 := by
      have hnat : (100032053644983383167 : ℕ)^1024*2500000000000000^4523 ≤ 2500181399865817^4523*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100032053644983383167 100000000000000000000 2500181399865817 2500000000000000 1024 4523 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500181399865817/2500000000000000 : ℝ)) (X := (100032053644983383167/100000000000000000000 : ℝ)) (by norm_num) 4523 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10005279908088920501/10000000000000000000 : ℝ) ≤ (2500298798517647/2500000000000000 : ℝ) ^ (4523/1024 : ℝ) := by
    have hpowers : (10005279908088920501/10000000000000000000 : ℝ)^1024 ≤ (2500298798517647/2500000000000000 : ℝ)^4523 := by
      have hnat : (10005279908088920501 : ℕ)^1024*2500000000000000^4523 ≤ 2500298798517647^4523*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005279908088920501 10000000000000000000 2500298798517647 2500000000000000 1024 4523 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500298798517647/2500000000000000 : ℝ)) (X := (10005279908088920501/10000000000000000000 : ℝ)) (by norm_num) 4523 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2827052269390331/50000000000000000000 : ℝ) ≤ ((189962119243131709/190000000000000000 : ℝ)+2*(11739865183/11400000000000 : ℝ)*(10923/100000 : ℝ))^(4523/1024 : ℝ) := by
    rw [show (189962119243131709/190000000000000000 : ℝ)+2*(11739865183/11400000000000 : ℝ)*(10923/100000 : ℝ)=(2500064001213987/2500000000000000 : ℝ) by norm_num, show 1+2*(2827052269390331/50000000000000000000 : ℝ)=(25002827052269390331/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5279908088920501/20000000000000000000 : ℝ)+(2827052269390331/50000000000000000000 : ℝ) ≤ ((189962119243131709/190000000000000000 : ℝ)+(11739865183/11400000000000 : ℝ)*((15483/100000 : ℝ)+(10923/100000 : ℝ)))^(4523/1024 : ℝ) := by
    rw [show (189962119243131709/190000000000000000 : ℝ)+(11739865183/11400000000000 : ℝ)*((15483/100000 : ℝ)+(10923/100000 : ℝ))=(2500181399865817/2500000000000000 : ℝ) by norm_num, show 1+(5279908088920501/20000000000000000000 : ℝ)+(2827052269390331/50000000000000000000 : ℝ)=(100032053644983383167/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5279908088920501/20000000000000000000 : ℝ) ≤ ((189962119243131709/190000000000000000 : ℝ)+2*(11739865183/11400000000000 : ℝ)*(15483/100000 : ℝ))^(4523/1024 : ℝ) := by
    rw [show (189962119243131709/190000000000000000 : ℝ)+2*(11739865183/11400000000000 : ℝ)*(15483/100000 : ℝ)=(2500298798517647/2500000000000000 : ℝ) by norm_num, show 1+2*(5279908088920501/20000000000000000000 : ℝ)=(10005279908088920501/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (189962119243131709/190000000000000000 : ℝ)*(X 1 0+X 2 0)+(11739865183/11400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4523/1024 : ℝ)) (lo := (10923/100000 : ℝ)) (hi := (15483/100000 : ℝ)) (c := (189962119243131709/190000000000000000 : ℝ)) (alpha := (11739865183/11400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (189962119243131709/190000000000000000 : ℝ)*(X 0 1+X 2 1)+(11739865183/11400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4523/1024 : ℝ)) (lo := (10923/100000 : ℝ)) (hi := (15483/100000 : ℝ)) (c := (189962119243131709/190000000000000000 : ℝ)) (alpha := (11739865183/11400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (189962119243131709/190000000000000000 : ℝ)*(X 0 2+X 1 2)+(11739865183/11400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4523/1024 : ℝ)) (lo := (10923/100000 : ℝ)) (hi := (15483/100000 : ℝ)) (c := (189962119243131709/190000000000000000 : ℝ)) (alpha := (11739865183/11400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-186506723/1000000000 : ℝ)*X 0 0+(2716486301/5000000000 : ℝ)*X 0 1+(5217737311/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334467429/625000000 : ℝ)*X 1 0+(-395059019/2000000000 : ℝ)*X 1 1+(1304434491/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351478677/10000000000 : ℝ)*X 2 0+(1043547651/2000000000 : ℝ)*X 2 1+(-987647479/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((533605291/1250000000 : ℝ)*X 0 0+(2015197739/5000000000 : ℝ)*X 0 1+(4519145287/10000000000 : ℝ)*X 0 2+(533605291/1250000000 : ℝ)*X 1 0+(2015197739/5000000000 : ℝ)*X 1 1+(4519145287/10000000000 : ℝ)*X 1 2+(533605291/1250000000 : ℝ)*X 2 0+(2015197739/5000000000 : ℝ)*X 2 1+(4519145287/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1865096007/10000000000 : ℝ)*X 0 0+(1304711557/2500000000 : ℝ)*X 0 1+(5431855601/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((661870013/1250000000 : ℝ)*X 1 0+(-880588653/5000000000 : ℝ)*X 1 1+(5431855841/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5294960339/10000000000 : ℝ)*X 2 0+(2715927891/5000000000 : ℝ)*X 2 1+(-1761177063/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((533613459/1250000000 : ℝ)*X 0 0+(4516628941/10000000000 : ℝ)*X 0 1+(2016465297/5000000000 : ℝ)*X 0 2+(533613459/1250000000 : ℝ)*X 1 0+(4516628941/10000000000 : ℝ)*X 1 1+(2016465297/5000000000 : ℝ)*X 1 2+(533613459/1250000000 : ℝ)*X 2 0+(4516628941/10000000000 : ℝ)*X 2 1+(2016465297/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2571842324969520627916121/950000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (856484339/100000000000000 : ℝ)*(base19) + (303783819/50000000000000 : ℝ)*(base23) + (94752047/50000000000000 : ℝ)*(upper3) + (4632471/10000000000000 : ℝ)*(upper4) + (117126077/50000000000000 : ℝ)*(upper5) + (334608641775541/10000000000000 : ℝ)*(major0) + (334608641775541/10000000000000 : ℝ)*(major1) + (334608641775541/10000000000000 : ℝ)*(major2) + (4646101098064747/100000000000000 : ℝ)*(sp0) + (4646124689802853/100000000000000 : ℝ)*(sp1) + (2323062469359777/50000000000000 : ℝ)*(sp2) + (15984704576549/781250000000 : ℝ)*(sp3) + (4889644489/20000000000000 : ℝ)*(sp4) + (5013185259/100000000000000 : ℝ)*(sp7) + (204604719898353/10000000000000 : ℝ)*(f.failure) + (580765693285899/12500000000000 : ℝ)*(f.sum) + (134912887/89062500000000000000000 : ℝ)*base65 + (116239900483961293/5700000000000000000000000000000 : ℝ)*base68 + (137871707047061293/5700000000000000000000000000000 : ℝ)*base70 + (101605830875861293/5700000000000000000000000000000 : ℝ)*base72 + (245113166897/57000000000000000000000000 : ℝ)*base74 + (121289104768061293/5700000000000000000000000000000 : ℝ)*base76 + (105923871952061293/5700000000000000000000000000000 : ℝ)*base78 + (193509608445161293/5700000000000000000000000000000 : ℝ)*base80 + (417547314143/57000000000000000000000000 : ℝ)*base82 + (4863239/1000000000000000000000 : ℝ)*base89 + (4863239/1000000000000000000000 : ℝ)*base91 + (4863239/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12891315379478980896404359/2375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (516717881/50000000000000 : ℝ)*(base19) + (1402500599/100000000000000 : ℝ)*(base23) + (307916071/100000000000000 : ℝ)*(lower1) + (3812581/12500000000000 : ℝ)*(upper2) + (276842977/100000000000000 : ℝ)*(upper3) + (160409453/100000000000000 : ℝ)*(upper5) + (1690503032331383/50000000000000 : ℝ)*(major0) + (1690503032331383/50000000000000 : ℝ)*(major1) + (1690503032331383/50000000000000 : ℝ)*(major2) + (9659582677/100000000000000 : ℝ)*(sp2) + (2347306134342379/50000000000000 : ℝ)*(sp4) + (1173652808812249/25000000000000 : ℝ)*(sp5) + (2347300603300741/50000000000000 : ℝ)*(sp6) + (1033699839855009/50000000000000 : ℝ)*(sp7) + (1033699839855009/50000000000000 : ℝ)*(f.failure) + (2347306134342379/50000000000000 : ℝ)*(f.sum) + (19549352939/285000000000000000000000000 : ℝ)*base65 + (102195734896820641/28500000000000000000000000000000 : ℝ)*base67 + (68055684988820641/28500000000000000000000000000000 : ℝ)*base69 + (380170772233820641/28500000000000000000000000000000 : ℝ)*base71 + (973404718081/285000000000000000000000000 : ℝ)*base74 + (56385463234179359/28500000000000000000000000000000 : ℝ)*base76 + (251161385658320641/28500000000000000000000000000000 : ℝ)*base77 + (504607619949320641/28500000000000000000000000000000 : ℝ)*base79 + (4201341678511/285000000000000000000000000 : ℝ)*base82 + (72283433/5000000000000000000000 : ℝ)*base90 + (72283433/5000000000000000000000 : ℝ)*base92 + (72283433/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1514_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163539063/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10923/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2731/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1514_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1514_box_0 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-82589963/500000000 : ℝ)*x 0 + (540261577/1000000000 : ℝ)*x 1 + (2701307863/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (82589963/500000000 : ℝ)^4525 ≤ (9754820030859/100000000000000 : ℝ)^3501 := by
    have hnat : (82589963 : ℕ)^4525*100000000000000^3501 ≤ 9754820030859^3501*500000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82589963 500000000 9754820030859 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (540261577/1000000000 : ℝ)^4525 ≤ (45122590216833/100000000000000 : ℝ)^3501 := by
    have hnat : (540261577 : ℕ)^4525*100000000000000^3501 ≤ 45122590216833^3501*1000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540261577 1000000000 45122590216833 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2701307863/5000000000 : ℝ)^4525 ≤ (45122589741859/100000000000000 : ℝ)^3501 := by
    have hnat : (2701307863 : ℕ)^4525*100000000000000^3501 ≤ 45122589741859^3501*5000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701307863 5000000000 45122589741859 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-82589963/500000000 : ℝ), (540261577/1000000000 : ℝ), (2701307863/5000000000 : ℝ)] ![(9754820030859/100000000000000 : ℝ), (45122590216833/100000000000000 : ℝ), (45122589741859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-82589963/500000000 : ℝ)|^4525 ≤ (9754820030859/100000000000000 : ℝ)^3501
        have hw : |(-82589963/500000000 : ℝ)|=(82589963/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(540261577/1000000000 : ℝ)|^4525 ≤ (45122590216833/100000000000000 : ℝ)^3501
        have hw : |(540261577/1000000000 : ℝ)|=(540261577/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2701307863/5000000000 : ℝ)|^4525 ≤ (45122589741859/100000000000000 : ℝ)^3501
        have hw : |(2701307863/5000000000 : ℝ)|=(2701307863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1514_box_1 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1054160693/2000000000 : ℝ)*x 0 + (-366932063/2000000000 : ℝ)*x 1 + (1080523089/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1054160693/2000000000 : ℝ)^4525 ≤ (10926200817557/25000000000000 : ℝ)^3501 := by
    have hnat : (1054160693 : ℕ)^4525*25000000000000^3501 ≤ 10926200817557^3501*2000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054160693 2000000000 10926200817557 25000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (366932063/2000000000 : ℝ)^4525 ≤ (11172610008613/100000000000000 : ℝ)^3501 := by
    have hnat : (366932063 : ℕ)^4525*100000000000000^3501 ≤ 11172610008613^3501*2000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      366932063 2000000000 11172610008613 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1080523089/2000000000 : ℝ)^4525 ≤ (11280646677127/25000000000000 : ℝ)^3501 := by
    have hnat : (1080523089 : ℕ)^4525*25000000000000^3501 ≤ 11280646677127^3501*2000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080523089 2000000000 11280646677127 25000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1054160693/2000000000 : ℝ), (-366932063/2000000000 : ℝ), (1080523089/2000000000 : ℝ)] ![(10926200817557/25000000000000 : ℝ), (11172610008613/100000000000000 : ℝ), (11280646677127/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1054160693/2000000000 : ℝ)|^4525 ≤ (10926200817557/25000000000000 : ℝ)^3501
        have hw : |(1054160693/2000000000 : ℝ)|=(1054160693/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-366932063/2000000000 : ℝ)|^4525 ≤ (11172610008613/100000000000000 : ℝ)^3501
        have hw : |(-366932063/2000000000 : ℝ)|=(366932063/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1080523089/2000000000 : ℝ)|^4525 ≤ (11280646677127/25000000000000 : ℝ)^3501
        have hw : |(1080523089/2000000000 : ℝ)|=(1080523089/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1514_box_2 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5270803119/10000000000 : ℝ)*x 0 + (216104639/400000000 : ℝ)*x 1 + (-1834660059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5270803119/10000000000 : ℝ)^4525 ≤ (21852399781049/50000000000000 : ℝ)^3501 := by
    have hnat : (5270803119 : ℕ)^4525*50000000000000^3501 ≤ 21852399781049^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5270803119 10000000000 21852399781049 50000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216104639/400000000 : ℝ)^4525 ≤ (2820162026861/6250000000000 : ℝ)^3501 := by
    have hnat : (216104639 : ℕ)^4525*6250000000000^3501 ≤ 2820162026861^3501*400000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216104639 400000000 2820162026861 6250000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1834660059/10000000000 : ℝ)^4525 ≤ (5586303996829/50000000000000 : ℝ)^3501 := by
    have hnat : (1834660059 : ℕ)^4525*50000000000000^3501 ≤ 5586303996829^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1834660059 10000000000 5586303996829 50000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5270803119/10000000000 : ℝ), (216104639/400000000 : ℝ), (-1834660059/10000000000 : ℝ)] ![(21852399781049/50000000000000 : ℝ), (2820162026861/6250000000000 : ℝ), (5586303996829/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5270803119/10000000000 : ℝ)|^4525 ≤ (21852399781049/50000000000000 : ℝ)^3501
        have hw : |(5270803119/10000000000 : ℝ)|=(5270803119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(216104639/400000000 : ℝ)|^4525 ≤ (2820162026861/6250000000000 : ℝ)^3501
        have hw : |(216104639/400000000 : ℝ)|=(216104639/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1834660059/10000000000 : ℝ)|^4525 ≤ (5586303996829/50000000000000 : ℝ)^3501
        have hw : |(-1834660059/10000000000 : ℝ)|=(1834660059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1514_box_3 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (44718123/100000000 : ℝ)*x 0 + (815298/1953125 : ℝ)*x 1 + (834865079/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (44718123/100000000 : ℝ)^4525 ≤ (4417374961633/12500000000000 : ℝ)^3501 := by
    have hnat : (44718123 : ℕ)^4525*12500000000000^3501 ≤ 4417374961633^3501*100000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44718123 100000000 4417374961633 12500000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (815298/1953125 : ℝ)^4525 ≤ (32330501971859/100000000000000 : ℝ)^3501 := by
    have hnat : (815298 : ℕ)^4525*100000000000000^3501 ≤ 32330501971859^3501*1953125^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      815298 1953125 32330501971859 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (834865079/2000000000 : ℝ)^4525 ≤ (32330498318053/100000000000000 : ℝ)^3501 := by
    have hnat : (834865079 : ℕ)^4525*100000000000000^3501 ≤ 32330498318053^3501*2000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      834865079 2000000000 32330498318053 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(44718123/100000000 : ℝ), (815298/1953125 : ℝ), (834865079/2000000000 : ℝ)] ![(4417374961633/12500000000000 : ℝ), (32330501971859/100000000000000 : ℝ), (32330498318053/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(44718123/100000000 : ℝ)|^4525 ≤ (4417374961633/12500000000000 : ℝ)^3501
        have hw : |(44718123/100000000 : ℝ)|=(44718123/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(815298/1953125 : ℝ)|^4525 ≤ (32330501971859/100000000000000 : ℝ)^3501
        have hw : |(815298/1953125 : ℝ)|=(815298/1953125 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(834865079/2000000000 : ℝ)|^4525 ≤ (32330498318053/100000000000000 : ℝ)^3501
        have hw : |(834865079/2000000000 : ℝ)|=(834865079/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1514_box_4 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2083771997/10000000000 : ℝ)*x 0 + (1048738281/2000000000 : ℝ)*x 1 + (5243689541/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2083771997/10000000000 : ℝ)^4525 ≤ (6585551543867/50000000000000 : ℝ)^3501 := by
    have hnat : (2083771997 : ℕ)^4525*50000000000000^3501 ≤ 6585551543867^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2083771997 10000000000 6585551543867 50000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048738281/2000000000 : ℝ)^4525 ≤ (21707229213449/50000000000000 : ℝ)^3501 := by
    have hnat : (1048738281 : ℕ)^4525*50000000000000^3501 ≤ 21707229213449^3501*2000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048738281 2000000000 21707229213449 50000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243689541/10000000000 : ℝ)^4525 ≤ (5426804810033/12500000000000 : ℝ)^3501 := by
    have hnat : (5243689541 : ℕ)^4525*12500000000000^3501 ≤ 5426804810033^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243689541 10000000000 5426804810033 12500000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2083771997/10000000000 : ℝ), (1048738281/2000000000 : ℝ), (5243689541/10000000000 : ℝ)] ![(6585551543867/50000000000000 : ℝ), (21707229213449/50000000000000 : ℝ), (5426804810033/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2083771997/10000000000 : ℝ)|^4525 ≤ (6585551543867/50000000000000 : ℝ)^3501
        have hw : |(-2083771997/10000000000 : ℝ)|=(2083771997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048738281/2000000000 : ℝ)|^4525 ≤ (21707229213449/50000000000000 : ℝ)^3501
        have hw : |(1048738281/2000000000 : ℝ)|=(1048738281/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243689541/10000000000 : ℝ)|^4525 ≤ (5426804810033/12500000000000 : ℝ)^3501
        have hw : |(5243689541/10000000000 : ℝ)|=(5243689541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1514_box_5 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2690716271/5000000000 : ℝ)*x 0 + (-1900244477/10000000000 : ℝ)*x 1 + (262184551/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2690716271/5000000000 : ℝ)^4525 ≤ (44894051796061/100000000000000 : ℝ)^3501 := by
    have hnat : (2690716271 : ℕ)^4525*100000000000000^3501 ≤ 44894051796061^3501*5000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2690716271 5000000000 44894051796061 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1900244477/10000000000 : ℝ)^4525 ≤ (2922873467879/25000000000000 : ℝ)^3501 := by
    have hnat : (1900244477 : ℕ)^4525*25000000000000^3501 ≤ 2922873467879^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1900244477 10000000000 2922873467879 25000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262184551/500000000 : ℝ)^4525 ≤ (43414454307019/100000000000000 : ℝ)^3501 := by
    have hnat : (262184551 : ℕ)^4525*100000000000000^3501 ≤ 43414454307019^3501*500000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262184551 500000000 43414454307019 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2690716271/5000000000 : ℝ), (-1900244477/10000000000 : ℝ), (262184551/500000000 : ℝ)] ![(44894051796061/100000000000000 : ℝ), (2922873467879/25000000000000 : ℝ), (43414454307019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2690716271/5000000000 : ℝ)|^4525 ≤ (44894051796061/100000000000000 : ℝ)^3501
        have hw : |(2690716271/5000000000 : ℝ)|=(2690716271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1900244477/10000000000 : ℝ)|^4525 ≤ (2922873467879/25000000000000 : ℝ)^3501
        have hw : |(-1900244477/10000000000 : ℝ)|=(1900244477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(262184551/500000000 : ℝ)|^4525 ≤ (43414454307019/100000000000000 : ℝ)^3501
        have hw : |(262184551/500000000 : ℝ)|=(262184551/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1514_box_6 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5381434401/10000000000 : ℝ)*x 0 + (327730571/625000000 : ℝ)*x 1 + (-475061123/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5381434401/10000000000 : ℝ)^4525 ≤ (44894071840633/100000000000000 : ℝ)^3501 := by
    have hnat : (5381434401 : ℕ)^4525*100000000000000^3501 ≤ 44894071840633^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5381434401 10000000000 44894071840633 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (327730571/625000000 : ℝ)^4525 ≤ (8682886829273/20000000000000 : ℝ)^3501 := by
    have hnat : (327730571 : ℕ)^4525*20000000000000^3501 ≤ 8682886829273^3501*625000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327730571 625000000 8682886829273 20000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (475061123/2500000000 : ℝ)^4525 ≤ (11691493990799/100000000000000 : ℝ)^3501 := by
    have hnat : (475061123 : ℕ)^4525*100000000000000^3501 ≤ 11691493990799^3501*2500000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      475061123 2500000000 11691493990799 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5381434401/10000000000 : ℝ), (327730571/625000000 : ℝ), (-475061123/2500000000 : ℝ)] ![(44894071840633/100000000000000 : ℝ), (8682886829273/20000000000000 : ℝ), (11691493990799/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5381434401/10000000000 : ℝ)|^4525 ≤ (44894071840633/100000000000000 : ℝ)^3501
        have hw : |(5381434401/10000000000 : ℝ)|=(5381434401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(327730571/625000000 : ℝ)|^4525 ≤ (8682886829273/20000000000000 : ℝ)^3501
        have hw : |(327730571/625000000 : ℝ)|=(327730571/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-475061123/2500000000 : ℝ)|^4525 ≤ (11691493990799/100000000000000 : ℝ)^3501
        have hw : |(-475061123/2500000000 : ℝ)|=(475061123/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1514_box_7 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4063442349/10000000000 : ℝ)*x 0 + (218918817/500000000 : ℝ)*x 1 + (4378376699/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4063442349/10000000000 : ℝ)^4525 ≤ (390310638019/1250000000000 : ℝ)^3501 := by
    have hnat : (4063442349 : ℕ)^4525*1250000000000^3501 ≤ 390310638019^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4063442349 10000000000 390310638019 1250000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (218918817/500000000 : ℝ)^4525 ≤ (34387572644183/100000000000000 : ℝ)^3501 := by
    have hnat : (218918817 : ℕ)^4525*100000000000000^3501 ≤ 34387572644183^3501*500000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218918817 500000000 34387572644183 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4378376699/10000000000 : ℝ)^4525 ≤ (34387576288443/100000000000000 : ℝ)^3501 := by
    have hnat : (4378376699 : ℕ)^4525*100000000000000^3501 ≤ 34387576288443^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4378376699 10000000000 34387576288443 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4063442349/10000000000 : ℝ), (218918817/500000000 : ℝ), (4378376699/10000000000 : ℝ)] ![(390310638019/1250000000000 : ℝ), (34387572644183/100000000000000 : ℝ), (34387576288443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4063442349/10000000000 : ℝ)|^4525 ≤ (390310638019/1250000000000 : ℝ)^3501
        have hw : |(4063442349/10000000000 : ℝ)|=(4063442349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(218918817/500000000 : ℝ)|^4525 ≤ (34387572644183/100000000000000 : ℝ)^3501
        have hw : |(218918817/500000000 : ℝ)|=(218918817/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4378376699/10000000000 : ℝ)|^4525 ≤ (34387576288443/100000000000000 : ℝ)^3501
        have hw : |(4378376699/10000000000 : ℝ)|=(4378376699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1514_box_8 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-398495089/2000000000 : ℝ)*x 0 + (5132328491/10000000000 : ℝ)*x 1 + (2711531377/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (398495089/2000000000 : ℝ)^4525 ≤ (2486016029337/20000000000000 : ℝ)^3501 := by
    have hnat : (398495089 : ℕ)^4525*20000000000000^3501 ≤ 2486016029337^3501*2000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      398495089 2000000000 2486016029337 20000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5132328491/10000000000 : ℝ)^4525 ≤ (42226485543591/100000000000000 : ℝ)^3501 := by
    have hnat : (5132328491 : ℕ)^4525*100000000000000^3501 ≤ 42226485543591^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5132328491 10000000000 42226485543591 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2711531377/5000000000 : ℝ)^4525 ≤ (22671717148747/50000000000000 : ℝ)^3501 := by
    have hnat : (2711531377 : ℕ)^4525*50000000000000^3501 ≤ 22671717148747^3501*5000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711531377 5000000000 22671717148747 50000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-398495089/2000000000 : ℝ), (5132328491/10000000000 : ℝ), (2711531377/5000000000 : ℝ)] ![(2486016029337/20000000000000 : ℝ), (42226485543591/100000000000000 : ℝ), (22671717148747/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-398495089/2000000000 : ℝ)|^4525 ≤ (2486016029337/20000000000000 : ℝ)^3501
        have hw : |(-398495089/2000000000 : ℝ)|=(398495089/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5132328491/10000000000 : ℝ)|^4525 ≤ (42226485543591/100000000000000 : ℝ)^3501
        have hw : |(5132328491/10000000000 : ℝ)|=(5132328491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2711531377/5000000000 : ℝ)|^4525 ≤ (22671717148747/50000000000000 : ℝ)^3501
        have hw : |(2711531377/5000000000 : ℝ)|=(2711531377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1514_box_9 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1314141007/2500000000 : ℝ)*x 0 + (-1825976647/10000000000 : ℝ)*x 1 + (2711531339/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1314141007/2500000000 : ℝ)^4525 ≤ (10888064397819/25000000000000 : ℝ)^3501 := by
    have hnat : (1314141007 : ℕ)^4525*25000000000000^3501 ≤ 10888064397819^3501*2500000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314141007 2500000000 10888064397819 25000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1825976647/10000000000 : ℝ)^4525 ≤ (5552154461921/50000000000000 : ℝ)^3501 := by
    have hnat : (1825976647 : ℕ)^4525*50000000000000^3501 ≤ 5552154461921^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1825976647 10000000000 5552154461921 50000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2711531339/5000000000 : ℝ)^4525 ≤ (45343433476179/100000000000000 : ℝ)^3501 := by
    have hnat : (2711531339 : ℕ)^4525*100000000000000^3501 ≤ 45343433476179^3501*5000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711531339 5000000000 45343433476179 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1314141007/2500000000 : ℝ), (-1825976647/10000000000 : ℝ), (2711531339/5000000000 : ℝ)] ![(10888064397819/25000000000000 : ℝ), (5552154461921/50000000000000 : ℝ), (45343433476179/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1314141007/2500000000 : ℝ)|^4525 ≤ (10888064397819/25000000000000 : ℝ)^3501
        have hw : |(1314141007/2500000000 : ℝ)|=(1314141007/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1825976647/10000000000 : ℝ)|^4525 ≤ (5552154461921/50000000000000 : ℝ)^3501
        have hw : |(-1825976647/10000000000 : ℝ)|=(1825976647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2711531339/5000000000 : ℝ)|^4525 ≤ (45343433476179/100000000000000 : ℝ)^3501
        have hw : |(2711531339/5000000000 : ℝ)|=(2711531339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1514_box_10 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (262828219/500000000 : ℝ)*x 0 + (2711531019/5000000000 : ℝ)*x 1 + (-912988523/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (262828219/500000000 : ℝ)^4525 ≤ (1742090454429/4000000000000 : ℝ)^3501 := by
    have hnat : (262828219 : ℕ)^4525*4000000000000^3501 ≤ 1742090454429^3501*500000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262828219 500000000 1742090454429 4000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2711531019/5000000000 : ℝ)^4525 ≤ (45343426559841/100000000000000 : ℝ)^3501 := by
    have hnat : (2711531019 : ℕ)^4525*100000000000000^3501 ≤ 45343426559841^3501*5000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711531019 5000000000 45343426559841 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (912988523/5000000000 : ℝ)^4525 ≤ (11104312059983/100000000000000 : ℝ)^3501 := by
    have hnat : (912988523 : ℕ)^4525*100000000000000^3501 ≤ 11104312059983^3501*5000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      912988523 5000000000 11104312059983 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(262828219/500000000 : ℝ), (2711531019/5000000000 : ℝ), (-912988523/5000000000 : ℝ)] ![(1742090454429/4000000000000 : ℝ), (45343426559841/100000000000000 : ℝ), (11104312059983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(262828219/500000000 : ℝ)|^4525 ≤ (1742090454429/4000000000000 : ℝ)^3501
        have hw : |(262828219/500000000 : ℝ)|=(262828219/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2711531019/5000000000 : ℝ)|^4525 ≤ (45343426559841/100000000000000 : ℝ)^3501
        have hw : |(2711531019/5000000000 : ℝ)|=(2711531019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-912988523/5000000000 : ℝ)|^4525 ≤ (11104312059983/100000000000000 : ℝ)^3501
        have hw : |(-912988523/5000000000 : ℝ)|=(912988523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1514_box_11 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (56540013/125000000 : ℝ)*x 0 + (1037010029/2500000000 : ℝ)*x 1 + (2074020363/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (56540013/125000000 : ℝ)^4525 ≤ (35864765601349/100000000000000 : ℝ)^3501 := by
    have hnat : (56540013 : ℕ)^4525*100000000000000^3501 ≤ 35864765601349^3501*125000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56540013 125000000 35864765601349 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1037010029/2500000000 : ℝ)^4525 ≤ (128270456561/400000000000 : ℝ)^3501 := by
    have hnat : (1037010029 : ℕ)^4525*400000000000^3501 ≤ 128270456561^3501*2500000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037010029 2500000000 128270456561 400000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2074020363/5000000000 : ℝ)^4525 ≤ (16033810117669/50000000000000 : ℝ)^3501 := by
    have hnat : (2074020363 : ℕ)^4525*50000000000000^3501 ≤ 16033810117669^3501*5000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2074020363 5000000000 16033810117669 50000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(56540013/125000000 : ℝ), (1037010029/2500000000 : ℝ), (2074020363/5000000000 : ℝ)] ![(35864765601349/100000000000000 : ℝ), (128270456561/400000000000 : ℝ), (16033810117669/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(56540013/125000000 : ℝ)|^4525 ≤ (35864765601349/100000000000000 : ℝ)^3501
        have hw : |(56540013/125000000 : ℝ)|=(56540013/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1037010029/2500000000 : ℝ)|^4525 ≤ (128270456561/400000000000 : ℝ)^3501
        have hw : |(1037010029/2500000000 : ℝ)|=(1037010029/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2074020363/5000000000 : ℝ)|^4525 ≤ (16033810117669/50000000000000 : ℝ)^3501
        have hw : |(2074020363/5000000000 : ℝ)|=(2074020363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1514_box_12 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1743036313/10000000000 : ℝ)*x 0 + (2755202089/5000000000 : ℝ)*x 1 + (5228661971/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1743036313/10000000000 : ℝ)^4525 ≤ (5228387667327/50000000000000 : ℝ)^3501 := by
    have hnat : (1743036313 : ℕ)^4525*50000000000000^3501 ≤ 5228387667327^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1743036313 10000000000 5228387667327 50000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2755202089/5000000000 : ℝ)^4525 ≤ (23144764248463/50000000000000 : ℝ)^3501 := by
    have hnat : (2755202089 : ℕ)^4525*50000000000000^3501 ≤ 23144764248463^3501*5000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2755202089 5000000000 23144764248463 50000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5228661971/10000000000 : ℝ)^4525 ≤ (43253696146059/100000000000000 : ℝ)^3501 := by
    have hnat : (5228661971 : ℕ)^4525*100000000000000^3501 ≤ 43253696146059^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5228661971 10000000000 43253696146059 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1743036313/10000000000 : ℝ), (2755202089/5000000000 : ℝ), (5228661971/10000000000 : ℝ)] ![(5228387667327/50000000000000 : ℝ), (23144764248463/50000000000000 : ℝ), (43253696146059/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1743036313/10000000000 : ℝ)|^4525 ≤ (5228387667327/50000000000000 : ℝ)^3501
        have hw : |(-1743036313/10000000000 : ℝ)|=(1743036313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2755202089/5000000000 : ℝ)|^4525 ≤ (23144764248463/50000000000000 : ℝ)^3501
        have hw : |(2755202089/5000000000 : ℝ)|=(2755202089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5228661971/10000000000 : ℝ)|^4525 ≤ (43253696146059/100000000000000 : ℝ)^3501
        have hw : |(5228661971/10000000000 : ℝ)|=(5228661971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1514_box_13 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (673986873/1250000000 : ℝ)*x 0 + (-1906266939/10000000000 : ℝ)*x 1 + (5228662103/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (673986873/1250000000 : ℝ)^4525 ≤ (9001378918749/20000000000000 : ℝ)^3501 := by
    have hnat : (673986873 : ℕ)^4525*20000000000000^3501 ≤ 9001378918749^3501*1250000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673986873 1250000000 9001378918749 20000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1906266939/10000000000 : ℝ)^4525 ≤ (11739407842317/100000000000000 : ℝ)^3501 := by
    have hnat : (1906266939 : ℕ)^4525*100000000000000^3501 ≤ 11739407842317^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1906266939 10000000000 11739407842317 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5228662103/10000000000 : ℝ)^4525 ≤ (43253697557403/100000000000000 : ℝ)^3501 := by
    have hnat : (5228662103 : ℕ)^4525*100000000000000^3501 ≤ 43253697557403^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5228662103 10000000000 43253697557403 100000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(673986873/1250000000 : ℝ), (-1906266939/10000000000 : ℝ), (5228662103/10000000000 : ℝ)] ![(9001378918749/20000000000000 : ℝ), (11739407842317/100000000000000 : ℝ), (43253697557403/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(673986873/1250000000 : ℝ)|^4525 ≤ (9001378918749/20000000000000 : ℝ)^3501
        have hw : |(673986873/1250000000 : ℝ)|=(673986873/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1906266939/10000000000 : ℝ)|^4525 ≤ (11739407842317/100000000000000 : ℝ)^3501
        have hw : |(-1906266939/10000000000 : ℝ)|=(1906266939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5228662103/10000000000 : ℝ)|^4525 ≤ (43253697557403/100000000000000 : ℝ)^3501
        have hw : |(5228662103/10000000000 : ℝ)|=(5228662103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1514_box_14 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1347973829/2500000000 : ℝ)*x 0 + (522866141/1000000000 : ℝ)*x 1 + (-1906267419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1347973829/2500000000 : ℝ)^4525 ≤ (703232783993/1562500000000 : ℝ)^3501 := by
    have hnat : (1347973829 : ℕ)^4525*1562500000000^3501 ≤ 703232783993^3501*2500000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347973829 2500000000 703232783993 1562500000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (522866141/1000000000 : ℝ)^4525 ≤ (10813422536961/25000000000000 : ℝ)^3501 := by
    have hnat : (522866141 : ℕ)^4525*25000000000000^3501 ≤ 10813422536961^3501*1000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522866141 1000000000 10813422536961 25000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1906267419/10000000000 : ℝ)^4525 ≤ (2347882332581/20000000000000 : ℝ)^3501 := by
    have hnat : (1906267419 : ℕ)^4525*20000000000000^3501 ≤ 2347882332581^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1906267419 10000000000 2347882332581 20000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1347973829/2500000000 : ℝ), (522866141/1000000000 : ℝ), (-1906267419/10000000000 : ℝ)] ![(703232783993/1562500000000 : ℝ), (10813422536961/25000000000000 : ℝ), (2347882332581/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1347973829/2500000000 : ℝ)|^4525 ≤ (703232783993/1562500000000 : ℝ)^3501
        have hw : |(1347973829/2500000000 : ℝ)|=(1347973829/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(522866141/1000000000 : ℝ)|^4525 ≤ (10813422536961/25000000000000 : ℝ)^3501
        have hw : |(522866141/1000000000 : ℝ)|=(522866141/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1906267419/10000000000 : ℝ)|^4525 ≤ (2347882332581/20000000000000 : ℝ)^3501
        have hw : |(-1906267419/10000000000 : ℝ)|=(1906267419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1514_box_15 (p : ℝ) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4023965193/10000000000 : ℝ)*x 0 + (175905993/400000000 : ℝ)*x 1 + (2198823999/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4023965193/10000000000 : ℝ)^4525 ≤ (7708331464439/25000000000000 : ℝ)^3501 := by
    have hnat : (4023965193 : ℕ)^4525*25000000000000^3501 ≤ 7708331464439^3501*10000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4023965193 10000000000 7708331464439 25000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (175905993/400000000 : ℝ)^4525 ≤ (6916669269677/20000000000000 : ℝ)^3501 := by
    have hnat : (175905993 : ℕ)^4525*20000000000000^3501 ≤ 6916669269677^3501*400000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      175905993 400000000 6916669269677 20000000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2198823999/5000000000 : ℝ)^4525 ≤ (4322915972301/12500000000000 : ℝ)^3501 := by
    have hnat : (2198823999 : ℕ)^4525*12500000000000^3501 ≤ 4322915972301^3501*5000000000^4525 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2198823999 5000000000 4322915972301 12500000000000 4525 3501 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4525/1024 : ℝ)) 4525 3501 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4023965193/10000000000 : ℝ), (175905993/400000000 : ℝ), (2198823999/5000000000 : ℝ)] ![(7708331464439/25000000000000 : ℝ), (6916669269677/20000000000000 : ℝ), (4322915972301/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4023965193/10000000000 : ℝ)|^4525 ≤ (7708331464439/25000000000000 : ℝ)^3501
        have hw : |(4023965193/10000000000 : ℝ)|=(4023965193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(175905993/400000000 : ℝ)|^4525 ≤ (6916669269677/20000000000000 : ℝ)^3501
        have hw : |(175905993/400000000 : ℝ)|=(175905993/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2198823999/5000000000 : ℝ)|^4525 ≤ (4322915972301/12500000000000 : ℝ)^3501
        have hw : |(2198823999/5000000000 : ℝ)|=(2198823999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1514_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163539063/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2731/25000 : ℝ)*pair X i i ≤ pair X i h) :
    -(31871/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58637/100000 : ℝ) ∧ (80341/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (17203/20000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7741/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2731/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7741/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2731/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7741/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2731/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7741/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2731/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7741/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2731/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7741/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2731/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2731/25000 : ℝ) ^ (4523/1024 : ℝ) ≤ (1414097819262949/25000000000000000000 : ℝ) := by
    have hpowers : (2731/25000 : ℝ)^4523 ≤ (1414097819262949/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2731 : ℕ)^4523*25000000000000000000^1024 ≤ 1414097819262949^1024*25000^4523 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2731 25000 1414097819262949 25000000000000000000 4523 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2731/25000 : ℝ)) (X := (1414097819262949/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4523 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7741/50000 : ℝ) ^ (4523/1024 : ℝ) ≤ (26392010011389857/100000000000000000000 : ℝ) := by
    have hpowers : (7741/50000 : ℝ)^4523 ≤ (26392010011389857/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7741 : ℕ)^4523*100000000000000000000^1024 ≤ 26392010011389857^1024*50000^4523 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7741 50000 26392010011389857 100000000000000000000 4523 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7741/50000 : ℝ)) (X := (26392010011389857/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4523 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501414097819262949/12500000000000000000 : ℝ) ≤ (1000025610838967/1000000000000000 : ℝ) ^ (4523/1024 : ℝ) := by
    have hpowers : (12501414097819262949/12500000000000000000 : ℝ)^1024 ≤ (1000025610838967/1000000000000000 : ℝ)^4523 := by
      have hnat : (12501414097819262949 : ℕ)^1024*1000000000000000^4523 ≤ 1000025610838967^4523*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501414097819262949 12500000000000000000 1000025610838967 1000000000000000 1024 4523 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000025610838967/1000000000000000 : ℝ)) (X := (12501414097819262949/12500000000000000000 : ℝ)) (by norm_num) 4523 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100032048401288441653/100000000000000000000 : ℝ) ≤ (10000725480776277/10000000000000000 : ℝ) ^ (4523/1024 : ℝ) := by
    have hpowers : (100032048401288441653/100000000000000000000 : ℝ)^1024 ≤ (10000725480776277/10000000000000000 : ℝ)^4523 := by
      have hnat : (100032048401288441653 : ℕ)^1024*10000000000000000^4523 ≤ 10000725480776277^4523*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100032048401288441653 100000000000000000000 10000725480776277 10000000000000000 1024 4523 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000725480776277/10000000000000000 : ℝ)) (X := (100032048401288441653/100000000000000000000 : ℝ)) (by norm_num) 4523 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50026392010011389857/50000000000000000000 : ℝ) ≤ (2500298713290721/2500000000000000 : ℝ) ^ (4523/1024 : ℝ) := by
    have hpowers : (50026392010011389857/50000000000000000000 : ℝ)^1024 ≤ (2500298713290721/2500000000000000 : ℝ)^4523 := by
      have hnat : (50026392010011389857 : ℕ)^1024*2500000000000000^4523 ≤ 2500298713290721^4523*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026392010011389857 50000000000000000000 2500298713290721 2500000000000000 1024 4523 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500298713290721/2500000000000000 : ℝ)) (X := (50026392010011389857/50000000000000000000 : ℝ)) (by norm_num) 4523 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1414097819262949/25000000000000000000 : ℝ) ≤ ((11392728123534381531/11395000000000000000 : ℝ)+2*(469372386607/455800000000000 : ℝ)*(2731/25000 : ℝ))^(4523/1024 : ℝ) := by
    rw [show (11392728123534381531/11395000000000000000 : ℝ)+2*(469372386607/455800000000000 : ℝ)*(2731/25000 : ℝ)=(1000025610838967/1000000000000000 : ℝ) by norm_num, show 1+2*(1414097819262949/25000000000000000000 : ℝ)=(12501414097819262949/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(26392010011389857/100000000000000000000 : ℝ)+(1414097819262949/25000000000000000000 : ℝ) ≤ ((11392728123534381531/11395000000000000000 : ℝ)+(469372386607/455800000000000 : ℝ)*((7741/50000 : ℝ)+(2731/25000 : ℝ)))^(4523/1024 : ℝ) := by
    rw [show (11392728123534381531/11395000000000000000 : ℝ)+(469372386607/455800000000000 : ℝ)*((7741/50000 : ℝ)+(2731/25000 : ℝ))=(10000725480776277/10000000000000000 : ℝ) by norm_num, show 1+(26392010011389857/100000000000000000000 : ℝ)+(1414097819262949/25000000000000000000 : ℝ)=(100032048401288441653/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(26392010011389857/100000000000000000000 : ℝ) ≤ ((11392728123534381531/11395000000000000000 : ℝ)+2*(469372386607/455800000000000 : ℝ)*(7741/50000 : ℝ))^(4523/1024 : ℝ) := by
    rw [show (11392728123534381531/11395000000000000000 : ℝ)+2*(469372386607/455800000000000 : ℝ)*(7741/50000 : ℝ)=(2500298713290721/2500000000000000 : ℝ) by norm_num, show 1+2*(26392010011389857/100000000000000000000 : ℝ)=(50026392010011389857/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11392728123534381531/11395000000000000000 : ℝ)*(X 1 0+X 2 0)+(469372386607/455800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4523/1024 : ℝ)) (lo := (2731/25000 : ℝ)) (hi := (7741/50000 : ℝ)) (c := (11392728123534381531/11395000000000000000 : ℝ)) (alpha := (469372386607/455800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11392728123534381531/11395000000000000000 : ℝ)*(X 0 1+X 2 1)+(469372386607/455800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4523/1024 : ℝ)) (lo := (2731/25000 : ℝ)) (hi := (7741/50000 : ℝ)) (c := (11392728123534381531/11395000000000000000 : ℝ)) (alpha := (469372386607/455800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11392728123534381531/11395000000000000000 : ℝ)*(X 0 2+X 1 2)+(469372386607/455800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4523/1024 : ℝ)) (lo := (2731/25000 : ℝ)) (hi := (7741/50000 : ℝ)) (c := (11392728123534381531/11395000000000000000 : ℝ)) (alpha := (469372386607/455800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-82589963/500000000 : ℝ)*X 0 0+(540261577/1000000000 : ℝ)*X 0 1+(2701307863/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1054160693/2000000000 : ℝ)*X 1 0+(-366932063/2000000000 : ℝ)*X 1 1+(1080523089/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5270803119/10000000000 : ℝ)*X 2 0+(216104639/400000000 : ℝ)*X 2 1+(-1834660059/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((44718123/100000000 : ℝ)*X 0 0+(815298/1953125 : ℝ)*X 0 1+(834865079/2000000000 : ℝ)*X 0 2+(44718123/100000000 : ℝ)*X 1 0+(815298/1953125 : ℝ)*X 1 1+(834865079/2000000000 : ℝ)*X 1 2+(44718123/100000000 : ℝ)*X 2 0+(815298/1953125 : ℝ)*X 2 1+(834865079/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2083771997/10000000000 : ℝ)*X 0 0+(1048738281/2000000000 : ℝ)*X 0 1+(5243689541/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2690716271/5000000000 : ℝ)*X 1 0+(-1900244477/10000000000 : ℝ)*X 1 1+(262184551/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5381434401/10000000000 : ℝ)*X 2 0+(327730571/625000000 : ℝ)*X 2 1+(-475061123/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4063442349/10000000000 : ℝ)*X 0 0+(218918817/500000000 : ℝ)*X 0 1+(4378376699/10000000000 : ℝ)*X 0 2+(4063442349/10000000000 : ℝ)*X 1 0+(218918817/500000000 : ℝ)*X 1 1+(4378376699/10000000000 : ℝ)*X 1 2+(4063442349/10000000000 : ℝ)*X 2 0+(218918817/500000000 : ℝ)*X 2 1+(4378376699/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-398495089/2000000000 : ℝ)*X 0 0+(5132328491/10000000000 : ℝ)*X 0 1+(2711531377/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1314141007/2500000000 : ℝ)*X 1 0+(-1825976647/10000000000 : ℝ)*X 1 1+(2711531339/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((262828219/500000000 : ℝ)*X 2 0+(2711531019/5000000000 : ℝ)*X 2 1+(-912988523/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((56540013/125000000 : ℝ)*X 0 0+(1037010029/2500000000 : ℝ)*X 0 1+(2074020363/5000000000 : ℝ)*X 0 2+(56540013/125000000 : ℝ)*X 1 0+(1037010029/2500000000 : ℝ)*X 1 1+(2074020363/5000000000 : ℝ)*X 1 2+(56540013/125000000 : ℝ)*X 2 0+(1037010029/2500000000 : ℝ)*X 2 1+(2074020363/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1743036313/10000000000 : ℝ)*X 0 0+(2755202089/5000000000 : ℝ)*X 0 1+(5228661971/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((673986873/1250000000 : ℝ)*X 1 0+(-1906266939/10000000000 : ℝ)*X 1 1+(5228662103/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1347973829/2500000000 : ℝ)*X 2 0+(522866141/1000000000 : ℝ)*X 2 1+(-1906267419/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4023965193/10000000000 : ℝ)*X 0 0+(175905993/400000000 : ℝ)*X 0 1+(2198823999/5000000000 : ℝ)*X 0 2+(4023965193/10000000000 : ℝ)*X 1 0+(175905993/400000000 : ℝ)*X 1 1+(2198823999/5000000000 : ℝ)*X 1 2+(4023965193/10000000000 : ℝ)*X 2 0+(175905993/400000000 : ℝ)*X 2 1+(2198823999/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1514_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31871/50000 : ℝ) ≤ (-363155253335451338573326936841979/569750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (89636333/100000000000000 : ℝ)*(upper0) + (32083737/100000000000000 : ℝ)*(lower2) + (6510021/3125000000000 : ℝ)*(upper4) + (9692651/6250000000000 : ℝ)*(upper5) + (2226396871284199/100000000000000 : ℝ)*(major0) + (2226396871284199/100000000000000 : ℝ)*(major1) + (2226396871284199/100000000000000 : ℝ)*(major2) + (15286730847/50000000000000 : ℝ)*(sp2) + (2198257477/50000000000000 : ℝ)*(sp3) + (622525835910327/20000000000000 : ℝ)*(sp4) + (48635231946381/1562500000000 : ℝ)*(sp5) + (311262427110669/10000000000000 : ℝ)*(sp6) + (680690484714603/50000000000000 : ℝ)*(sp7) + (25665016749/100000000000000 : ℝ)*(sp8) + (1361385365944159/100000000000000 : ℝ)*(f.failure) + (48635231946381/1562500000000 : ℝ)*(f.sum) + (253496593643467/22790000000000000000000000000 : ℝ)*base66 + (1887917433685446331/1139500000000000000000000000000000 : ℝ)*base68 + (9722720712379946331/1139500000000000000000000000000000 : ℝ)*base70 + (11403468532201446331/1139500000000000000000000000000000 : ℝ)*base72 + (68756300611687/22790000000000000000000000000 : ℝ)*base74 + (8753798619540446331/1139500000000000000000000000000000 : ℝ)*base76 + (15582600903847446331/1139500000000000000000000000000000 : ℝ)*base78 + (7604547993247446331/1139500000000000000000000000000000 : ℝ)*base80 + (84180811587627/22790000000000000000000000000 : ℝ)*base82 + (26816983/10000000000000000000000 : ℝ)*base90 + (26816983/10000000000000000000000 : ℝ)*base92 + (26816983/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (58637/100000 : ℝ) ≤ (3340990201965440516065078041/5697500000000000000000000000 : ℝ) := by norm_num
    linear_combination (28279709/50000000000000 : ℝ)*(upper3) + (41078287/100000000000000 : ℝ)*(upper4) + (474443/10000000000000 : ℝ)*(lower5) + (575690650737881/25000000000000 : ℝ)*(major0) + (575690650737881/25000000000000 : ℝ)*(major1) + (575690650737881/25000000000000 : ℝ)*(major2) + (1588948779810163/50000000000000 : ℝ)*(sp0) + (635565245119407/20000000000000 : ℝ)*(sp1) + (794473283506689/25000000000000 : ℝ)*(sp2) + (7040321766511/500000000000 : ℝ)*(sp3) + (4465394843/100000000000000 : ℝ)*(sp6) + (4975159/12500000000000 : ℝ)*(sp8) + (17843456141/25000000000000 : ℝ)*(sp9) + (16725743437/100000000000000 : ℝ)*(sp11) + (1408081079045637/100000000000000 : ℝ)*(f.failure) + (1588948799710799/50000000000000 : ℝ)*(f.sum) + (29909070442033/5697500000000000000000000000 : ℝ)*base66 + (412164333415650811/284875000000000000000000000000000 : ℝ)*base67 + (1280326091465900811/284875000000000000000000000000000 : ℝ)*base69 + (2255682145703974189/284875000000000000000000000000000 : ℝ)*base72 + (34842102194271/11395000000000000000000000000 : ℝ)*base74 + (367769423386275811/284875000000000000000000000000000 : ℝ)*base75 + (844279196611474189/284875000000000000000000000000000 : ℝ)*base78 + (587396855347349189/284875000000000000000000000000000 : ℝ)*base80 + (8675899522811/2848750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (9218131/10000000000000000000000 : ℝ)*base89 + (9218131/10000000000000000000000 : ℝ)*base91 + (9218131/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (80341/100000 : ℝ) ≤ (447027159072515744072501798697/556396484375000000000000000000 : ℝ) := by norm_num
    linear_combination (125174821/100000000000000 : ℝ)*(upper0) + (18286059/100000000000000 : ℝ)*(upper2) + (42157041/50000000000000 : ℝ)*(lower5) + (78013577695351/3125000000000 : ℝ)*(major0) + (78013577695351/3125000000000 : ℝ)*(major1) + (78013577695351/3125000000000 : ℝ)*(major2) + (48934280633/50000000000000 : ℝ)*(sp1) + (27421880751/100000000000000 : ℝ)*(sp3) + (2614620983/100000000000000 : ℝ)*(sp4) + (1719784751826399/50000000000000 : ℝ)*(sp8) + (1719741737894497/50000000000000 : ℝ)*(sp9) + (171979067217513/5000000000000 : ℝ)*(sp10) + (1526479114512473/100000000000000 : ℝ)*(sp11) + (4613038239/50000000000000 : ℝ)*(sp12) + (190813317049153/12500000000000 : ℝ)*(f.failure) + (171979067217513/5000000000000 : ℝ)*(f.sum) + (99806965520863/11395000000000000000000000000 : ℝ)*base66 + (37751205905079747/17804687500000000000000000000000 : ℝ)*base68 + (79246133335925119/35609375000000000000000000000000 : ℝ)*base70 + (231469590467393869/35609375000000000000000000000000 : ℝ)*base72 + (1057430251843/712187500000000000000000000 : ℝ)*base74 + (137740723141798497/17804687500000000000000000000000 : ℝ)*base76 + (615461301554300119/35609375000000000000000000000000 : ℝ)*base78 + (83538944337925119/35609375000000000000000000000000 : ℝ)*base80 + (4253204154127/11395000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (6563639/1250000000000000000000 : ℝ)*base89 + (6563639/1250000000000000000000 : ℝ)*base91 + (6563639/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-17203/20000 : ℝ) ≤ (-9801087409298318132704811903139/11395000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (78272463/25000000000000 : ℝ)*(lower0) + (24777393/100000000000000 : ℝ)*(upper3) + (10391257/12500000000000 : ℝ)*(lower4) + (50711219462477/2000000000000 : ℝ)*(major0) + (50711219462477/2000000000000 : ℝ)*(major1) + (50711219462477/2000000000000 : ℝ)*(major2) + (13018005549/50000000000000 : ℝ)*(sp0) + (286668702849/100000000000000 : ℝ)*(sp5) + (478824575663/100000000000000 : ℝ)*(sp6) + (846414551/1000000000000 : ℝ)*(sp7) + (3549335242097017/100000000000000 : ℝ)*(sp12) + (1774537304702633/50000000000000 : ℝ)*(sp13) + (887220613383113/25000000000000 : ℝ)*(sp14) + (96896671992721/6250000000000 : ℝ)*(sp15) + (387607848334659/25000000000000 : ℝ)*(f.failure) + (1774680639054057/50000000000000 : ℝ)*(f.sum) + (128135836459/1139500000000000000000000000 : ℝ)*base66 + (81415925969152713/22790000000000000000000000000000 : ℝ)*base68 + (29207285617217287/22790000000000000000000000000000 : ℝ)*base69 + (277806986202712713/22790000000000000000000000000000 : ℝ)*base72 + (5359511718577/569750000000000000000000000 : ℝ)*base73 + (75781292639952713/22790000000000000000000000000000 : ℝ)*base76 + (168029374685182713/22790000000000000000000000000000 : ℝ)*base78 + (56914314605267287/22790000000000000000000000000000 : ℝ)*base79 + (15453172287619/2279000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (6715483/2500000000000000000000 : ℝ)*base90 + (6715483/2500000000000000000000 : ℝ)*base92 + (6715483/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1514_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163539063/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2731/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31871/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58637/100000 : ℝ) else (80341/100000 : ℝ) ≤ X j i ∧ X j i ≤ (17203/20000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1514_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1514_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163539063/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10923/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31871/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58637/100000 : ℝ) else (80341/100000 : ℝ) ≤ X j i ∧ X j i ≤ (17203/20000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1514_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1514_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4523/1024 : ℝ) ≤ p) (hpb : p ≤ (4525/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163539063/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10923/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31871/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58637/100000 : ℝ) else (80341/100000 : ℝ) ≤ X j i ∧ X j i ≤ (17203/20000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1514_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
