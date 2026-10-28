-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1198_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:02:14.92598+00:00
-- url     : https://prove2.me/submissions/1e62ee73-9f80-45c1-a733-144463af3c70

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
theorem support_rectangle_w1198_s6_0 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-214036679/1000000000 : ℝ)*x 0 + (5392263839/10000000000 : ℝ)*x 1 + (526636397/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214036679/1000000000 : ℝ)^8391 ≤ (13011254556321/100000000000000 : ℝ)^6343 := by
    have hnat : (214036679 : ℕ)^8391*100000000000000^6343 ≤ 13011254556321^6343*1000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214036679 1000000000 13011254556321 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392263839/10000000000 : ℝ)^8391 ≤ (44173984520221/100000000000000 : ℝ)^6343 := by
    have hnat : (5392263839 : ℕ)^8391*100000000000000^6343 ≤ 44173984520221^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392263839 10000000000 44173984520221 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526636397/1000000000 : ℝ)^8391 ≤ (428147609111/1000000000000 : ℝ)^6343 := by
    have hnat : (526636397 : ℕ)^8391*1000000000000^6343 ≤ 428147609111^6343*1000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526636397 1000000000 428147609111 1000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-214036679/1000000000 : ℝ), (5392263839/10000000000 : ℝ), (526636397/1000000000 : ℝ)] ![(13011254556321/100000000000000 : ℝ), (44173984520221/100000000000000 : ℝ), (428147609111/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-214036679/1000000000 : ℝ)|^8391 ≤ (13011254556321/100000000000000 : ℝ)^6343
        have hw : |(-214036679/1000000000 : ℝ)|=(214036679/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392263839/10000000000 : ℝ)|^8391 ≤ (44173984520221/100000000000000 : ℝ)^6343
        have hw : |(5392263839/10000000000 : ℝ)|=(5392263839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526636397/1000000000 : ℝ)|^8391 ≤ (428147609111/1000000000000 : ℝ)^6343
        have hw : |(526636397/1000000000 : ℝ)|=(526636397/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_s6_1 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344589901/10000000000 : ℝ)*x 0 + (-551053821/2500000000 : ℝ)*x 1 + (1316591011/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344589901/10000000000 : ℝ)^8391 ≤ (43658074546927/100000000000000 : ℝ)^6343 := by
    have hnat : (5344589901 : ℕ)^8391*100000000000000^6343 ≤ 43658074546927^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344589901 10000000000 43658074546927 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (551053821/2500000000 : ℝ)^8391 ≤ (13527163726237/100000000000000 : ℝ)^6343 := by
    have hnat : (551053821 : ℕ)^8391*100000000000000^6343 ≤ 13527163726237^6343*2500000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551053821 2500000000 13527163726237 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316591011/2500000000 : ℝ)^8391 ≤ (21407380853477/50000000000000 : ℝ)^6343 := by
    have hnat : (1316591011 : ℕ)^8391*50000000000000^6343 ≤ 21407380853477^6343*2500000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316591011 2500000000 21407380853477 50000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344589901/10000000000 : ℝ), (-551053821/2500000000 : ℝ), (1316591011/2500000000 : ℝ)] ![(43658074546927/100000000000000 : ℝ), (13527163726237/100000000000000 : ℝ), (21407380853477/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344589901/10000000000 : ℝ)|^8391 ≤ (43658074546927/100000000000000 : ℝ)^6343
        have hw : |(5344589901/10000000000 : ℝ)|=(5344589901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-551053821/2500000000 : ℝ)|^8391 ≤ (13527163726237/100000000000000 : ℝ)^6343
        have hw : |(-551053821/2500000000 : ℝ)|=(551053821/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316591011/2500000000 : ℝ)|^8391 ≤ (21407380853477/50000000000000 : ℝ)^6343
        have hw : |(1316591011/2500000000 : ℝ)|=(1316591011/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_s6_2 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (534459003/1000000000 : ℝ)*x 0 + (5266363757/10000000000 : ℝ)*x 1 + (-2204215493/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534459003/1000000000 : ℝ)^8391 ≤ (8731615188183/20000000000000 : ℝ)^6343 := by
    have hnat : (534459003 : ℕ)^8391*20000000000000^6343 ≤ 8731615188183^6343*1000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534459003 1000000000 8731615188183 20000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266363757/10000000000 : ℝ)^8391 ≤ (42814758620331/100000000000000 : ℝ)^6343 := by
    have hnat : (5266363757 : ℕ)^8391*100000000000000^6343 ≤ 42814758620331^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266363757 10000000000 42814758620331 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2204215493/10000000000 : ℝ)^8391 ≤ (13527165422987/100000000000000 : ℝ)^6343 := by
    have hnat : (2204215493 : ℕ)^8391*100000000000000^6343 ≤ 13527165422987^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2204215493 10000000000 13527165422987 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534459003/1000000000 : ℝ), (5266363757/10000000000 : ℝ), (-2204215493/10000000000 : ℝ)] ![(8731615188183/20000000000000 : ℝ), (42814758620331/100000000000000 : ℝ), (13527165422987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534459003/1000000000 : ℝ)|^8391 ≤ (8731615188183/20000000000000 : ℝ)^6343
        have hw : |(534459003/1000000000 : ℝ)|=(534459003/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266363757/10000000000 : ℝ)|^8391 ≤ (42814758620331/100000000000000 : ℝ)^6343
        have hw : |(5266363757/10000000000 : ℝ)|=(5266363757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2204215493/10000000000 : ℝ)|^8391 ≤ (13527165422987/100000000000000 : ℝ)^6343
        have hw : |(-2204215493/10000000000 : ℝ)|=(2204215493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_s6_3 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2178415561/5000000000 : ℝ)*x 0 + (4232022901/10000000000 : ℝ)*x 1 + (2242626293/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2178415561/5000000000 : ℝ)^8391 ≤ (33317143095191/100000000000000 : ℝ)^6343 := by
    have hnat : (2178415561 : ℕ)^8391*100000000000000^6343 ≤ 33317143095191^6343*5000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178415561 5000000000 33317143095191 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4232022901/10000000000 : ℝ)^8391 ≤ (32060439344309/100000000000000 : ℝ)^6343 := by
    have hnat : (4232022901 : ℕ)^8391*100000000000000^6343 ≤ 32060439344309^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4232022901 10000000000 32060439344309 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2242626293/5000000000 : ℝ)^8391 ≤ (34622417539511/100000000000000 : ℝ)^6343 := by
    have hnat : (2242626293 : ℕ)^8391*100000000000000^6343 ≤ 34622417539511^6343*5000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2242626293 5000000000 34622417539511 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2178415561/5000000000 : ℝ), (4232022901/10000000000 : ℝ), (2242626293/5000000000 : ℝ)] ![(33317143095191/100000000000000 : ℝ), (32060439344309/100000000000000 : ℝ), (34622417539511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2178415561/5000000000 : ℝ)|^8391 ≤ (33317143095191/100000000000000 : ℝ)^6343
        have hw : |(2178415561/5000000000 : ℝ)|=(2178415561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4232022901/10000000000 : ℝ)|^8391 ≤ (32060439344309/100000000000000 : ℝ)^6343
        have hw : |(4232022901/10000000000 : ℝ)|=(4232022901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2242626293/5000000000 : ℝ)|^8391 ≤ (34622417539511/100000000000000 : ℝ)^6343
        have hw : |(2242626293/5000000000 : ℝ)|=(2242626293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_s6_4 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2140371739/10000000000 : ℝ)*x 0 + (5266681979/10000000000 : ℝ)*x 1 + (673993071/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2140371739/10000000000 : ℝ)^8391 ≤ (13011294354903/100000000000000 : ℝ)^6343 := by
    have hnat : (2140371739 : ℕ)^8391*100000000000000^6343 ≤ 13011294354903^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2140371739 10000000000 13011294354903 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266681979/10000000000 : ℝ)^8391 ≤ (8563636212461/20000000000000 : ℝ)^6343 := by
    have hnat : (5266681979 : ℕ)^8391*20000000000000^6343 ≤ 8563636212461^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266681979 10000000000 8563636212461 20000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (673993071/1250000000 : ℝ)^8391 ≤ (44170524570627/100000000000000 : ℝ)^6343 := by
    have hnat : (673993071 : ℕ)^8391*100000000000000^6343 ≤ 44170524570627^6343*1250000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673993071 1250000000 44170524570627 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2140371739/10000000000 : ℝ), (5266681979/10000000000 : ℝ), (673993071/1250000000 : ℝ)] ![(13011294354903/100000000000000 : ℝ), (8563636212461/20000000000000 : ℝ), (44170524570627/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2140371739/10000000000 : ℝ)|^8391 ≤ (13011294354903/100000000000000 : ℝ)^6343
        have hw : |(-2140371739/10000000000 : ℝ)|=(2140371739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266681979/10000000000 : ℝ)|^8391 ≤ (8563636212461/20000000000000 : ℝ)^6343
        have hw : |(5266681979/10000000000 : ℝ)|=(5266681979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(673993071/1250000000 : ℝ)|^8391 ≤ (44170524570627/100000000000000 : ℝ)^6343
        have hw : |(673993071/1250000000 : ℝ)|=(673993071/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_s6_5 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656281699/5000000000 : ℝ)*x 0 + (-2078634591/10000000000 : ℝ)*x 1 + (5391944601/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656281699/5000000000 : ℝ)^8391 ≤ (5414041003437/12500000000000 : ℝ)^6343 := by
    have hnat : (2656281699 : ℕ)^8391*12500000000000^6343 ≤ 5414041003437^6343*5000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656281699 5000000000 5414041003437 12500000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2078634591/10000000000 : ℝ)^8391 ≤ (12517147031641/100000000000000 : ℝ)^6343 := by
    have hnat : (2078634591 : ℕ)^8391*100000000000000^6343 ≤ 12517147031641^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2078634591 10000000000 12517147031641 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391944601/10000000000 : ℝ)^8391 ≤ (22085262464123/50000000000000 : ℝ)^6343 := by
    have hnat : (5391944601 : ℕ)^8391*50000000000000^6343 ≤ 22085262464123^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391944601 10000000000 22085262464123 50000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656281699/5000000000 : ℝ), (-2078634591/10000000000 : ℝ), (5391944601/10000000000 : ℝ)] ![(5414041003437/12500000000000 : ℝ), (12517147031641/100000000000000 : ℝ), (22085262464123/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656281699/5000000000 : ℝ)|^8391 ≤ (5414041003437/12500000000000 : ℝ)^6343
        have hw : |(2656281699/5000000000 : ℝ)|=(2656281699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2078634591/10000000000 : ℝ)|^8391 ≤ (12517147031641/100000000000000 : ℝ)^6343
        have hw : |(-2078634591/10000000000 : ℝ)|=(2078634591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391944601/10000000000 : ℝ)|^8391 ≤ (22085262464123/50000000000000 : ℝ)^6343
        have hw : |(5391944601/10000000000 : ℝ)|=(5391944601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_s6_6 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312563417/10000000000 : ℝ)*x 0 + (539194459/1000000000 : ℝ)*x 1 + (-2078634581/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312563417/10000000000 : ℝ)^8391 ≤ (21656164116207/50000000000000 : ℝ)^6343 := by
    have hnat : (5312563417 : ℕ)^8391*50000000000000^6343 ≤ 21656164116207^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312563417 10000000000 21656164116207 50000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539194459/1000000000 : ℝ)^8391 ≤ (552131560113/1250000000000 : ℝ)^6343 := by
    have hnat : (539194459 : ℕ)^8391*1250000000000^6343 ≤ 552131560113^6343*1000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539194459 1000000000 552131560113 1250000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2078634581/10000000000 : ℝ)^8391 ≤ (625857347599/5000000000000 : ℝ)^6343 := by
    have hnat : (2078634581 : ℕ)^8391*5000000000000^6343 ≤ 625857347599^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2078634581 10000000000 625857347599 5000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312563417/10000000000 : ℝ), (539194459/1000000000 : ℝ), (-2078634581/10000000000 : ℝ)] ![(21656164116207/50000000000000 : ℝ), (552131560113/1250000000000 : ℝ), (625857347599/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312563417/10000000000 : ℝ)|^8391 ≤ (21656164116207/50000000000000 : ℝ)^6343
        have hw : |(5312563417/10000000000 : ℝ)|=(5312563417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539194459/1000000000 : ℝ)|^8391 ≤ (552131560113/1250000000000 : ℝ)^6343
        have hw : |(539194459/1000000000 : ℝ)|=(539194459/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2078634581/10000000000 : ℝ)|^8391 ≤ (625857347599/5000000000000 : ℝ)^6343
        have hw : |(-2078634581/10000000000 : ℝ)|=(2078634581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_s6_7 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1089210131/2500000000 : ℝ)*x 0 + (2242306261/5000000000 : ℝ)*x 1 + (132270799/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089210131/2500000000 : ℝ)^8391 ≤ (8329309551859/25000000000000 : ℝ)^6343 := by
    have hnat : (1089210131 : ℕ)^8391*25000000000000^6343 ≤ 8329309551859^6343*2500000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089210131 2500000000 8329309551859 25000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2242306261/5000000000 : ℝ)^8391 ≤ (34615881677273/100000000000000 : ℝ)^6343 := by
    have hnat : (2242306261 : ℕ)^8391*100000000000000^6343 ≤ 34615881677273^6343*5000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2242306261 5000000000 34615881677273 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (132270799/312500000 : ℝ)^8391 ≤ (32066880104311/100000000000000 : ℝ)^6343 := by
    have hnat : (132270799 : ℕ)^8391*100000000000000^6343 ≤ 32066880104311^6343*312500000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132270799 312500000 32066880104311 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1089210131/2500000000 : ℝ), (2242306261/5000000000 : ℝ), (132270799/312500000 : ℝ)] ![(8329309551859/25000000000000 : ℝ), (34615881677273/100000000000000 : ℝ), (32066880104311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1089210131/2500000000 : ℝ)|^8391 ≤ (8329309551859/25000000000000 : ℝ)^6343
        have hw : |(1089210131/2500000000 : ℝ)|=(1089210131/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2242306261/5000000000 : ℝ)|^8391 ≤ (34615881677273/100000000000000 : ℝ)^6343
        have hw : |(2242306261/5000000000 : ℝ)|=(2242306261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(132270799/312500000 : ℝ)|^8391 ≤ (32066880104311/100000000000000 : ℝ)^6343
        have hw : |(132270799/312500000 : ℝ)|=(132270799/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1198_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150567503/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (441/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2279/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (11419/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7043/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (441/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2279/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (441/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2279/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (441/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2279/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (441/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2279/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (441/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2279/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (441/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2279/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2279/20000 : ℝ) ^ (4195/1024 : ℝ) ≤ (3416652129905473/25000000000000000000 : ℝ) := by
    have hpowers : (2279/20000 : ℝ)^4195 ≤ (3416652129905473/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2279 : ℕ)^4195*25000000000000000000^1024 ≤ 3416652129905473^1024*20000^4195 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2279 20000 3416652129905473 25000000000000000000 4195 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2279/20000 : ℝ)) (X := (3416652129905473/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4195 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (441/3125 : ℝ) ^ (4195/1024 : ℝ) ≤ (16409931341055327/50000000000000000000 : ℝ) := by
    have hpowers : (441/3125 : ℝ)^4195 ≤ (16409931341055327/50000000000000000000 : ℝ)^1024 := by
      have hnat : (441 : ℕ)^4195*50000000000000000000^1024 ≤ 16409931341055327^1024*3125^4195 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        441 3125 16409931341055327 50000000000000000000 4195 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (441/3125 : ℝ)) (X := (16409931341055327/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4195 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503416652129905473/12500000000000000000 : ℝ) ≤ (5000333567619313/5000000000000000 : ℝ) ^ (4195/1024 : ℝ) := by
    have hpowers : (12503416652129905473/12500000000000000000 : ℝ)^1024 ≤ (5000333567619313/5000000000000000 : ℝ)^4195 := by
      have hnat : (12503416652129905473 : ℕ)^1024*5000000000000000^4195 ≤ 5000333567619313^4195*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503416652129905473 12500000000000000000 5000333567619313 5000000000000000 1024 4195 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000333567619313/5000000000000000 : ℝ)) (X := (12503416652129905473/12500000000000000000 : ℝ)) (by norm_num) 4195 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023243235600866273/50000000000000000000 : ℝ) ≤ (10001134536002341/10000000000000000 : ℝ) ^ (4195/1024 : ℝ) := by
    have hpowers : (50023243235600866273/50000000000000000000 : ℝ)^1024 ≤ (10001134536002341/10000000000000000 : ℝ)^4195 := by
      have hnat : (50023243235600866273 : ℕ)^1024*10000000000000000^4195 ≤ 10001134536002341^4195*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023243235600866273 50000000000000000000 10001134536002341 10000000000000000 1024 4195 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001134536002341/10000000000000000 : ℝ)) (X := (50023243235600866273/50000000000000000000 : ℝ)) (by norm_num) 4195 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016409931341055327/25000000000000000000 : ℝ) ≤ (1250200242095757/1250000000000000 : ℝ) ^ (4195/1024 : ℝ) := by
    have hpowers : (25016409931341055327/25000000000000000000 : ℝ)^1024 ≤ (1250200242095757/1250000000000000 : ℝ)^4195 := by
      have hnat : (25016409931341055327 : ℕ)^1024*1250000000000000^4195 ≤ 1250200242095757^4195*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016409931341055327 25000000000000000000 1250200242095757 1250000000000000 1024 4195 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250200242095757/1250000000000000 : ℝ)) (X := (25016409931341055327/25000000000000000000 : ℝ)) (by norm_num) 4195 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3416652129905473/25000000000000000000 : ℝ) ≤ ((3395145067879785249/3396250000000000000 : ℝ)+2*(93480152743/54340000000000 : ℝ)*(2279/20000 : ℝ))^(4195/1024 : ℝ) := by
    rw [show (3395145067879785249/3396250000000000000 : ℝ)+2*(93480152743/54340000000000 : ℝ)*(2279/20000 : ℝ)=(5000333567619313/5000000000000000 : ℝ) by norm_num, show 1+2*(3416652129905473/25000000000000000000 : ℝ)=(12503416652129905473/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16409931341055327/50000000000000000000 : ℝ)+(3416652129905473/25000000000000000000 : ℝ) ≤ ((3395145067879785249/3396250000000000000 : ℝ)+(93480152743/54340000000000 : ℝ)*((441/3125 : ℝ)+(2279/20000 : ℝ)))^(4195/1024 : ℝ) := by
    rw [show (3395145067879785249/3396250000000000000 : ℝ)+(93480152743/54340000000000 : ℝ)*((441/3125 : ℝ)+(2279/20000 : ℝ))=(10001134536002341/10000000000000000 : ℝ) by norm_num, show 1+(16409931341055327/50000000000000000000 : ℝ)+(3416652129905473/25000000000000000000 : ℝ)=(50023243235600866273/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16409931341055327/50000000000000000000 : ℝ) ≤ ((3395145067879785249/3396250000000000000 : ℝ)+2*(93480152743/54340000000000 : ℝ)*(441/3125 : ℝ))^(4195/1024 : ℝ) := by
    rw [show (3395145067879785249/3396250000000000000 : ℝ)+2*(93480152743/54340000000000 : ℝ)*(441/3125 : ℝ)=(1250200242095757/1250000000000000 : ℝ) by norm_num, show 1+2*(16409931341055327/50000000000000000000 : ℝ)=(25016409931341055327/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3395145067879785249/3396250000000000000 : ℝ)*(X 1 0+X 2 0)+(93480152743/54340000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4195/1024 : ℝ)) (lo := (2279/20000 : ℝ)) (hi := (441/3125 : ℝ)) (c := (3395145067879785249/3396250000000000000 : ℝ)) (alpha := (93480152743/54340000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3395145067879785249/3396250000000000000 : ℝ)*(X 0 1+X 2 1)+(93480152743/54340000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4195/1024 : ℝ)) (lo := (2279/20000 : ℝ)) (hi := (441/3125 : ℝ)) (c := (3395145067879785249/3396250000000000000 : ℝ)) (alpha := (93480152743/54340000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3395145067879785249/3396250000000000000 : ℝ)*(X 0 2+X 1 2)+(93480152743/54340000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4195/1024 : ℝ)) (lo := (2279/20000 : ℝ)) (hi := (441/3125 : ℝ)) (c := (3395145067879785249/3396250000000000000 : ℝ)) (alpha := (93480152743/54340000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-214036679/1000000000 : ℝ)*X 0 0+(5392263839/10000000000 : ℝ)*X 0 1+(526636397/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344589901/10000000000 : ℝ)*X 1 0+(-551053821/2500000000 : ℝ)*X 1 1+(1316591011/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534459003/1000000000 : ℝ)*X 2 0+(5266363757/10000000000 : ℝ)*X 2 1+(-2204215493/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2178415561/5000000000 : ℝ)*X 0 0+(4232022901/10000000000 : ℝ)*X 0 1+(2242626293/5000000000 : ℝ)*X 0 2+(2178415561/5000000000 : ℝ)*X 1 0+(4232022901/10000000000 : ℝ)*X 1 1+(2242626293/5000000000 : ℝ)*X 1 2+(2178415561/5000000000 : ℝ)*X 2 0+(4232022901/10000000000 : ℝ)*X 2 1+(2242626293/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2140371739/10000000000 : ℝ)*X 0 0+(5266681979/10000000000 : ℝ)*X 0 1+(673993071/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656281699/5000000000 : ℝ)*X 1 0+(-2078634591/10000000000 : ℝ)*X 1 1+(5391944601/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312563417/10000000000 : ℝ)*X 2 0+(539194459/1000000000 : ℝ)*X 2 1+(-2078634581/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1089210131/2500000000 : ℝ)*X 0 0+(2242306261/5000000000 : ℝ)*X 0 1+(132270799/312500000 : ℝ)*X 0 2+(1089210131/2500000000 : ℝ)*X 1 0+(2242306261/5000000000 : ℝ)*X 1 1+(132270799/312500000 : ℝ)*X 1 2+(1089210131/2500000000 : ℝ)*X 2 0+(2242306261/5000000000 : ℝ)*X 2 1+(132270799/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (46070928263945404892752473/4468750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1552051697/100000000000000 : ℝ)*(base19) + (396501133/25000000000000 : ℝ)*(base23) + (181909869/100000000000000 : ℝ)*(lower2) + (420086241/100000000000000 : ℝ)*(upper3) + (97592929/100000000000000 : ℝ)*(lower4) + (5945966708032921/100000000000000 : ℝ)*(major0) + (5945966708032921/100000000000000 : ℝ)*(major1) + (5945966708032921/100000000000000 : ℝ)*(major2) + (992858267267807/12500000000000 : ℝ)*(sp0) + (7942894318068993/100000000000000 : ℝ)*(sp1) + (7942894284116157/100000000000000 : ℝ)*(sp2) + (1974502703314261/50000000000000 : ℝ)*(sp3) + (29731978233/100000000000000 : ℝ)*(sp4) + (31795664009/100000000000000 : ℝ)*(sp7) + (394903720229253/10000000000000 : ℝ)*(f.failure) + (7942895870120689/100000000000000 : ℝ)*(f.sum) + (407658543351/71500000000000000000000000 : ℝ)*base66 + (198915706960645009/17875000000000000000000000000000 : ℝ)*base68 + (175245345192020009/17875000000000000000000000000000 : ℝ)*base70 + (284250731413895009/17875000000000000000000000000000 : ℝ)*base72 + (612063326707/143000000000000000000000000 : ℝ)*base74 + (209604474067520009/17875000000000000000000000000000 : ℝ)*base76 + (104439802657229991/17875000000000000000000000000000 : ℝ)*base77 + (308348426034895009/17875000000000000000000000000000 : ℝ)*base80 + (161041750849/17875000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1765259/1000000000000000000000 : ℝ)*base89 + (1765259/1000000000000000000000 : ℝ)*base91 + (1765259/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (114939406744983360921044451/33962500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (620184511/100000000000000 : ℝ)*(base19) + (683664429/100000000000000 : ℝ)*(base23) + (76338099/100000000000000 : ℝ)*(upper3) + (11962803/100000000000000 : ℝ)*(lower4) + (12608513/20000000000000 : ℝ)*(upper5) + (1195231881876567/20000000000000 : ℝ)*(major0) + (1195231881876567/20000000000000 : ℝ)*(major1) + (1195231881876567/20000000000000 : ℝ)*(major2) + (1877607653/10000000000000 : ℝ)*(sp1) + (10417333327/50000000000000 : ℝ)*(sp2) + (7983228902173099/100000000000000 : ℝ)*(sp4) + (3991604752956029/50000000000000 : ℝ)*(sp5) + (249475230745063/3125000000000 : ℝ)*(sp6) + (79381796075649/2000000000000 : ℝ)*(sp7) + (79381796075649/2000000000000 : ℝ)*(f.failure) + (7983228902173099/100000000000000 : ℝ)*(f.sum) + (470559593879/1358500000000000000000000000 : ℝ)*base66 + (285354132026002317/67925000000000000000000000000000 : ℝ)*base68 + (3324671926822683/67925000000000000000000000000000 : ℝ)*base69 + (675658373044472683/67925000000000000000000000000000 : ℝ)*base71 + (13539852162729/2717000000000000000000000000 : ℝ)*base74 + (61101001344772683/67925000000000000000000000000000 : ℝ)*base75 + (130761605183677317/67925000000000000000000000000000 : ℝ)*base78 + (193784090597772683/67925000000000000000000000000000 : ℝ)*base79 + (6971596535011/2717000000000000000000000000 : ℝ)*base81 + (965553/200000000000000000000 : ℝ)*base90 + (965553/200000000000000000000 : ℝ)*base92 + (965553/200000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1198_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150567503/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (441/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2279/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11419/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7043/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1198_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1198_s7_0 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1070195253/5000000000 : ℝ)*x 0 + (1348004739/2500000000 : ℝ)*x 1 + (526659299/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070195253/5000000000 : ℝ)^8391 ≤ (13011445274547/100000000000000 : ℝ)^6343 := by
    have hnat : (1070195253 : ℕ)^8391*100000000000000^6343 ≤ 13011445274547^6343*5000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070195253 5000000000 13011445274547 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348004739/2500000000 : ℝ)^8391 ≤ (11042832677437/25000000000000 : ℝ)^6343 := by
    have hnat : (1348004739 : ℕ)^8391*25000000000000^6343 ≤ 11042832677437^6343*2500000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348004739 2500000000 11042832677437 25000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526659299/1000000000 : ℝ)^8391 ≤ (42817223988851/100000000000000 : ℝ)^6343 := by
    have hnat : (526659299 : ℕ)^8391*100000000000000^6343 ≤ 42817223988851^6343*1000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526659299 1000000000 42817223988851 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1070195253/5000000000 : ℝ), (1348004739/2500000000 : ℝ), (526659299/1000000000 : ℝ)] ![(13011445274547/100000000000000 : ℝ), (11042832677437/25000000000000 : ℝ), (42817223988851/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1070195253/5000000000 : ℝ)|^8391 ≤ (13011445274547/100000000000000 : ℝ)^6343
        have hw : |(-1070195253/5000000000 : ℝ)|=(1070195253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348004739/2500000000 : ℝ)|^8391 ≤ (11042832677437/25000000000000 : ℝ)^6343
        have hw : |(1348004739/2500000000 : ℝ)|=(1348004739/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526659299/1000000000 : ℝ)|^8391 ≤ (42817223988851/100000000000000 : ℝ)^6343
        have hw : |(526659299/1000000000 : ℝ)|=(526659299/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_s7_1 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344527423/10000000000 : ℝ)*x 0 + (-2203995147/10000000000 : ℝ)*x 1 + (526659299/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344527423/10000000000 : ℝ)^8391 ≤ (8731479880869/20000000000000 : ℝ)^6343 := by
    have hnat : (5344527423 : ℕ)^8391*20000000000000^6343 ≤ 8731479880869^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344527423 10000000000 8731479880869 20000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2203995147/10000000000 : ℝ)^8391 ≤ (3381344147369/25000000000000 : ℝ)^6343 := by
    have hnat : (2203995147 : ℕ)^8391*25000000000000^6343 ≤ 3381344147369^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2203995147 10000000000 3381344147369 25000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526659299/1000000000 : ℝ)^8391 ≤ (42817223988851/100000000000000 : ℝ)^6343 := by
    have hnat : (526659299 : ℕ)^8391*100000000000000^6343 ≤ 42817223988851^6343*1000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526659299 1000000000 42817223988851 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344527423/10000000000 : ℝ), (-2203995147/10000000000 : ℝ), (526659299/1000000000 : ℝ)] ![(8731479880869/20000000000000 : ℝ), (3381344147369/25000000000000 : ℝ), (42817223988851/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344527423/10000000000 : ℝ)|^8391 ≤ (8731479880869/20000000000000 : ℝ)^6343
        have hw : |(5344527423/10000000000 : ℝ)|=(5344527423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2203995147/10000000000 : ℝ)|^8391 ≤ (3381344147369/25000000000000 : ℝ)^6343
        have hw : |(-2203995147/10000000000 : ℝ)|=(2203995147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526659299/1000000000 : ℝ)|^8391 ≤ (42817223988851/100000000000000 : ℝ)^6343
        have hw : |(526659299/1000000000 : ℝ)|=(526659299/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_s7_2 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672263711/5000000000 : ℝ)*x 0 + (5266592991/10000000000 : ℝ)*x 1 + (-2203995147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672263711/5000000000 : ℝ)^8391 ≤ (43657399393539/100000000000000 : ℝ)^6343 := by
    have hnat : (2672263711 : ℕ)^8391*100000000000000^6343 ≤ 43657399393539^6343*5000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672263711 5000000000 43657399393539 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266592991/10000000000 : ℝ)^8391 ≤ (21408611999803/50000000000000 : ℝ)^6343 := by
    have hnat : (5266592991 : ℕ)^8391*50000000000000^6343 ≤ 21408611999803^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266592991 10000000000 21408611999803 50000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2203995147/10000000000 : ℝ)^8391 ≤ (3381344147369/25000000000000 : ℝ)^6343 := by
    have hnat : (2203995147 : ℕ)^8391*25000000000000^6343 ≤ 3381344147369^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2203995147 10000000000 3381344147369 25000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672263711/5000000000 : ℝ), (5266592991/10000000000 : ℝ), (-2203995147/10000000000 : ℝ)] ![(43657399393539/100000000000000 : ℝ), (21408611999803/50000000000000 : ℝ), (3381344147369/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672263711/5000000000 : ℝ)|^8391 ≤ (43657399393539/100000000000000 : ℝ)^6343
        have hw : |(2672263711/5000000000 : ℝ)|=(2672263711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266592991/10000000000 : ℝ)|^8391 ≤ (21408611999803/50000000000000 : ℝ)^6343
        have hw : |(5266592991/10000000000 : ℝ)|=(5266592991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2203995147/10000000000 : ℝ)|^8391 ≤ (3381344147369/25000000000000 : ℝ)^6343
        have hw : |(-2203995147/10000000000 : ℝ)|=(2203995147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_s7_3 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (435684289/1000000000 : ℝ)*x 0 + (2116249283/5000000000 : ℝ)*x 1 + (4484774089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (435684289/1000000000 : ℝ)^8391 ≤ (33317262142309/100000000000000 : ℝ)^6343 := by
    have hnat : (435684289 : ℕ)^8391*100000000000000^6343 ≤ 33317262142309^6343*1000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435684289 1000000000 33317262142309 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2116249283/5000000000 : ℝ)^8391 ≤ (8016301598137/25000000000000 : ℝ)^6343 := by
    have hnat : (2116249283 : ℕ)^8391*25000000000000^6343 ≤ 8016301598137^6343*5000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2116249283 5000000000 8016301598137 25000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4484774089/10000000000 : ℝ)^8391 ≤ (17308765726043/50000000000000 : ℝ)^6343 := by
    have hnat : (4484774089 : ℕ)^8391*50000000000000^6343 ≤ 17308765726043^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4484774089 10000000000 17308765726043 50000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(435684289/1000000000 : ℝ), (2116249283/5000000000 : ℝ), (4484774089/10000000000 : ℝ)] ![(33317262142309/100000000000000 : ℝ), (8016301598137/25000000000000 : ℝ), (17308765726043/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(435684289/1000000000 : ℝ)|^8391 ≤ (33317262142309/100000000000000 : ℝ)^6343
        have hw : |(435684289/1000000000 : ℝ)|=(435684289/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2116249283/5000000000 : ℝ)|^8391 ≤ (8016301598137/25000000000000 : ℝ)^6343
        have hw : |(2116249283/5000000000 : ℝ)|=(2116249283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4484774089/10000000000 : ℝ)|^8391 ≤ (17308765726043/50000000000000 : ℝ)^6343
        have hw : |(4484774089/10000000000 : ℝ)|=(4484774089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_s7_4 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-535098911/2500000000 : ℝ)*x 0 + (5266908863/10000000000 : ℝ)*x 1 + (673962707/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535098911/2500000000 : ℝ)^8391 ≤ (6505743296583/50000000000000 : ℝ)^6343 := by
    have hnat : (535098911 : ℕ)^8391*50000000000000^6343 ≤ 6505743296583^6343*2500000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535098911 2500000000 6505743296583 50000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266908863/10000000000 : ℝ)^8391 ≤ (42820621215091/100000000000000 : ℝ)^6343 := by
    have hnat : (5266908863 : ℕ)^8391*100000000000000^6343 ≤ 42820621215091^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266908863 10000000000 42820621215091 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (673962707/1250000000 : ℝ)^8391 ≤ (44167892170161/100000000000000 : ℝ)^6343 := by
    have hnat : (673962707 : ℕ)^8391*100000000000000^6343 ≤ 44167892170161^6343*1250000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673962707 1250000000 44167892170161 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-535098911/2500000000 : ℝ), (5266908863/10000000000 : ℝ), (673962707/1250000000 : ℝ)] ![(6505743296583/50000000000000 : ℝ), (42820621215091/100000000000000 : ℝ), (44167892170161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-535098911/2500000000 : ℝ)|^8391 ≤ (6505743296583/50000000000000 : ℝ)^6343
        have hw : |(-535098911/2500000000 : ℝ)|=(535098911/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266908863/10000000000 : ℝ)|^8391 ≤ (42820621215091/100000000000000 : ℝ)^6343
        have hw : |(5266908863/10000000000 : ℝ)|=(5266908863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(673962707/1250000000 : ℝ)|^8391 ≤ (44167892170161/100000000000000 : ℝ)^6343
        have hw : |(673962707/1250000000 : ℝ)|=(673962707/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_s7_5 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312621469/10000000000 : ℝ)*x 0 + (-2078885977/10000000000 : ℝ)*x 1 + (5391702011/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312621469/10000000000 : ℝ)^8391 ≤ (21656477166683/50000000000000 : ℝ)^6343 := by
    have hnat : (5312621469 : ℕ)^8391*50000000000000^6343 ≤ 21656477166683^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312621469 10000000000 21656477166683 50000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2078885977/10000000000 : ℝ)^8391 ≤ (1251914963887/10000000000000 : ℝ)^6343 := by
    have hnat : (2078885977 : ℕ)^8391*10000000000000^6343 ≤ 1251914963887^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2078885977 10000000000 1251914963887 10000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391702011/10000000000 : ℝ)^8391 ≤ (22083948008607/50000000000000 : ℝ)^6343 := by
    have hnat : (5391702011 : ℕ)^8391*50000000000000^6343 ≤ 22083948008607^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391702011 10000000000 22083948008607 50000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312621469/10000000000 : ℝ), (-2078885977/10000000000 : ℝ), (5391702011/10000000000 : ℝ)] ![(21656477166683/50000000000000 : ℝ), (1251914963887/10000000000000 : ℝ), (22083948008607/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312621469/10000000000 : ℝ)|^8391 ≤ (21656477166683/50000000000000 : ℝ)^6343
        have hw : |(5312621469/10000000000 : ℝ)|=(5312621469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2078885977/10000000000 : ℝ)|^8391 ≤ (1251914963887/10000000000000 : ℝ)^6343
        have hw : |(-2078885977/10000000000 : ℝ)|=(2078885977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391702011/10000000000 : ℝ)|^8391 ≤ (22083948008607/50000000000000 : ℝ)^6343
        have hw : |(5391702011/10000000000 : ℝ)|=(5391702011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_s7_6 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (664077627/1250000000 : ℝ)*x 0 + (5391702347/10000000000 : ℝ)*x 1 + (-519721533/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664077627/1250000000 : ℝ)^8391 ≤ (21656474723837/50000000000000 : ℝ)^6343 := by
    have hnat : (664077627 : ℕ)^8391*50000000000000^6343 ≤ 21656474723837^6343*1250000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664077627 1250000000 21656474723837 50000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391702347/10000000000 : ℝ)^8391 ≤ (44167899658369/100000000000000 : ℝ)^6343 := by
    have hnat : (5391702347 : ℕ)^8391*100000000000000^6343 ≤ 44167899658369^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391702347 10000000000 44167899658369 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (519721533/2500000000 : ℝ)^8391 ≤ (2503830174733/20000000000000 : ℝ)^6343 := by
    have hnat : (519721533 : ℕ)^8391*20000000000000^6343 ≤ 2503830174733^6343*2500000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519721533 2500000000 2503830174733 20000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664077627/1250000000 : ℝ), (5391702347/10000000000 : ℝ), (-519721533/2500000000 : ℝ)] ![(21656474723837/50000000000000 : ℝ), (44167899658369/100000000000000 : ℝ), (2503830174733/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664077627/1250000000 : ℝ)|^8391 ≤ (21656474723837/50000000000000 : ℝ)^6343
        have hw : |(664077627/1250000000 : ℝ)|=(664077627/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391702347/10000000000 : ℝ)|^8391 ≤ (44167899658369/100000000000000 : ℝ)^6343
        have hw : |(5391702347/10000000000 : ℝ)|=(5391702347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-519721533/2500000000 : ℝ)|^8391 ≤ (2503830174733/20000000000000 : ℝ)^6343
        have hw : |(-519721533/2500000000 : ℝ)|=(519721533/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_s7_7 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4356852841/10000000000 : ℝ)*x 0 + (4484138633/10000000000 : ℝ)*x 1 + (4233135937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4356852841/10000000000 : ℝ)^8391 ≤ (16658681404211/50000000000000 : ℝ)^6343 := by
    have hnat : (4356852841 : ℕ)^8391*50000000000000^6343 ≤ 16658681404211^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4356852841 10000000000 16658681404211 50000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4484138633/10000000000 : ℝ)^8391 ≤ (34611042865807/100000000000000 : ℝ)^6343 := by
    have hnat : (4484138633 : ℕ)^8391*100000000000000^6343 ≤ 34611042865807^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4484138633 10000000000 34611042865807 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4233135937/10000000000 : ℝ)^8391 ≤ (32071594306933/100000000000000 : ℝ)^6343 := by
    have hnat : (4233135937 : ℕ)^8391*100000000000000^6343 ≤ 32071594306933^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4233135937 10000000000 32071594306933 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4356852841/10000000000 : ℝ), (4484138633/10000000000 : ℝ), (4233135937/10000000000 : ℝ)] ![(16658681404211/50000000000000 : ℝ), (34611042865807/100000000000000 : ℝ), (32071594306933/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4356852841/10000000000 : ℝ)|^8391 ≤ (16658681404211/50000000000000 : ℝ)^6343
        have hw : |(4356852841/10000000000 : ℝ)|=(4356852841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4484138633/10000000000 : ℝ)|^8391 ≤ (34611042865807/100000000000000 : ℝ)^6343
        have hw : |(4484138633/10000000000 : ℝ)|=(4484138633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4233135937/10000000000 : ℝ)|^8391 ≤ (32071594306933/100000000000000 : ℝ)^6343
        have hw : |(4233135937/10000000000 : ℝ)|=(4233135937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1198_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150567503/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7043/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11419/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (357/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14081/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7043/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11419/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7043/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11419/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7043/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11419/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7043/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11419/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7043/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11419/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7043/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11419/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11419/100000 : ℝ) ^ (4195/1024 : ℝ) ≤ (2756982846921881/20000000000000000000 : ℝ) := by
    have hpowers : (11419/100000 : ℝ)^4195 ≤ (2756982846921881/20000000000000000000 : ℝ)^1024 := by
      have hnat : (11419 : ℕ)^4195*20000000000000000000^1024 ≤ 2756982846921881^1024*100000^4195 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11419 100000 2756982846921881 20000000000000000000 4195 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11419/100000 : ℝ)) (X := (2756982846921881/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4195 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7043/50000 : ℝ) ^ (4195/1024 : ℝ) ≤ (16286426357060589/50000000000000000000 : ℝ) := by
    have hpowers : (7043/50000 : ℝ)^4195 ≤ (16286426357060589/50000000000000000000 : ℝ)^1024 := by
      have hnat : (7043 : ℕ)^4195*50000000000000000000^1024 ≤ 16286426357060589^1024*50000^4195 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7043 50000 16286426357060589 50000000000000000000 4195 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7043/50000 : ℝ)) (X := (16286426357060589/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4195 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002756982846921881/10000000000000000000 : ℝ) ≤ (10000672909728251/10000000000000000 : ℝ) ^ (4195/1024 : ℝ) := by
    have hpowers : (10002756982846921881/10000000000000000000 : ℝ)^1024 ≤ (10000672909728251/10000000000000000 : ℝ)^4195 := by
      have hnat : (10002756982846921881 : ℕ)^1024*10000000000000000^4195 ≤ 10000672909728251^4195*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002756982846921881 10000000000000000000 10000672909728251 10000000000000000 1024 4195 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000672909728251/10000000000000000 : ℝ)) (X := (10002756982846921881/10000000000000000000 : ℝ)) (by norm_num) 4195 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046357766948730583/100000000000000000000 : ℝ) ≤ (1000113139543197/1000000000000000 : ℝ) ^ (4195/1024 : ℝ) := by
    have hpowers : (100046357766948730583/100000000000000000000 : ℝ)^1024 ≤ (1000113139543197/1000000000000000 : ℝ)^4195 := by
      have hnat : (100046357766948730583 : ℕ)^1024*1000000000000000^4195 ≤ 1000113139543197^4195*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046357766948730583 100000000000000000000 1000113139543197 1000000000000000 1024 4195 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000113139543197/1000000000000000 : ℝ)) (X := (100046357766948730583/100000000000000000000 : ℝ)) (by norm_num) 4195 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016286426357060589/25000000000000000000 : ℝ) ≤ (10001589881135689/10000000000000000 : ℝ) ^ (4195/1024 : ℝ) := by
    have hpowers : (25016286426357060589/25000000000000000000 : ℝ)^1024 ≤ (10001589881135689/10000000000000000 : ℝ)^4195 := by
      have hnat : (25016286426357060589 : ℕ)^1024*10000000000000000^4195 ≤ 10001589881135689^4195*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016286426357060589 25000000000000000000 10001589881135689 10000000000000000 1024 4195 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001589881135689/10000000000000000 : ℝ)) (X := (25016286426357060589/25000000000000000000 : ℝ)) (by norm_num) 4195 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2756982846921881/20000000000000000000 : ℝ) ≤ ((5332264750748742179/5334000000000000000 : ℝ)+2*(458485703719/266700000000000 : ℝ)*(11419/100000 : ℝ))^(4195/1024 : ℝ) := by
    rw [show (5332264750748742179/5334000000000000000 : ℝ)+2*(458485703719/266700000000000 : ℝ)*(11419/100000 : ℝ)=(10000672909728251/10000000000000000 : ℝ) by norm_num, show 1+2*(2756982846921881/20000000000000000000 : ℝ)=(10002756982846921881/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16286426357060589/50000000000000000000 : ℝ)+(2756982846921881/20000000000000000000 : ℝ) ≤ ((5332264750748742179/5334000000000000000 : ℝ)+(458485703719/266700000000000 : ℝ)*((7043/50000 : ℝ)+(11419/100000 : ℝ)))^(4195/1024 : ℝ) := by
    rw [show (5332264750748742179/5334000000000000000 : ℝ)+(458485703719/266700000000000 : ℝ)*((7043/50000 : ℝ)+(11419/100000 : ℝ))=(1000113139543197/1000000000000000 : ℝ) by norm_num, show 1+(16286426357060589/50000000000000000000 : ℝ)+(2756982846921881/20000000000000000000 : ℝ)=(100046357766948730583/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16286426357060589/50000000000000000000 : ℝ) ≤ ((5332264750748742179/5334000000000000000 : ℝ)+2*(458485703719/266700000000000 : ℝ)*(7043/50000 : ℝ))^(4195/1024 : ℝ) := by
    rw [show (5332264750748742179/5334000000000000000 : ℝ)+2*(458485703719/266700000000000 : ℝ)*(7043/50000 : ℝ)=(10001589881135689/10000000000000000 : ℝ) by norm_num, show 1+2*(16286426357060589/50000000000000000000 : ℝ)=(25016286426357060589/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5332264750748742179/5334000000000000000 : ℝ)*(X 1 0+X 2 0)+(458485703719/266700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4195/1024 : ℝ)) (lo := (11419/100000 : ℝ)) (hi := (7043/50000 : ℝ)) (c := (5332264750748742179/5334000000000000000 : ℝ)) (alpha := (458485703719/266700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5332264750748742179/5334000000000000000 : ℝ)*(X 0 1+X 2 1)+(458485703719/266700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4195/1024 : ℝ)) (lo := (11419/100000 : ℝ)) (hi := (7043/50000 : ℝ)) (c := (5332264750748742179/5334000000000000000 : ℝ)) (alpha := (458485703719/266700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5332264750748742179/5334000000000000000 : ℝ)*(X 0 2+X 1 2)+(458485703719/266700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4195/1024 : ℝ)) (lo := (11419/100000 : ℝ)) (hi := (7043/50000 : ℝ)) (c := (5332264750748742179/5334000000000000000 : ℝ)) (alpha := (458485703719/266700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1070195253/5000000000 : ℝ)*X 0 0+(1348004739/2500000000 : ℝ)*X 0 1+(526659299/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344527423/10000000000 : ℝ)*X 1 0+(-2203995147/10000000000 : ℝ)*X 1 1+(526659299/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672263711/5000000000 : ℝ)*X 2 0+(5266592991/10000000000 : ℝ)*X 2 1+(-2203995147/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((435684289/1000000000 : ℝ)*X 0 0+(2116249283/5000000000 : ℝ)*X 0 1+(4484774089/10000000000 : ℝ)*X 0 2+(435684289/1000000000 : ℝ)*X 1 0+(2116249283/5000000000 : ℝ)*X 1 1+(4484774089/10000000000 : ℝ)*X 1 2+(435684289/1000000000 : ℝ)*X 2 0+(2116249283/5000000000 : ℝ)*X 2 1+(4484774089/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-535098911/2500000000 : ℝ)*X 0 0+(5266908863/10000000000 : ℝ)*X 0 1+(673962707/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312621469/10000000000 : ℝ)*X 1 0+(-2078885977/10000000000 : ℝ)*X 1 1+(5391702011/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((664077627/1250000000 : ℝ)*X 2 0+(5391702347/10000000000 : ℝ)*X 2 1+(-519721533/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4356852841/10000000000 : ℝ)*X 0 0+(4484138633/10000000000 : ℝ)*X 0 1+(4233135937/10000000000 : ℝ)*X 0 2+(4356852841/10000000000 : ℝ)*X 1 0+(4484138633/10000000000 : ℝ)*X 1 1+(4233135937/10000000000 : ℝ)*X 1 2+(4356852841/10000000000 : ℝ)*X 2 0+(4484138633/10000000000 : ℝ)*X 2 1+(4233135937/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (150200978329023673394053461/17780000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1652736927/100000000000000 : ℝ)*(base19) + (76823589/5000000000000 : ℝ)*(base23) + (30670467/50000000000000 : ℝ)*(lower2) + (8534589/4000000000000 : ℝ)*(upper3) + (32140913/25000000000000 : ℝ)*(upper5) + (1193689067453159/20000000000000 : ℝ)*(major0) + (1193689067453159/20000000000000 : ℝ)*(major1) + (1193689067453159/20000000000000 : ℝ)*(major2) + (7972878444628337/100000000000000 : ℝ)*(sp0) + (7972922267792437/100000000000000 : ℝ)*(sp1) + (498307649003599/6250000000000 : ℝ)*(sp2) + (3963942019246709/100000000000000 : ℝ)*(sp3) + (22737950513/50000000000000 : ℝ)*(sp4) + (24453163871/100000000000000 : ℝ)*(sp7) + (198198323620529/5000000000000 : ℝ)*(f.failure) + (1993230980132341/25000000000000 : ℝ)*(f.sum) + (553894400191/666750000000000000000000000 : ℝ)*base66 + (545584104093446539/106680000000000000000000000000000 : ℝ)*base68 + (1363639912769006539/106680000000000000000000000000000 : ℝ)*base70 + (640296472451553461/106680000000000000000000000000000 : ℝ)*base71 + (386461582229/533400000000000000000000000 : ℝ)*base74 + (1225314351594926539/106680000000000000000000000000000 : ℝ)*base76 + (203274534523593461/106680000000000000000000000000000 : ℝ)*base77 + (1164951556308566539/106680000000000000000000000000000 : ℝ)*base80 + (18136957814861/2667000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (3930913/500000000000000000000 : ℝ)*base90 + (3930913/500000000000000000000 : ℝ)*base92 + (3930913/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9210777530042077493135593/3175000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (778443689/50000000000000 : ℝ)*(base19) + (282367823/25000000000000 : ℝ)*(base23) + (32735629/25000000000000 : ℝ)*(upper2) + (203991013/50000000000000 : ℝ)*(upper3) + (44284323/25000000000000 : ℝ)*(upper5) + (1499660190317269/25000000000000 : ℝ)*(major0) + (1499660190317269/25000000000000 : ℝ)*(major1) + (1499660190317269/25000000000000 : ℝ)*(major2) + (47474499929/100000000000000 : ℝ)*(sp1) + (49037195971/100000000000000 : ℝ)*(sp2) + (2003315135918903/25000000000000 : ℝ)*(sp4) + (1602642302457661/20000000000000 : ℝ)*(sp5) + (8013210377008349/100000000000000 : ℝ)*(sp6) + (249001305135091/6250000000000 : ℝ)*(sp7) + (249001305135091/6250000000000 : ℝ)*(f.failure) + (2003315135918903/25000000000000 : ℝ)*(f.sum) + (4948251804091/3333750000000000000000000000 : ℝ)*base65 + (698098952647209151/133350000000000000000000000000000 : ℝ)*base67 + (1261369809001790849/133350000000000000000000000000000 : ℝ)*base70 + (2106957062731190849/133350000000000000000000000000000 : ℝ)*base72 + (88566542971/208359375000000000000000000 : ℝ)*base73 + (935991220828340849/133350000000000000000000000000000 : ℝ)*base76 + (1158786067370090849/133350000000000000000000000000000 : ℝ)*base78 + (2049709855160409151/133350000000000000000000000000000 : ℝ)*base79 + (65757244041199/13335000000000000000000000000 : ℝ)*base81 + (4547773/625000000000000000000 : ℝ)*base89 + (4547773/625000000000000000000 : ℝ)*base91 + (4547773/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1198_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150567503/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7043/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11419/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (357/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14081/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1198_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1198_s8_0 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2140393941/10000000000 : ℝ)*x 0 + (2695985501/5000000000 : ℝ)*x 1 + (5266638743/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2140393941/10000000000 : ℝ)^8391 ≤ (13011472898027/100000000000000 : ℝ)^6343 := by
    have hnat : (2140393941 : ℕ)^8391*100000000000000^6343 ≤ 13011472898027^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2140393941 10000000000 13011472898027 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695985501/5000000000 : ℝ)^8391 ≤ (22085405517091/50000000000000 : ℝ)^6343 := by
    have hnat : (2695985501 : ℕ)^8391*50000000000000^6343 ≤ 22085405517091^6343*5000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695985501 5000000000 22085405517091 50000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266638743/10000000000 : ℝ)^8391 ≤ (2676107253753/6250000000000 : ℝ)^6343 := by
    have hnat : (5266638743 : ℕ)^8391*6250000000000^6343 ≤ 2676107253753^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266638743 10000000000 2676107253753 6250000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2140393941/10000000000 : ℝ), (2695985501/5000000000 : ℝ), (5266638743/10000000000 : ℝ)] ![(13011472898027/100000000000000 : ℝ), (22085405517091/50000000000000 : ℝ), (2676107253753/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2140393941/10000000000 : ℝ)|^8391 ≤ (13011472898027/100000000000000 : ℝ)^6343
        have hw : |(-2140393941/10000000000 : ℝ)|=(2140393941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695985501/5000000000 : ℝ)|^8391 ≤ (22085405517091/50000000000000 : ℝ)^6343
        have hw : |(2695985501/5000000000 : ℝ)|=(2695985501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266638743/10000000000 : ℝ)|^8391 ≤ (2676107253753/6250000000000 : ℝ)^6343
        have hw : |(5266638743/10000000000 : ℝ)|=(5266638743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_s8_1 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068903103/2000000000 : ℝ)*x 0 + (-1101975207/5000000000 : ℝ)*x 1 + (5266638721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068903103/2000000000 : ℝ)^8391 ≤ (21828635362887/50000000000000 : ℝ)^6343 := by
    have hnat : (1068903103 : ℕ)^8391*50000000000000^6343 ≤ 21828635362887^6343*2000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068903103 2000000000 21828635362887 50000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1101975207/5000000000 : ℝ)^8391 ≤ (6762506720451/50000000000000 : ℝ)^6343 := by
    have hnat : (1101975207 : ℕ)^8391*50000000000000^6343 ≤ 6762506720451^6343*5000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101975207 5000000000 6762506720451 50000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266638721/10000000000 : ℝ)^8391 ≤ (21408857911719/50000000000000 : ℝ)^6343 := by
    have hnat : (5266638721 : ℕ)^8391*50000000000000^6343 ≤ 21408857911719^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266638721 10000000000 21408857911719 50000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068903103/2000000000 : ℝ), (-1101975207/5000000000 : ℝ), (5266638721/10000000000 : ℝ)] ![(21828635362887/50000000000000 : ℝ), (6762506720451/50000000000000 : ℝ), (21408857911719/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068903103/2000000000 : ℝ)|^8391 ≤ (21828635362887/50000000000000 : ℝ)^6343
        have hw : |(1068903103/2000000000 : ℝ)|=(1068903103/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1101975207/5000000000 : ℝ)|^8391 ≤ (6762506720451/50000000000000 : ℝ)^6343
        have hw : |(-1101975207/5000000000 : ℝ)|=(1101975207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266638721/10000000000 : ℝ)|^8391 ≤ (21408857911719/50000000000000 : ℝ)^6343
        have hw : |(5266638721/10000000000 : ℝ)|=(5266638721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_s8_2 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068903099/2000000000 : ℝ)*x 0 + (5266638757/10000000000 : ℝ)*x 1 + (-275493799/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068903099/2000000000 : ℝ)^8391 ≤ (43657270509653/100000000000000 : ℝ)^6343 := by
    have hnat : (1068903099 : ℕ)^8391*100000000000000^6343 ≤ 43657270509653^6343*2000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068903099 2000000000 43657270509653 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266638757/10000000000 : ℝ)^8391 ≤ (42817716210617/100000000000000 : ℝ)^6343 := by
    have hnat : (5266638757 : ℕ)^8391*100000000000000^6343 ≤ 42817716210617^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266638757 10000000000 42817716210617 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (275493799/1250000000 : ℝ)^8391 ≤ (13525013262303/100000000000000 : ℝ)^6343 := by
    have hnat : (275493799 : ℕ)^8391*100000000000000^6343 ≤ 13525013262303^6343*1250000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275493799 1250000000 13525013262303 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068903099/2000000000 : ℝ), (5266638757/10000000000 : ℝ), (-275493799/1250000000 : ℝ)] ![(43657270509653/100000000000000 : ℝ), (42817716210617/100000000000000 : ℝ), (13525013262303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068903099/2000000000 : ℝ)|^8391 ≤ (43657270509653/100000000000000 : ℝ)^6343
        have hw : |(1068903099/2000000000 : ℝ)|=(1068903099/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266638757/10000000000 : ℝ)|^8391 ≤ (42817716210617/100000000000000 : ℝ)^6343
        have hw : |(5266638757/10000000000 : ℝ)|=(5266638757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-275493799/1250000000 : ℝ)|^8391 ≤ (13525013262303/100000000000000 : ℝ)^6343
        have hw : |(-275493799/1250000000 : ℝ)|=(275493799/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_s8_3 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1089211317/2500000000 : ℝ)*x 0 + (1058148121/2500000000 : ℝ)*x 1 + (2242339777/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089211317/2500000000 : ℝ)^8391 ≤ (1665864309929/5000000000000 : ℝ)^6343 := by
    have hnat : (1089211317 : ℕ)^8391*5000000000000^6343 ≤ 1665864309929^6343*2500000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089211317 2500000000 1665864309929 5000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1058148121/2500000000 : ℝ)^8391 ≤ (6413229529217/20000000000000 : ℝ)^6343 := by
    have hnat : (1058148121 : ℕ)^8391*20000000000000^6343 ≤ 6413229529217^6343*2500000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058148121 2500000000 6413229529217 20000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2242339777/5000000000 : ℝ)^8391 ≤ (34616566144577/100000000000000 : ℝ)^6343 := by
    have hnat : (2242339777 : ℕ)^8391*100000000000000^6343 ≤ 34616566144577^6343*5000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2242339777 5000000000 34616566144577 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1089211317/2500000000 : ℝ), (1058148121/2500000000 : ℝ), (2242339777/5000000000 : ℝ)] ![(1665864309929/5000000000000 : ℝ), (6413229529217/20000000000000 : ℝ), (34616566144577/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1089211317/2500000000 : ℝ)|^8391 ≤ (1665864309929/5000000000000 : ℝ)^6343
        have hw : |(1089211317/2500000000 : ℝ)|=(1089211317/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1058148121/2500000000 : ℝ)|^8391 ≤ (6413229529217/20000000000000 : ℝ)^6343
        have hw : |(1058148121/2500000000 : ℝ)|=(1058148121/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2242339777/5000000000 : ℝ)|^8391 ≤ (34616566144577/100000000000000 : ℝ)^6343
        have hw : |(2242339777/5000000000 : ℝ)|=(2242339777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_s8_4 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1070199401/5000000000 : ℝ)*x 0 + (5266954031/10000000000 : ℝ)*x 1 + (1078330897/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070199401/5000000000 : ℝ)^8391 ≤ (2602302397819/20000000000000 : ℝ)^6343 := by
    have hnat : (1070199401 : ℕ)^8391*20000000000000^6343 ≤ 2602302397819^6343*5000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070199401 5000000000 2602302397819 20000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266954031/10000000000 : ℝ)^8391 ≤ (1070527675101/2500000000000 : ℝ)^6343 := by
    have hnat : (5266954031 : ℕ)^8391*2500000000000^6343 ≤ 1070527675101^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266954031 10000000000 1070527675101 2500000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078330897/2000000000 : ℝ)^8391 ≤ (8833476197927/20000000000000 : ℝ)^6343 := by
    have hnat : (1078330897 : ℕ)^8391*20000000000000^6343 ≤ 8833476197927^6343*2000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078330897 2000000000 8833476197927 20000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1070199401/5000000000 : ℝ), (5266954031/10000000000 : ℝ), (1078330897/2000000000 : ℝ)] ![(2602302397819/20000000000000 : ℝ), (1070527675101/2500000000000 : ℝ), (8833476197927/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1070199401/5000000000 : ℝ)|^8391 ≤ (2602302397819/20000000000000 : ℝ)^6343
        have hw : |(-1070199401/5000000000 : ℝ)|=(1070199401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266954031/10000000000 : ℝ)|^8391 ≤ (1070527675101/2500000000000 : ℝ)^6343
        have hw : |(5266954031/10000000000 : ℝ)|=(5266954031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078330897/2000000000 : ℝ)|^8391 ≤ (8833476197927/20000000000000 : ℝ)^6343
        have hw : |(1078330897/2000000000 : ℝ)|=(1078330897/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_s8_5 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312633449/10000000000 : ℝ)*x 0 + (-2078934473/10000000000 : ℝ)*x 1 + (1347913609/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312633449/10000000000 : ℝ)^8391 ≤ (43313083540033/100000000000000 : ℝ)^6343 := by
    have hnat : (5312633449 : ℕ)^8391*100000000000000^6343 ≤ 43313083540033^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312633449 10000000000 43313083540033 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2078934473/10000000000 : ℝ)^8391 ≤ (3129883994951/25000000000000 : ℝ)^6343 := by
    have hnat : (2078934473 : ℕ)^8391*25000000000000^6343 ≤ 3129883994951^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2078934473 10000000000 3129883994951 25000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347913609/2500000000 : ℝ)^8391 ≤ (8833476091727/20000000000000 : ℝ)^6343 := by
    have hnat : (1347913609 : ℕ)^8391*20000000000000^6343 ≤ 8833476091727^6343*2500000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347913609 2500000000 8833476091727 20000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312633449/10000000000 : ℝ), (-2078934473/10000000000 : ℝ), (1347913609/2500000000 : ℝ)] ![(43313083540033/100000000000000 : ℝ), (3129883994951/25000000000000 : ℝ), (8833476091727/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312633449/10000000000 : ℝ)|^8391 ≤ (43313083540033/100000000000000 : ℝ)^6343
        have hw : |(5312633449/10000000000 : ℝ)|=(5312633449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2078934473/10000000000 : ℝ)|^8391 ≤ (3129883994951/25000000000000 : ℝ)^6343
        have hw : |(-2078934473/10000000000 : ℝ)|=(2078934473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347913609/2500000000 : ℝ)|^8391 ≤ (8833476091727/20000000000000 : ℝ)^6343
        have hw : |(1347913609/2500000000 : ℝ)|=(1347913609/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_s8_6 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312633333/10000000000 : ℝ)*x 0 + (5391654473/10000000000 : ℝ)*x 1 + (-2078934581/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312633333/10000000000 : ℝ)^8391 ≤ (43313082288949/100000000000000 : ℝ)^6343 := by
    have hnat : (5312633333 : ℕ)^8391*100000000000000^6343 ≤ 43313082288949^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312633333 10000000000 43313082288949 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391654473/10000000000 : ℝ)^8391 ≤ (22083690429797/50000000000000 : ℝ)^6343 := by
    have hnat : (5391654473 : ℕ)^8391*50000000000000^6343 ≤ 22083690429797^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391654473 10000000000 22083690429797 50000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2078934581/10000000000 : ℝ)^8391 ≤ (1564942105023/12500000000000 : ℝ)^6343 := by
    have hnat : (2078934581 : ℕ)^8391*12500000000000^6343 ≤ 1564942105023^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2078934581 10000000000 1564942105023 12500000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312633333/10000000000 : ℝ), (5391654473/10000000000 : ℝ), (-2078934581/10000000000 : ℝ)] ![(43313082288949/100000000000000 : ℝ), (22083690429797/50000000000000 : ℝ), (1564942105023/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312633333/10000000000 : ℝ)|^8391 ≤ (43313082288949/100000000000000 : ℝ)^6343
        have hw : |(5312633333/10000000000 : ℝ)|=(5312633333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391654473/10000000000 : ℝ)|^8391 ≤ (22083690429797/50000000000000 : ℝ)^6343
        have hw : |(5391654473/10000000000 : ℝ)|=(5391654473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2078934581/10000000000 : ℝ)|^8391 ≤ (1564942105023/12500000000000 : ℝ)^6343
        have hw : |(-2078934581/10000000000 : ℝ)|=(2078934581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_s8_7 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2178427389/5000000000 : ℝ)*x 0 + (4484045273/10000000000 : ℝ)*x 1 + (2116614547/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2178427389/5000000000 : ℝ)^8391 ≤ (33317382403473/100000000000000 : ℝ)^6343 := by
    have hnat : (2178427389 : ℕ)^8391*100000000000000^6343 ≤ 33317382403473^6343*5000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178427389 5000000000 33317382403473 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4484045273/10000000000 : ℝ)^8391 ≤ (3461008959993/10000000000000 : ℝ)^6343 := by
    have hnat : (4484045273 : ℕ)^8391*10000000000000^6343 ≤ 3461008959993^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4484045273 10000000000 3461008959993 10000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2116614547/5000000000 : ℝ)^8391 ≤ (32072527979033/100000000000000 : ℝ)^6343 := by
    have hnat : (2116614547 : ℕ)^8391*100000000000000^6343 ≤ 32072527979033^6343*5000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2116614547 5000000000 32072527979033 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2178427389/5000000000 : ℝ), (4484045273/10000000000 : ℝ), (2116614547/5000000000 : ℝ)] ![(33317382403473/100000000000000 : ℝ), (3461008959993/10000000000000 : ℝ), (32072527979033/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2178427389/5000000000 : ℝ)|^8391 ≤ (33317382403473/100000000000000 : ℝ)^6343
        have hw : |(2178427389/5000000000 : ℝ)|=(2178427389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4484045273/10000000000 : ℝ)|^8391 ≤ (3461008959993/10000000000000 : ℝ)^6343
        have hw : |(4484045273/10000000000 : ℝ)|=(4484045273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2116614547/5000000000 : ℝ)|^8391 ≤ (32072527979033/100000000000000 : ℝ)^6343
        have hw : |(2116614547/5000000000 : ℝ)|=(2116614547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1198_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150567503/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14081/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (357/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (457/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (88/625 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14081/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (357/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14081/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (357/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14081/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (357/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14081/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (357/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14081/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (357/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14081/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (357/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (357/3125 : ℝ) ^ (4195/1024 : ℝ) ≤ (1726207297335419/12500000000000000000 : ℝ) := by
    have hpowers : (357/3125 : ℝ)^4195 ≤ (1726207297335419/12500000000000000000 : ℝ)^1024 := by
      have hnat : (357 : ℕ)^4195*12500000000000000000^1024 ≤ 1726207297335419^1024*3125^4195 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        357 3125 1726207297335419 12500000000000000000 4195 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (357/3125 : ℝ)) (X := (1726207297335419/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4195 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14081/100000 : ℝ) ^ (4195/1024 : ℝ) ≤ (32525512368022693/100000000000000000000 : ℝ) := by
    have hpowers : (14081/100000 : ℝ)^4195 ≤ (32525512368022693/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14081 : ℕ)^4195*100000000000000000000^1024 ≤ 32525512368022693^1024*100000^4195 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14081 100000 32525512368022693 100000000000000000000 4195 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14081/100000 : ℝ)) (X := (32525512368022693/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4195 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251726207297335419/6250000000000000000 : ℝ) ≤ (250016852937151/250000000000000 : ℝ) ^ (4195/1024 : ℝ) := by
    have hpowers : (6251726207297335419/6250000000000000000 : ℝ)^1024 ≤ (250016852937151/250000000000000 : ℝ)^4195 := by
      have hnat : (6251726207297335419 : ℕ)^1024*250000000000000^4195 ≤ 250016852937151^4195*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251726207297335419 6250000000000000000 250016852937151 250000000000000 1024 4195 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250016852937151/250000000000000 : ℝ)) (X := (6251726207297335419/6250000000000000000 : ℝ)) (by norm_num) 4195 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009267034149341209/20000000000000000000 : ℝ) ≤ (2000226168810313/2000000000000000 : ℝ) ^ (4195/1024 : ℝ) := by
    have hpowers : (20009267034149341209/20000000000000000000 : ℝ)^1024 ≤ (2000226168810313/2000000000000000 : ℝ)^4195 := by
      have hnat : (20009267034149341209 : ℕ)^1024*2000000000000000^4195 ≤ 2000226168810313^4195*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009267034149341209 20000000000000000000 2000226168810313 2000000000000000 1024 4195 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000226168810313/2000000000000000 : ℝ)) (X := (20009267034149341209/20000000000000000000 : ℝ)) (by norm_num) 4195 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032525512368022693/50000000000000000000 : ℝ) ≤ (1000158757061709/1000000000000000 : ℝ) ^ (4195/1024 : ℝ) := by
    have hpowers : (50032525512368022693/50000000000000000000 : ℝ)^1024 ≤ (1000158757061709/1000000000000000 : ℝ)^4195 := by
      have hnat : (50032525512368022693 : ℕ)^1024*1000000000000000^4195 ≤ 1000158757061709^4195*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032525512368022693 50000000000000000000 1000158757061709 1000000000000000 1024 4195 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000158757061709/1000000000000000 : ℝ)) (X := (50032525512368022693/50000000000000000000 : ℝ)) (by norm_num) 4195 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1726207297335419/12500000000000000000 : ℝ) ≤ ((664033896039782327/664250000000000000 : ℝ)+2*(18269062621/10628000000000 : ℝ)*(357/3125 : ℝ))^(4195/1024 : ℝ) := by
    rw [show (664033896039782327/664250000000000000 : ℝ)+2*(18269062621/10628000000000 : ℝ)*(357/3125 : ℝ)=(250016852937151/250000000000000 : ℝ) by norm_num, show 1+2*(1726207297335419/12500000000000000000 : ℝ)=(6251726207297335419/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32525512368022693/100000000000000000000 : ℝ)+(1726207297335419/12500000000000000000 : ℝ) ≤ ((664033896039782327/664250000000000000 : ℝ)+(18269062621/10628000000000 : ℝ)*((14081/100000 : ℝ)+(357/3125 : ℝ)))^(4195/1024 : ℝ) := by
    rw [show (664033896039782327/664250000000000000 : ℝ)+(18269062621/10628000000000 : ℝ)*((14081/100000 : ℝ)+(357/3125 : ℝ))=(2000226168810313/2000000000000000 : ℝ) by norm_num, show 1+(32525512368022693/100000000000000000000 : ℝ)+(1726207297335419/12500000000000000000 : ℝ)=(20009267034149341209/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32525512368022693/100000000000000000000 : ℝ) ≤ ((664033896039782327/664250000000000000 : ℝ)+2*(18269062621/10628000000000 : ℝ)*(14081/100000 : ℝ))^(4195/1024 : ℝ) := by
    rw [show (664033896039782327/664250000000000000 : ℝ)+2*(18269062621/10628000000000 : ℝ)*(14081/100000 : ℝ)=(1000158757061709/1000000000000000 : ℝ) by norm_num, show 1+2*(32525512368022693/100000000000000000000 : ℝ)=(50032525512368022693/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (664033896039782327/664250000000000000 : ℝ)*(X 1 0+X 2 0)+(18269062621/10628000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4195/1024 : ℝ)) (lo := (357/3125 : ℝ)) (hi := (14081/100000 : ℝ)) (c := (664033896039782327/664250000000000000 : ℝ)) (alpha := (18269062621/10628000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (664033896039782327/664250000000000000 : ℝ)*(X 0 1+X 2 1)+(18269062621/10628000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4195/1024 : ℝ)) (lo := (357/3125 : ℝ)) (hi := (14081/100000 : ℝ)) (c := (664033896039782327/664250000000000000 : ℝ)) (alpha := (18269062621/10628000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (664033896039782327/664250000000000000 : ℝ)*(X 0 2+X 1 2)+(18269062621/10628000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4195/1024 : ℝ)) (lo := (357/3125 : ℝ)) (hi := (14081/100000 : ℝ)) (c := (664033896039782327/664250000000000000 : ℝ)) (alpha := (18269062621/10628000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2140393941/10000000000 : ℝ)*X 0 0+(2695985501/5000000000 : ℝ)*X 0 1+(5266638743/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1068903103/2000000000 : ℝ)*X 1 0+(-1101975207/5000000000 : ℝ)*X 1 1+(5266638721/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068903099/2000000000 : ℝ)*X 2 0+(5266638757/10000000000 : ℝ)*X 2 1+(-275493799/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1089211317/2500000000 : ℝ)*X 0 0+(1058148121/2500000000 : ℝ)*X 0 1+(2242339777/5000000000 : ℝ)*X 0 2+(1089211317/2500000000 : ℝ)*X 1 0+(1058148121/2500000000 : ℝ)*X 1 1+(2242339777/5000000000 : ℝ)*X 1 2+(1089211317/2500000000 : ℝ)*X 2 0+(1058148121/2500000000 : ℝ)*X 2 1+(2242339777/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1070199401/5000000000 : ℝ)*X 0 0+(5266954031/10000000000 : ℝ)*X 0 1+(1078330897/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312633449/10000000000 : ℝ)*X 1 0+(-2078934473/10000000000 : ℝ)*X 1 1+(1347913609/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312633333/10000000000 : ℝ)*X 2 0+(5391654473/10000000000 : ℝ)*X 2 1+(-2078934581/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2178427389/5000000000 : ℝ)*X 0 0+(4484045273/10000000000 : ℝ)*X 0 1+(2116614547/5000000000 : ℝ)*X 0 2+(2178427389/5000000000 : ℝ)*X 1 0+(4484045273/10000000000 : ℝ)*X 1 1+(2116614547/5000000000 : ℝ)*X 1 2+(2178427389/5000000000 : ℝ)*X 2 0+(4484045273/10000000000 : ℝ)*X 2 1+(2116614547/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (136440938383689962215518417/16606250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (81057291/5000000000000 : ℝ)*(base19) + (1475102779/100000000000000 : ℝ)*(base23) + (62095169/100000000000000 : ℝ)*(lower2) + (97435373/50000000000000 : ℝ)*(upper3) + (69535053/50000000000000 : ℝ)*(upper5) + (2986452584950557/50000000000000 : ℝ)*(major0) + (2986452584950557/50000000000000 : ℝ)*(major1) + (2986452584950557/50000000000000 : ℝ)*(major2) + (797883718989317/10000000000000 : ℝ)*(sp0) + (7978879956965129/100000000000000 : ℝ)*(sp1) + (797888010300817/10000000000000 : ℝ)*(sp2) + (1983452520914477/50000000000000 : ℝ)*(sp3) + (44388217779/100000000000000 : ℝ)*(sp4) + (11722993823/50000000000000 : ℝ)*(sp7) + (19834642439083/500000000000 : ℝ)*(f.failure) + (7978881578110949/100000000000000 : ℝ)*(f.sum) + (8009814269723/1328500000000000000000000000 : ℝ)*base65 + (108142084206918861/33212500000000000000000000000000 : ℝ)*base68 + (129726913929093861/33212500000000000000000000000000 : ℝ)*base70 + (222940504548281139/33212500000000000000000000000000 : ℝ)*base71 + (1052132867023/1328500000000000000000000000 : ℝ)*base74 + (647276832601443861/33212500000000000000000000000000 : ℝ)*base76 + (9645919938843639/33212500000000000000000000000000 : ℝ)*base77 + (449628731470131361/33212500000000000000000000000000 : ℝ)*base80 + (906440477277/265700000000000000000000000 : ℝ)*base81 + (80251/50000000000000000000 : ℝ)*base90 + (80251/50000000000000000000 : ℝ)*base92 + (80251/50000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8466308241673520481339/2657000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1355849751/100000000000000 : ℝ)*(base19) + (324553443/25000000000000 : ℝ)*(base23) + (107006851/25000000000000 : ℝ)*(lower1) + (80294733/100000000000000 : ℝ)*(upper2) + (10917811/12500000000000 : ℝ)*(upper3) + (63184943/50000000000000 : ℝ)*(upper5) + (6003071953344807/100000000000000 : ℝ)*(major0) + (6003071953344807/100000000000000 : ℝ)*(major1) + (6003071953344807/100000000000000 : ℝ)*(major2) + (5611977747/100000000000000 : ℝ)*(sp1) + (4009589962324339/50000000000000 : ℝ)*(sp4) + (400958647841059/5000000000000 : ℝ)*(sp5) + (4009589313217453/50000000000000 : ℝ)*(sp6) + (498370484478381/12500000000000 : ℝ)*(sp7) + (498370484478381/12500000000000 : ℝ)*(f.failure) + (4009589962324339/50000000000000 : ℝ)*(f.sum) + (478980626419/2657000000000000000000000000 : ℝ)*base65 + (480078999426336611/66425000000000000000000000000000 : ℝ)*base68 + (2196424030210163389/66425000000000000000000000000000 : ℝ)*base69 + (337608317745811611/66425000000000000000000000000000 : ℝ)*base72 + (2107920056107/2657000000000000000000000000 : ℝ)*base74 + (364809402407561611/66425000000000000000000000000000 : ℝ)*base76 + (40055857287663389/66425000000000000000000000000000 : ℝ)*base77 + (441414200007663389/66425000000000000000000000000000 : ℝ)*base79 + (69671250010953/2657000000000000000000000000 : ℝ)*base81 + (2847357/1250000000000000000000 : ℝ)*base90 + (2847357/1250000000000000000000 : ℝ)*base92 + (2847357/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1198_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150567503/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14081/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (357/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (457/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (88/625 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1198_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1198_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150567503/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (441/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2279/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (457/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (88/625 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1198_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1198_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1198_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150567503/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (441/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2279/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (457/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (88/625 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1198_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
