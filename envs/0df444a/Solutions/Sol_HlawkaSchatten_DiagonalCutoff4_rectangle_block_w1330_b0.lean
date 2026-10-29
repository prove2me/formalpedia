-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1330_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:01:51.456661+00:00
-- url     : https://prove2.me/submissions/f8b27863-752a-4ef5-a281-822bec82b3b4

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
theorem support_rectangle_w1330_s0_0 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1816261549/10000000000 : ℝ)*x 0 + (46891529/78125000 : ℝ)*x 1 + (4808037877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1816261549/10000000000 : ℝ)^2145 ≤ (5319564679923/50000000000000 : ℝ)^1633 := by
    have hnat : (1816261549 : ℕ)^2145*50000000000000^1633 ≤ 5319564679923^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1816261549 10000000000 5319564679923 50000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (46891529/78125000 : ℝ)^2145 ≤ (51144081425193/100000000000000 : ℝ)^1633 := by
    have hnat : (46891529 : ℕ)^2145*100000000000000^1633 ≤ 51144081425193^1633*78125000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46891529 78125000 51144081425193 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4808037877/10000000000 : ℝ)^2145 ≤ (764335783869/2000000000000 : ℝ)^1633 := by
    have hnat : (4808037877 : ℕ)^2145*2000000000000^1633 ≤ 764335783869^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4808037877 10000000000 764335783869 2000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1816261549/10000000000 : ℝ), (46891529/78125000 : ℝ), (4808037877/10000000000 : ℝ)] ![(5319564679923/50000000000000 : ℝ), (51144081425193/100000000000000 : ℝ), (764335783869/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1816261549/10000000000 : ℝ)|^2145 ≤ (5319564679923/50000000000000 : ℝ)^1633
        have hw : |(-1816261549/10000000000 : ℝ)|=(1816261549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(46891529/78125000 : ℝ)|^2145 ≤ (51144081425193/100000000000000 : ℝ)^1633
        have hw : |(46891529/78125000 : ℝ)|=(46891529/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4808037877/10000000000 : ℝ)|^2145 ≤ (764335783869/2000000000000 : ℝ)^1633
        have hw : |(4808037877/10000000000 : ℝ)|=(4808037877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1330_s0_1 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (550315703/1000000000 : ℝ)*x 0 + (-2495563989/10000000000 : ℝ)*x 1 + (24040191/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (550315703/1000000000 : ℝ)^2145 ≤ (45633636730939/100000000000000 : ℝ)^1633 := by
    have hnat : (550315703 : ℕ)^2145*100000000000000^1633 ≤ 45633636730939^1633*1000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550315703 1000000000 45633636730939 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2495563989/10000000000 : ℝ)^2145 ≤ (16149570688581/100000000000000 : ℝ)^1633 := by
    have hnat : (2495563989 : ℕ)^2145*100000000000000^1633 ≤ 16149570688581^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2495563989 10000000000 16149570688581 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (24040191/50000000 : ℝ)^2145 ≤ (38216792565779/100000000000000 : ℝ)^1633 := by
    have hnat : (24040191 : ℕ)^2145*100000000000000^1633 ≤ 38216792565779^1633*50000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24040191 50000000 38216792565779 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(550315703/1000000000 : ℝ), (-2495563989/10000000000 : ℝ), (24040191/50000000 : ℝ)] ![(45633636730939/100000000000000 : ℝ), (16149570688581/100000000000000 : ℝ), (38216792565779/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(550315703/1000000000 : ℝ)|^2145 ≤ (45633636730939/100000000000000 : ℝ)^1633
        have hw : |(550315703/1000000000 : ℝ)|=(550315703/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2495563989/10000000000 : ℝ)|^2145 ≤ (16149570688581/100000000000000 : ℝ)^1633
        have hw : |(-2495563989/10000000000 : ℝ)|=(2495563989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(24040191/50000000 : ℝ)|^2145 ≤ (38216792565779/100000000000000 : ℝ)^1633
        have hw : |(24040191/50000000 : ℝ)|=(24040191/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1330_s0_2 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5503156493/10000000000 : ℝ)*x 0 + (961607661/2000000000 : ℝ)*x 1 + (-623891137/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5503156493/10000000000 : ℝ)^2145 ≤ (9126726176369/20000000000000 : ℝ)^1633 := by
    have hnat : (5503156493 : ℕ)^2145*20000000000000^1633 ≤ 9126726176369^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5503156493 10000000000 9126726176369 20000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (961607661/2000000000 : ℝ)^2145 ≤ (38216793662047/100000000000000 : ℝ)^1633 := by
    have hnat : (961607661 : ℕ)^2145*100000000000000^1633 ≤ 38216793662047^1633*2000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      961607661 2000000000 38216793662047 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (623891137/2500000000 : ℝ)^2145 ≤ (201869693003/1250000000000 : ℝ)^1633 := by
    have hnat : (623891137 : ℕ)^2145*1250000000000^1633 ≤ 201869693003^1633*2500000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      623891137 2500000000 201869693003 1250000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5503156493/10000000000 : ℝ), (961607661/2000000000 : ℝ), (-623891137/2500000000 : ℝ)] ![(9126726176369/20000000000000 : ℝ), (38216793662047/100000000000000 : ℝ), (201869693003/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5503156493/10000000000 : ℝ)|^2145 ≤ (9126726176369/20000000000000 : ℝ)^1633
        have hw : |(5503156493/10000000000 : ℝ)|=(5503156493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(961607661/2000000000 : ℝ)|^2145 ≤ (38216793662047/100000000000000 : ℝ)^1633
        have hw : |(961607661/2000000000 : ℝ)|=(961607661/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-623891137/2500000000 : ℝ)|^2145 ≤ (201869693003/1250000000000 : ℝ)^1633
        have hw : |(-623891137/2500000000 : ℝ)|=(623891137/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1330_s0_3 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2090274349/5000000000 : ℝ)*x 0 + (3107182717/10000000000 : ℝ)*x 1 + (1399244113/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2090274349/5000000000 : ℝ)^2145 ≤ (3975459140423/12500000000000 : ℝ)^1633 := by
    have hnat : (2090274349 : ℕ)^2145*12500000000000^1633 ≤ 3975459140423^1633*5000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2090274349 5000000000 3975459140423 12500000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3107182717/10000000000 : ℝ)^2145 ≤ (2692259097769/12500000000000 : ℝ)^1633 := by
    have hnat : (3107182717 : ℕ)^2145*12500000000000^1633 ≤ 2692259097769^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3107182717 10000000000 2692259097769 12500000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1399244113/2500000000 : ℝ)^2145 ≤ (4665825408079/10000000000000 : ℝ)^1633 := by
    have hnat : (1399244113 : ℕ)^2145*10000000000000^1633 ≤ 4665825408079^1633*2500000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1399244113 2500000000 4665825408079 10000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2090274349/5000000000 : ℝ), (3107182717/10000000000 : ℝ), (1399244113/2500000000 : ℝ)] ![(3975459140423/12500000000000 : ℝ), (2692259097769/12500000000000 : ℝ), (4665825408079/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2090274349/5000000000 : ℝ)|^2145 ≤ (3975459140423/12500000000000 : ℝ)^1633
        have hw : |(2090274349/5000000000 : ℝ)|=(2090274349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3107182717/10000000000 : ℝ)|^2145 ≤ (2692259097769/12500000000000 : ℝ)^1633
        have hw : |(3107182717/10000000000 : ℝ)|=(3107182717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1399244113/2500000000 : ℝ)|^2145 ≤ (4665825408079/10000000000000 : ℝ)^1633
        have hw : |(1399244113/2500000000 : ℝ)|=(1399244113/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1330_s0_4 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1820781541/10000000000 : ℝ)*x 0 + (4838791941/10000000000 : ℝ)*x 1 + (1492566043/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1820781541/10000000000 : ℝ)^2145 ≤ (1334240133803/12500000000000 : ℝ)^1633 := by
    have hnat : (1820781541 : ℕ)^2145*12500000000000^1633 ≤ 1334240133803^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1820781541 10000000000 1334240133803 12500000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4838791941/10000000000 : ℝ)^2145 ≤ (38538203033349/100000000000000 : ℝ)^1633 := by
    have hnat : (4838791941 : ℕ)^2145*100000000000000^1633 ≤ 38538203033349^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4838791941 10000000000 38538203033349 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1492566043/2500000000 : ℝ)^2145 ≤ (50787875877841/100000000000000 : ℝ)^1633 := by
    have hnat : (1492566043 : ℕ)^2145*100000000000000^1633 ≤ 50787875877841^1633*2500000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1492566043 2500000000 50787875877841 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1820781541/10000000000 : ℝ), (4838791941/10000000000 : ℝ), (1492566043/2500000000 : ℝ)] ![(1334240133803/12500000000000 : ℝ), (38538203033349/100000000000000 : ℝ), (50787875877841/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1820781541/10000000000 : ℝ)|^2145 ≤ (1334240133803/12500000000000 : ℝ)^1633
        have hw : |(-1820781541/10000000000 : ℝ)|=(1820781541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4838791941/10000000000 : ℝ)|^2145 ≤ (38538203033349/100000000000000 : ℝ)^1633
        have hw : |(4838791941/10000000000 : ℝ)|=(4838791941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1492566043/2500000000 : ℝ)|^2145 ≤ (50787875877841/100000000000000 : ℝ)^1633
        have hw : |(1492566043/2500000000 : ℝ)|=(1492566043/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1330_s0_5 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2588905291/5000000000 : ℝ)*x 0 + (-1333339373/10000000000 : ℝ)*x 1 + (186570729/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2588905291/5000000000 : ℝ)^2145 ≤ (42123208078791/100000000000000 : ℝ)^1633 := by
    have hnat : (2588905291 : ℕ)^2145*100000000000000^1633 ≤ 42123208078791^1633*5000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588905291 5000000000 42123208078791 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1333339373/10000000000 : ℝ)^2145 ≤ (7088925465977/100000000000000 : ℝ)^1633 := by
    have hnat : (1333339373 : ℕ)^2145*100000000000000^1633 ≤ 7088925465977^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1333339373 10000000000 7088925465977 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (186570729/312500000 : ℝ)^2145 ≤ (1587120826469/3125000000000 : ℝ)^1633 := by
    have hnat : (186570729 : ℕ)^2145*3125000000000^1633 ≤ 1587120826469^1633*312500000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      186570729 312500000 1587120826469 3125000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2588905291/5000000000 : ℝ), (-1333339373/10000000000 : ℝ), (186570729/312500000 : ℝ)] ![(42123208078791/100000000000000 : ℝ), (7088925465977/100000000000000 : ℝ), (1587120826469/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2588905291/5000000000 : ℝ)|^2145 ≤ (42123208078791/100000000000000 : ℝ)^1633
        have hw : |(2588905291/5000000000 : ℝ)|=(2588905291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1333339373/10000000000 : ℝ)|^2145 ≤ (7088925465977/100000000000000 : ℝ)^1633
        have hw : |(-1333339373/10000000000 : ℝ)|=(1333339373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(186570729/312500000 : ℝ)|^2145 ≤ (1587120826469/3125000000000 : ℝ)^1633
        have hw : |(186570729/312500000 : ℝ)|=(186570729/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1330_s0_6 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2588905477/5000000000 : ℝ)*x 0 + (5970263647/10000000000 : ℝ)*x 1 + (-333334573/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2588905477/5000000000 : ℝ)^2145 ≤ (21061606026997/50000000000000 : ℝ)^1633 := by
    have hnat : (2588905477 : ℕ)^2145*50000000000000^1633 ≤ 21061606026997^1633*5000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588905477 5000000000 21061606026997 50000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5970263647/10000000000 : ℝ)^2145 ≤ (10157574002301/20000000000000 : ℝ)^1633 := by
    have hnat : (5970263647 : ℕ)^2145*20000000000000^1633 ≤ 10157574002301^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5970263647 10000000000 10157574002301 20000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (333334573/2500000000 : ℝ)^2145 ≤ (7088917916681/100000000000000 : ℝ)^1633 := by
    have hnat : (333334573 : ℕ)^2145*100000000000000^1633 ≤ 7088917916681^1633*2500000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      333334573 2500000000 7088917916681 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2588905477/5000000000 : ℝ), (5970263647/10000000000 : ℝ), (-333334573/2500000000 : ℝ)] ![(21061606026997/50000000000000 : ℝ), (10157574002301/20000000000000 : ℝ), (7088917916681/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2588905477/5000000000 : ℝ)|^2145 ≤ (21061606026997/50000000000000 : ℝ)^1633
        have hw : |(2588905477/5000000000 : ℝ)|=(2588905477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5970263647/10000000000 : ℝ)|^2145 ≤ (10157574002301/20000000000000 : ℝ)^1633
        have hw : |(5970263647/10000000000 : ℝ)|=(5970263647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-333334573/2500000000 : ℝ)|^2145 ≤ (7088917916681/100000000000000 : ℝ)^1633
        have hw : |(-333334573/2500000000 : ℝ)|=(333334573/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1330_s0_7 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2094986033/5000000000 : ℝ)*x 0 + (5532851031/10000000000 : ℝ)*x 1 + (3173596269/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2094986033/5000000000 : ℝ)^2145 ≤ (3189787175999/10000000000000 : ℝ)^1633 := by
    have hnat : (2094986033 : ℕ)^2145*10000000000000^1633 ≤ 3189787175999^1633*5000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2094986033 5000000000 3189787175999 10000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5532851031/10000000000 : ℝ)^2145 ≤ (45957341994471/100000000000000 : ℝ)^1633 := by
    have hnat : (5532851031 : ℕ)^2145*100000000000000^1633 ≤ 45957341994471^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5532851031 10000000000 45957341994471 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3173596269/10000000000 : ℝ)^2145 ≤ (22144786231787/100000000000000 : ℝ)^1633 := by
    have hnat : (3173596269 : ℕ)^2145*100000000000000^1633 ≤ 22144786231787^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3173596269 10000000000 22144786231787 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2094986033/5000000000 : ℝ), (5532851031/10000000000 : ℝ), (3173596269/10000000000 : ℝ)] ![(3189787175999/10000000000000 : ℝ), (45957341994471/100000000000000 : ℝ), (22144786231787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2094986033/5000000000 : ℝ)|^2145 ≤ (3189787175999/10000000000000 : ℝ)^1633
        have hw : |(2094986033/5000000000 : ℝ)|=(2094986033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5532851031/10000000000 : ℝ)|^2145 ≤ (45957341994471/100000000000000 : ℝ)^1633
        have hw : |(5532851031/10000000000 : ℝ)|=(5532851031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3173596269/10000000000 : ℝ)|^2145 ≤ (22144786231787/100000000000000 : ℝ)^1633
        have hw : |(3173596269/10000000000 : ℝ)|=(3173596269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1330_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154255973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (331/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13479/50000 : ℝ)*pair X 0 0 := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
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
  have hpowlo : (0 : ℝ) ^ (4289/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4289 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4289*1^1024 ≤ 0^1024*1^4289 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4289 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4289 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4289/1024 : ℝ) ≤ (2153959833364462047/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4289 ≤ (2153959833364462047/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4289*100000000000000000000^1024 ≤ 2153959833364462047^1024*5^4289 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2153959833364462047 100000000000000000000 4289 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2153959833364462047/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4289 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4289/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4289 := by
      have hnat : (1 : ℕ)^1024*1^4289 ≤ 1^4289*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4289 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4289 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (102153959833364462047/100000000000000000000 : ℝ) ≤ (502550474607013/500000000000000 : ℝ) ^ (4289/1024 : ℝ) := by
    have hpowers : (102153959833364462047/100000000000000000000 : ℝ)^1024 ≤ (502550474607013/500000000000000 : ℝ)^4289 := by
      have hnat : (102153959833364462047 : ℕ)^1024*500000000000000^4289 ≤ 502550474607013^4289*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102153959833364462047 100000000000000000000 502550474607013 500000000000000 1024 4289 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (502550474607013/500000000000000 : ℝ)) (X := (102153959833364462047/100000000000000000000 : ℝ)) (by norm_num) 4289 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (52153959833364462047/50000000000000000000 : ℝ) ≤ (252550474607013/250000000000000 : ℝ) ^ (4289/1024 : ℝ) := by
    have hpowers : (52153959833364462047/50000000000000000000 : ℝ)^1024 ≤ (252550474607013/250000000000000 : ℝ)^4289 := by
      have hnat : (52153959833364462047 : ℕ)^1024*250000000000000^4289 ≤ 252550474607013^4289*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52153959833364462047 50000000000000000000 252550474607013 250000000000000 1024 4289 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (252550474607013/250000000000000 : ℝ)) (X := (52153959833364462047/50000000000000000000 : ℝ)) (by norm_num) 4289 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(2550474607013/200000000000000 : ℝ)*(0 : ℝ))^(4289/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(2550474607013/200000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2153959833364462047/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(2550474607013/200000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4289/1024 : ℝ) := by
    rw [show (1 : ℝ)+(2550474607013/200000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(502550474607013/500000000000000 : ℝ) by norm_num, show 1+(2153959833364462047/100000000000000000000 : ℝ)+(0 : ℝ)=(102153959833364462047/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2153959833364462047/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(2550474607013/200000000000000 : ℝ)*(2/5 : ℝ))^(4289/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(2550474607013/200000000000000 : ℝ)*(2/5 : ℝ)=(252550474607013/250000000000000 : ℝ) by norm_num, show 1+2*(2153959833364462047/100000000000000000000 : ℝ)=(52153959833364462047/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(2550474607013/200000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4289/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2550474607013/200000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(2550474607013/200000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4289/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2550474607013/200000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(2550474607013/200000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4289/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2550474607013/200000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1816261549/10000000000 : ℝ)*X 0 0+(46891529/78125000 : ℝ)*X 0 1+(4808037877/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((550315703/1000000000 : ℝ)*X 1 0+(-2495563989/10000000000 : ℝ)*X 1 1+(24040191/50000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5503156493/10000000000 : ℝ)*X 2 0+(961607661/2000000000 : ℝ)*X 2 1+(-623891137/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2090274349/5000000000 : ℝ)*X 0 0+(3107182717/10000000000 : ℝ)*X 0 1+(1399244113/2500000000 : ℝ)*X 0 2+(2090274349/5000000000 : ℝ)*X 1 0+(3107182717/10000000000 : ℝ)*X 1 1+(1399244113/2500000000 : ℝ)*X 1 2+(2090274349/5000000000 : ℝ)*X 2 0+(3107182717/10000000000 : ℝ)*X 2 1+(1399244113/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1820781541/10000000000 : ℝ)*X 0 0+(4838791941/10000000000 : ℝ)*X 0 1+(1492566043/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2588905291/5000000000 : ℝ)*X 1 0+(-1333339373/10000000000 : ℝ)*X 1 1+(186570729/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2588905477/5000000000 : ℝ)*X 2 0+(5970263647/10000000000 : ℝ)*X 2 1+(-333334573/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2094986033/5000000000 : ℝ)*X 0 0+(5532851031/10000000000 : ℝ)*X 0 1+(3173596269/10000000000 : ℝ)*X 0 2+(2094986033/5000000000 : ℝ)*X 1 0+(5532851031/10000000000 : ℝ)*X 1 1+(3173596269/10000000000 : ℝ)*X 1 2+(2094986033/5000000000 : ℝ)*X 2 0+(5532851031/10000000000 : ℝ)*X 2 1+(3173596269/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8205345139862266898697/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8022361/12500000000000 : ℝ)*(base1) + (584451/20000000000000 : ℝ)*(base16) + (104044059/12500000000000 : ℝ)*(base19) + (376777001/50000000000000 : ℝ)*(base23) + (6333313/4000000000000 : ℝ)*(upper3) + (619557078309277/100000000000000 : ℝ)*(major0) + (619557078309277/100000000000000 : ℝ)*(major1) + (619557078309277/100000000000000 : ℝ)*(major2) + (20936740091347/2500000000000 : ℝ)*(sp0) + (167494203072333/20000000000000 : ℝ)*(sp1) + (83747109708239/10000000000000 : ℝ)*(sp2) + (200820343849019/50000000000000 : ℝ)*(sp3) + (11555807/500000000000 : ℝ)*(sp4) + (722350313/50000000000000 : ℝ)*(sp7) + (401642196577553/100000000000000 : ℝ)*(f.failure) + (104683981329549/12500000000000 : ℝ)*(f.sum) + (10619143959601/10000000000000000000000000000 : ℝ)*base65 + (202385154919601/20000000000000000000000000000 : ℝ)*base67 + (255012264559601/20000000000000000000000000000 : ℝ)*base69 + (199962591359601/20000000000000000000000000000 : ℝ)*base71 + (16814682510399/10000000000000000000000000000 : ℝ)*base74 + (107647675759601/20000000000000000000000000000 : ℝ)*base75 + (137018524959601/20000000000000000000000000000 : ℝ)*base77 + (153726975119601/20000000000000000000000000000 : ℝ)*base79 + (50232488659601/10000000000000000000000000000 : ℝ)*base81 + (7974069/10000000000000000000000 : ℝ)*base89 + (7974069/10000000000000000000000 : ℝ)*base91 + (7974069/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18225584331906014249961/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (47109719/2500000000000 : ℝ)*(base19) + (100148739/5000000000000 : ℝ)*(base23) + (3647389/25000000000000 : ℝ)*(base32) + (230920811/100000000000000 : ℝ)*(upper3) + (101739623/50000000000000 : ℝ)*(upper5) + (653833639333501/100000000000000 : ℝ)*(major0) + (653833639333501/100000000000000 : ℝ)*(major1) + (653833639333501/100000000000000 : ℝ)*(major2) + (1952483847/50000000000000 : ℝ)*(sp1) + (38253701/800000000000 : ℝ)*(sp2) + (441902133061281/50000000000000 : ℝ)*(sp4) + (220949619191527/25000000000000 : ℝ)*(sp5) + (883797481435157/100000000000000 : ℝ)*(sp6) + (42386275494709/10000000000000 : ℝ)*(sp7) + (211931384768323/50000000000000 : ℝ)*(f.failure) + (441902133061281/50000000000000 : ℝ)*(f.sum) + (11794621462513/10000000000000000000000000000 : ℝ)*base65 + (78925767802513/20000000000000000000000000000 : ℝ)*base67 + (42825102962513/20000000000000000000000000000 : ℝ)*base69 + (63624411877487/20000000000000000000000000000 : ℝ)*base72 + (46604139042513/10000000000000000000000000000 : ℝ)*base73 + (5342111762513/20000000000000000000000000000 : ℝ)*base75 + (32699783582513/20000000000000000000000000000 : ℝ)*base77 + (69135539437487/20000000000000000000000000000 : ℝ)*base80 + (25549651782513/10000000000000000000000000000 : ℝ)*base81 + (6056721/5000000000000000000000 : ℝ)*base90 + (6056721/5000000000000000000000 : ℝ)*base92 + (6056721/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1330_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154255973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (331/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13479/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1330_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1330_s1_0 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1001403329/5000000000 : ℝ)*x 0 + (5647564787/10000000000 : ℝ)*x 1 + (1260783783/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1001403329/5000000000 : ℝ)^2145 ≤ (12097052182777/100000000000000 : ℝ)^1633 := by
    have hnat : (1001403329 : ℕ)^2145*100000000000000^1633 ≤ 12097052182777^1633*5000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1001403329 5000000000 12097052182777 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5647564787/10000000000 : ℝ)^2145 ≤ (9442596436751/20000000000000 : ℝ)^1633 := by
    have hnat : (5647564787 : ℕ)^2145*20000000000000^1633 ≤ 9442596436751^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5647564787 10000000000 9442596436751 20000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1260783783/2500000000 : ℝ)^2145 ≤ (40689965628277/100000000000000 : ℝ)^1633 := by
    have hnat : (1260783783 : ℕ)^2145*100000000000000^1633 ≤ 40689965628277^1633*2500000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1260783783 2500000000 40689965628277 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1001403329/5000000000 : ℝ), (5647564787/10000000000 : ℝ), (1260783783/2500000000 : ℝ)] ![(12097052182777/100000000000000 : ℝ), (9442596436751/20000000000000 : ℝ), (40689965628277/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1001403329/5000000000 : ℝ)|^2145 ≤ (12097052182777/100000000000000 : ℝ)^1633
        have hw : |(-1001403329/5000000000 : ℝ)|=(1001403329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5647564787/10000000000 : ℝ)|^2145 ≤ (9442596436751/20000000000000 : ℝ)^1633
        have hw : |(5647564787/10000000000 : ℝ)|=(5647564787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1260783783/2500000000 : ℝ)|^2145 ≤ (40689965628277/100000000000000 : ℝ)^1633
        have hw : |(1260783783/2500000000 : ℝ)|=(1260783783/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1330_s1_1 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5406974281/10000000000 : ℝ)*x 0 + (-465135727/2000000000 : ℝ)*x 1 + (315195939/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5406974281/10000000000 : ℝ)^2145 ≤ (22294440097519/50000000000000 : ℝ)^1633 := by
    have hnat : (5406974281 : ℕ)^2145*50000000000000^1633 ≤ 22294440097519^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406974281 10000000000 22294440097519 50000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (465135727/2000000000 : ℝ)^2145 ≤ (3680288825137/25000000000000 : ℝ)^1633 := by
    have hnat : (465135727 : ℕ)^2145*25000000000000^1633 ≤ 3680288825137^1633*2000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      465135727 2000000000 3680288825137 25000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (315195939/625000000 : ℝ)^2145 ≤ (20344982241841/50000000000000 : ℝ)^1633 := by
    have hnat : (315195939 : ℕ)^2145*50000000000000^1633 ≤ 20344982241841^1633*625000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      315195939 625000000 20344982241841 50000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5406974281/10000000000 : ℝ), (-465135727/2000000000 : ℝ), (315195939/625000000 : ℝ)] ![(22294440097519/50000000000000 : ℝ), (3680288825137/25000000000000 : ℝ), (20344982241841/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5406974281/10000000000 : ℝ)|^2145 ≤ (22294440097519/50000000000000 : ℝ)^1633
        have hw : |(5406974281/10000000000 : ℝ)|=(5406974281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-465135727/2000000000 : ℝ)|^2145 ≤ (3680288825137/25000000000000 : ℝ)^1633
        have hw : |(-465135727/2000000000 : ℝ)|=(465135727/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(315195939/625000000 : ℝ)|^2145 ≤ (20344982241841/50000000000000 : ℝ)^1633
        have hw : |(315195939/625000000 : ℝ)|=(315195939/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1330_s1_2 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2703487219/5000000000 : ℝ)*x 0 + (5043134707/10000000000 : ℝ)*x 1 + (-1162839417/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2703487219/5000000000 : ℝ)^2145 ≤ (34835063981/78125000000 : ℝ)^1633 := by
    have hnat : (2703487219 : ℕ)^2145*78125000000^1633 ≤ 34835063981^1633*5000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703487219 5000000000 34835063981 78125000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5043134707/10000000000 : ℝ)^2145 ≤ (20344980562043/50000000000000 : ℝ)^1633 := by
    have hnat : (5043134707 : ℕ)^2145*50000000000000^1633 ≤ 20344980562043^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5043134707 10000000000 20344980562043 50000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1162839417/5000000000 : ℝ)^2145 ≤ (14721156955123/100000000000000 : ℝ)^1633 := by
    have hnat : (1162839417 : ℕ)^2145*100000000000000^1633 ≤ 14721156955123^1633*5000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1162839417 5000000000 14721156955123 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2703487219/5000000000 : ℝ), (5043134707/10000000000 : ℝ), (-1162839417/5000000000 : ℝ)] ![(34835063981/78125000000 : ℝ), (20344980562043/50000000000000 : ℝ), (14721156955123/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2703487219/5000000000 : ℝ)|^2145 ≤ (34835063981/78125000000 : ℝ)^1633
        have hw : |(2703487219/5000000000 : ℝ)|=(2703487219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5043134707/10000000000 : ℝ)|^2145 ≤ (20344980562043/50000000000000 : ℝ)^1633
        have hw : |(5043134707/10000000000 : ℝ)|=(5043134707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1162839417/5000000000 : ℝ)|^2145 ≤ (14721156955123/100000000000000 : ℝ)^1633
        have hw : |(-1162839417/5000000000 : ℝ)|=(1162839417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1330_s1_3 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2147220341/5000000000 : ℝ)*x 0 + (926839399/2500000000 : ℝ)*x 1 + (124191659/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2147220341/5000000000 : ℝ)^2145 ≤ (32946598131541/100000000000000 : ℝ)^1633 := by
    have hnat : (2147220341 : ℕ)^2145*100000000000000^1633 ≤ 32946598131541^1633*5000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2147220341 5000000000 32946598131541 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (926839399/2500000000 : ℝ)^2145 ≤ (27161378656659/100000000000000 : ℝ)^1633 := by
    have hnat : (926839399 : ℕ)^2145*100000000000000^1633 ≤ 27161378656659^1633*2500000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      926839399 2500000000 27161378656659 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (124191659/250000000 : ℝ)^2145 ≤ (2493251449831/6250000000000 : ℝ)^1633 := by
    have hnat : (124191659 : ℕ)^2145*6250000000000^1633 ≤ 2493251449831^1633*250000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      124191659 250000000 2493251449831 6250000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2147220341/5000000000 : ℝ), (926839399/2500000000 : ℝ), (124191659/250000000 : ℝ)] ![(32946598131541/100000000000000 : ℝ), (27161378656659/100000000000000 : ℝ), (2493251449831/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2147220341/5000000000 : ℝ)|^2145 ≤ (32946598131541/100000000000000 : ℝ)^1633
        have hw : |(2147220341/5000000000 : ℝ)|=(2147220341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(926839399/2500000000 : ℝ)|^2145 ≤ (27161378656659/100000000000000 : ℝ)^1633
        have hw : |(926839399/2500000000 : ℝ)|=(926839399/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(124191659/250000000 : ℝ)|^2145 ≤ (2493251449831/6250000000000 : ℝ)^1633
        have hw : |(124191659/250000000 : ℝ)|=(124191659/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1330_s1_4 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-62605181/312500000 : ℝ)*x 0 + (2525394463/5000000000 : ℝ)*x 1 + (563977043/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (62605181/312500000 : ℝ)^2145 ≤ (6050744219117/50000000000000 : ℝ)^1633 := by
    have hnat : (62605181 : ℕ)^2145*50000000000000^1633 ≤ 6050744219117^1633*312500000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62605181 312500000 6050744219117 50000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2525394463/5000000000 : ℝ)^2145 ≤ (8154220112093/20000000000000 : ℝ)^1633 := by
    have hnat : (2525394463 : ℕ)^2145*20000000000000^1633 ≤ 8154220112093^1633*5000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2525394463 5000000000 8154220112093 20000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (563977043/1000000000 : ℝ)^2145 ≤ (23563705492691/50000000000000 : ℝ)^1633 := by
    have hnat : (563977043 : ℕ)^2145*50000000000000^1633 ≤ 23563705492691^1633*1000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563977043 1000000000 23563705492691 50000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-62605181/312500000 : ℝ), (2525394463/5000000000 : ℝ), (563977043/1000000000 : ℝ)] ![(6050744219117/50000000000000 : ℝ), (8154220112093/20000000000000 : ℝ), (23563705492691/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-62605181/312500000 : ℝ)|^2145 ≤ (6050744219117/50000000000000 : ℝ)^1633
        have hw : |(-62605181/312500000 : ℝ)|=(62605181/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2525394463/5000000000 : ℝ)|^2145 ≤ (8154220112093/20000000000000 : ℝ)^1633
        have hw : |(2525394463/5000000000 : ℝ)|=(2525394463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(563977043/1000000000 : ℝ)|^2145 ≤ (23563705492691/50000000000000 : ℝ)^1633
        have hw : |(563977043/1000000000 : ℝ)|=(563977043/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1330_s1_5 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1050058357/2000000000 : ℝ)*x 0 + (-864521721/5000000000 : ℝ)*x 1 + (5639769899/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050058357/2000000000 : ℝ)^2145 ≤ (21449719345889/50000000000000 : ℝ)^1633 := by
    have hnat : (1050058357 : ℕ)^2145*50000000000000^1633 ≤ 21449719345889^1633*2000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050058357 2000000000 21449719345889 50000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (864521721/5000000000 : ℝ)^2145 ≤ (9973156145029/100000000000000 : ℝ)^1633 := by
    have hnat : (864521721 : ℕ)^2145*100000000000000^1633 ≤ 9973156145029^1633*5000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      864521721 5000000000 9973156145029 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5639769899/10000000000 : ℝ)^2145 ≤ (47127405157003/100000000000000 : ℝ)^1633 := by
    have hnat : (5639769899 : ℕ)^2145*100000000000000^1633 ≤ 47127405157003^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5639769899 10000000000 47127405157003 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050058357/2000000000 : ℝ), (-864521721/5000000000 : ℝ), (5639769899/10000000000 : ℝ)] ![(21449719345889/50000000000000 : ℝ), (9973156145029/100000000000000 : ℝ), (47127405157003/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050058357/2000000000 : ℝ)|^2145 ≤ (21449719345889/50000000000000 : ℝ)^1633
        have hw : |(1050058357/2000000000 : ℝ)|=(1050058357/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-864521721/5000000000 : ℝ)|^2145 ≤ (9973156145029/100000000000000 : ℝ)^1633
        have hw : |(-864521721/5000000000 : ℝ)|=(864521721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5639769899/10000000000 : ℝ)|^2145 ≤ (47127405157003/100000000000000 : ℝ)^1633
        have hw : |(5639769899/10000000000 : ℝ)|=(5639769899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1330_s1_6 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2625145701/5000000000 : ℝ)*x 0 + (5639769723/10000000000 : ℝ)*x 1 + (-864522119/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2625145701/5000000000 : ℝ)^2145 ≤ (42899434581151/100000000000000 : ℝ)^1633 := by
    have hnat : (2625145701 : ℕ)^2145*100000000000000^1633 ≤ 42899434581151^1633*5000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2625145701 5000000000 42899434581151 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5639769723/10000000000 : ℝ)^2145 ≤ (23563701612593/50000000000000 : ℝ)^1633 := by
    have hnat : (5639769723 : ℕ)^2145*50000000000000^1633 ≤ 23563701612593^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5639769723 10000000000 23563701612593 50000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (864522119/5000000000 : ℝ)^2145 ≤ (9973162175913/100000000000000 : ℝ)^1633 := by
    have hnat : (864522119 : ℕ)^2145*100000000000000^1633 ≤ 9973162175913^1633*5000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      864522119 5000000000 9973162175913 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2625145701/5000000000 : ℝ), (5639769723/10000000000 : ℝ), (-864522119/5000000000 : ℝ)] ![(42899434581151/100000000000000 : ℝ), (23563701612593/50000000000000 : ℝ), (9973162175913/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2625145701/5000000000 : ℝ)|^2145 ≤ (42899434581151/100000000000000 : ℝ)^1633
        have hw : |(2625145701/5000000000 : ℝ)|=(2625145701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5639769723/10000000000 : ℝ)|^2145 ≤ (23563701612593/50000000000000 : ℝ)^1633
        have hw : |(5639769723/10000000000 : ℝ)|=(5639769723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-864522119/5000000000 : ℝ)|^2145 ≤ (9973162175913/100000000000000 : ℝ)^1633
        have hw : |(-864522119/5000000000 : ℝ)|=(864522119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1330_s1_7 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4295605643/10000000000 : ℝ)*x 0 + (4951706207/10000000000 : ℝ)*x 1 + (116362857/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4295605643/10000000000 : ℝ)^2145 ≤ (32958338316419/100000000000000 : ℝ)^1633 := by
    have hnat : (4295605643 : ℕ)^2145*100000000000000^1633 ≤ 32958338316419^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4295605643 10000000000 32958338316419 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4951706207/10000000000 : ℝ)^2145 ≤ (39723758560787/100000000000000 : ℝ)^1633 := by
    have hnat : (4951706207 : ℕ)^2145*100000000000000^1633 ≤ 39723758560787^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4951706207 10000000000 39723758560787 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (116362857/312500000 : ℝ)^2145 ≤ (3414737888571/12500000000000 : ℝ)^1633 := by
    have hnat : (116362857 : ℕ)^2145*12500000000000^1633 ≤ 3414737888571^1633*312500000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      116362857 312500000 3414737888571 12500000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4295605643/10000000000 : ℝ), (4951706207/10000000000 : ℝ), (116362857/312500000 : ℝ)] ![(32958338316419/100000000000000 : ℝ), (39723758560787/100000000000000 : ℝ), (3414737888571/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4295605643/10000000000 : ℝ)|^2145 ≤ (32958338316419/100000000000000 : ℝ)^1633
        have hw : |(4295605643/10000000000 : ℝ)|=(4295605643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4951706207/10000000000 : ℝ)|^2145 ≤ (39723758560787/100000000000000 : ℝ)^1633
        have hw : |(4951706207/10000000000 : ℝ)|=(4951706207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(116362857/312500000 : ℝ)|^2145 ≤ (3414737888571/12500000000000 : ℝ)^1633
        have hw : |(116362857/312500000 : ℝ)|=(116362857/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1330_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154255973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13479/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (331/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (6777/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (611/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13479/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (331/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13479/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (331/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13479/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (331/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13479/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (331/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13479/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (331/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13479/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (331/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (331/25000 : ℝ) ^ (4289/1024 : ℝ) ≤ (1360103141907/100000000000000000000 : ℝ) := by
    have hpowers : (331/25000 : ℝ)^4289 ≤ (1360103141907/100000000000000000000 : ℝ)^1024 := by
      have hnat : (331 : ℕ)^4289*100000000000000000000^1024 ≤ 1360103141907^1024*25000^4289 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        331 25000 1360103141907 100000000000000000000 4289 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (331/25000 : ℝ)) (X := (1360103141907/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4289 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (13479/50000 : ℝ) ^ (4289/1024 : ℝ) ≤ (206261726709318993/50000000000000000000 : ℝ) := by
    have hpowers : (13479/50000 : ℝ)^4289 ≤ (206261726709318993/50000000000000000000 : ℝ)^1024 := by
      have hnat : (13479 : ℕ)^4289*50000000000000000000^1024 ≤ 206261726709318993^1024*50000^4289 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13479 50000 206261726709318993 50000000000000000000 4289 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13479/50000 : ℝ)) (X := (206261726709318993/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4289 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000001360103141907/50000000000000000000 : ℝ) ≤ (2500000016236251/2500000000000000 : ℝ) ^ (4289/1024 : ℝ) := by
    have hpowers : (50000001360103141907/50000000000000000000 : ℝ)^1024 ≤ (2500000016236251/2500000000000000 : ℝ)^4289 := by
      have hnat : (50000001360103141907 : ℕ)^1024*2500000000000000^4289 ≤ 2500000016236251^4289*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000001360103141907 50000000000000000000 2500000016236251 2500000000000000 1024 4289 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000016236251/2500000000000000 : ℝ)) (X := (50000001360103141907/50000000000000000000 : ℝ)) (by norm_num) 4289 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100412524813521779893/100000000000000000000 : ℝ) ≤ (10009833614603041/10000000000000000 : ℝ) ^ (4289/1024 : ℝ) := by
    have hpowers : (100412524813521779893/100000000000000000000 : ℝ)^1024 ≤ (10009833614603041/10000000000000000 : ℝ)^4289 := by
      have hnat : (100412524813521779893 : ℕ)^1024*10000000000000000^4289 ≤ 10009833614603041^4289*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100412524813521779893 100000000000000000000 10009833614603041 10000000000000000 1024 4289 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10009833614603041/10000000000000000 : ℝ)) (X := (100412524813521779893/100000000000000000000 : ℝ)) (by norm_num) 4289 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25206261726709318993/25000000000000000000 : ℝ) ≤ (5009833582130539/5000000000000000 : ℝ) ^ (4289/1024 : ℝ) := by
    have hpowers : (25206261726709318993/25000000000000000000 : ℝ)^1024 ≤ (5009833582130539/5000000000000000 : ℝ)^4289 := by
      have hnat : (25206261726709318993 : ℕ)^1024*5000000000000000^4289 ≤ 5009833582130539^4289*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25206261726709318993 25000000000000000000 5009833582130539 5000000000000000 1024 4289 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5009833582130539/5000000000000000 : ℝ)) (X := (25206261726709318993/25000000000000000000 : ℝ)) (by norm_num) 4289 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1360103141907/100000000000000000000 : ℝ) ≤ ((228851752165451563/228875000000000000 : ℝ)+2*(1404792808291/366200000000000 : ℝ)*(331/25000 : ℝ))^(4289/1024 : ℝ) := by
    rw [show (228851752165451563/228875000000000000 : ℝ)+2*(1404792808291/366200000000000 : ℝ)*(331/25000 : ℝ)=(2500000016236251/2500000000000000 : ℝ) by norm_num, show 1+2*(1360103141907/100000000000000000000 : ℝ)=(50000001360103141907/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(206261726709318993/50000000000000000000 : ℝ)+(1360103141907/100000000000000000000 : ℝ) ≤ ((228851752165451563/228875000000000000 : ℝ)+(1404792808291/366200000000000 : ℝ)*((13479/50000 : ℝ)+(331/25000 : ℝ)))^(4289/1024 : ℝ) := by
    rw [show (228851752165451563/228875000000000000 : ℝ)+(1404792808291/366200000000000 : ℝ)*((13479/50000 : ℝ)+(331/25000 : ℝ))=(10009833614603041/10000000000000000 : ℝ) by norm_num, show 1+(206261726709318993/50000000000000000000 : ℝ)+(1360103141907/100000000000000000000 : ℝ)=(100412524813521779893/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(206261726709318993/50000000000000000000 : ℝ) ≤ ((228851752165451563/228875000000000000 : ℝ)+2*(1404792808291/366200000000000 : ℝ)*(13479/50000 : ℝ))^(4289/1024 : ℝ) := by
    rw [show (228851752165451563/228875000000000000 : ℝ)+2*(1404792808291/366200000000000 : ℝ)*(13479/50000 : ℝ)=(5009833582130539/5000000000000000 : ℝ) by norm_num, show 1+2*(206261726709318993/50000000000000000000 : ℝ)=(25206261726709318993/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (228851752165451563/228875000000000000 : ℝ)*(X 1 0+X 2 0)+(1404792808291/366200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4289/1024 : ℝ)) (lo := (331/25000 : ℝ)) (hi := (13479/50000 : ℝ)) (c := (228851752165451563/228875000000000000 : ℝ)) (alpha := (1404792808291/366200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (228851752165451563/228875000000000000 : ℝ)*(X 0 1+X 2 1)+(1404792808291/366200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4289/1024 : ℝ)) (lo := (331/25000 : ℝ)) (hi := (13479/50000 : ℝ)) (c := (228851752165451563/228875000000000000 : ℝ)) (alpha := (1404792808291/366200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (228851752165451563/228875000000000000 : ℝ)*(X 0 2+X 1 2)+(1404792808291/366200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4289/1024 : ℝ)) (lo := (331/25000 : ℝ)) (hi := (13479/50000 : ℝ)) (c := (228851752165451563/228875000000000000 : ℝ)) (alpha := (1404792808291/366200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1001403329/5000000000 : ℝ)*X 0 0+(5647564787/10000000000 : ℝ)*X 0 1+(1260783783/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5406974281/10000000000 : ℝ)*X 1 0+(-465135727/2000000000 : ℝ)*X 1 1+(315195939/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2703487219/5000000000 : ℝ)*X 2 0+(5043134707/10000000000 : ℝ)*X 2 1+(-1162839417/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2147220341/5000000000 : ℝ)*X 0 0+(926839399/2500000000 : ℝ)*X 0 1+(124191659/250000000 : ℝ)*X 0 2+(2147220341/5000000000 : ℝ)*X 1 0+(926839399/2500000000 : ℝ)*X 1 1+(124191659/250000000 : ℝ)*X 1 2+(2147220341/5000000000 : ℝ)*X 2 0+(926839399/2500000000 : ℝ)*X 2 1+(124191659/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-62605181/312500000 : ℝ)*X 0 0+(2525394463/5000000000 : ℝ)*X 0 1+(563977043/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1050058357/2000000000 : ℝ)*X 1 0+(-864521721/5000000000 : ℝ)*X 1 1+(5639769899/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2625145701/5000000000 : ℝ)*X 2 0+(5639769723/10000000000 : ℝ)*X 2 1+(-864522119/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4295605643/10000000000 : ℝ)*X 0 0+(4951706207/10000000000 : ℝ)*X 0 1+(116362857/312500000 : ℝ)*X 0 2+(4295605643/10000000000 : ℝ)*X 1 0+(4951706207/10000000000 : ℝ)*X 1 1+(116362857/312500000 : ℝ)*X 1 2+(4295605643/10000000000 : ℝ)*X 2 0+(4951706207/10000000000 : ℝ)*X 2 1+(116362857/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (50121184619077818694037031/5721875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (116022321/100000000000000 : ℝ)*(base1) + (1454576477/100000000000000 : ℝ)*(base19) + (751308237/50000000000000 : ℝ)*(base23) + (225250607/100000000000000 : ℝ)*(upper3) + (156269657/100000000000000 : ℝ)*(upper5) + (611982710804757/50000000000000 : ℝ)*(major0) + (611982710804757/50000000000000 : ℝ)*(major1) + (611982710804757/50000000000000 : ℝ)*(major2) + (827229881289237/50000000000000 : ℝ)*(sp0) + (1654465221122091/100000000000000 : ℝ)*(sp1) + (827232586541047/50000000000000 : ℝ)*(sp2) + (793459820309507/100000000000000 : ℝ)*(sp3) + (439321401/6250000000000 : ℝ)*(sp4) + (3939202841/100000000000000 : ℝ)*(sp7) + (79346387553467/10000000000000 : ℝ)*(f.failure) + (206808334462321/12500000000000 : ℝ)*(f.sum) + (1322129943309/1144375000000000000000000000 : ℝ)*base65 + (762454632865397/89404296875000000000000000000 : ℝ)*base67 + (10349712505232283/5721875000000000000000000000000 : ℝ)*base69 + (40749521951994783/5721875000000000000000000000000 : ℝ)*base71 + (34692304685817/9155000000000000000000000000 : ℝ)*base73 + (41532170428307283/5721875000000000000000000000000 : ℝ)*base75 + (4557668299380727/1430468750000000000000000000000 : ℝ)*base77 + (17470041930905727/1430468750000000000000000000000 : ℝ)*base79 + (634718496453/9155000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1608391/1000000000000000000000 : ℝ)*base89 + (1608391/1000000000000000000000 : ℝ)*base91 + (1608391/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2216253529941462953536431/572187500000000000000000000000 : ℝ) := by norm_num
    linear_combination (433761323/100000000000000 : ℝ)*(base19) + (155436893/50000000000000 : ℝ)*(base23) + (507099/1562500000000 : ℝ)*(upper2) + (64441847/100000000000000 : ℝ)*(upper3) + (14292567/25000000000000 : ℝ)*(upper5) + (62802941903273/5000000000000 : ℝ)*(major0) + (62802941903273/5000000000000 : ℝ)*(major1) + (62802941903273/5000000000000 : ℝ)*(major2) + (292026701/20000000000000 : ℝ)*(sp0) + (2038919381/100000000000000 : ℝ)*(sp1) + (424461728080421/25000000000000 : ℝ)*(sp4) + (848922949887243/50000000000000 : ℝ)*(sp5) + (1697848061581403/100000000000000 : ℝ)*(sp6) + (407134587282873/50000000000000 : ℝ)*(sp7) + (407134587282873/50000000000000 : ℝ)*(f.failure) + (1697848372455189/100000000000000 : ℝ)*(f.sum) + (259890425213/915500000000000000000000000 : ℝ)*base65 + (489453974726801/1144375000000000000000000000000 : ℝ)*base68 + (3419024568407537/572187500000000000000000000000 : ℝ)*base69 + (231734574243199/1144375000000000000000000000000 : ℝ)*base71 + (6140747172039/1831000000000000000000000000 : ℝ)*base74 + (257760168179/4470214843750000000000000000 : ℝ)*base75 + (2750127310407537/572187500000000000000000000000 : ℝ)*base77 + (5821200188991949/1144375000000000000000000000000 : ℝ)*base79 + (1120616125699/457750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (850429/5000000000000000000000 : ℝ)*base89 + (850429/5000000000000000000000 : ℝ)*base91 + (850429/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1330_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154255973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13479/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (331/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (6777/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (611/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1330_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1330_s2_0 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-511005439/2500000000 : ℝ)*x 0 + (2741537773/5000000000 : ℝ)*x 1 + (5181241437/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (511005439/2500000000 : ℝ)^2145 ≤ (12425094791599/100000000000000 : ℝ)^1633 := by
    have hnat : (511005439 : ℕ)^2145*100000000000000^1633 ≤ 12425094791599^1633*2500000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      511005439 2500000000 12425094791599 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2741537773/5000000000 : ℝ)^2145 ≤ (363320248691/800000000000 : ℝ)^1633 := by
    have hnat : (2741537773 : ℕ)^2145*800000000000^1633 ≤ 363320248691^1633*5000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2741537773 5000000000 363320248691 800000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5181241437/10000000000 : ℝ)^2145 ≤ (42159874106229/100000000000000 : ℝ)^1633 := by
    have hnat : (5181241437 : ℕ)^2145*100000000000000^1633 ≤ 42159874106229^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181241437 10000000000 42159874106229 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-511005439/2500000000 : ℝ), (2741537773/5000000000 : ℝ), (5181241437/10000000000 : ℝ)] ![(12425094791599/100000000000000 : ℝ), (363320248691/800000000000 : ℝ), (42159874106229/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-511005439/2500000000 : ℝ)|^2145 ≤ (12425094791599/100000000000000 : ℝ)^1633
        have hw : |(-511005439/2500000000 : ℝ)|=(511005439/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2741537773/5000000000 : ℝ)|^2145 ≤ (363320248691/800000000000 : ℝ)^1633
        have hw : |(2741537773/5000000000 : ℝ)|=(2741537773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5181241437/10000000000 : ℝ)|^2145 ≤ (42159874106229/100000000000000 : ℝ)^1633
        have hw : |(5181241437/10000000000 : ℝ)|=(5181241437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1330_s2_1 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1073360643/2000000000 : ℝ)*x 0 + (-440017361/2000000000 : ℝ)*x 1 + (5181240963/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073360643/2000000000 : ℝ)^2145 ≤ (22077125072233/50000000000000 : ℝ)^1633 := by
    have hnat : (1073360643 : ℕ)^2145*50000000000000^1633 ≤ 22077125072233^1633*2000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073360643 2000000000 22077125072233 50000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (440017361/2000000000 : ℝ)^2145 ≤ (547435232221/4000000000000 : ℝ)^1633 := by
    have hnat : (440017361 : ℕ)^2145*4000000000000^1633 ≤ 547435232221^1633*2000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      440017361 2000000000 547435232221 4000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5181240963/10000000000 : ℝ)^2145 ≤ (42159869039999/100000000000000 : ℝ)^1633 := by
    have hnat : (5181240963 : ℕ)^2145*100000000000000^1633 ≤ 42159869039999^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181240963 10000000000 42159869039999 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073360643/2000000000 : ℝ), (-440017361/2000000000 : ℝ), (5181240963/10000000000 : ℝ)] ![(22077125072233/50000000000000 : ℝ), (547435232221/4000000000000 : ℝ), (42159869039999/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073360643/2000000000 : ℝ)|^2145 ≤ (22077125072233/50000000000000 : ℝ)^1633
        have hw : |(1073360643/2000000000 : ℝ)|=(1073360643/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-440017361/2000000000 : ℝ)|^2145 ≤ (547435232221/4000000000000 : ℝ)^1633
        have hw : |(-440017361/2000000000 : ℝ)|=(440017361/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5181240963/10000000000 : ℝ)|^2145 ≤ (42159869039999/100000000000000 : ℝ)^1633
        have hw : |(5181240963/10000000000 : ℝ)|=(5181240963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1330_s2_2 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5366802611/10000000000 : ℝ)*x 0 + (2590620777/5000000000 : ℝ)*x 1 + (-220008683/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5366802611/10000000000 : ℝ)^2145 ≤ (22077121808573/50000000000000 : ℝ)^1633 := by
    have hnat : (5366802611 : ℕ)^2145*50000000000000^1633 ≤ 22077121808573^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5366802611 10000000000 22077121808573 50000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2590620777/5000000000 : ℝ)^2145 ≤ (8431975071351/20000000000000 : ℝ)^1633 := by
    have hnat : (2590620777 : ℕ)^2145*20000000000000^1633 ≤ 8431975071351^1633*5000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590620777 5000000000 8431975071351 20000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (220008683/1000000000 : ℝ)^2145 ≤ (68429405049/500000000000 : ℝ)^1633 := by
    have hnat : (220008683 : ℕ)^2145*500000000000^1633 ≤ 68429405049^1633*1000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220008683 1000000000 68429405049 500000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5366802611/10000000000 : ℝ), (2590620777/5000000000 : ℝ), (-220008683/1000000000 : ℝ)] ![(22077121808573/50000000000000 : ℝ), (8431975071351/20000000000000 : ℝ), (68429405049/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5366802611/10000000000 : ℝ)|^2145 ≤ (22077121808573/50000000000000 : ℝ)^1633
        have hw : |(5366802611/10000000000 : ℝ)|=(5366802611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2590620777/5000000000 : ℝ)|^2145 ≤ (8431975071351/20000000000000 : ℝ)^1633
        have hw : |(2590620777/5000000000 : ℝ)|=(2590620777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-220008683/1000000000 : ℝ)|^2145 ≤ (68429405049/500000000000 : ℝ)^1633
        have hw : |(-220008683/1000000000 : ℝ)|=(220008683/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1330_s2_3 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4323221223/10000000000 : ℝ)*x 0 + (401926467/1000000000 : ℝ)*x 1 + (1162158601/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4323221223/10000000000 : ℝ)^2145 ≤ (33236933121121/100000000000000 : ℝ)^1633 := by
    have hnat : (4323221223 : ℕ)^2145*100000000000000^1633 ≤ 33236933121121^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4323221223 10000000000 33236933121121 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (401926467/1000000000 : ℝ)^2145 ≤ (30201836709051/100000000000000 : ℝ)^1633 := by
    have hnat : (401926467 : ℕ)^2145*100000000000000^1633 ≤ 30201836709051^1633*1000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      401926467 1000000000 30201836709051 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1162158601/2500000000 : ℝ)^2145 ≤ (36561230151091/100000000000000 : ℝ)^1633 := by
    have hnat : (1162158601 : ℕ)^2145*100000000000000^1633 ≤ 36561230151091^1633*2500000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1162158601 2500000000 36561230151091 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4323221223/10000000000 : ℝ), (401926467/1000000000 : ℝ), (1162158601/2500000000 : ℝ)] ![(33236933121121/100000000000000 : ℝ), (30201836709051/100000000000000 : ℝ), (36561230151091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4323221223/10000000000 : ℝ)|^2145 ≤ (33236933121121/100000000000000 : ℝ)^1633
        have hw : |(4323221223/10000000000 : ℝ)|=(4323221223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(401926467/1000000000 : ℝ)|^2145 ≤ (30201836709051/100000000000000 : ℝ)^1633
        have hw : |(401926467/1000000000 : ℝ)|=(401926467/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1162158601/2500000000 : ℝ)|^2145 ≤ (36561230151091/100000000000000 : ℝ)^1633
        have hw : |(1162158601/2500000000 : ℝ)|=(1162158601/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1330_s2_4 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-204409097/1000000000 : ℝ)*x 0 + (2591579583/5000000000 : ℝ)*x 1 + (5481140549/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (204409097/1000000000 : ℝ)^2145 ≤ (6212823721683/50000000000000 : ℝ)^1633 := by
    have hnat : (204409097 : ℕ)^2145*50000000000000^1633 ≤ 6212823721683^1633*1000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      204409097 1000000000 6212823721683 50000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2591579583/5000000000 : ℝ)^2145 ≤ (21090186230831/50000000000000 : ℝ)^1633 := by
    have hnat : (2591579583 : ℕ)^2145*50000000000000^1633 ≤ 21090186230831^1633*5000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591579583 5000000000 21090186230831 50000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5481140549/10000000000 : ℝ)^2145 ≤ (11348495021189/25000000000000 : ℝ)^1633 := by
    have hnat : (5481140549 : ℕ)^2145*25000000000000^1633 ≤ 11348495021189^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5481140549 10000000000 11348495021189 25000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-204409097/1000000000 : ℝ), (2591579583/5000000000 : ℝ), (5481140549/10000000000 : ℝ)] ![(6212823721683/50000000000000 : ℝ), (21090186230831/50000000000000 : ℝ), (11348495021189/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-204409097/1000000000 : ℝ)|^2145 ≤ (6212823721683/50000000000000 : ℝ)^1633
        have hw : |(-204409097/1000000000 : ℝ)|=(204409097/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2591579583/5000000000 : ℝ)|^2145 ≤ (21090186230831/50000000000000 : ℝ)^1633
        have hw : |(2591579583/5000000000 : ℝ)|=(2591579583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5481140549/10000000000 : ℝ)|^2145 ≤ (11348495021189/25000000000000 : ℝ)^1633
        have hw : |(5481140549/10000000000 : ℝ)|=(5481140549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1330_s2_5 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2644553687/5000000000 : ℝ)*x 0 + (-190018659/1000000000 : ℝ)*x 1 + (5481140583/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644553687/5000000000 : ℝ)^2145 ≤ (2165825852831/5000000000000 : ℝ)^1633 := by
    have hnat : (2644553687 : ℕ)^2145*5000000000000^1633 ≤ 2165825852831^1633*5000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644553687 5000000000 2165825852831 5000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (190018659/1000000000 : ℝ)^2145 ≤ (2257900496011/20000000000000 : ℝ)^1633 := by
    have hnat : (190018659 : ℕ)^2145*20000000000000^1633 ≤ 2257900496011^1633*1000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      190018659 1000000000 2257900496011 20000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5481140583/10000000000 : ℝ)^2145 ≤ (1418561889207/3125000000000 : ℝ)^1633 := by
    have hnat : (5481140583 : ℕ)^2145*3125000000000^1633 ≤ 1418561889207^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5481140583 10000000000 1418561889207 3125000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644553687/5000000000 : ℝ), (-190018659/1000000000 : ℝ), (5481140583/10000000000 : ℝ)] ![(2165825852831/5000000000000 : ℝ), (2257900496011/20000000000000 : ℝ), (1418561889207/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644553687/5000000000 : ℝ)|^2145 ≤ (2165825852831/5000000000000 : ℝ)^1633
        have hw : |(2644553687/5000000000 : ℝ)|=(2644553687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-190018659/1000000000 : ℝ)|^2145 ≤ (2257900496011/20000000000000 : ℝ)^1633
        have hw : |(-190018659/1000000000 : ℝ)|=(190018659/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5481140583/10000000000 : ℝ)|^2145 ≤ (1418561889207/3125000000000 : ℝ)^1633
        have hw : |(5481140583/10000000000 : ℝ)|=(5481140583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1330_s2_6 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5289107429/10000000000 : ℝ)*x 0 + (1370285139/2500000000 : ℝ)*x 1 + (-1900186551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289107429/10000000000 : ℝ)^2145 ≤ (43316517648283/100000000000000 : ℝ)^1633 := by
    have hnat : (5289107429 : ℕ)^2145*100000000000000^1633 ≤ 43316517648283^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289107429 10000000000 43316517648283 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1370285139/2500000000 : ℝ)^2145 ≤ (9078796032181/20000000000000 : ℝ)^1633 := by
    have hnat : (1370285139 : ℕ)^2145*20000000000000^1633 ≤ 9078796032181^1633*2500000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1370285139 2500000000 9078796032181 20000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1900186551/10000000000 : ℝ)^2145 ≤ (5644751087849/50000000000000 : ℝ)^1633 := by
    have hnat : (1900186551 : ℕ)^2145*50000000000000^1633 ≤ 5644751087849^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1900186551 10000000000 5644751087849 50000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289107429/10000000000 : ℝ), (1370285139/2500000000 : ℝ), (-1900186551/10000000000 : ℝ)] ![(43316517648283/100000000000000 : ℝ), (9078796032181/20000000000000 : ℝ), (5644751087849/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289107429/10000000000 : ℝ)|^2145 ≤ (43316517648283/100000000000000 : ℝ)^1633
        have hw : |(5289107429/10000000000 : ℝ)|=(5289107429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1370285139/2500000000 : ℝ)|^2145 ≤ (9078796032181/20000000000000 : ℝ)^1633
        have hw : |(1370285139/2500000000 : ℝ)|=(1370285139/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1900186551/10000000000 : ℝ)|^2145 ≤ (5644751087849/50000000000000 : ℝ)^1633
        have hw : |(-1900186551/10000000000 : ℝ)|=(1900186551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1330_s2_7 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1080840913/2500000000 : ℝ)*x 0 + (92892663/200000000 : ℝ)*x 1 + (4023305727/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1080840913/2500000000 : ℝ)^2145 ≤ (1329534857611/4000000000000 : ℝ)^1633 := by
    have hnat : (1080840913 : ℕ)^2145*4000000000000^1633 ≤ 1329534857611^1633*2500000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080840913 2500000000 1329534857611 4000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (92892663/200000000 : ℝ)^2145 ≤ (18259949665449/50000000000000 : ℝ)^1633 := by
    have hnat : (92892663 : ℕ)^2145*50000000000000^1633 ≤ 18259949665449^1633*200000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      92892663 200000000 18259949665449 50000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4023305727/10000000000 : ℝ)^2145 ≤ (30241729210417/100000000000000 : ℝ)^1633 := by
    have hnat : (4023305727 : ℕ)^2145*100000000000000^1633 ≤ 30241729210417^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4023305727 10000000000 30241729210417 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1080840913/2500000000 : ℝ), (92892663/200000000 : ℝ), (4023305727/10000000000 : ℝ)] ![(1329534857611/4000000000000 : ℝ), (18259949665449/50000000000000 : ℝ), (30241729210417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1080840913/2500000000 : ℝ)|^2145 ≤ (1329534857611/4000000000000 : ℝ)^1633
        have hw : |(1080840913/2500000000 : ℝ)|=(1080840913/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(92892663/200000000 : ℝ)|^2145 ≤ (18259949665449/50000000000000 : ℝ)^1633
        have hw : |(92892663/200000000 : ℝ)|=(92892663/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4023305727/10000000000 : ℝ)|^2145 ≤ (30241729210417/100000000000000 : ℝ)^1633
        have hw : |(4023305727/10000000000 : ℝ)|=(4023305727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1330_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154255973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (611/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6777/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2443/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2019/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (611/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (6777/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (611/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (6777/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (611/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (6777/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (611/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (6777/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (611/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (6777/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (611/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (6777/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (6777/100000 : ℝ) ^ (4289/1024 : ℝ) ≤ (79379420397397/6250000000000000000 : ℝ) := by
    have hpowers : (6777/100000 : ℝ)^4289 ≤ (79379420397397/6250000000000000000 : ℝ)^1024 := by
      have hnat : (6777 : ℕ)^4289*6250000000000000000^1024 ≤ 79379420397397^1024*100000^4289 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6777 100000 79379420397397 6250000000000000000 4289 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6777/100000 : ℝ)) (X := (79379420397397/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4289 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (611/3125 : ℝ) ^ (4289/1024 : ℝ) ≤ (53720606892488273/50000000000000000000 : ℝ) := by
    have hpowers : (611/3125 : ℝ)^4289 ≤ (53720606892488273/50000000000000000000 : ℝ)^1024 := by
      have hnat : (611 : ℕ)^4289*50000000000000000000^1024 ≤ 53720606892488273^1024*3125^4289 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        611 3125 53720606892488273 50000000000000000000 4289 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (611/3125 : ℝ)) (X := (53720606892488273/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4289 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125079379420397397/3125000000000000000 : ℝ) ≤ (5000030322682437/5000000000000000 : ℝ) ^ (4289/1024 : ℝ) := by
    have hpowers : (3125079379420397397/3125000000000000000 : ℝ)^1024 ≤ (5000030322682437/5000000000000000 : ℝ)^4289 := by
      have hnat : (3125079379420397397 : ℕ)^1024*5000000000000000^4289 ≤ 5000030322682437^4289*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125079379420397397 3125000000000000000 5000030322682437 5000000000000000 1024 4289 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000030322682437/5000000000000000 : ℝ)) (X := (3125079379420397397/3125000000000000000 : ℝ)) (by norm_num) 4289 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50054355642255667449/50000000000000000000 : ℝ) ≤ (10002594411805497/10000000000000000 : ℝ) ^ (4289/1024 : ℝ) := by
    have hpowers : (50054355642255667449/50000000000000000000 : ℝ)^1024 ≤ (10002594411805497/10000000000000000 : ℝ)^4289 := by
      have hnat : (50054355642255667449 : ℕ)^1024*10000000000000000^4289 ≤ 10002594411805497^4289*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50054355642255667449 50000000000000000000 10002594411805497 10000000000000000 1024 4289 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002594411805497/10000000000000000 : ℝ)) (X := (50054355642255667449/50000000000000000000 : ℝ)) (by norm_num) 4289 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25053720606892488273/25000000000000000000 : ℝ) ≤ (250128204456153/250000000000000 : ℝ) ^ (4289/1024 : ℝ) := by
    have hpowers : (25053720606892488273/25000000000000000000 : ℝ)^1024 ≤ (250128204456153/250000000000000 : ℝ)^4289 := by
      have hnat : (25053720606892488273 : ℕ)^1024*250000000000000^4289 ≤ 250128204456153^4289*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25053720606892488273 25000000000000000000 250128204456153 250000000000000 1024 4289 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250128204456153/250000000000000 : ℝ)) (X := (25053720606892488273/25000000000000000000 : ℝ)) (by norm_num) 4289 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(79379420397397/6250000000000000000 : ℝ) ≤ ((15964554009275007651/15968750000000000000 : ℝ)+2*(2533766440623/1277500000000000 : ℝ)*(6777/100000 : ℝ))^(4289/1024 : ℝ) := by
    rw [show (15964554009275007651/15968750000000000000 : ℝ)+2*(2533766440623/1277500000000000 : ℝ)*(6777/100000 : ℝ)=(5000030322682437/5000000000000000 : ℝ) by norm_num, show 1+2*(79379420397397/6250000000000000000 : ℝ)=(3125079379420397397/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(53720606892488273/50000000000000000000 : ℝ)+(79379420397397/6250000000000000000 : ℝ) ≤ ((15964554009275007651/15968750000000000000 : ℝ)+(2533766440623/1277500000000000 : ℝ)*((611/3125 : ℝ)+(6777/100000 : ℝ)))^(4289/1024 : ℝ) := by
    rw [show (15964554009275007651/15968750000000000000 : ℝ)+(2533766440623/1277500000000000 : ℝ)*((611/3125 : ℝ)+(6777/100000 : ℝ))=(10002594411805497/10000000000000000 : ℝ) by norm_num, show 1+(53720606892488273/50000000000000000000 : ℝ)+(79379420397397/6250000000000000000 : ℝ)=(50054355642255667449/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(53720606892488273/50000000000000000000 : ℝ) ≤ ((15964554009275007651/15968750000000000000 : ℝ)+2*(2533766440623/1277500000000000 : ℝ)*(611/3125 : ℝ))^(4289/1024 : ℝ) := by
    rw [show (15964554009275007651/15968750000000000000 : ℝ)+2*(2533766440623/1277500000000000 : ℝ)*(611/3125 : ℝ)=(250128204456153/250000000000000 : ℝ) by norm_num, show 1+2*(53720606892488273/50000000000000000000 : ℝ)=(25053720606892488273/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (15964554009275007651/15968750000000000000 : ℝ)*(X 1 0+X 2 0)+(2533766440623/1277500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4289/1024 : ℝ)) (lo := (6777/100000 : ℝ)) (hi := (611/3125 : ℝ)) (c := (15964554009275007651/15968750000000000000 : ℝ)) (alpha := (2533766440623/1277500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (15964554009275007651/15968750000000000000 : ℝ)*(X 0 1+X 2 1)+(2533766440623/1277500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4289/1024 : ℝ)) (lo := (6777/100000 : ℝ)) (hi := (611/3125 : ℝ)) (c := (15964554009275007651/15968750000000000000 : ℝ)) (alpha := (2533766440623/1277500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (15964554009275007651/15968750000000000000 : ℝ)*(X 0 2+X 1 2)+(2533766440623/1277500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4289/1024 : ℝ)) (lo := (6777/100000 : ℝ)) (hi := (611/3125 : ℝ)) (c := (15964554009275007651/15968750000000000000 : ℝ)) (alpha := (2533766440623/1277500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-511005439/2500000000 : ℝ)*X 0 0+(2741537773/5000000000 : ℝ)*X 0 1+(5181241437/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1073360643/2000000000 : ℝ)*X 1 0+(-440017361/2000000000 : ℝ)*X 1 1+(5181240963/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5366802611/10000000000 : ℝ)*X 2 0+(2590620777/5000000000 : ℝ)*X 2 1+(-220008683/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4323221223/10000000000 : ℝ)*X 0 0+(401926467/1000000000 : ℝ)*X 0 1+(1162158601/2500000000 : ℝ)*X 0 2+(4323221223/10000000000 : ℝ)*X 1 0+(401926467/1000000000 : ℝ)*X 1 1+(1162158601/2500000000 : ℝ)*X 1 2+(4323221223/10000000000 : ℝ)*X 2 0+(401926467/1000000000 : ℝ)*X 2 1+(1162158601/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-204409097/1000000000 : ℝ)*X 0 0+(2591579583/5000000000 : ℝ)*X 0 1+(5481140549/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2644553687/5000000000 : ℝ)*X 1 0+(-190018659/1000000000 : ℝ)*X 1 1+(5481140583/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5289107429/10000000000 : ℝ)*X 2 0+(1370285139/2500000000 : ℝ)*X 2 1+(-1900186551/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1080840913/2500000000 : ℝ)*X 0 0+(92892663/200000000 : ℝ)*X 0 1+(4023305727/10000000000 : ℝ)*X 0 2+(1080840913/2500000000 : ℝ)*X 1 0+(92892663/200000000 : ℝ)*X 1 1+(4023305727/10000000000 : ℝ)*X 1 2+(1080840913/2500000000 : ℝ)*X 2 0+(92892663/200000000 : ℝ)*X 2 1+(4023305727/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (133550926625373818635935249/28515625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2035738061/100000000000000 : ℝ)*(base19) + (988000559/100000000000000 : ℝ)*(base23) + (181094691/50000000000000 : ℝ)*(lower2) + (780998449/100000000000000 : ℝ)*(upper3) + (130485999/100000000000000 : ℝ)*(upper5) + (1225503659893431/50000000000000 : ℝ)*(major0) + (1225503659893431/50000000000000 : ℝ)*(major1) + (1225503659893431/50000000000000 : ℝ)*(major2) + (66261818074537/2000000000000 : ℝ)*(sp0) + (828272574901653/25000000000000 : ℝ)*(sp1) + (1656545673672057/50000000000000 : ℝ)*(sp2) + (794451628569577/50000000000000 : ℝ)*(sp3) + (1431617823/100000000000000 : ℝ)*(sp4) + (18890975567/100000000000000 : ℝ)*(sp7) + (9930763425717/625000000000 : ℝ)*(f.failure) + (3313092335344673/100000000000000 : ℝ)*(f.sum) + (153173461894737/31937500000000000000000000000 : ℝ)*base66 + (6678938879455196919/798437500000000000000000000000000 : ℝ)*base68 + (2118546329914571919/798437500000000000000000000000000 : ℝ)*base70 + (43064388922928081/798437500000000000000000000000000 : ℝ)*base71 + (90382636353431/15968750000000000000000000000 : ℝ)*base74 + (8197976469553634419/798437500000000000000000000000000 : ℝ)*base76 + (287348270161446919/798437500000000000000000000000000 : ℝ)*base78 + (5085327443233321919/798437500000000000000000000000000 : ℝ)*base80 + (298704835049349/63875000000000000000000000000 : ℝ)*base82 + (307641/62500000000000000000 : ℝ)*base89 + (307641/62500000000000000000 : ℝ)*base91 + (307641/62500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1071741529418884082657056239/399218750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (306627979/50000000000000 : ℝ)*(base19) + (6120117/781250000000 : ℝ)*(base23) + (92763507/100000000000000 : ℝ)*(upper3) + (6039497/12500000000000 : ℝ)*(lower4) + (3381987/50000000000000 : ℝ)*(upper5) + (1241342582322821/50000000000000 : ℝ)*(major0) + (1241342582322821/50000000000000 : ℝ)*(major1) + (1241342582322821/50000000000000 : ℝ)*(major2) + (6527795567/100000000000000 : ℝ)*(sp1) + (4757215397/50000000000000 : ℝ)*(sp2) + (419489024569047/12500000000000 : ℝ)*(sp4) + (3355905055500851/100000000000000 : ℝ)*(sp5) + (1677950949373303/50000000000000 : ℝ)*(sp6) + (160945804325233/10000000000000 : ℝ)*(sp7) + (160945804325233/10000000000000 : ℝ)*(f.failure) + (419489024569047/12500000000000 : ℝ)*(f.sum) + (40696006195017/31937500000000000000000000000 : ℝ)*base66 + (5911358550710809029/798437500000000000000000000000000 : ℝ)*base68 + (10663315556332684029/798437500000000000000000000000000 : ℝ)*base70 + (2240314129074871529/798437500000000000000000000000000 : ℝ)*base72 + (66195736938159/63875000000000000000000000000 : ℝ)*base74 + (7103444220442059029/798437500000000000000000000000000 : ℝ)*base76 + (2939279034885809029/798437500000000000000000000000000 : ℝ)*base78 + (5097342254392059029/798437500000000000000000000000000 : ℝ)*base80 + (143486547944017/31937500000000000000000000000 : ℝ)*base82 + (4866709/1000000000000000000000 : ℝ)*base89 + (4866709/1000000000000000000000 : ℝ)*base91 + (4866709/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1330_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154255973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (611/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6777/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2443/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2019/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1330_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1330_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154255973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2443/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2019/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1330_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1330_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1330_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154255973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2443/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2019/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1330_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
