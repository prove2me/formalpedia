-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1368_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:19:41.319956+00:00
-- url     : https://prove2.me/submissions/fc6fa2b7-7350-4f21-a04d-87b5687bf2a2

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
theorem support_rectangle_w1368_s6_0 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2021716017/10000000000 : ℝ)*x 0 + (1352843849/2500000000 : ℝ)*x 1 + (1311341421/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2021716017/10000000000 : ℝ)^541 ≤ (12318102988651/100000000000000 : ℝ)^413 := by
    have hnat : (2021716017 : ℕ)^541*100000000000000^413 ≤ 12318102988651^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2021716017 10000000000 12318102988651 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352843849/2500000000 : ℝ)^541 ≤ (22367755908971/50000000000000 : ℝ)^413 := by
    have hnat : (1352843849 : ℕ)^541*50000000000000^413 ≤ 22367755908971^413*2500000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352843849 2500000000 22367755908971 50000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311341421/2500000000 : ℝ)^541 ≤ (42946385178007/100000000000000 : ℝ)^413 := by
    have hnat : (1311341421 : ℕ)^541*100000000000000^413 ≤ 42946385178007^413*2500000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311341421 2500000000 42946385178007 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2021716017/10000000000 : ℝ), (1352843849/2500000000 : ℝ), (1311341421/2500000000 : ℝ)] ![(12318102988651/100000000000000 : ℝ), (22367755908971/50000000000000 : ℝ), (42946385178007/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2021716017/10000000000 : ℝ)|^541 ≤ (12318102988651/100000000000000 : ℝ)^413
        have hw : |(-2021716017/10000000000 : ℝ)|=(2021716017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352843849/2500000000 : ℝ)|^541 ≤ (22367755908971/50000000000000 : ℝ)^413
        have hw : |(1352843849/2500000000 : ℝ)|=(1352843849/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311341421/2500000000 : ℝ)|^541 ≤ (42946385178007/100000000000000 : ℝ)^413
        have hw : |(1311341421/2500000000 : ℝ)|=(1311341421/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_s6_1 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2674268609/5000000000 : ℝ)*x 0 + (-1053139557/5000000000 : ℝ)*x 1 + (5245365687/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674268609/5000000000 : ℝ)^541 ≤ (220281296651/500000000000 : ℝ)^413 := by
    have hnat : (2674268609 : ℕ)^541*500000000000^413 ≤ 220281296651^413*5000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674268609 5000000000 220281296651 500000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053139557/5000000000 : ℝ)^541 ≤ (12997355450939/100000000000000 : ℝ)^413 := by
    have hnat : (1053139557 : ℕ)^541*100000000000000^413 ≤ 12997355450939^413*5000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053139557 5000000000 12997355450939 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245365687/10000000000 : ℝ)^541 ≤ (21473192605091/50000000000000 : ℝ)^413 := by
    have hnat : (5245365687 : ℕ)^541*50000000000000^413 ≤ 21473192605091^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245365687 10000000000 21473192605091 50000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674268609/5000000000 : ℝ), (-1053139557/5000000000 : ℝ), (5245365687/10000000000 : ℝ)] ![(220281296651/500000000000 : ℝ), (12997355450939/100000000000000 : ℝ), (21473192605091/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674268609/5000000000 : ℝ)|^541 ≤ (220281296651/500000000000 : ℝ)^413
        have hw : |(2674268609/5000000000 : ℝ)|=(2674268609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1053139557/5000000000 : ℝ)|^541 ≤ (12997355450939/100000000000000 : ℝ)^413
        have hw : |(-1053139557/5000000000 : ℝ)|=(1053139557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245365687/10000000000 : ℝ)|^541 ≤ (21473192605091/50000000000000 : ℝ)^413
        have hw : |(5245365687/10000000000 : ℝ)|=(5245365687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_s6_2 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5348537221/10000000000 : ℝ)*x 0 + (655670711/1250000000 : ℝ)*x 1 + (-526569777/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348537221/10000000000 : ℝ)^541 ≤ (4405625936257/10000000000000 : ℝ)^413 := by
    have hnat : (5348537221 : ℕ)^541*10000000000000^413 ≤ 4405625936257^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348537221 10000000000 4405625936257 10000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655670711/1250000000 : ℝ)^541 ≤ (42946385220907/100000000000000 : ℝ)^413 := by
    have hnat : (655670711 : ℕ)^541*100000000000000^413 ≤ 42946385220907^413*1250000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655670711 1250000000 42946385220907 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526569777/2500000000 : ℝ)^541 ≤ (12997355402439/100000000000000 : ℝ)^413 := by
    have hnat : (526569777 : ℕ)^541*100000000000000^413 ≤ 12997355402439^413*2500000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526569777 2500000000 12997355402439 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348537221/10000000000 : ℝ), (655670711/1250000000 : ℝ), (-526569777/2500000000 : ℝ)] ![(4405625936257/10000000000000 : ℝ), (42946385220907/100000000000000 : ℝ), (12997355402439/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348537221/10000000000 : ℝ)|^541 ≤ (4405625936257/10000000000000 : ℝ)^413
        have hw : |(5348537221/10000000000 : ℝ)|=(5348537221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655670711/1250000000 : ℝ)|^541 ≤ (42946385220907/100000000000000 : ℝ)^413
        have hw : |(655670711/1250000000 : ℝ)|=(655670711/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-526569777/2500000000 : ℝ)|^541 ≤ (12997355402439/100000000000000 : ℝ)^413
        have hw : |(-526569777/2500000000 : ℝ)|=(526569777/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_s6_3 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4319865641/10000000000 : ℝ)*x 0 + (2073799747/5000000000 : ℝ)*x 1 + (281170211/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4319865641/10000000000 : ℝ)^541 ≤ (8325925132861/25000000000000 : ℝ)^413 := by
    have hnat : (4319865641 : ℕ)^541*25000000000000^413 ≤ 8325925132861^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4319865641 10000000000 8325925132861 25000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2073799747/5000000000 : ℝ)^541 ≤ (15787435602931/50000000000000 : ℝ)^413 := by
    have hnat : (2073799747 : ℕ)^541*50000000000000^413 ≤ 15787435602931^413*5000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2073799747 5000000000 15787435602931 50000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (281170211/625000000 : ℝ)^541 ≤ (7024285648073/20000000000000 : ℝ)^413 := by
    have hnat : (281170211 : ℕ)^541*20000000000000^413 ≤ 7024285648073^413*625000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281170211 625000000 7024285648073 20000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4319865641/10000000000 : ℝ), (2073799747/5000000000 : ℝ), (281170211/625000000 : ℝ)] ![(8325925132861/25000000000000 : ℝ), (15787435602931/50000000000000 : ℝ), (7024285648073/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4319865641/10000000000 : ℝ)|^541 ≤ (8325925132861/25000000000000 : ℝ)^413
        have hw : |(4319865641/10000000000 : ℝ)|=(4319865641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2073799747/5000000000 : ℝ)|^541 ≤ (15787435602931/50000000000000 : ℝ)^413
        have hw : |(2073799747/5000000000 : ℝ)|=(2073799747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(281170211/625000000 : ℝ)|^541 ≤ (7024285648073/20000000000000 : ℝ)^413
        have hw : |(281170211/625000000 : ℝ)|=(281170211/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_s6_4 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-25271599/125000000 : ℝ)*x 0 + (1049192269/2000000000 : ℝ)*x 1 + (2705388333/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (25271599/125000000 : ℝ)^541 ≤ (12318197989551/100000000000000 : ℝ)^413 := by
    have hnat : (25271599 : ℕ)^541*100000000000000^413 ≤ 12318197989551^413*125000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25271599 125000000 12318197989551 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1049192269/2000000000 : ℝ)^541 ≤ (42952773765783/100000000000000 : ℝ)^413 := by
    have hnat : (1049192269 : ℕ)^541*100000000000000^413 ≤ 42952773765783^413*2000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049192269 2000000000 42952773765783 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2705388333/5000000000 : ℝ)^541 ≤ (8945805645617/20000000000000 : ℝ)^413 := by
    have hnat : (2705388333 : ℕ)^541*20000000000000^413 ≤ 8945805645617^413*5000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705388333 5000000000 8945805645617 20000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-25271599/125000000 : ℝ), (1049192269/2000000000 : ℝ), (2705388333/5000000000 : ℝ)] ![(12318197989551/100000000000000 : ℝ), (42952773765783/100000000000000 : ℝ), (8945805645617/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-25271599/125000000 : ℝ)|^541 ≤ (12318197989551/100000000000000 : ℝ)^413
        have hw : |(-25271599/125000000 : ℝ)|=(25271599/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1049192269/2000000000 : ℝ)|^541 ≤ (42952773765783/100000000000000 : ℝ)^413
        have hw : |(1049192269/2000000000 : ℝ)|=(1049192269/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2705388333/5000000000 : ℝ)|^541 ≤ (8945805645617/20000000000000 : ℝ)^413
        have hw : |(2705388333/5000000000 : ℝ)|=(2705388333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_s6_5 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5305651467/10000000000 : ℝ)*x 0 + (-1940868131/10000000000 : ℝ)*x 1 + (5410776663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305651467/10000000000 : ℝ)^541 ≤ (8718819969127/20000000000000 : ℝ)^413 := by
    have hnat : (5305651467 : ℕ)^541*20000000000000^413 ≤ 8718819969127^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305651467 10000000000 8718819969127 20000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1940868131/10000000000 : ℝ)^541 ≤ (233537438829/2000000000000 : ℝ)^413 := by
    have hnat : (1940868131 : ℕ)^541*2000000000000^413 ≤ 233537438829^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1940868131 10000000000 233537438829 2000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5410776663/10000000000 : ℝ)^541 ≤ (22364514097799/50000000000000 : ℝ)^413 := by
    have hnat : (5410776663 : ℕ)^541*50000000000000^413 ≤ 22364514097799^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410776663 10000000000 22364514097799 50000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305651467/10000000000 : ℝ), (-1940868131/10000000000 : ℝ), (5410776663/10000000000 : ℝ)] ![(8718819969127/20000000000000 : ℝ), (233537438829/2000000000000 : ℝ), (22364514097799/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305651467/10000000000 : ℝ)|^541 ≤ (8718819969127/20000000000000 : ℝ)^413
        have hw : |(5305651467/10000000000 : ℝ)|=(5305651467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1940868131/10000000000 : ℝ)|^541 ≤ (233537438829/2000000000000 : ℝ)^413
        have hw : |(-1940868131/10000000000 : ℝ)|=(1940868131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5410776663/10000000000 : ℝ)|^541 ≤ (22364514097799/50000000000000 : ℝ)^413
        have hw : |(5410776663/10000000000 : ℝ)|=(5410776663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_s6_6 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1061130293/2000000000 : ℝ)*x 0 + (2705388333/5000000000 : ℝ)*x 1 + (-194086813/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061130293/2000000000 : ℝ)^541 ≤ (43594099824109/100000000000000 : ℝ)^413 := by
    have hnat : (1061130293 : ℕ)^541*100000000000000^413 ≤ 43594099824109^413*2000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061130293 2000000000 43594099824109 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2705388333/5000000000 : ℝ)^541 ≤ (8945805645617/20000000000000 : ℝ)^413 := by
    have hnat : (2705388333 : ℕ)^541*20000000000000^413 ≤ 8945805645617^413*5000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705388333 5000000000 8945805645617 20000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (194086813/1000000000 : ℝ)^541 ≤ (11676871933569/100000000000000 : ℝ)^413 := by
    have hnat : (194086813 : ℕ)^541*100000000000000^413 ≤ 11676871933569^413*1000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      194086813 1000000000 11676871933569 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061130293/2000000000 : ℝ), (2705388333/5000000000 : ℝ), (-194086813/1000000000 : ℝ)] ![(43594099824109/100000000000000 : ℝ), (8945805645617/20000000000000 : ℝ), (11676871933569/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061130293/2000000000 : ℝ)|^541 ≤ (43594099824109/100000000000000 : ℝ)^413
        have hw : |(1061130293/2000000000 : ℝ)|=(1061130293/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2705388333/5000000000 : ℝ)|^541 ≤ (8945805645617/20000000000000 : ℝ)^413
        have hw : |(2705388333/5000000000 : ℝ)|=(2705388333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-194086813/1000000000 : ℝ)|^541 ≤ (11676871933569/100000000000000 : ℝ)^413
        have hw : |(-194086813/1000000000 : ℝ)|=(194086813/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_s6_7 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4319890827/10000000000 : ℝ)*x 0 + (2248731761/5000000000 : ℝ)*x 1 + (4148865861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4319890827/10000000000 : ℝ)^541 ≤ (33303954879873/100000000000000 : ℝ)^413 := by
    have hnat : (4319890827 : ℕ)^541*100000000000000^413 ≤ 33303954879873^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4319890827 10000000000 33303954879873 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2248731761/5000000000 : ℝ)^541 ≤ (35108544811527/100000000000000 : ℝ)^413 := by
    have hnat : (2248731761 : ℕ)^541*100000000000000^413 ≤ 35108544811527^413*5000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248731761 5000000000 35108544811527 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4148865861/10000000000 : ℝ)^541 ≤ (31587500297647/100000000000000 : ℝ)^413 := by
    have hnat : (4148865861 : ℕ)^541*100000000000000^413 ≤ 31587500297647^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4148865861 10000000000 31587500297647 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4319890827/10000000000 : ℝ), (2248731761/5000000000 : ℝ), (4148865861/10000000000 : ℝ)] ![(33303954879873/100000000000000 : ℝ), (35108544811527/100000000000000 : ℝ), (31587500297647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4319890827/10000000000 : ℝ)|^541 ≤ (33303954879873/100000000000000 : ℝ)^413
        have hw : |(4319890827/10000000000 : ℝ)|=(4319890827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2248731761/5000000000 : ℝ)|^541 ≤ (35108544811527/100000000000000 : ℝ)^413
        have hw : |(2248731761/5000000000 : ℝ)|=(2248731761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4148865861/10000000000 : ℝ)|^541 ≤ (31587500297647/100000000000000 : ℝ)^413
        have hw : |(4148865861/10000000000 : ℝ)|=(4148865861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1368_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7787701/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1473/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11203/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11209/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14723/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1473/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11203/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1473/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11203/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1473/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11203/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1473/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11203/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1473/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11203/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1473/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11203/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11203/100000 : ℝ) ^ (4327/1024 : ℝ) ≤ (4806739022604503/50000000000000000000 : ℝ) := by
    have hpowers : (11203/100000 : ℝ)^4327 ≤ (4806739022604503/50000000000000000000 : ℝ)^1024 := by
      have hnat : (11203 : ℕ)^4327*50000000000000000000^1024 ≤ 4806739022604503^1024*100000^4327 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11203 100000 4806739022604503 50000000000000000000 4327 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11203/100000 : ℝ)) (X := (4806739022604503/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4327 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1473/10000 : ℝ) ^ (4327/1024 : ℝ) ≤ (1222444681901291/4000000000000000000 : ℝ) := by
    have hpowers : (1473/10000 : ℝ)^4327 ≤ (1222444681901291/4000000000000000000 : ℝ)^1024 := by
      have hnat : (1473 : ℕ)^4327*4000000000000000000^1024 ≤ 1222444681901291^1024*10000^4327 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1473 10000 1222444681901291 4000000000000000000 4327 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1473/10000 : ℝ)) (X := (1222444681901291/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4327 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004806739022604503/25000000000000000000 : ℝ) ≤ (5000227489697057/5000000000000000 : ℝ) ^ (4327/1024 : ℝ) := by
    have hpowers : (25004806739022604503/25000000000000000000 : ℝ)^1024 ≤ (5000227489697057/5000000000000000 : ℝ)^4327 := by
      have hnat : (25004806739022604503 : ℕ)^1024*5000000000000000^4327 ≤ 5000227489697057^4327*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004806739022604503 25000000000000000000 5000227489697057 5000000000000000 1024 4327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000227489697057/5000000000000000 : ℝ)) (X := (25004806739022604503/25000000000000000000 : ℝ)) (by norm_num) 4327 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100040174595092741281/100000000000000000000 : ℝ) ≤ (2000190120077749/2000000000000000 : ℝ) ^ (4327/1024 : ℝ) := by
    have hpowers : (100040174595092741281/100000000000000000000 : ℝ)^1024 ≤ (2000190120077749/2000000000000000 : ℝ)^4327 := by
      have hnat : (100040174595092741281 : ℕ)^1024*2000000000000000^4327 ≤ 2000190120077749^4327*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100040174595092741281 100000000000000000000 2000190120077749 2000000000000000 1024 4327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000190120077749/2000000000000000 : ℝ)) (X := (100040174595092741281/100000000000000000000 : ℝ)) (by norm_num) 4327 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2001222444681901291/2000000000000000000 : ℝ) ≤ (625090388836461/625000000000000 : ℝ) ^ (4327/1024 : ℝ) := by
    have hpowers : (2001222444681901291/2000000000000000000 : ℝ)^1024 ≤ (625090388836461/625000000000000 : ℝ)^4327 := by
      have hnat : (2001222444681901291 : ℕ)^1024*625000000000000^4327 ≤ 625090388836461^4327*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2001222444681901291 2000000000000000000 625090388836461 625000000000000 1024 4327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625090388836461/625000000000000 : ℝ)) (X := (2001222444681901291/2000000000000000000 : ℝ)) (by norm_num) 4327 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4806739022604503/50000000000000000000 : ℝ) ≤ ((8815124957079334473/8817500000000000000 : ℝ)+2*(495620994631/352700000000000 : ℝ)*(11203/100000 : ℝ))^(4327/1024 : ℝ) := by
    rw [show (8815124957079334473/8817500000000000000 : ℝ)+2*(495620994631/352700000000000 : ℝ)*(11203/100000 : ℝ)=(5000227489697057/5000000000000000 : ℝ) by norm_num, show 1+2*(4806739022604503/50000000000000000000 : ℝ)=(25004806739022604503/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1222444681901291/4000000000000000000 : ℝ)+(4806739022604503/50000000000000000000 : ℝ) ≤ ((8815124957079334473/8817500000000000000 : ℝ)+(495620994631/352700000000000 : ℝ)*((1473/10000 : ℝ)+(11203/100000 : ℝ)))^(4327/1024 : ℝ) := by
    rw [show (8815124957079334473/8817500000000000000 : ℝ)+(495620994631/352700000000000 : ℝ)*((1473/10000 : ℝ)+(11203/100000 : ℝ))=(2000190120077749/2000000000000000 : ℝ) by norm_num, show 1+(1222444681901291/4000000000000000000 : ℝ)+(4806739022604503/50000000000000000000 : ℝ)=(100040174595092741281/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1222444681901291/4000000000000000000 : ℝ) ≤ ((8815124957079334473/8817500000000000000 : ℝ)+2*(495620994631/352700000000000 : ℝ)*(1473/10000 : ℝ))^(4327/1024 : ℝ) := by
    rw [show (8815124957079334473/8817500000000000000 : ℝ)+2*(495620994631/352700000000000 : ℝ)*(1473/10000 : ℝ)=(625090388836461/625000000000000 : ℝ) by norm_num, show 1+2*(1222444681901291/4000000000000000000 : ℝ)=(2001222444681901291/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8815124957079334473/8817500000000000000 : ℝ)*(X 1 0+X 2 0)+(495620994631/352700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4327/1024 : ℝ)) (lo := (11203/100000 : ℝ)) (hi := (1473/10000 : ℝ)) (c := (8815124957079334473/8817500000000000000 : ℝ)) (alpha := (495620994631/352700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8815124957079334473/8817500000000000000 : ℝ)*(X 0 1+X 2 1)+(495620994631/352700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4327/1024 : ℝ)) (lo := (11203/100000 : ℝ)) (hi := (1473/10000 : ℝ)) (c := (8815124957079334473/8817500000000000000 : ℝ)) (alpha := (495620994631/352700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8815124957079334473/8817500000000000000 : ℝ)*(X 0 2+X 1 2)+(495620994631/352700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4327/1024 : ℝ)) (lo := (11203/100000 : ℝ)) (hi := (1473/10000 : ℝ)) (c := (8815124957079334473/8817500000000000000 : ℝ)) (alpha := (495620994631/352700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2021716017/10000000000 : ℝ)*X 0 0+(1352843849/2500000000 : ℝ)*X 0 1+(1311341421/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674268609/5000000000 : ℝ)*X 1 0+(-1053139557/5000000000 : ℝ)*X 1 1+(5245365687/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348537221/10000000000 : ℝ)*X 2 0+(655670711/1250000000 : ℝ)*X 2 1+(-526569777/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4319865641/10000000000 : ℝ)*X 0 0+(2073799747/5000000000 : ℝ)*X 0 1+(281170211/625000000 : ℝ)*X 0 2+(4319865641/10000000000 : ℝ)*X 1 0+(2073799747/5000000000 : ℝ)*X 1 1+(281170211/625000000 : ℝ)*X 1 2+(4319865641/10000000000 : ℝ)*X 2 0+(2073799747/5000000000 : ℝ)*X 2 1+(281170211/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-25271599/125000000 : ℝ)*X 0 0+(1049192269/2000000000 : ℝ)*X 0 1+(2705388333/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305651467/10000000000 : ℝ)*X 1 0+(-1940868131/10000000000 : ℝ)*X 1 1+(5410776663/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1061130293/2000000000 : ℝ)*X 2 0+(2705388333/5000000000 : ℝ)*X 2 1+(-194086813/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4319890827/10000000000 : ℝ)*X 0 0+(2248731761/5000000000 : ℝ)*X 0 1+(4148865861/10000000000 : ℝ)*X 0 2+(4319890827/10000000000 : ℝ)*X 1 0+(2248731761/5000000000 : ℝ)*X 1 1+(4148865861/10000000000 : ℝ)*X 1 2+(4319890827/10000000000 : ℝ)*X 2 0+(2248731761/5000000000 : ℝ)*X 2 1+(4148865861/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (518066046991968522787596057/220437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (223476271/50000000000000 : ℝ)*(base19) + (211675483/50000000000000 : ℝ)*(base23) + (14430519/100000000000000 : ℝ)*(lower2) + (29095927/50000000000000 : ℝ)*(upper3) + (46042739/100000000000000 : ℝ)*(upper5) + (2217942385158203/50000000000000 : ℝ)*(major0) + (2217942385158203/50000000000000 : ℝ)*(major1) + (2217942385158203/50000000000000 : ℝ)*(major2) + (6023753423079817/100000000000000 : ℝ)*(sp0) + (1505940603682641/25000000000000 : ℝ)*(sp1) + (301188121916607/5000000000000 : ℝ)*(sp2) + (284800196806747/10000000000000 : ℝ)*(sp3) + (9438603289/100000000000000 : ℝ)*(sp4) + (1158135791/25000000000000 : ℝ)*(sp7) + (1424003300305317/50000000000000 : ℝ)*(f.failure) + (3011881430841553/50000000000000 : ℝ)*(f.sum) + (26866659653729/17635000000000000000000000000 : ℝ)*base66 + (447579691526203/125000000000000000000000000000 : ℝ)*base68 + (560915591651203/125000000000000000000000000000 : ℝ)*base70 + (287643330348797/125000000000000000000000000000 : ℝ)*base71 + (13655410582617/8817500000000000000000000000 : ℝ)*base74 + (850778487401203/125000000000000000000000000000 : ℝ)*base76 + (331663168151203/125000000000000000000000000000 : ℝ)*base78 + (1057199548098797/125000000000000000000000000000 : ℝ)*base79 + (15476830726323/8817500000000000000000000000 : ℝ)*base81 + (2506217/250000000000000000000 : ℝ)*base89 + (2506217/250000000000000000000 : ℝ)*base91 + (2506217/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (46343151985777419720442179/22043750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (36501641/10000000000000 : ℝ)*(base19) + (198940471/50000000000000 : ℝ)*(base23) + (43712657/100000000000000 : ℝ)*(upper3) + (391879/2500000000000 : ℝ)*(lower4) + (42753087/100000000000000 : ℝ)*(upper5) + (446801662566959/10000000000000 : ℝ)*(major0) + (446801662566959/10000000000000 : ℝ)*(major1) + (446801662566959/10000000000000 : ℝ)*(major2) + (7374438539/100000000000000 : ℝ)*(sp1) + (2017040823/25000000000000 : ℝ)*(sp2) + (3033698354199557/50000000000000 : ℝ)*(sp4) + (1213477793788833/20000000000000 : ℝ)*(sp5) + (18960588257359/312500000000 : ℝ)*(sp6) + (717159118215631/25000000000000 : ℝ)*(sp7) + (717159118215631/25000000000000 : ℝ)*(f.failure) + (3033698354199557/50000000000000 : ℝ)*(f.sum) + (1068794017811/1763500000000000000000000000 : ℝ)*base65 + (181198690904041/25000000000000000000000000000 : ℝ)*base67 + (34021960154041/25000000000000000000000000000 : ℝ)*base69 + (23649839729041/25000000000000000000000000000 : ℝ)*base71 + (4645408484149/3527000000000000000000000000 : ℝ)*base73 + (262852991054041/25000000000000000000000000000 : ℝ)*base75 + (34385314645959/25000000000000000000000000000 : ℝ)*base78 + (287276024754041/25000000000000000000000000000 : ℝ)*base79 + (1821436842551/1763500000000000000000000000 : ℝ)*base81 + (254331/125000000000000000000 : ℝ)*base89 + (254331/125000000000000000000 : ℝ)*base91 + (254331/125000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1368_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7787701/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1473/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11203/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11209/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14723/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1368_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1368_s7_0 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1010862337/5000000000 : ℝ)*x 0 + (2705660853/5000000000 : ℝ)*x 1 + (1311353363/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1010862337/5000000000 : ℝ)^541 ≤ (6159086041187/50000000000000 : ℝ)^413 := by
    have hnat : (1010862337 : ℕ)^541*50000000000000^413 ≤ 6159086041187^413*5000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1010862337 5000000000 6159086041187 50000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2705660853/5000000000 : ℝ)^541 ≤ (11183732601249/25000000000000 : ℝ)^413 := by
    have hnat : (2705660853 : ℕ)^541*25000000000000^413 ≤ 11183732601249^413*5000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705660853 5000000000 11183732601249 25000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311353363/2500000000 : ℝ)^541 ≤ (42946897491423/100000000000000 : ℝ)^413 := by
    have hnat : (1311353363 : ℕ)^541*100000000000000^413 ≤ 42946897491423^413*2500000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311353363 2500000000 42946897491423 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1010862337/5000000000 : ℝ), (2705660853/5000000000 : ℝ), (1311353363/2500000000 : ℝ)] ![(6159086041187/50000000000000 : ℝ), (11183732601249/25000000000000 : ℝ), (42946897491423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1010862337/5000000000 : ℝ)|^541 ≤ (6159086041187/50000000000000 : ℝ)^413
        have hw : |(-1010862337/5000000000 : ℝ)|=(1010862337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2705660853/5000000000 : ℝ)|^541 ≤ (11183732601249/25000000000000 : ℝ)^413
        have hw : |(2705660853/5000000000 : ℝ)|=(2705660853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311353363/2500000000 : ℝ)|^541 ≤ (42946897491423/100000000000000 : ℝ)^413
        have hw : |(1311353363/2500000000 : ℝ)|=(1311353363/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_s7_1 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1337130951/2500000000 : ℝ)*x 0 + (-105311737/500000000 : ℝ)*x 1 + (41963301/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337130951/2500000000 : ℝ)^541 ≤ (44056114593741/100000000000000 : ℝ)^413 := by
    have hnat : (1337130951 : ℕ)^541*100000000000000^413 ≤ 44056114593741^413*2500000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337130951 2500000000 44056114593741 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (105311737/500000000 : ℝ)^541 ≤ (2599399353149/20000000000000 : ℝ)^413 := by
    have hnat : (105311737 : ℕ)^541*20000000000000^413 ≤ 2599399353149^413*500000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105311737 500000000 2599399353149 20000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41963301/80000000 : ℝ)^541 ≤ (2684180538863/6250000000000 : ℝ)^413 := by
    have hnat : (41963301 : ℕ)^541*6250000000000^413 ≤ 2684180538863^413*80000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41963301 80000000 2684180538863 6250000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337130951/2500000000 : ℝ), (-105311737/500000000 : ℝ), (41963301/80000000 : ℝ)] ![(44056114593741/100000000000000 : ℝ), (2599399353149/20000000000000 : ℝ), (2684180538863/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337130951/2500000000 : ℝ)|^541 ≤ (44056114593741/100000000000000 : ℝ)^413
        have hw : |(1337130951/2500000000 : ℝ)|=(1337130951/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-105311737/500000000 : ℝ)|^541 ≤ (2599399353149/20000000000000 : ℝ)^413
        have hw : |(-105311737/500000000 : ℝ)|=(105311737/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(41963301/80000000 : ℝ)|^541 ≤ (2684180538863/6250000000000 : ℝ)^413
        have hw : |(41963301/80000000 : ℝ)|=(41963301/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_s7_2 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5348523437/10000000000 : ℝ)*x 0 + (1311353279/2500000000 : ℝ)*x 1 + (-2106234579/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348523437/10000000000 : ℝ)^541 ≤ (44056110633829/100000000000000 : ℝ)^413 := by
    have hnat : (5348523437 : ℕ)^541*100000000000000^413 ≤ 44056110633829^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348523437 10000000000 44056110633829 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311353279/2500000000 : ℝ)^541 ≤ (42946893887807/100000000000000 : ℝ)^413 := by
    have hnat : (1311353279 : ℕ)^541*100000000000000^413 ≤ 42946893887807^413*2500000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311353279 2500000000 42946893887807 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2106234579/10000000000 : ℝ)^541 ≤ (259939909287/2000000000000 : ℝ)^413 := by
    have hnat : (2106234579 : ℕ)^541*2000000000000^413 ≤ 259939909287^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2106234579 10000000000 259939909287 2000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348523437/10000000000 : ℝ), (1311353279/2500000000 : ℝ), (-2106234579/10000000000 : ℝ)] ![(44056110633829/100000000000000 : ℝ), (42946893887807/100000000000000 : ℝ), (259939909287/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348523437/10000000000 : ℝ)|^541 ≤ (44056110633829/100000000000000 : ℝ)^413
        have hw : |(5348523437/10000000000 : ℝ)|=(5348523437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311353279/2500000000 : ℝ)|^541 ≤ (42946893887807/100000000000000 : ℝ)^413
        have hw : |(1311353279/2500000000 : ℝ)|=(1311353279/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2106234579/10000000000 : ℝ)|^541 ≤ (259939909287/2000000000000 : ℝ)^413
        have hw : |(-2106234579/10000000000 : ℝ)|=(2106234579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_s7_3 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2159934441/5000000000 : ℝ)*x 0 + (829541203/2000000000 : ℝ)*x 1 + (281163519/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2159934441/5000000000 : ℝ)^541 ≤ (8325933315409/25000000000000 : ℝ)^413 := by
    have hnat : (2159934441 : ℕ)^541*25000000000000^413 ≤ 8325933315409^413*5000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2159934441 5000000000 8325933315409 25000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (829541203/2000000000 : ℝ)^541 ≤ (3946991682659/12500000000000 : ℝ)^413 := by
    have hnat : (829541203 : ℕ)^541*12500000000000^413 ≤ 3946991682659^413*2000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      829541203 2000000000 3946991682659 12500000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (281163519/625000000 : ℝ)^541 ≤ (7024066652971/20000000000000 : ℝ)^413 := by
    have hnat : (281163519 : ℕ)^541*20000000000000^413 ≤ 7024066652971^413*625000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281163519 625000000 7024066652971 20000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2159934441/5000000000 : ℝ), (829541203/2000000000 : ℝ), (281163519/625000000 : ℝ)] ![(8325933315409/25000000000000 : ℝ), (3946991682659/12500000000000 : ℝ), (7024066652971/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2159934441/5000000000 : ℝ)|^541 ≤ (8325933315409/25000000000000 : ℝ)^413
        have hw : |(2159934441/5000000000 : ℝ)|=(2159934441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(829541203/2000000000 : ℝ)|^541 ≤ (3946991682659/12500000000000 : ℝ)^413
        have hw : |(829541203/2000000000 : ℝ)|=(829541203/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(281163519/625000000 : ℝ)|^541 ≤ (7024066652971/20000000000000 : ℝ)^413
        have hw : |(281163519/625000000 : ℝ)|=(281163519/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_s7_4 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2021735423/10000000000 : ℝ)*x 0 + (81968881/156250000 : ℝ)*x 1 + (2705362273/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2021735423/10000000000 : ℝ)^541 ≤ (12318257873011/100000000000000 : ℝ)^413 := by
    have hnat : (2021735423 : ℕ)^541*100000000000000^413 ≤ 12318257873011^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2021735423 10000000000 12318257873011 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (81968881/156250000 : ℝ)^541 ≤ (21476639139197/50000000000000 : ℝ)^413 := by
    have hnat : (81968881 : ℕ)^541*50000000000000^413 ≤ 21476639139197^413*156250000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81968881 156250000 21476639139197 50000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2705362273/5000000000 : ℝ)^541 ≤ (22364231918057/50000000000000 : ℝ)^413 := by
    have hnat : (2705362273 : ℕ)^541*50000000000000^413 ≤ 22364231918057^413*5000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705362273 5000000000 22364231918057 50000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2021735423/10000000000 : ℝ), (81968881/156250000 : ℝ), (2705362273/5000000000 : ℝ)] ![(12318257873011/100000000000000 : ℝ), (21476639139197/50000000000000 : ℝ), (22364231918057/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2021735423/10000000000 : ℝ)|^541 ≤ (12318257873011/100000000000000 : ℝ)^413
        have hw : |(-2021735423/10000000000 : ℝ)|=(2021735423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(81968881/156250000 : ℝ)|^541 ≤ (21476639139197/50000000000000 : ℝ)^413
        have hw : |(81968881/156250000 : ℝ)|=(81968881/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2705362273/5000000000 : ℝ)|^541 ≤ (22364231918057/50000000000000 : ℝ)^413
        have hw : |(2705362273/5000000000 : ℝ)|=(2705362273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_s7_5 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5305663479/10000000000 : ℝ)*x 0 + (-970461661/5000000000 : ℝ)*x 1 + (5410724557/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305663479/10000000000 : ℝ)^541 ≤ (43594229131691/100000000000000 : ℝ)^413 := by
    have hnat : (5305663479 : ℕ)^541*100000000000000^413 ≤ 43594229131691^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305663479 10000000000 43594229131691 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (970461661/5000000000 : ℝ)^541 ≤ (11677306900007/100000000000000 : ℝ)^413 := by
    have hnat : (970461661 : ℕ)^541*100000000000000^413 ≤ 11677306900007^413*5000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      970461661 5000000000 11677306900007 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5410724557/10000000000 : ℝ)^541 ≤ (44728463955229/100000000000000 : ℝ)^413 := by
    have hnat : (5410724557 : ℕ)^541*100000000000000^413 ≤ 44728463955229^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410724557 10000000000 44728463955229 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305663479/10000000000 : ℝ), (-970461661/5000000000 : ℝ), (5410724557/10000000000 : ℝ)] ![(43594229131691/100000000000000 : ℝ), (11677306900007/100000000000000 : ℝ), (44728463955229/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305663479/10000000000 : ℝ)|^541 ≤ (43594229131691/100000000000000 : ℝ)^413
        have hw : |(5305663479/10000000000 : ℝ)|=(5305663479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-970461661/5000000000 : ℝ)|^541 ≤ (11677306900007/100000000000000 : ℝ)^413
        have hw : |(-970461661/5000000000 : ℝ)|=(970461661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5410724557/10000000000 : ℝ)|^541 ≤ (44728463955229/100000000000000 : ℝ)^413
        have hw : |(5410724557/10000000000 : ℝ)|=(5410724557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_s7_6 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (331603967/625000000 : ℝ)*x 0 + (1352681139/2500000000 : ℝ)*x 1 + (-485230833/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (331603967/625000000 : ℝ)^541 ≤ (871884581127/2000000000000 : ℝ)^413 := by
    have hnat : (331603967 : ℕ)^541*2000000000000^413 ≤ 871884581127^413*625000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331603967 625000000 871884581127 2000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352681139/2500000000 : ℝ)^541 ≤ (44728463944401/100000000000000 : ℝ)^413 := by
    have hnat : (1352681139 : ℕ)^541*100000000000000^413 ≤ 44728463944401^413*2500000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352681139 2500000000 44728463944401 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (485230833/2500000000 : ℝ)^541 ≤ (11677306978817/100000000000000 : ℝ)^413 := by
    have hnat : (485230833 : ℕ)^541*100000000000000^413 ≤ 11677306978817^413*2500000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      485230833 2500000000 11677306978817 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(331603967/625000000 : ℝ), (1352681139/2500000000 : ℝ), (-485230833/2500000000 : ℝ)] ![(871884581127/2000000000000 : ℝ), (44728463944401/100000000000000 : ℝ), (11677306978817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(331603967/625000000 : ℝ)|^541 ≤ (871884581127/2000000000000 : ℝ)^413
        have hw : |(331603967/625000000 : ℝ)|=(331603967/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352681139/2500000000 : ℝ)|^541 ≤ (44728463944401/100000000000000 : ℝ)^413
        have hw : |(1352681139/2500000000 : ℝ)|=(1352681139/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-485230833/2500000000 : ℝ)|^541 ≤ (11677306978817/100000000000000 : ℝ)^413
        have hw : |(-485230833/2500000000 : ℝ)|=(485230833/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_s7_7 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1079973587/2500000000 : ℝ)*x 0 + (22486791/50000000 : ℝ)*x 1 + (4148970283/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079973587/2500000000 : ℝ)^541 ≤ (33303990437791/100000000000000 : ℝ)^413 := by
    have hnat : (1079973587 : ℕ)^541*100000000000000^413 ≤ 33303990437791^413*2500000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079973587 2500000000 33303990437791 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (22486791/50000000 : ℝ)^541 ≤ (35107467825883/100000000000000 : ℝ)^413 := by
    have hnat : (22486791 : ℕ)^541*100000000000000^413 ≤ 35107467825883^413*50000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22486791 50000000 35107467825883 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4148970283/10000000000 : ℝ)^541 ≤ (31588541719723/100000000000000 : ℝ)^413 := by
    have hnat : (4148970283 : ℕ)^541*100000000000000^413 ≤ 31588541719723^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4148970283 10000000000 31588541719723 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1079973587/2500000000 : ℝ), (22486791/50000000 : ℝ), (4148970283/10000000000 : ℝ)] ![(33303990437791/100000000000000 : ℝ), (35107467825883/100000000000000 : ℝ), (31588541719723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1079973587/2500000000 : ℝ)|^541 ≤ (33303990437791/100000000000000 : ℝ)^413
        have hw : |(1079973587/2500000000 : ℝ)|=(1079973587/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(22486791/50000000 : ℝ)|^541 ≤ (35107467825883/100000000000000 : ℝ)^413
        have hw : |(22486791/50000000 : ℝ)|=(22486791/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4148970283/10000000000 : ℝ)|^541 ≤ (31588541719723/100000000000000 : ℝ)^413
        have hw : |(4148970283/10000000000 : ℝ)|=(4148970283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_s7_8 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-24141491/10000000000 : ℝ)*x 0 + (5889366161/10000000000 : ℝ)*x 1 + (1472349343/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (24141491/10000000000 : ℝ)^541 ≤ (37291604583/100000000000000 : ℝ)^413 := by
    have hnat : (24141491 : ℕ)^541*100000000000000^413 ≤ 37291604583^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24141491 10000000000 37291604583 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5889366161/10000000000 : ℝ)^541 ≤ (24990590353349/50000000000000 : ℝ)^413 := by
    have hnat : (5889366161 : ℕ)^541*50000000000000^413 ≤ 24990590353349^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5889366161 10000000000 24990590353349 50000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1472349343/2500000000 : ℝ)^541 ≤ (49981527677723/100000000000000 : ℝ)^413 := by
    have hnat : (1472349343 : ℕ)^541*100000000000000^413 ≤ 49981527677723^413*2500000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1472349343 2500000000 49981527677723 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-24141491/10000000000 : ℝ), (5889366161/10000000000 : ℝ), (1472349343/2500000000 : ℝ)] ![(37291604583/100000000000000 : ℝ), (24990590353349/50000000000000 : ℝ), (49981527677723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-24141491/10000000000 : ℝ)|^541 ≤ (37291604583/100000000000000 : ℝ)^413
        have hw : |(-24141491/10000000000 : ℝ)|=(24141491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5889366161/10000000000 : ℝ)|^541 ≤ (24990590353349/50000000000000 : ℝ)^413
        have hw : |(5889366161/10000000000 : ℝ)|=(5889366161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1472349343/2500000000 : ℝ)|^541 ≤ (49981527677723/100000000000000 : ℝ)^413
        have hw : |(1472349343/2500000000 : ℝ)|=(1472349343/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_s7_9 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1414753419/10000000000 : ℝ)*x 0 + (692518139/1250000000 : ℝ)*x 1 + (1385328287/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1414753419/10000000000 : ℝ)^541 ≤ (7717088472043/100000000000000 : ℝ)^413 := by
    have hnat : (1414753419 : ℕ)^541*100000000000000^413 ≤ 7717088472043^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1414753419 10000000000 7717088472043 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (692518139/1250000000 : ℝ)^541 ≤ (461350849027/1000000000000 : ℝ)^413 := by
    have hnat : (692518139 : ℕ)^541*1000000000000^413 ≤ 461350849027^413*1250000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      692518139 1250000000 461350849027 1000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1385328287/2500000000 : ℝ)^541 ≤ (46147826615557/100000000000000 : ℝ)^413 := by
    have hnat : (1385328287 : ℕ)^541*100000000000000^413 ≤ 46147826615557^413*2500000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1385328287 2500000000 46147826615557 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1414753419/10000000000 : ℝ), (692518139/1250000000 : ℝ), (1385328287/2500000000 : ℝ)] ![(7717088472043/100000000000000 : ℝ), (461350849027/1000000000000 : ℝ), (46147826615557/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1414753419/10000000000 : ℝ)|^541 ≤ (7717088472043/100000000000000 : ℝ)^413
        have hw : |(1414753419/10000000000 : ℝ)|=(1414753419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(692518139/1250000000 : ℝ)|^541 ≤ (461350849027/1000000000000 : ℝ)^413
        have hw : |(692518139/1250000000 : ℝ)|=(692518139/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1385328287/2500000000 : ℝ)|^541 ≤ (46147826615557/100000000000000 : ℝ)^413
        have hw : |(1385328287/2500000000 : ℝ)|=(1385328287/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1368_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7787701/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14723/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11209/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1121/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7361/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14723/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11209/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14723/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11209/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14723/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11209/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14723/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11209/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14723/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11209/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14723/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11209/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11209/100000 : ℝ) ^ (4327/1024 : ℝ) ≤ (9635253112568077/100000000000000000000 : ℝ) := by
    have hpowers : (11209/100000 : ℝ)^4327 ≤ (9635253112568077/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11209 : ℕ)^4327*100000000000000000000^1024 ≤ 9635253112568077^1024*100000^4327 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11209 100000 9635253112568077 100000000000000000000 4327 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11209/100000 : ℝ)) (X := (9635253112568077/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4327 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14723/100000 : ℝ) ^ (4327/1024 : ℝ) ≤ (3049979472594721/10000000000000000000 : ℝ) := by
    have hpowers : (14723/100000 : ℝ)^4327 ≤ (3049979472594721/10000000000000000000 : ℝ)^1024 := by
      have hnat : (14723 : ℕ)^4327*10000000000000000000^1024 ≤ 3049979472594721^1024*100000^4327 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14723 100000 3049979472594721 10000000000000000000 4327 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14723/100000 : ℝ)) (X := (3049979472594721/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4327 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009635253112568077/50000000000000000000 : ℝ) ≤ (10000456009872193/10000000000000000 : ℝ) ^ (4327/1024 : ℝ) := by
    have hpowers : (50009635253112568077/50000000000000000000 : ℝ)^1024 ≤ (10000456009872193/10000000000000000 : ℝ)^4327 := by
      have hnat : (50009635253112568077 : ℕ)^1024*10000000000000000^4327 ≤ 10000456009872193^4327*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009635253112568077 50000000000000000000 10000456009872193 10000000000000000 1024 4327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000456009872193/10000000000000000 : ℝ)) (X := (50009635253112568077/50000000000000000000 : ℝ)) (by norm_num) 4327 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100040135047838515287/100000000000000000000 : ℝ) ≤ (1250118708096953/1250000000000000 : ℝ) ^ (4327/1024 : ℝ) := by
    have hpowers : (100040135047838515287/100000000000000000000 : ℝ)^1024 ≤ (1250118708096953/1250000000000000 : ℝ)^4327 := by
      have hnat : (100040135047838515287 : ℕ)^1024*1250000000000000^4327 ≤ 1250118708096953^4327*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100040135047838515287 100000000000000000000 1250118708096953 1250000000000000 1024 4327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250118708096953/1250000000000000 : ℝ)) (X := (100040135047838515287/100000000000000000000 : ℝ)) (by norm_num) 4327 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003049979472594721/5000000000000000000 : ℝ) ≤ (2000288663935811/2000000000000000 : ℝ) ^ (4327/1024 : ℝ) := by
    have hpowers : (5003049979472594721/5000000000000000000 : ℝ)^1024 ≤ (2000288663935811/2000000000000000 : ℝ)^4327 := by
      have hnat : (5003049979472594721 : ℕ)^1024*2000000000000000^4327 ≤ 2000288663935811^4327*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003049979472594721 5000000000000000000 2000288663935811 2000000000000000 1024 4327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000288663935811/2000000000000000 : ℝ)) (X := (5003049979472594721/5000000000000000000 : ℝ)) (by norm_num) 4327 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9635253112568077/100000000000000000000 : ℝ) ≤ ((8782633915766442511/8785000000000000000 : ℝ)+2*(493654903431/351400000000000 : ℝ)*(11209/100000 : ℝ))^(4327/1024 : ℝ) := by
    rw [show (8782633915766442511/8785000000000000000 : ℝ)+2*(493654903431/351400000000000 : ℝ)*(11209/100000 : ℝ)=(10000456009872193/10000000000000000 : ℝ) by norm_num, show 1+2*(9635253112568077/100000000000000000000 : ℝ)=(50009635253112568077/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3049979472594721/10000000000000000000 : ℝ)+(9635253112568077/100000000000000000000 : ℝ) ≤ ((8782633915766442511/8785000000000000000 : ℝ)+(493654903431/351400000000000 : ℝ)*((14723/100000 : ℝ)+(11209/100000 : ℝ)))^(4327/1024 : ℝ) := by
    rw [show (8782633915766442511/8785000000000000000 : ℝ)+(493654903431/351400000000000 : ℝ)*((14723/100000 : ℝ)+(11209/100000 : ℝ))=(1250118708096953/1250000000000000 : ℝ) by norm_num, show 1+(3049979472594721/10000000000000000000 : ℝ)+(9635253112568077/100000000000000000000 : ℝ)=(100040135047838515287/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3049979472594721/10000000000000000000 : ℝ) ≤ ((8782633915766442511/8785000000000000000 : ℝ)+2*(493654903431/351400000000000 : ℝ)*(14723/100000 : ℝ))^(4327/1024 : ℝ) := by
    rw [show (8782633915766442511/8785000000000000000 : ℝ)+2*(493654903431/351400000000000 : ℝ)*(14723/100000 : ℝ)=(2000288663935811/2000000000000000 : ℝ) by norm_num, show 1+2*(3049979472594721/10000000000000000000 : ℝ)=(5003049979472594721/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8782633915766442511/8785000000000000000 : ℝ)*(X 1 0+X 2 0)+(493654903431/351400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4327/1024 : ℝ)) (lo := (11209/100000 : ℝ)) (hi := (14723/100000 : ℝ)) (c := (8782633915766442511/8785000000000000000 : ℝ)) (alpha := (493654903431/351400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8782633915766442511/8785000000000000000 : ℝ)*(X 0 1+X 2 1)+(493654903431/351400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4327/1024 : ℝ)) (lo := (11209/100000 : ℝ)) (hi := (14723/100000 : ℝ)) (c := (8782633915766442511/8785000000000000000 : ℝ)) (alpha := (493654903431/351400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8782633915766442511/8785000000000000000 : ℝ)*(X 0 2+X 1 2)+(493654903431/351400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4327/1024 : ℝ)) (lo := (11209/100000 : ℝ)) (hi := (14723/100000 : ℝ)) (c := (8782633915766442511/8785000000000000000 : ℝ)) (alpha := (493654903431/351400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1010862337/5000000000 : ℝ)*X 0 0+(2705660853/5000000000 : ℝ)*X 0 1+(1311353363/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337130951/2500000000 : ℝ)*X 1 0+(-105311737/500000000 : ℝ)*X 1 1+(41963301/80000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348523437/10000000000 : ℝ)*X 2 0+(1311353279/2500000000 : ℝ)*X 2 1+(-2106234579/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2159934441/5000000000 : ℝ)*X 0 0+(829541203/2000000000 : ℝ)*X 0 1+(281163519/625000000 : ℝ)*X 0 2+(2159934441/5000000000 : ℝ)*X 1 0+(829541203/2000000000 : ℝ)*X 1 1+(281163519/625000000 : ℝ)*X 1 2+(2159934441/5000000000 : ℝ)*X 2 0+(829541203/2000000000 : ℝ)*X 2 1+(281163519/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2021735423/10000000000 : ℝ)*X 0 0+(81968881/156250000 : ℝ)*X 0 1+(2705362273/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305663479/10000000000 : ℝ)*X 1 0+(-970461661/5000000000 : ℝ)*X 1 1+(5410724557/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((331603967/625000000 : ℝ)*X 2 0+(1352681139/2500000000 : ℝ)*X 2 1+(-485230833/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1079973587/2500000000 : ℝ)*X 0 0+(22486791/50000000 : ℝ)*X 0 1+(4148970283/10000000000 : ℝ)*X 0 2+(1079973587/2500000000 : ℝ)*X 1 0+(22486791/50000000 : ℝ)*X 1 1+(4148970283/10000000000 : ℝ)*X 1 2+(1079973587/2500000000 : ℝ)*X 2 0+(22486791/50000000 : ℝ)*X 2 1+(4148970283/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-24141491/10000000000 : ℝ)*X 0 0+(5889366161/10000000000 : ℝ)*X 0 1+(1472349343/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s7_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1414753419/10000000000 : ℝ)*X 0 0+(692518139/1250000000 : ℝ)*X 0 1+(1385328287/2500000000 : ℝ)*X 0 2+(1414753419/10000000000 : ℝ)*X 1 0+(692518139/1250000000 : ℝ)*X 1 1+(1385328287/2500000000 : ℝ)*X 1 2+(1414753419/10000000000 : ℝ)*X 2 0+(692518139/1250000000 : ℝ)*X 2 1+(1385328287/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_s7_9 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (51633883613279301757827567/27453125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (395380301/100000000000000 : ℝ)*(lower3) + (106370807/50000000000000 : ℝ)*(lower4) + (26586653/50000000000000 : ℝ)*(lower5) + (138705763632419/3125000000000 : ℝ)*(major0) + (138705763632419/3125000000000 : ℝ)*(major1) + (138705763632419/3125000000000 : ℝ)*(major2) + (3013711454990641/50000000000000 : ℝ)*(sp0) + (3013699634269341/50000000000000 : ℝ)*(sp1) + (6027401243332937/100000000000000 : ℝ)*(sp2) + (284973911726359/10000000000000 : ℝ)*(sp3) + (29652514723/100000000000000 : ℝ)*(sp5) + (6919430117/25000000000000 : ℝ)*(sp6) + (6011072123/100000000000000 : ℝ)*(sp8) + (771464423/100000000000000 : ℝ)*(sp9) + (1424869944364007/50000000000000 : ℝ)*(f.failure) + (1205485784210681/20000000000000 : ℝ)*(f.sum) + (6807400533009/2196250000000000000000000000 : ℝ)*base66 + (955470669429001/1715820312500000000000000000000 : ℝ)*base68 + (209424806153339109/27453125000000000000000000000000 : ℝ)*base69 + (676401499402620359/27453125000000000000000000000000 : ℝ)*base71 + (9413771246881/2196250000000000000000000000 : ℝ)*base73 + (48003874101080871/6863281250000000000000000000000 : ℝ)*base75 + (304955180308245359/27453125000000000000000000000000 : ℝ)*base77 + (46781870886245359/27453125000000000000000000000000 : ℝ)*base79 + (313292542601/8785000000000000000000000000 : ℝ)*base82 + (1677907/250000000000000000000 : ℝ)*base89 + (1677907/250000000000000000000 : ℝ)*base91 + (1677907/250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6851644567035233141243493/1568750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11889457/25000000000000 : ℝ)*(lower1) + (51721071/50000000000000 : ℝ)*(lower3) + (3243941/50000000000000 : ℝ)*(lower4) + (92337827/100000000000000 : ℝ)*(lower5) + (223535277513653/5000000000000 : ℝ)*(major0) + (223535277513653/5000000000000 : ℝ)*(major1) + (223535277513653/5000000000000 : ℝ)*(major2) + (65274471/12500000000000 : ℝ)*(sp1) + (6071046963658449/100000000000000 : ℝ)*(sp4) + (6071047568118427/100000000000000 : ℝ)*(sp5) + (1214209618062839/20000000000000 : ℝ)*(sp6) + (287036200511217/10000000000000 : ℝ)*(sp7) + (563327873/50000000000000 : ℝ)*(sp8) + (859533673/100000000000000 : ℝ)*(sp9) + (717590716161461/25000000000000 : ℝ)*(f.failure) + (1214209618062839/20000000000000 : ℝ)*(f.sum) + (19252150467/31375000000000000000000000 : ℝ)*base66 + (82375485279789669/6275000000000000000000000000000 : ℝ)*base67 + (52640975669760331/6275000000000000000000000000000 : ℝ)*base70 + (53316059085939669/6275000000000000000000000000000 : ℝ)*base71 + (141455255159/62750000000000000000000000 : ℝ)*base73 + (23686905894664669/6275000000000000000000000000000 : ℝ)*base75 + (34254516466314669/6275000000000000000000000000000 : ℝ)*base77 + (93125659044839669/6275000000000000000000000000000 : ℝ)*base79 + (1833425773/490234375000000000000000 : ℝ)*base82 + (991161/125000000000000000000 : ℝ)*base89 + (991161/125000000000000000000 : ℝ)*base91 + (991161/125000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1368_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7787701/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14723/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11209/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1121/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7361/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1368_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1368_box_0 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-928256243/5000000000 : ℝ)*x 0 + (1347211669/2500000000 : ℝ)*x 1 + (269442327/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (928256243/5000000000 : ℝ)^541 ≤ (550829690183/5000000000000 : ℝ)^413 := by
    have hnat : (928256243 : ℕ)^541*5000000000000^413 ≤ 550829690183^413*5000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      928256243 5000000000 550829690183 5000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1347211669/2500000000 : ℝ)^541 ≤ (44491703827213/100000000000000 : ℝ)^413 := by
    have hnat : (1347211669 : ℕ)^541*100000000000000^413 ≤ 44491703827213^413*2500000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347211669 2500000000 44491703827213 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269442327/500000000 : ℝ)^541 ≤ (1112292558909/2500000000000 : ℝ)^413 := by
    have hnat : (269442327 : ℕ)^541*2500000000000^413 ≤ 1112292558909^413*500000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269442327 500000000 1112292558909 2500000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-928256243/5000000000 : ℝ), (1347211669/2500000000 : ℝ), (269442327/500000000 : ℝ)] ![(550829690183/5000000000000 : ℝ), (44491703827213/100000000000000 : ℝ), (1112292558909/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-928256243/5000000000 : ℝ)|^541 ≤ (550829690183/5000000000000 : ℝ)^413
        have hw : |(-928256243/5000000000 : ℝ)|=(928256243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1347211669/2500000000 : ℝ)|^541 ≤ (44491703827213/100000000000000 : ℝ)^413
        have hw : |(1347211669/2500000000 : ℝ)|=(1347211669/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269442327/500000000 : ℝ)|^541 ≤ (1112292558909/2500000000000 : ℝ)^413
        have hw : |(269442327/500000000 : ℝ)|=(269442327/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_box_1 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5285496521/10000000000 : ℝ)*x 0 + (-399646171/2000000000 : ℝ)*x 1 + (5388846421/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285496521/10000000000 : ℝ)^541 ≤ (43377298539823/100000000000000 : ℝ)^413 := by
    have hnat : (5285496521 : ℕ)^541*100000000000000^413 ≤ 43377298539823^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285496521 10000000000 43377298539823 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (399646171/2000000000 : ℝ)^541 ≤ (12131000372693/100000000000000 : ℝ)^413 := by
    have hnat : (399646171 : ℕ)^541*100000000000000^413 ≤ 12131000372693^413*2000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      399646171 2000000000 12131000372693 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5388846421/10000000000 : ℝ)^541 ≤ (44491701069363/100000000000000 : ℝ)^413 := by
    have hnat : (5388846421 : ℕ)^541*100000000000000^413 ≤ 44491701069363^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5388846421 10000000000 44491701069363 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285496521/10000000000 : ℝ), (-399646171/2000000000 : ℝ), (5388846421/10000000000 : ℝ)] ![(43377298539823/100000000000000 : ℝ), (12131000372693/100000000000000 : ℝ), (44491701069363/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285496521/10000000000 : ℝ)|^541 ≤ (43377298539823/100000000000000 : ℝ)^413
        have hw : |(5285496521/10000000000 : ℝ)|=(5285496521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-399646171/2000000000 : ℝ)|^541 ≤ (12131000372693/100000000000000 : ℝ)^413
        have hw : |(-399646171/2000000000 : ℝ)|=(399646171/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5388846421/10000000000 : ℝ)|^541 ≤ (44491701069363/100000000000000 : ℝ)^413
        have hw : |(5388846421/10000000000 : ℝ)|=(5388846421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_box_2 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5285495973/10000000000 : ℝ)*x 0 + (2694423523/5000000000 : ℝ)*x 1 + (-999115373/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285495973/10000000000 : ℝ)^541 ≤ (43377292648613/100000000000000 : ℝ)^413 := by
    have hnat : (5285495973 : ℕ)^541*100000000000000^413 ≤ 43377292648613^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285495973 10000000000 43377292648613 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2694423523/5000000000 : ℝ)^541 ≤ (44491707828799/100000000000000 : ℝ)^413 := by
    have hnat : (2694423523 : ℕ)^541*100000000000000^413 ≤ 44491707828799^413*5000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2694423523 5000000000 44491707828799 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (999115373/5000000000 : ℝ)^541 ≤ (6065499752941/50000000000000 : ℝ)^413 := by
    have hnat : (999115373 : ℕ)^541*50000000000000^413 ≤ 6065499752941^413*5000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      999115373 5000000000 6065499752941 50000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285495973/10000000000 : ℝ), (2694423523/5000000000 : ℝ), (-999115373/5000000000 : ℝ)] ![(43377292648613/100000000000000 : ℝ), (44491707828799/100000000000000 : ℝ), (6065499752941/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285495973/10000000000 : ℝ)|^541 ≤ (43377292648613/100000000000000 : ℝ)^413
        have hw : |(5285495973/10000000000 : ℝ)|=(5285495973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2694423523/5000000000 : ℝ)|^541 ≤ (44491707828799/100000000000000 : ℝ)^413
        have hw : |(2694423523/5000000000 : ℝ)|=(2694423523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-999115373/5000000000 : ℝ)|^541 ≤ (6065499752941/50000000000000 : ℝ)^413
        have hw : |(-999115373/5000000000 : ℝ)|=(999115373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_box_3 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4467454509/10000000000 : ℝ)*x 0 + (2124954301/5000000000 : ℝ)*x 1 + (4249908917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4467454509/10000000000 : ℝ)^541 ≤ (34801999889243/100000000000000 : ℝ)^413 := by
    have hnat : (4467454509 : ℕ)^541*100000000000000^413 ≤ 34801999889243^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4467454509 10000000000 34801999889243 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2124954301/5000000000 : ℝ)^541 ≤ (32598998462957/100000000000000 : ℝ)^413 := by
    have hnat : (2124954301 : ℕ)^541*100000000000000^413 ≤ 32598998462957^413*5000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124954301 5000000000 32598998462957 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4249908917/10000000000 : ℝ)^541 ≤ (32599001628021/100000000000000 : ℝ)^413 := by
    have hnat : (4249908917 : ℕ)^541*100000000000000^413 ≤ 32599001628021^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4249908917 10000000000 32599001628021 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4467454509/10000000000 : ℝ), (2124954301/5000000000 : ℝ), (4249908917/10000000000 : ℝ)] ![(34801999889243/100000000000000 : ℝ), (32598998462957/100000000000000 : ℝ), (32599001628021/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4467454509/10000000000 : ℝ)|^541 ≤ (34801999889243/100000000000000 : ℝ)^413
        have hw : |(4467454509/10000000000 : ℝ)|=(4467454509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2124954301/5000000000 : ℝ)|^541 ≤ (32598998462957/100000000000000 : ℝ)^413
        have hw : |(2124954301/5000000000 : ℝ)|=(2124954301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4249908917/10000000000 : ℝ)|^541 ≤ (32599001628021/100000000000000 : ℝ)^413
        have hw : |(4249908917/10000000000 : ℝ)|=(4249908917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_box_4 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1094840411/5000000000 : ℝ)*x 0 + (658184449/1250000000 : ℝ)*x 1 + (1316368967/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1094840411/5000000000 : ℝ)^541 ≤ (3418903085193/25000000000000 : ℝ)^413 := by
    have hnat : (1094840411 : ℕ)^541*25000000000000^413 ≤ 3418903085193^413*5000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094840411 5000000000 3418903085193 25000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658184449/1250000000 : ℝ)^541 ≤ (1079054808517/2500000000000 : ℝ)^413 := by
    have hnat : (658184449 : ℕ)^541*2500000000000^413 ≤ 1079054808517^413*1250000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658184449 1250000000 1079054808517 2500000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316368967/2500000000 : ℝ)^541 ≤ (21581097652149/50000000000000 : ℝ)^413 := by
    have hnat : (1316368967 : ℕ)^541*50000000000000^413 ≤ 21581097652149^413*2500000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316368967 2500000000 21581097652149 50000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1094840411/5000000000 : ℝ), (658184449/1250000000 : ℝ), (1316368967/2500000000 : ℝ)] ![(3418903085193/25000000000000 : ℝ), (1079054808517/2500000000000 : ℝ), (21581097652149/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1094840411/5000000000 : ℝ)|^541 ≤ (3418903085193/25000000000000 : ℝ)^413
        have hw : |(-1094840411/5000000000 : ℝ)|=(1094840411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658184449/1250000000 : ℝ)|^541 ≤ (1079054808517/2500000000000 : ℝ)^413
        have hw : |(658184449/1250000000 : ℝ)|=(658184449/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316368967/2500000000 : ℝ)|^541 ≤ (21581097652149/50000000000000 : ℝ)^413
        have hw : |(1316368967/2500000000 : ℝ)|=(1316368967/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_box_5 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2686027671/5000000000 : ℝ)*x 0 + (-2047914247/10000000000 : ℝ)*x 1 + (329092223/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2686027671/5000000000 : ℝ)^541 ≤ (22155095834543/50000000000000 : ℝ)^413 := by
    have hnat : (2686027671 : ℕ)^541*50000000000000^413 ≤ 22155095834543^413*5000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2686027671 5000000000 22155095834543 50000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2047914247/10000000000 : ℝ)^541 ≤ (626380811791/5000000000000 : ℝ)^413 := by
    have hnat : (2047914247 : ℕ)^541*5000000000000^413 ≤ 626380811791^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2047914247 10000000000 626380811791 5000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (329092223/625000000 : ℝ)^541 ≤ (21581096041487/50000000000000 : ℝ)^413 := by
    have hnat : (329092223 : ℕ)^541*50000000000000^413 ≤ 21581096041487^413*625000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329092223 625000000 21581096041487 50000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2686027671/5000000000 : ℝ), (-2047914247/10000000000 : ℝ), (329092223/625000000 : ℝ)] ![(22155095834543/50000000000000 : ℝ), (626380811791/5000000000000 : ℝ), (21581096041487/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2686027671/5000000000 : ℝ)|^541 ≤ (22155095834543/50000000000000 : ℝ)^413
        have hw : |(2686027671/5000000000 : ℝ)|=(2686027671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2047914247/10000000000 : ℝ)|^541 ≤ (626380811791/5000000000000 : ℝ)^413
        have hw : |(-2047914247/10000000000 : ℝ)|=(2047914247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(329092223/625000000 : ℝ)|^541 ≤ (21581096041487/50000000000000 : ℝ)^413
        have hw : |(329092223/625000000 : ℝ)|=(329092223/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_box_6 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5372055019/10000000000 : ℝ)*x 0 + (2632737849/5000000000 : ℝ)*x 1 + (-511978627/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5372055019/10000000000 : ℝ)^541 ≤ (44310188179187/100000000000000 : ℝ)^413 := by
    have hnat : (5372055019 : ℕ)^541*100000000000000^413 ≤ 44310188179187^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5372055019 10000000000 44310188179187 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632737849/5000000000 : ℝ)^541 ≤ (43162193478881/100000000000000 : ℝ)^413 := by
    have hnat : (2632737849 : ℕ)^541*100000000000000^413 ≤ 43162193478881^413*5000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632737849 5000000000 43162193478881 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (511978627/2500000000 : ℝ)^541 ≤ (2505523665451/20000000000000 : ℝ)^413 := by
    have hnat : (511978627 : ℕ)^541*20000000000000^413 ≤ 2505523665451^413*2500000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      511978627 2500000000 2505523665451 20000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5372055019/10000000000 : ℝ), (2632737849/5000000000 : ℝ), (-511978627/2500000000 : ℝ)] ![(44310188179187/100000000000000 : ℝ), (43162193478881/100000000000000 : ℝ), (2505523665451/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5372055019/10000000000 : ℝ)|^541 ≤ (44310188179187/100000000000000 : ℝ)^413
        have hw : |(5372055019/10000000000 : ℝ)|=(5372055019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632737849/5000000000 : ℝ)|^541 ≤ (43162193478881/100000000000000 : ℝ)^413
        have hw : |(2632737849/5000000000 : ℝ)|=(2632737849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-511978627/2500000000 : ℝ)|^541 ≤ (2505523665451/20000000000000 : ℝ)^413
        have hw : |(-511978627/2500000000 : ℝ)|=(511978627/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_box_7 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4171320719/10000000000 : ℝ)*x 0 + (4397922931/10000000000 : ℝ)*x 1 + (879584583/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4171320719/10000000000 : ℝ)^541 ≤ (31811633932041/100000000000000 : ℝ)^413 := by
    have hnat : (4171320719 : ℕ)^541*100000000000000^413 ≤ 31811633932041^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171320719 10000000000 31811633932041 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4397922931/10000000000 : ℝ)^541 ≤ (1704709155357/5000000000000 : ℝ)^413 := by
    have hnat : (4397922931 : ℕ)^541*5000000000000^413 ≤ 1704709155357^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4397922931 10000000000 1704709155357 5000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (879584583/2000000000 : ℝ)^541 ≤ (1704709147233/5000000000000 : ℝ)^413 := by
    have hnat : (879584583 : ℕ)^541*5000000000000^413 ≤ 1704709147233^413*2000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      879584583 2000000000 1704709147233 5000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4171320719/10000000000 : ℝ), (4397922931/10000000000 : ℝ), (879584583/2000000000 : ℝ)] ![(31811633932041/100000000000000 : ℝ), (1704709155357/5000000000000 : ℝ), (1704709147233/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4171320719/10000000000 : ℝ)|^541 ≤ (31811633932041/100000000000000 : ℝ)^413
        have hw : |(4171320719/10000000000 : ℝ)|=(4171320719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4397922931/10000000000 : ℝ)|^541 ≤ (1704709155357/5000000000000 : ℝ)^413
        have hw : |(4397922931/10000000000 : ℝ)|=(4397922931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(879584583/2000000000 : ℝ)|^541 ≤ (1704709147233/5000000000000 : ℝ)^413
        have hw : |(879584583/2000000000 : ℝ)|=(879584583/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_box_8 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2119649449/10000000000 : ℝ)*x 0 + (1295105599/2500000000 : ℝ)*x 1 + (270142699/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2119649449/10000000000 : ℝ)^541 ≤ (13105537438171/100000000000000 : ℝ)^413 := by
    have hnat : (2119649449 : ℕ)^541*100000000000000^413 ≤ 13105537438171^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119649449 10000000000 13105537438171 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1295105599/2500000000 : ℝ)^541 ≤ (21125603689021/50000000000000 : ℝ)^413 := by
    have hnat : (1295105599 : ℕ)^541*50000000000000^413 ≤ 21125603689021^413*2500000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295105599 2500000000 21125603689021 50000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270142699/500000000 : ℝ)^541 ≤ (44643255164131/100000000000000 : ℝ)^413 := by
    have hnat : (270142699 : ℕ)^541*100000000000000^413 ≤ 44643255164131^413*500000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270142699 500000000 44643255164131 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2119649449/10000000000 : ℝ), (1295105599/2500000000 : ℝ), (270142699/500000000 : ℝ)] ![(13105537438171/100000000000000 : ℝ), (21125603689021/50000000000000 : ℝ), (44643255164131/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2119649449/10000000000 : ℝ)|^541 ≤ (13105537438171/100000000000000 : ℝ)^413
        have hw : |(-2119649449/10000000000 : ℝ)|=(2119649449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1295105599/2500000000 : ℝ)|^541 ≤ (21125603689021/50000000000000 : ℝ)^413
        have hw : |(1295105599/2500000000 : ℝ)|=(1295105599/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(270142699/500000000 : ℝ)|^541 ≤ (44643255164131/100000000000000 : ℝ)^413
        have hw : |(270142699/500000000 : ℝ)|=(270142699/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_box_9 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2637831891/5000000000 : ℝ)*x 0 + (-996229659/5000000000 : ℝ)*x 1 + (337678363/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2637831891/5000000000 : ℝ)^541 ≤ (21635811659537/50000000000000 : ℝ)^413 := by
    have hnat : (2637831891 : ℕ)^541*50000000000000^413 ≤ 21635811659537^413*5000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2637831891 5000000000 21635811659537 50000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (996229659/5000000000 : ℝ)^541 ≤ (6042561681823/50000000000000 : ℝ)^413 := by
    have hnat : (996229659 : ℕ)^541*50000000000000^413 ≤ 6042561681823^413*5000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      996229659 5000000000 6042561681823 50000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337678363/625000000 : ℝ)^541 ≤ (44643253302437/100000000000000 : ℝ)^413 := by
    have hnat : (337678363 : ℕ)^541*100000000000000^413 ≤ 44643253302437^413*625000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337678363 625000000 44643253302437 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2637831891/5000000000 : ℝ), (-996229659/5000000000 : ℝ), (337678363/625000000 : ℝ)] ![(21635811659537/50000000000000 : ℝ), (6042561681823/50000000000000 : ℝ), (44643253302437/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2637831891/5000000000 : ℝ)|^541 ≤ (21635811659537/50000000000000 : ℝ)^413
        have hw : |(2637831891/5000000000 : ℝ)|=(2637831891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-996229659/5000000000 : ℝ)|^541 ≤ (6042561681823/50000000000000 : ℝ)^413
        have hw : |(-996229659/5000000000 : ℝ)|=(996229659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(337678363/625000000 : ℝ)|^541 ≤ (44643253302437/100000000000000 : ℝ)^413
        have hw : |(337678363/625000000 : ℝ)|=(337678363/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_box_10 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5275663767/10000000000 : ℝ)*x 0 + (1080570743/2000000000 : ℝ)*x 1 + (-398491893/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275663767/10000000000 : ℝ)^541 ≤ (5408952894739/12500000000000 : ℝ)^413 := by
    have hnat : (5275663767 : ℕ)^541*12500000000000^413 ≤ 5408952894739^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275663767 10000000000 5408952894739 12500000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1080570743/2000000000 : ℝ)^541 ≤ (2790203268489/6250000000000 : ℝ)^413 := by
    have hnat : (1080570743 : ℕ)^541*6250000000000^413 ≤ 2790203268489^413*2000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080570743 2000000000 2790203268489 6250000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (398491893/2000000000 : ℝ)^541 ≤ (12085124531601/100000000000000 : ℝ)^413 := by
    have hnat : (398491893 : ℕ)^541*100000000000000^413 ≤ 12085124531601^413*2000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      398491893 2000000000 12085124531601 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275663767/10000000000 : ℝ), (1080570743/2000000000 : ℝ), (-398491893/2000000000 : ℝ)] ![(5408952894739/12500000000000 : ℝ), (2790203268489/6250000000000 : ℝ), (12085124531601/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275663767/10000000000 : ℝ)|^541 ≤ (5408952894739/12500000000000 : ℝ)^413
        have hw : |(5275663767/10000000000 : ℝ)|=(5275663767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1080570743/2000000000 : ℝ)|^541 ≤ (2790203268489/6250000000000 : ℝ)^413
        have hw : |(1080570743/2000000000 : ℝ)|=(1080570743/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-398491893/2000000000 : ℝ)|^541 ≤ (12085124531601/100000000000000 : ℝ)^413
        have hw : |(-398491893/2000000000 : ℝ)|=(398491893/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_box_11 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (56256481/125000000 : ℝ)*x 0 + (211654471/500000000 : ℝ)*x 1 + (423308949/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (56256481/125000000 : ℝ)^541 ≤ (1756989356811/5000000000000 : ℝ)^413 := by
    have hnat : (56256481 : ℕ)^541*5000000000000^413 ≤ 1756989356811^413*125000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56256481 125000000 1756989356811 5000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (211654471/500000000 : ℝ)^541 ≤ (8107526517981/25000000000000 : ℝ)^413 := by
    have hnat : (211654471 : ℕ)^541*25000000000000^413 ≤ 8107526517981^413*500000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211654471 500000000 8107526517981 25000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (423308949/1000000000 : ℝ)^541 ≤ (32430106774407/100000000000000 : ℝ)^413 := by
    have hnat : (423308949 : ℕ)^541*100000000000000^413 ≤ 32430106774407^413*1000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423308949 1000000000 32430106774407 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(56256481/125000000 : ℝ), (211654471/500000000 : ℝ), (423308949/1000000000 : ℝ)] ![(1756989356811/5000000000000 : ℝ), (8107526517981/25000000000000 : ℝ), (32430106774407/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(56256481/125000000 : ℝ)|^541 ≤ (1756989356811/5000000000000 : ℝ)^413
        have hw : |(56256481/125000000 : ℝ)|=(56256481/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(211654471/500000000 : ℝ)|^541 ≤ (8107526517981/25000000000000 : ℝ)^413
        have hw : |(211654471/500000000 : ℝ)|=(211654471/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(423308949/1000000000 : ℝ)|^541 ≤ (32430106774407/100000000000000 : ℝ)^413
        have hw : |(423308949/1000000000 : ℝ)|=(423308949/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_box_12 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-240853889/1250000000 : ℝ)*x 0 + (341984497/625000000 : ℝ)*x 1 + (525438713/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (240853889/1250000000 : ℝ)^541 ≤ (462654852317/4000000000000 : ℝ)^413 := by
    have hnat : (240853889 : ℕ)^541*4000000000000^413 ≤ 462654852317^413*1250000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      240853889 1250000000 462654852317 4000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (341984497/625000000 : ℝ)^541 ≤ (1418451954219/3125000000000 : ℝ)^413 := by
    have hnat : (341984497 : ℕ)^541*3125000000000^413 ≤ 1418451954219^413*625000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341984497 625000000 1418451954219 3125000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (525438713/1000000000 : ℝ)^541 ≤ (43043166131983/100000000000000 : ℝ)^413 := by
    have hnat : (525438713 : ℕ)^541*100000000000000^413 ≤ 43043166131983^413*1000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525438713 1000000000 43043166131983 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-240853889/1250000000 : ℝ), (341984497/625000000 : ℝ), (525438713/1000000000 : ℝ)] ![(462654852317/4000000000000 : ℝ), (1418451954219/3125000000000 : ℝ), (43043166131983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-240853889/1250000000 : ℝ)|^541 ≤ (462654852317/4000000000000 : ℝ)^413
        have hw : |(-240853889/1250000000 : ℝ)|=(240853889/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(341984497/625000000 : ℝ)|^541 ≤ (1418451954219/3125000000000 : ℝ)^413
        have hw : |(341984497/625000000 : ℝ)|=(341984497/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(525438713/1000000000 : ℝ)|^541 ≤ (43043166131983/100000000000000 : ℝ)^413
        have hw : |(525438713/1000000000 : ℝ)|=(525438713/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_box_13 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (672479121/1250000000 : ℝ)*x 0 + (-2052277517/10000000000 : ℝ)*x 1 + (2627193449/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (672479121/1250000000 : ℝ)^541 ≤ (22197122488769/50000000000000 : ℝ)^413 := by
    have hnat : (672479121 : ℕ)^541*50000000000000^413 ≤ 22197122488769^413*1250000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672479121 1250000000 22197122488769 50000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2052277517/10000000000 : ℝ)^541 ≤ (12562591360381/100000000000000 : ℝ)^413 := by
    have hnat : (2052277517 : ℕ)^541*100000000000000^413 ≤ 12562591360381^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2052277517 10000000000 12562591360381 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2627193449/5000000000 : ℝ)^541 ≤ (43043163642453/100000000000000 : ℝ)^413 := by
    have hnat : (2627193449 : ℕ)^541*100000000000000^413 ≤ 43043163642453^413*5000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627193449 5000000000 43043163642453 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(672479121/1250000000 : ℝ), (-2052277517/10000000000 : ℝ), (2627193449/5000000000 : ℝ)] ![(22197122488769/50000000000000 : ℝ), (12562591360381/100000000000000 : ℝ), (43043163642453/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(672479121/1250000000 : ℝ)|^541 ≤ (22197122488769/50000000000000 : ℝ)^413
        have hw : |(672479121/1250000000 : ℝ)|=(672479121/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2052277517/10000000000 : ℝ)|^541 ≤ (12562591360381/100000000000000 : ℝ)^413
        have hw : |(-2052277517/10000000000 : ℝ)|=(2052277517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2627193449/5000000000 : ℝ)|^541 ≤ (43043163642453/100000000000000 : ℝ)^413
        have hw : |(2627193449/5000000000 : ℝ)|=(2627193449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_box_14 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (672479107/1250000000 : ℝ)*x 0 + (1313596779/2500000000 : ℝ)*x 1 + (-2052277377/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (672479107/1250000000 : ℝ)^541 ≤ (11098560941719/25000000000000 : ℝ)^413 := by
    have hnat : (672479107 : ℕ)^541*25000000000000^413 ≤ 11098560941719^413*1250000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672479107 1250000000 11098560941719 25000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1313596779/2500000000 : ℝ)^541 ≤ (43043165981753/100000000000000 : ℝ)^413 := by
    have hnat : (1313596779 : ℕ)^541*100000000000000^413 ≤ 43043165981753^413*2500000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313596779 2500000000 43043165981753 100000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2052277377/10000000000 : ℝ)^541 ≤ (6281295118899/50000000000000 : ℝ)^413 := by
    have hnat : (2052277377 : ℕ)^541*50000000000000^413 ≤ 6281295118899^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2052277377 10000000000 6281295118899 50000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(672479107/1250000000 : ℝ), (1313596779/2500000000 : ℝ), (-2052277377/10000000000 : ℝ)] ![(11098560941719/25000000000000 : ℝ), (43043165981753/100000000000000 : ℝ), (6281295118899/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(672479107/1250000000 : ℝ)|^541 ≤ (11098560941719/25000000000000 : ℝ)^413
        have hw : |(672479107/1250000000 : ℝ)|=(672479107/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1313596779/2500000000 : ℝ)|^541 ≤ (43043165981753/100000000000000 : ℝ)^413
        have hw : |(1313596779/2500000000 : ℝ)|=(1313596779/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2052277377/10000000000 : ℝ)|^541 ≤ (6281295118899/50000000000000 : ℝ)^413
        have hw : |(-2052277377/10000000000 : ℝ)|=(2052277377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1368_box_15 (p : ℝ) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ)) (x : Fin 3 → ℝ) :
    (518031809/1250000000 : ℝ)*x 0 + (4411216429/10000000000 : ℝ)*x 1 + (4411216271/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (518031809/1250000000 : ℝ)^541 ≤ (15770759034857/50000000000000 : ℝ)^413 := by
    have hnat : (518031809 : ℕ)^541*50000000000000^413 ≤ 15770759034857^413*1250000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518031809 1250000000 15770759034857 50000000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4411216429/10000000000 : ℝ)^541 ≤ (213932760973/625000000000 : ℝ)^413 := by
    have hnat : (4411216429 : ℕ)^541*625000000000^413 ≤ 213932760973^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4411216429 10000000000 213932760973 625000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4411216271/10000000000 : ℝ)^541 ≤ (4278655018711/12500000000000 : ℝ)^413 := by
    have hnat : (4411216271 : ℕ)^541*12500000000000^413 ≤ 4278655018711^413*10000000000^541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4411216271 10000000000 4278655018711 12500000000000 541 413 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (541/128 : ℝ)) 541 413 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(518031809/1250000000 : ℝ), (4411216429/10000000000 : ℝ), (4411216271/10000000000 : ℝ)] ![(15770759034857/50000000000000 : ℝ), (213932760973/625000000000 : ℝ), (4278655018711/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(518031809/1250000000 : ℝ)|^541 ≤ (15770759034857/50000000000000 : ℝ)^413
        have hw : |(518031809/1250000000 : ℝ)|=(518031809/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4411216429/10000000000 : ℝ)|^541 ≤ (213932760973/625000000000 : ℝ)^413
        have hw : |(4411216429/10000000000 : ℝ)|=(4411216429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4411216271/10000000000 : ℝ)|^541 ≤ (4278655018711/12500000000000 : ℝ)^413
        have hw : |(4411216271/10000000000 : ℝ)|=(4411216271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1368_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7787701/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7361/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1121/10000 : ℝ)*pair X i i ≤ pair X i h) :
    -(31433/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(3687/6250 : ℝ) ∧ (16021/20000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84453/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7361/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1121/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7361/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1121/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7361/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1121/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7361/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1121/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7361/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1121/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7361/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1121/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1121/10000 : ℝ) ^ (4327/1024 : ℝ) ≤ (9638885947665981/100000000000000000000 : ℝ) := by
    have hpowers : (1121/10000 : ℝ)^4327 ≤ (9638885947665981/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1121 : ℕ)^4327*100000000000000000000^1024 ≤ 9638885947665981^1024*10000^4327 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1121 10000 9638885947665981 100000000000000000000 4327 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1121/10000 : ℝ)) (X := (9638885947665981/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4327 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7361/50000 : ℝ) ^ (4327/1024 : ℝ) ≤ (6098208413550103/20000000000000000000 : ℝ) := by
    have hpowers : (7361/50000 : ℝ)^4327 ≤ (6098208413550103/20000000000000000000 : ℝ)^1024 := by
      have hnat : (7361 : ℕ)^4327*20000000000000000000^1024 ≤ 6098208413550103^1024*50000^4327 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7361 50000 6098208413550103 20000000000000000000 4327 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7361/50000 : ℝ)) (X := (6098208413550103/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4327 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009638885947665981/50000000000000000000 : ℝ) ≤ (10000456181791579/10000000000000000 : ℝ) ^ (4327/1024 : ℝ) := by
    have hpowers : (50009638885947665981/50000000000000000000 : ℝ)^1024 ≤ (10000456181791579/10000000000000000 : ℝ)^4327 := by
      have hnat : (50009638885947665981 : ℕ)^1024*10000000000000000^4327 ≤ 10000456181791579^4327*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009638885947665981 50000000000000000000 10000456181791579 10000000000000000 1024 4327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000456181791579/10000000000000000 : ℝ)) (X := (50009638885947665981/50000000000000000000 : ℝ)) (by norm_num) 4327 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6252508120500963531/6250000000000000000 : ℝ) ≤ (10000949543650287/10000000000000000 : ℝ) ^ (4327/1024 : ℝ) := by
    have hpowers : (6252508120500963531/6250000000000000000 : ℝ)^1024 ≤ (10000949543650287/10000000000000000 : ℝ)^4327 := by
      have hnat : (6252508120500963531 : ℕ)^1024*10000000000000000^4327 ≤ 10000949543650287^4327*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252508120500963531 6250000000000000000 10000949543650287 10000000000000000 1024 4327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000949543650287/10000000000000000 : ℝ)) (X := (6252508120500963531/6250000000000000000 : ℝ)) (by norm_num) 4327 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006098208413550103/10000000000000000000 : ℝ) ≤ (2000288581101799/2000000000000000 : ℝ) ^ (4327/1024 : ℝ) := by
    have hpowers : (10006098208413550103/10000000000000000000 : ℝ)^1024 ≤ (2000288581101799/2000000000000000 : ℝ)^4327 := by
      have hnat : (10006098208413550103 : ℕ)^1024*2000000000000000^4327 ≤ 2000288581101799^4327*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006098208413550103 10000000000000000000 2000288581101799 2000000000000000 1024 4327 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000288581101799/2000000000000000 : ℝ)) (X := (10006098208413550103/10000000000000000000 : ℝ)) (by norm_num) 4327 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9638885947665981/100000000000000000000 : ℝ) ≤ ((4388817617197474011/4390000000000000000 : ℝ)+2*(123340464677/87800000000000 : ℝ)*(1121/10000 : ℝ))^(4327/1024 : ℝ) := by
    rw [show (4388817617197474011/4390000000000000000 : ℝ)+2*(123340464677/87800000000000 : ℝ)*(1121/10000 : ℝ)=(10000456181791579/10000000000000000 : ℝ) by norm_num, show 1+2*(9638885947665981/100000000000000000000 : ℝ)=(50009638885947665981/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6098208413550103/20000000000000000000 : ℝ)+(9638885947665981/100000000000000000000 : ℝ) ≤ ((4388817617197474011/4390000000000000000 : ℝ)+(123340464677/87800000000000 : ℝ)*((7361/50000 : ℝ)+(1121/10000 : ℝ)))^(4327/1024 : ℝ) := by
    rw [show (4388817617197474011/4390000000000000000 : ℝ)+(123340464677/87800000000000 : ℝ)*((7361/50000 : ℝ)+(1121/10000 : ℝ))=(10000949543650287/10000000000000000 : ℝ) by norm_num, show 1+(6098208413550103/20000000000000000000 : ℝ)+(9638885947665981/100000000000000000000 : ℝ)=(6252508120500963531/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6098208413550103/20000000000000000000 : ℝ) ≤ ((4388817617197474011/4390000000000000000 : ℝ)+2*(123340464677/87800000000000 : ℝ)*(7361/50000 : ℝ))^(4327/1024 : ℝ) := by
    rw [show (4388817617197474011/4390000000000000000 : ℝ)+2*(123340464677/87800000000000 : ℝ)*(7361/50000 : ℝ)=(2000288581101799/2000000000000000 : ℝ) by norm_num, show 1+2*(6098208413550103/20000000000000000000 : ℝ)=(10006098208413550103/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4388817617197474011/4390000000000000000 : ℝ)*(X 1 0+X 2 0)+(123340464677/87800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4327/1024 : ℝ)) (lo := (1121/10000 : ℝ)) (hi := (7361/50000 : ℝ)) (c := (4388817617197474011/4390000000000000000 : ℝ)) (alpha := (123340464677/87800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4388817617197474011/4390000000000000000 : ℝ)*(X 0 1+X 2 1)+(123340464677/87800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4327/1024 : ℝ)) (lo := (1121/10000 : ℝ)) (hi := (7361/50000 : ℝ)) (c := (4388817617197474011/4390000000000000000 : ℝ)) (alpha := (123340464677/87800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4388817617197474011/4390000000000000000 : ℝ)*(X 0 2+X 1 2)+(123340464677/87800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4327/1024 : ℝ)) (lo := (1121/10000 : ℝ)) (hi := (7361/50000 : ℝ)) (c := (4388817617197474011/4390000000000000000 : ℝ)) (alpha := (123340464677/87800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-928256243/5000000000 : ℝ)*X 0 0+(1347211669/2500000000 : ℝ)*X 0 1+(269442327/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5285496521/10000000000 : ℝ)*X 1 0+(-399646171/2000000000 : ℝ)*X 1 1+(5388846421/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5285495973/10000000000 : ℝ)*X 2 0+(2694423523/5000000000 : ℝ)*X 2 1+(-999115373/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4467454509/10000000000 : ℝ)*X 0 0+(2124954301/5000000000 : ℝ)*X 0 1+(4249908917/10000000000 : ℝ)*X 0 2+(4467454509/10000000000 : ℝ)*X 1 0+(2124954301/5000000000 : ℝ)*X 1 1+(4249908917/10000000000 : ℝ)*X 1 2+(4467454509/10000000000 : ℝ)*X 2 0+(2124954301/5000000000 : ℝ)*X 2 1+(4249908917/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1094840411/5000000000 : ℝ)*X 0 0+(658184449/1250000000 : ℝ)*X 0 1+(1316368967/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2686027671/5000000000 : ℝ)*X 1 0+(-2047914247/10000000000 : ℝ)*X 1 1+(329092223/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5372055019/10000000000 : ℝ)*X 2 0+(2632737849/5000000000 : ℝ)*X 2 1+(-511978627/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4171320719/10000000000 : ℝ)*X 0 0+(4397922931/10000000000 : ℝ)*X 0 1+(879584583/2000000000 : ℝ)*X 0 2+(4171320719/10000000000 : ℝ)*X 1 0+(4397922931/10000000000 : ℝ)*X 1 1+(879584583/2000000000 : ℝ)*X 1 2+(4171320719/10000000000 : ℝ)*X 2 0+(4397922931/10000000000 : ℝ)*X 2 1+(879584583/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2119649449/10000000000 : ℝ)*X 0 0+(1295105599/2500000000 : ℝ)*X 0 1+(270142699/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2637831891/5000000000 : ℝ)*X 1 0+(-996229659/5000000000 : ℝ)*X 1 1+(337678363/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5275663767/10000000000 : ℝ)*X 2 0+(1080570743/2000000000 : ℝ)*X 2 1+(-398491893/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((56256481/125000000 : ℝ)*X 0 0+(211654471/500000000 : ℝ)*X 0 1+(423308949/1000000000 : ℝ)*X 0 2+(56256481/125000000 : ℝ)*X 1 0+(211654471/500000000 : ℝ)*X 1 1+(423308949/1000000000 : ℝ)*X 1 2+(56256481/125000000 : ℝ)*X 2 0+(211654471/500000000 : ℝ)*X 2 1+(423308949/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-240853889/1250000000 : ℝ)*X 0 0+(341984497/625000000 : ℝ)*X 0 1+(525438713/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((672479121/1250000000 : ℝ)*X 1 0+(-2052277517/10000000000 : ℝ)*X 1 1+(2627193449/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((672479107/1250000000 : ℝ)*X 2 0+(1313596779/2500000000 : ℝ)*X 2 1+(-2052277377/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((518031809/1250000000 : ℝ)*X 0 0+(4411216429/10000000000 : ℝ)*X 0 1+(4411216271/10000000000 : ℝ)*X 0 2+(518031809/1250000000 : ℝ)*X 1 0+(4411216429/10000000000 : ℝ)*X 1 1+(4411216271/10000000000 : ℝ)*X 1 2+(518031809/1250000000 : ℝ)*X 2 0+(4411216429/10000000000 : ℝ)*X 2 1+(4411216271/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1368_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31433/50000 : ℝ) ≤ (-137986155825660478301127482751813/219500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (52782619/50000000000000 : ℝ)*(lower0) + (24546797/100000000000000 : ℝ)*(lower3) + (88643403/50000000000000 : ℝ)*(lower4) + (2949783650678887/100000000000000 : ℝ)*(major0) + (2949783650678887/100000000000000 : ℝ)*(major1) + (2949783650678887/100000000000000 : ℝ)*(major2) + (923197269/12500000000000 : ℝ)*(sp1) + (12841493951/100000000000000 : ℝ)*(sp2) + (1006661020451623/25000000000000 : ℝ)*(sp4) + (4026641328096017/100000000000000 : ℝ)*(sp5) + (4026635872180219/100000000000000 : ℝ)*(sp6) + (946935624666347/50000000000000 : ℝ)*(sp7) + (4631867677/100000000000000 : ℝ)*(sp12) + (1955788359/100000000000000 : ℝ)*(sp15) + (946936602560527/50000000000000 : ℝ)*(f.failure) + (402664871367417/10000000000000 : ℝ)*(f.sum) + (20175299507959/4390000000000000000000000000 : ℝ)*base65 + (4252367522386855757/439000000000000000000000000000000 : ℝ)*base67 + (2265870804178855757/439000000000000000000000000000000 : ℝ)*base69 + (1864205087253855757/439000000000000000000000000000000 : ℝ)*base71 + (14905074743759/4390000000000000000000000000 : ℝ)*base73 + (2472607062680855757/439000000000000000000000000000000 : ℝ)*base75 + (774411083411855757/439000000000000000000000000000000 : ℝ)*base77 + (2684945310626855757/439000000000000000000000000000000 : ℝ)*base79 + (17571053106109/4390000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1178427/250000000000000000000 : ℝ)*base89 + (1178427/250000000000000000000 : ℝ)*base91 + (1178427/250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (3687/6250 : ℝ) ≤ (129493011658903327559088704227263/219500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5598511/25000000000000 : ℝ)*(lower1) + (16800691/25000000000000 : ℝ)*(upper2) + (50041/400000000000 : ℝ)*(lower4) + (3019343137224689/100000000000000 : ℝ)*(major0) + (3019343137224689/100000000000000 : ℝ)*(major1) + (3019343137224689/100000000000000 : ℝ)*(major2) + (2040243806737461/50000000000000 : ℝ)*(sp0) + (510055648013017/12500000000000 : ℝ)*(sp1) + (1020119168267137/25000000000000 : ℝ)*(sp2) + (77541291795649/4000000000000 : ℝ)*(sp3) + (5858148309/50000000000000 : ℝ)*(sp6) + (148815851/20000000000000 : ℝ)*(sp7) + (4320526103/10000000000000 : ℝ)*(sp9) + (193972561/25000000000000 : ℝ)*(sp12) + (24231662987131/1250000000000 : ℝ)*(f.failure) + (2040244194682583/50000000000000 : ℝ)*(f.sum) + (34428142965047/4390000000000000000000000000 : ℝ)*base66 + (748429823082707579/439000000000000000000000000000000 : ℝ)*base67 + (667178897517707579/439000000000000000000000000000000 : ℝ)*base69 + (5054859688613707579/439000000000000000000000000000000 : ℝ)*base71 + (715575143197/4390000000000000000000000000 : ℝ)*base74 + (1640981913173707579/439000000000000000000000000000000 : ℝ)*base75 + (1824207371956292421/439000000000000000000000000000000 : ℝ)*base78 + (90096619185292421/439000000000000000000000000000000 : ℝ)*base80 + (1184650431767/4390000000000000000000000000 : ℝ)*base82 + (13331/6250000000000000000 : ℝ)*base89 + (13331/6250000000000000000 : ℝ)*base91 + (13331/6250000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (16021/20000 : ℝ) ≤ (43959140280763035249232348700523/54875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12017041/100000000000000 : ℝ)*(upper1) + (7745809/12500000000000 : ℝ)*(upper2) + (6688383/100000000000000 : ℝ)*(lower5) + (832585929647531/25000000000000 : ℝ)*(major0) + (832585929647531/25000000000000 : ℝ)*(major1) + (832585929647531/25000000000000 : ℝ)*(major2) + (28081090751/50000000000000 : ℝ)*(sp1) + (34521898741/100000000000000 : ℝ)*(sp3) + (5492728479/100000000000000 : ℝ)*(sp4) + (561970938384573/12500000000000 : ℝ)*(sp8) + (224786072642483/5000000000000 : ℝ)*(sp9) + (2247888807515581/50000000000000 : ℝ)*(sp10) + (534543177335817/25000000000000 : ℝ)*(sp11) + (2307613049/50000000000000 : ℝ)*(sp12) + (2138207231242009/100000000000000 : ℝ)*(f.failure) + (2247888807515581/50000000000000 : ℝ)*(f.sum) + (48135045055569/2195000000000000000000000000 : ℝ)*base65 + (317138046629666841/109750000000000000000000000000000 : ℝ)*base67 + (118953235840583159/109750000000000000000000000000000 : ℝ)*base70 + (1511619256305083159/109750000000000000000000000000000 : ℝ)*base72 + (2272988151667/1097500000000000000000000000 : ℝ)*base73 + (507055772293083159/109750000000000000000000000000000 : ℝ)*base76 + (310808183222916841/109750000000000000000000000000000 : ℝ)*base77 + (659753694664833159/109750000000000000000000000000000 : ℝ)*base80 + (2438645253991/2195000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (4731309/500000000000000000000 : ℝ)*base89 + (4731309/500000000000000000000 : ℝ)*base91 + (4731309/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-84453/100000 : ℝ) ≤ (-11585522183686538686178987319939/13718750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (27195703/100000000000000 : ℝ)*(lower0) + (9888069/100000000000000 : ℝ)*(lower1) + (841599/400000000000 : ℝ)*(lower2) + (11071827/6250000000000 : ℝ)*(lower4) + (210444605614767/6250000000000 : ℝ)*(major0) + (210444605614767/6250000000000 : ℝ)*(major1) + (210444605614767/6250000000000 : ℝ)*(major2) + (3829445599/100000000000000 : ℝ)*(sp4) + (54500445597/50000000000000 : ℝ)*(sp5) + (21098893791/25000000000000 : ℝ)*(sp7) + (2300279345966227/50000000000000 : ℝ)*(sp12) + (230022676024343/5000000000000 : ℝ)*(sp13) + (4600562521378053/100000000000000 : ℝ)*(sp14) + (2161730554585527/100000000000000 : ℝ)*(sp15) + (2161814950160691/100000000000000 : ℝ)*(f.failure) + (4600562521378053/100000000000000 : ℝ)*(f.sum) + (23504047409721/1097500000000000000000000000 : ℝ)*base65 + (118235164197792063/27437500000000000000000000000000 : ℝ)*base68 + (52262689947417063/27437500000000000000000000000000 : ℝ)*base70 + (7108622216229563/27437500000000000000000000000000 : ℝ)*base72 + (1320104315583/2195000000000000000000000000 : ℝ)*base74 + (148795676339917063/27437500000000000000000000000000 : ℝ)*base76 + (607506453592520437/27437500000000000000000000000000 : ℝ)*base77 + (375766176380457937/27437500000000000000000000000000 : ℝ)*base79 + (56736707511/68593750000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (3461391/500000000000000000000 : ℝ)*base89 + (3461391/500000000000000000000 : ℝ)*base91 + (3461391/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1368_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7787701/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7361/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1121/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31433/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(3687/6250 : ℝ) else (16021/20000 : ℝ) ≤ X j i ∧ X j i ≤ (84453/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1368_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1368_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7787701/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1473/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11203/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31433/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(3687/6250 : ℝ) else (16021/20000 : ℝ) ≤ X j i ∧ X j i ≤ (84453/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1368_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1368_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1368_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4327/1024 : ℝ) ≤ p) (hpb : p ≤ (541/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7787701/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1473/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11203/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31433/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(3687/6250 : ℝ) else (16021/20000 : ℝ) ≤ X j i ∧ X j i ≤ (84453/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1368_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
