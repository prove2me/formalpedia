-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1515_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:56:22.501871+00:00
-- url     : https://prove2.me/submissions/d1d2a93f-3b06-47ed-9509-7997a4e91e83

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
theorem support_rectangle_w1515_s0_0 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1682656903/10000000000 : ℝ)*x 0 + (5910522303/10000000000 : ℝ)*x 1 + (4856598283/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1682656903/10000000000 : ℝ)^4527 ≤ (1249245915871/12500000000000 : ℝ)^3503 := by
    have hnat : (1682656903 : ℕ)^4527*12500000000000^3503 ≤ 1249245915871^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1682656903 10000000000 1249245915871 12500000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5910522303/10000000000 : ℝ)^4527 ≤ (10136717176531/20000000000000 : ℝ)^3503 := by
    have hnat : (5910522303 : ℕ)^4527*20000000000000^3503 ≤ 10136717176531^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5910522303 10000000000 10136717176531 20000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4856598283/10000000000 : ℝ)^4527 ≤ (39322446769697/100000000000000 : ℝ)^3503 := by
    have hnat : (4856598283 : ℕ)^4527*100000000000000^3503 ≤ 39322446769697^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4856598283 10000000000 39322446769697 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1682656903/10000000000 : ℝ), (5910522303/10000000000 : ℝ), (4856598283/10000000000 : ℝ)] ![(1249245915871/12500000000000 : ℝ), (10136717176531/20000000000000 : ℝ), (39322446769697/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1682656903/10000000000 : ℝ)|^4527 ≤ (1249245915871/12500000000000 : ℝ)^3503
        have hw : |(-1682656903/10000000000 : ℝ)|=(1682656903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5910522303/10000000000 : ℝ)|^4527 ≤ (10136717176531/20000000000000 : ℝ)^3503
        have hw : |(5910522303/10000000000 : ℝ)|=(5910522303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4856598283/10000000000 : ℝ)|^4527 ≤ (39322446769697/100000000000000 : ℝ)^3503
        have hw : |(4856598283/10000000000 : ℝ)|=(4856598283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_s0_1 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5477327571/10000000000 : ℝ)*x 0 + (-1136586713/5000000000 : ℝ)*x 1 + (2428299093/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5477327571/10000000000 : ℝ)^4527 ≤ (9187067136571/20000000000000 : ℝ)^3503 := by
    have hnat : (5477327571 : ℕ)^4527*20000000000000^3503 ≤ 9187067136571^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5477327571 10000000000 9187067136571 20000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1136586713/5000000000 : ℝ)^4527 ≤ (14742218543223/100000000000000 : ℝ)^3503 := by
    have hnat : (1136586713 : ℕ)^4527*100000000000000^3503 ≤ 14742218543223^3503*5000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1136586713 5000000000 14742218543223 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2428299093/5000000000 : ℝ)^4527 ≤ (19661222877367/50000000000000 : ℝ)^3503 := by
    have hnat : (2428299093 : ℕ)^4527*50000000000000^3503 ≤ 19661222877367^3503*5000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2428299093 5000000000 19661222877367 50000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5477327571/10000000000 : ℝ), (-1136586713/5000000000 : ℝ), (2428299093/5000000000 : ℝ)] ![(9187067136571/20000000000000 : ℝ), (14742218543223/100000000000000 : ℝ), (19661222877367/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5477327571/10000000000 : ℝ)|^4527 ≤ (9187067136571/20000000000000 : ℝ)^3503
        have hw : |(5477327571/10000000000 : ℝ)|=(5477327571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1136586713/5000000000 : ℝ)|^4527 ≤ (14742218543223/100000000000000 : ℝ)^3503
        have hw : |(-1136586713/5000000000 : ℝ)|=(1136586713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2428299093/5000000000 : ℝ)|^4527 ≤ (19661222877367/50000000000000 : ℝ)^3503
        have hw : |(2428299093/5000000000 : ℝ)|=(2428299093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_s0_2 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2738663829/5000000000 : ℝ)*x 0 + (303537389/625000000 : ℝ)*x 1 + (-2273173267/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2738663829/5000000000 : ℝ)^4527 ≤ (287095853911/625000000000 : ℝ)^3503 := by
    have hnat : (2738663829 : ℕ)^4527*625000000000^3503 ≤ 287095853911^3503*5000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2738663829 5000000000 287095853911 625000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (303537389/625000000 : ℝ)^4527 ≤ (9830611538087/25000000000000 : ℝ)^3503 := by
    have hnat : (303537389 : ℕ)^4527*25000000000000^3503 ≤ 9830611538087^3503*625000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      303537389 625000000 9830611538087 25000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2273173267/10000000000 : ℝ)^4527 ≤ (14742217210629/100000000000000 : ℝ)^3503 := by
    have hnat : (2273173267 : ℕ)^4527*100000000000000^3503 ≤ 14742217210629^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2273173267 10000000000 14742217210629 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2738663829/5000000000 : ℝ), (303537389/625000000 : ℝ), (-2273173267/10000000000 : ℝ)] ![(287095853911/625000000000 : ℝ), (9830611538087/25000000000000 : ℝ), (14742217210629/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2738663829/5000000000 : ℝ)|^4527 ≤ (287095853911/625000000000 : ℝ)^3503
        have hw : |(2738663829/5000000000 : ℝ)|=(2738663829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(303537389/625000000 : ℝ)|^4527 ≤ (9830611538087/25000000000000 : ℝ)^3503
        have hw : |(303537389/625000000 : ℝ)|=(303537389/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2273173267/10000000000 : ℝ)|^4527 ≤ (14742217210629/100000000000000 : ℝ)^3503
        have hw : |(-2273173267/10000000000 : ℝ)|=(2273173267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_s0_3 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2072167909/5000000000 : ℝ)*x 0 + (3091297799/10000000000 : ℝ)*x 1 + (5486213619/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2072167909/5000000000 : ℝ)^4527 ≤ (32035317689087/100000000000000 : ℝ)^3503 := by
    have hnat : (2072167909 : ℕ)^4527*100000000000000^3503 ≤ 32035317689087^3503*5000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2072167909 5000000000 32035317689087 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3091297799/10000000000 : ℝ)^4527 ≤ (10966508466601/50000000000000 : ℝ)^3503 := by
    have hnat : (3091297799 : ℕ)^4527*50000000000000^3503 ≤ 10966508466601^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3091297799 10000000000 10966508466601 50000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5486213619/10000000000 : ℝ)^4527 ≤ (46031665363503/100000000000000 : ℝ)^3503 := by
    have hnat : (5486213619 : ℕ)^4527*100000000000000^3503 ≤ 46031665363503^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5486213619 10000000000 46031665363503 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2072167909/5000000000 : ℝ), (3091297799/10000000000 : ℝ), (5486213619/10000000000 : ℝ)] ![(32035317689087/100000000000000 : ℝ), (10966508466601/50000000000000 : ℝ), (46031665363503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2072167909/5000000000 : ℝ)|^4527 ≤ (32035317689087/100000000000000 : ℝ)^3503
        have hw : |(2072167909/5000000000 : ℝ)|=(2072167909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3091297799/10000000000 : ℝ)|^4527 ≤ (10966508466601/50000000000000 : ℝ)^3503
        have hw : |(3091297799/10000000000 : ℝ)|=(3091297799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5486213619/10000000000 : ℝ)|^4527 ≤ (46031665363503/100000000000000 : ℝ)^3503
        have hw : |(5486213619/10000000000 : ℝ)|=(5486213619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_s0_4 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1686151699/10000000000 : ℝ)*x 0 + (4883465669/10000000000 : ℝ)*x 1 + (2941346479/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1686151699/10000000000 : ℝ)^4527 ≤ (10020800145547/100000000000000 : ℝ)^3503 := by
    have hnat : (1686151699 : ℕ)^4527*100000000000000^3503 ≤ 10020800145547^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1686151699 10000000000 10020800145547 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4883465669/10000000000 : ℝ)^4527 ≤ (39603801801391/100000000000000 : ℝ)^3503 := by
    have hnat : (4883465669 : ℕ)^4527*100000000000000^3503 ≤ 39603801801391^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4883465669 10000000000 39603801801391 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2941346479/5000000000 : ℝ)^4527 ≤ (2518769901977/5000000000000 : ℝ)^3503 := by
    have hnat : (2941346479 : ℕ)^4527*5000000000000^3503 ≤ 2518769901977^3503*5000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2941346479 5000000000 2518769901977 5000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1686151699/10000000000 : ℝ), (4883465669/10000000000 : ℝ), (2941346479/5000000000 : ℝ)] ![(10020800145547/100000000000000 : ℝ), (39603801801391/100000000000000 : ℝ), (2518769901977/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1686151699/10000000000 : ℝ)|^4527 ≤ (10020800145547/100000000000000 : ℝ)^3503
        have hw : |(-1686151699/10000000000 : ℝ)|=(1686151699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4883465669/10000000000 : ℝ)|^4527 ≤ (39603801801391/100000000000000 : ℝ)^3503
        have hw : |(4883465669/10000000000 : ℝ)|=(4883465669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2941346479/5000000000 : ℝ)|^4527 ≤ (2518769901977/5000000000000 : ℝ)^3503
        have hw : |(2941346479/5000000000 : ℝ)|=(2941346479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_s0_5 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (162167819/312500000 : ℝ)*x 0 + (-623539353/5000000000 : ℝ)*x 1 + (5882693003/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (162167819/312500000 : ℝ)^4527 ≤ (42838743365251/100000000000000 : ℝ)^3503 := by
    have hnat : (162167819 : ℕ)^4527*100000000000000^3503 ≤ 42838743365251^3503*312500000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      162167819 312500000 42838743365251 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (623539353/5000000000 : ℝ)^4527 ≤ (6785858091727/100000000000000 : ℝ)^3503 := by
    have hnat : (623539353 : ℕ)^4527*100000000000000^3503 ≤ 6785858091727^3503*5000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      623539353 5000000000 6785858091727 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5882693003/10000000000 : ℝ)^4527 ≤ (10075079707507/20000000000000 : ℝ)^3503 := by
    have hnat : (5882693003 : ℕ)^4527*20000000000000^3503 ≤ 10075079707507^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5882693003 10000000000 10075079707507 20000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(162167819/312500000 : ℝ), (-623539353/5000000000 : ℝ), (5882693003/10000000000 : ℝ)] ![(42838743365251/100000000000000 : ℝ), (6785858091727/100000000000000 : ℝ), (10075079707507/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(162167819/312500000 : ℝ)|^4527 ≤ (42838743365251/100000000000000 : ℝ)^3503
        have hw : |(162167819/312500000 : ℝ)|=(162167819/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-623539353/5000000000 : ℝ)|^4527 ≤ (6785858091727/100000000000000 : ℝ)^3503
        have hw : |(-623539353/5000000000 : ℝ)|=(623539353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5882693003/10000000000 : ℝ)|^4527 ≤ (10075079707507/20000000000000 : ℝ)^3503
        have hw : |(5882693003/10000000000 : ℝ)|=(5882693003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_s0_6 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (81083909/156250000 : ℝ)*x 0 + (2941346551/5000000000 : ℝ)*x 1 + (-623539299/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (81083909/156250000 : ℝ)^4527 ≤ (10709685755967/25000000000000 : ℝ)^3503 := by
    have hnat : (81083909 : ℕ)^4527*25000000000000^3503 ≤ 10709685755967^3503*156250000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81083909 156250000 10709685755967 25000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2941346551/5000000000 : ℝ)^4527 ≤ (80600639413/160000000000 : ℝ)^3503 := by
    have hnat : (2941346551 : ℕ)^4527*160000000000^3503 ≤ 80600639413^3503*5000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2941346551 5000000000 80600639413 160000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (623539299/5000000000 : ℝ)^4527 ≤ (3392928666133/50000000000000 : ℝ)^3503 := by
    have hnat : (623539299 : ℕ)^4527*50000000000000^3503 ≤ 3392928666133^3503*5000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      623539299 5000000000 3392928666133 50000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(81083909/156250000 : ℝ), (2941346551/5000000000 : ℝ), (-623539299/5000000000 : ℝ)] ![(10709685755967/25000000000000 : ℝ), (80600639413/160000000000 : ℝ), (3392928666133/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(81083909/156250000 : ℝ)|^4527 ≤ (10709685755967/25000000000000 : ℝ)^3503
        have hw : |(81083909/156250000 : ℝ)|=(81083909/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2941346551/5000000000 : ℝ)|^4527 ≤ (80600639413/160000000000 : ℝ)^3503
        have hw : |(2941346551/5000000000 : ℝ)|=(2941346551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-623539299/5000000000 : ℝ)|^4527 ≤ (3392928666133/50000000000000 : ℝ)^3503
        have hw : |(-623539299/5000000000 : ℝ)|=(623539299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_s0_7 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (207613863/500000000 : ℝ)*x 0 + (1356290151/2500000000 : ℝ)*x 1 + (3154536857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (207613863/500000000 : ℝ)^4527 ≤ (32114671060783/100000000000000 : ℝ)^3503 := by
    have hnat : (207613863 : ℕ)^4527*100000000000000^3503 ≤ 32114671060783^3503*500000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207613863 500000000 32114671060783 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1356290151/2500000000 : ℝ)^4527 ≤ (11342684927753/25000000000000 : ℝ)^3503 := by
    have hnat : (1356290151 : ℕ)^4527*25000000000000^3503 ≤ 11342684927753^3503*2500000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356290151 2500000000 11342684927753 25000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3154536857/10000000000 : ℝ)^4527 ≤ (22514589211993/100000000000000 : ℝ)^3503 := by
    have hnat : (3154536857 : ℕ)^4527*100000000000000^3503 ≤ 22514589211993^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3154536857 10000000000 22514589211993 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(207613863/500000000 : ℝ), (1356290151/2500000000 : ℝ), (3154536857/10000000000 : ℝ)] ![(32114671060783/100000000000000 : ℝ), (11342684927753/25000000000000 : ℝ), (22514589211993/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(207613863/500000000 : ℝ)|^4527 ≤ (32114671060783/100000000000000 : ℝ)^3503
        have hw : |(207613863/500000000 : ℝ)|=(207613863/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1356290151/2500000000 : ℝ)|^4527 ≤ (11342684927753/25000000000000 : ℝ)^3503
        have hw : |(1356290151/2500000000 : ℝ)|=(1356290151/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3154536857/10000000000 : ℝ)|^4527 ≤ (22514589211993/100000000000000 : ℝ)^3503
        have hw : |(3154536857/10000000000 : ℝ)|=(3154536857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1515_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163618979/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1433/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5089/20000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4525/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4525 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4525*1^1024 ≤ 0^1024*1^4525 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4525 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4525 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4525/1024 : ℝ) ≤ (1743913196302229059/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4525 ≤ (1743913196302229059/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4525*100000000000000000000^1024 ≤ 1743913196302229059^1024*5^4525 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1743913196302229059 100000000000000000000 4525 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1743913196302229059/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4525 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4525/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4525 := by
      have hnat : (1 : ℕ)^1024*1^4525 ≤ 1^4525*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4525 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4525 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101743913196302229059/100000000000000000000 : ℝ) ≤ (2007840187622191/2000000000000000 : ℝ) ^ (4525/1024 : ℝ) := by
    have hpowers : (101743913196302229059/100000000000000000000 : ℝ)^1024 ≤ (2007840187622191/2000000000000000 : ℝ)^4525 := by
      have hnat : (101743913196302229059 : ℕ)^1024*2000000000000000^4525 ≤ 2007840187622191^4525*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101743913196302229059 100000000000000000000 2007840187622191 2000000000000000 1024 4525 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2007840187622191/2000000000000000 : ℝ)) (X := (101743913196302229059/100000000000000000000 : ℝ)) (by norm_num) 4525 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51743913196302229059/50000000000000000000 : ℝ) ≤ (1007840187622191/1000000000000000 : ℝ) ^ (4525/1024 : ℝ) := by
    have hpowers : (51743913196302229059/50000000000000000000 : ℝ)^1024 ≤ (1007840187622191/1000000000000000 : ℝ)^4525 := by
      have hnat : (51743913196302229059 : ℕ)^1024*1000000000000000^4525 ≤ 1007840187622191^4525*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51743913196302229059 50000000000000000000 1007840187622191 1000000000000000 1024 4525 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1007840187622191/1000000000000000 : ℝ)) (X := (51743913196302229059/50000000000000000000 : ℝ)) (by norm_num) 4525 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(7840187622191/800000000000000 : ℝ)*(0 : ℝ))^(4525/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(7840187622191/800000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1743913196302229059/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(7840187622191/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4525/1024 : ℝ) := by
    rw [show (1 : ℝ)+(7840187622191/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2007840187622191/2000000000000000 : ℝ) by norm_num, show 1+(1743913196302229059/100000000000000000000 : ℝ)+(0 : ℝ)=(101743913196302229059/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1743913196302229059/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(7840187622191/800000000000000 : ℝ)*(2/5 : ℝ))^(4525/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(7840187622191/800000000000000 : ℝ)*(2/5 : ℝ)=(1007840187622191/1000000000000000 : ℝ) by norm_num, show 1+2*(1743913196302229059/100000000000000000000 : ℝ)=(51743913196302229059/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(7840187622191/800000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4525/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (7840187622191/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(7840187622191/800000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4525/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (7840187622191/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(7840187622191/800000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4525/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (7840187622191/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1682656903/10000000000 : ℝ)*X 0 0+(5910522303/10000000000 : ℝ)*X 0 1+(4856598283/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5477327571/10000000000 : ℝ)*X 1 0+(-1136586713/5000000000 : ℝ)*X 1 1+(2428299093/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2738663829/5000000000 : ℝ)*X 2 0+(303537389/625000000 : ℝ)*X 2 1+(-2273173267/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2072167909/5000000000 : ℝ)*X 0 0+(3091297799/10000000000 : ℝ)*X 0 1+(5486213619/10000000000 : ℝ)*X 0 2+(2072167909/5000000000 : ℝ)*X 1 0+(3091297799/10000000000 : ℝ)*X 1 1+(5486213619/10000000000 : ℝ)*X 1 2+(2072167909/5000000000 : ℝ)*X 2 0+(3091297799/10000000000 : ℝ)*X 2 1+(5486213619/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1686151699/10000000000 : ℝ)*X 0 0+(4883465669/10000000000 : ℝ)*X 0 1+(2941346479/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((162167819/312500000 : ℝ)*X 1 0+(-623539353/5000000000 : ℝ)*X 1 1+(5882693003/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((81083909/156250000 : ℝ)*X 2 0+(2941346551/5000000000 : ℝ)*X 2 1+(-623539299/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((207613863/500000000 : ℝ)*X 0 0+(1356290151/2500000000 : ℝ)*X 0 1+(3154536857/10000000000 : ℝ)*X 0 2+(207613863/500000000 : ℝ)*X 1 0+(1356290151/2500000000 : ℝ)*X 1 1+(3154536857/10000000000 : ℝ)*X 1 2+(207613863/500000000 : ℝ)*X 2 0+(1356290151/2500000000 : ℝ)*X 2 1+(3154536857/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (94732408956244284077193/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (28116769/100000000000000 : ℝ)*(base1) + (4405637/390625000000 : ℝ)*(base19) + (22858283/2000000000000 : ℝ)*(base23) + (30529203/25000000000000 : ℝ)*(upper3) + (85949873/50000000000000 : ℝ)*(upper5) + (341599460155059/50000000000000 : ℝ)*(major0) + (341599460155059/50000000000000 : ℝ)*(major1) + (341599460155059/50000000000000 : ℝ)*(major2) + (474419329110409/50000000000000 : ℝ)*(sp0) + (948841742797917/100000000000000 : ℝ)*(sp1) + (23721043193171/2500000000000 : ℝ)*(sp2) + (417553016729499/100000000000000 : ℝ)*(sp3) + (4240536941/100000000000000 : ℝ)*(sp4) + (883622811/50000000000000 : ℝ)*(sp7) + (417554812091889/100000000000000 : ℝ)*(f.failure) + (94884287064099/10000000000000 : ℝ)*(f.sum) + (18416739534269/20000000000000000000000000000 : ℝ)*base65 + (262355861565731/40000000000000000000000000000 : ℝ)*base68 + (112591213034269/40000000000000000000000000000 : ℝ)*base69 + (163128548954269/40000000000000000000000000000 : ℝ)*base71 + (72538525625731/20000000000000000000000000000 : ℝ)*base74 + (401648749434269/40000000000000000000000000000 : ℝ)*base75 + (26290295565731/40000000000000000000000000000 : ℝ)*base78 + (26893852645731/40000000000000000000000000000 : ℝ)*base80 + (84122356214269/20000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (67638669/10000000000000000000000 : ℝ)*base90 + (67638669/10000000000000000000000 : ℝ)*base92 + (67638669/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7331487562141971774687/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (67417743/10000000000000 : ℝ)*(base19) + (135196493/20000000000000 : ℝ)*(base23) + (1887719/25000000000000 : ℝ)*(base32) + (20083959/20000000000000 : ℝ)*(upper3) + (17479209/20000000000000 : ℝ)*(upper5) + (90073809507381/12500000000000 : ℝ)*(major0) + (90073809507381/12500000000000 : ℝ)*(major1) + (90073809507381/12500000000000 : ℝ)*(major2) + (1770433167/100000000000000 : ℝ)*(sp1) + (1914174911/100000000000000 : ℝ)*(sp2) + (1000773219221909/100000000000000 : ℝ)*(sp4) + (62548173413207/6250000000000 : ℝ)*(sp5) + (250192657266133/25000000000000 : ℝ)*(sp6) + (22020381379607/5000000000000 : ℝ)*(sp7) + (55050954392877/12500000000000 : ℝ)*(f.failure) + (1000773219221909/100000000000000 : ℝ)*(f.sum) + (7739638846771/5000000000000000000000000000 : ℝ)*base65 + (10509507081771/10000000000000000000000000000 : ℝ)*base67 + (42539754128229/10000000000000000000000000000 : ℝ)*base70 + (8818687361771/10000000000000000000000000000 : ℝ)*base71 + (3767903161771/5000000000000000000000000000 : ℝ)*base73 + (23738435888229/10000000000000000000000000000 : ℝ)*base76 + (9662229191771/10000000000000000000000000000 : ℝ)*base77 + (82478765011771/10000000000000000000000000000 : ℝ)*base79 + (17109114143229/5000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (387417/1250000000000000000000 : ℝ)*base90 + (387417/1250000000000000000000 : ℝ)*base92 + (387417/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1515_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163618979/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1433/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5089/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1515_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1515_s1_0 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-73422719/400000000 : ℝ)*x 0 + (2784259461/5000000000 : ℝ)*x 1 + (2550154847/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (73422719/400000000 : ℝ)^4527 ≤ (11182919983853/100000000000000 : ℝ)^3503 := by
    have hnat : (73422719 : ℕ)^4527*100000000000000^3503 ≤ 11182919983853^3503*400000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      73422719 400000000 11182919983853 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2784259461/5000000000 : ℝ)^4527 ≤ (46926061788997/100000000000000 : ℝ)^3503 := by
    have hnat : (2784259461 : ℕ)^4527*100000000000000^3503 ≤ 46926061788997^3503*5000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2784259461 5000000000 46926061788997 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2550154847/5000000000 : ℝ)^4527 ≤ (5236377276581/12500000000000 : ℝ)^3503 := by
    have hnat : (2550154847 : ℕ)^4527*12500000000000^3503 ≤ 5236377276581^3503*5000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2550154847 5000000000 5236377276581 12500000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-73422719/400000000 : ℝ), (2784259461/5000000000 : ℝ), (2550154847/5000000000 : ℝ)] ![(11182919983853/100000000000000 : ℝ), (46926061788997/100000000000000 : ℝ), (5236377276581/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-73422719/400000000 : ℝ)|^4527 ≤ (11182919983853/100000000000000 : ℝ)^3503
        have hw : |(-73422719/400000000 : ℝ)|=(73422719/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2784259461/5000000000 : ℝ)|^4527 ≤ (46926061788997/100000000000000 : ℝ)^3503
        have hw : |(2784259461/5000000000 : ℝ)|=(2784259461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2550154847/5000000000 : ℝ)|^4527 ≤ (5236377276581/12500000000000 : ℝ)^3503
        have hw : |(2550154847/5000000000 : ℝ)|=(2550154847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_s1_1 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5386074871/10000000000 : ℝ)*x 0 + (-104100907/500000000 : ℝ)*x 1 + (318769349/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5386074871/10000000000 : ℝ)^4527 ≤ (11237189522103/25000000000000 : ℝ)^3503 := by
    have hnat : (5386074871 : ℕ)^4527*25000000000000^3503 ≤ 11237189522103^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386074871 10000000000 11237189522103 25000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (104100907/500000000 : ℝ)^4527 ≤ (13160224844233/100000000000000 : ℝ)^3503 := by
    have hnat : (104100907 : ℕ)^4527*100000000000000^3503 ≤ 13160224844233^3503*500000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104100907 500000000 13160224844233 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (318769349/625000000 : ℝ)^4527 ≤ (20945508522533/50000000000000 : ℝ)^3503 := by
    have hnat : (318769349 : ℕ)^4527*50000000000000^3503 ≤ 20945508522533^3503*625000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      318769349 625000000 20945508522533 50000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5386074871/10000000000 : ℝ), (-104100907/500000000 : ℝ), (318769349/625000000 : ℝ)] ![(11237189522103/25000000000000 : ℝ), (13160224844233/100000000000000 : ℝ), (20945508522533/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5386074871/10000000000 : ℝ)|^4527 ≤ (11237189522103/25000000000000 : ℝ)^3503
        have hw : |(5386074871/10000000000 : ℝ)|=(5386074871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-104100907/500000000 : ℝ)|^4527 ≤ (13160224844233/100000000000000 : ℝ)^3503
        have hw : |(-104100907/500000000 : ℝ)|=(104100907/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(318769349/625000000 : ℝ)|^4527 ≤ (20945508522533/50000000000000 : ℝ)^3503
        have hw : |(318769349/625000000 : ℝ)|=(318769349/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_s1_2 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5386075279/10000000000 : ℝ)*x 0 + (5100309377/10000000000 : ℝ)*x 1 + (-2082017871/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5386075279/10000000000 : ℝ)^4527 ≤ (22474381244323/50000000000000 : ℝ)^3503 := by
    have hnat : (5386075279 : ℕ)^4527*50000000000000^3503 ≤ 22474381244323^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386075279 10000000000 22474381244323 50000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5100309377/10000000000 : ℝ)^4527 ≤ (2618188427993/6250000000000 : ℝ)^3503 := by
    have hnat : (5100309377 : ℕ)^4527*6250000000000^3503 ≤ 2618188427993^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5100309377 10000000000 2618188427993 6250000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2082017871/10000000000 : ℝ)^4527 ≤ (1645027830859/12500000000000 : ℝ)^3503 := by
    have hnat : (2082017871 : ℕ)^4527*12500000000000^3503 ≤ 1645027830859^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2082017871 10000000000 1645027830859 12500000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5386075279/10000000000 : ℝ), (5100309377/10000000000 : ℝ), (-2082017871/10000000000 : ℝ)] ![(22474381244323/50000000000000 : ℝ), (2618188427993/6250000000000 : ℝ), (1645027830859/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5386075279/10000000000 : ℝ)|^4527 ≤ (22474381244323/50000000000000 : ℝ)^3503
        have hw : |(5386075279/10000000000 : ℝ)|=(5386075279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5100309377/10000000000 : ℝ)|^4527 ≤ (2618188427993/6250000000000 : ℝ)^3503
        have hw : |(5100309377/10000000000 : ℝ)|=(5100309377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2082017871/10000000000 : ℝ)|^4527 ≤ (1645027830859/12500000000000 : ℝ)^3503
        have hw : |(-2082017871/10000000000 : ℝ)|=(2082017871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_s1_3 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (849703679/2000000000 : ℝ)*x 0 + (3744597163/10000000000 : ℝ)*x 1 + (4808547439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (849703679/2000000000 : ℝ)^4527 ≤ (33079852714497/100000000000000 : ℝ)^3503 := by
    have hnat : (849703679 : ℕ)^4527*100000000000000^3503 ≤ 33079852714497^3503*2000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849703679 2000000000 33079852714497 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3744597163/10000000000 : ℝ)^4527 ≤ (5619950745951/20000000000000 : ℝ)^3503 := by
    have hnat : (3744597163 : ℕ)^4527*20000000000000^3503 ≤ 5619950745951^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3744597163 10000000000 5619950745951 20000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4808547439/10000000000 : ℝ)^4527 ≤ (9705098384681/25000000000000 : ℝ)^3503 := by
    have hnat : (4808547439 : ℕ)^4527*25000000000000^3503 ≤ 9705098384681^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4808547439 10000000000 9705098384681 25000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(849703679/2000000000 : ℝ), (3744597163/10000000000 : ℝ), (4808547439/10000000000 : ℝ)] ![(33079852714497/100000000000000 : ℝ), (5619950745951/20000000000000 : ℝ), (9705098384681/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(849703679/2000000000 : ℝ)|^4527 ≤ (33079852714497/100000000000000 : ℝ)^3503
        have hw : |(849703679/2000000000 : ℝ)|=(849703679/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3744597163/10000000000 : ℝ)|^4527 ≤ (5619950745951/20000000000000 : ℝ)^3503
        have hw : |(3744597163/10000000000 : ℝ)|=(3744597163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4808547439/10000000000 : ℝ)|^4527 ≤ (9705098384681/25000000000000 : ℝ)^3503
        have hw : |(4808547439/10000000000 : ℝ)|=(4808547439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_s1_4 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-91793211/500000000 : ℝ)*x 0 + (319095221/625000000 : ℝ)*x 1 + (1390805391/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (91793211/500000000 : ℝ)^4527 ≤ (11185252455513/100000000000000 : ℝ)^3503 := by
    have hnat : (91793211 : ℕ)^4527*100000000000000^3503 ≤ 11185252455513^3503*500000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91793211 500000000 11185252455513 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (319095221/625000000 : ℝ)^4527 ≤ (4194636819179/10000000000000 : ℝ)^3503 := by
    have hnat : (319095221 : ℕ)^4527*10000000000000^3503 ≤ 4194636819179^3503*625000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      319095221 625000000 4194636819179 10000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1390805391/2500000000 : ℝ)^4527 ≤ (46868379340621/100000000000000 : ℝ)^3503 := by
    have hnat : (1390805391 : ℕ)^4527*100000000000000^3503 ≤ 46868379340621^3503*2500000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1390805391 2500000000 46868379340621 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-91793211/500000000 : ℝ), (319095221/625000000 : ℝ), (1390805391/2500000000 : ℝ)] ![(11185252455513/100000000000000 : ℝ), (4194636819179/10000000000000 : ℝ), (46868379340621/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-91793211/500000000 : ℝ)|^4527 ≤ (11185252455513/100000000000000 : ℝ)^3503
        have hw : |(-91793211/500000000 : ℝ)|=(91793211/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(319095221/625000000 : ℝ)|^4527 ≤ (4194636819179/10000000000000 : ℝ)^3503
        have hw : |(319095221/625000000 : ℝ)|=(319095221/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1390805391/2500000000 : ℝ)|^4527 ≤ (46868379340621/100000000000000 : ℝ)^3503
        have hw : |(1390805391/2500000000 : ℝ)|=(1390805391/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_s1_5 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2631353559/5000000000 : ℝ)*x 0 + (-809552837/5000000000 : ℝ)*x 1 + (2781610839/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2631353559/5000000000 : ℝ)^4527 ≤ (43622729176027/100000000000000 : ℝ)^3503 := by
    have hnat : (2631353559 : ℕ)^4527*100000000000000^3503 ≤ 43622729176027^3503*5000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631353559 5000000000 43622729176027 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (809552837/5000000000 : ℝ)^4527 ≤ (4754445109321/50000000000000 : ℝ)^3503 := by
    have hnat : (809552837 : ℕ)^4527*50000000000000^3503 ≤ 4754445109321^3503*5000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      809552837 5000000000 4754445109321 50000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2781610839/5000000000 : ℝ)^4527 ≤ (5858547572723/12500000000000 : ℝ)^3503 := by
    have hnat : (2781610839 : ℕ)^4527*12500000000000^3503 ≤ 5858547572723^3503*5000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2781610839 5000000000 5858547572723 12500000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2631353559/5000000000 : ℝ), (-809552837/5000000000 : ℝ), (2781610839/5000000000 : ℝ)] ![(43622729176027/100000000000000 : ℝ), (4754445109321/50000000000000 : ℝ), (5858547572723/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2631353559/5000000000 : ℝ)|^4527 ≤ (43622729176027/100000000000000 : ℝ)^3503
        have hw : |(2631353559/5000000000 : ℝ)|=(2631353559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-809552837/5000000000 : ℝ)|^4527 ≤ (4754445109321/50000000000000 : ℝ)^3503
        have hw : |(-809552837/5000000000 : ℝ)|=(809552837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2781610839/5000000000 : ℝ)|^4527 ≤ (5858547572723/12500000000000 : ℝ)^3503
        have hw : |(2781610839/5000000000 : ℝ)|=(2781610839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_s1_6 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (328919181/625000000 : ℝ)*x 0 + (5563221793/10000000000 : ℝ)*x 1 + (-1619105823/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (328919181/625000000 : ℝ)^4527 ≤ (8724545359589/20000000000000 : ℝ)^3503 := by
    have hnat : (328919181 : ℕ)^4527*20000000000000^3503 ≤ 8724545359589^3503*625000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328919181 625000000 8724545359589 20000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5563221793/10000000000 : ℝ)^4527 ≤ (23434190916917/50000000000000 : ℝ)^3503 := by
    have hnat : (5563221793 : ℕ)^4527*50000000000000^3503 ≤ 23434190916917^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5563221793 10000000000 23434190916917 50000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1619105823/10000000000 : ℝ)^4527 ≤ (2377222837377/25000000000000 : ℝ)^3503 := by
    have hnat : (1619105823 : ℕ)^4527*25000000000000^3503 ≤ 2377222837377^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1619105823 10000000000 2377222837377 25000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(328919181/625000000 : ℝ), (5563221793/10000000000 : ℝ), (-1619105823/10000000000 : ℝ)] ![(8724545359589/20000000000000 : ℝ), (23434190916917/50000000000000 : ℝ), (2377222837377/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(328919181/625000000 : ℝ)|^4527 ≤ (8724545359589/20000000000000 : ℝ)^3503
        have hw : |(328919181/625000000 : ℝ)|=(328919181/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5563221793/10000000000 : ℝ)|^4527 ≤ (23434190916917/50000000000000 : ℝ)^3503
        have hw : |(5563221793/10000000000 : ℝ)|=(5563221793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1619105823/10000000000 : ℝ)|^4527 ≤ (2377222837377/25000000000000 : ℝ)^3503
        have hw : |(-1619105823/10000000000 : ℝ)|=(1619105823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_s1_7 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4249191961/10000000000 : ℝ)*x 0 + (1199174817/2500000000 : ℝ)*x 1 + (150265391/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4249191961/10000000000 : ℝ)^4527 ≤ (33086630481599/100000000000000 : ℝ)^3503 := by
    have hnat : (4249191961 : ℕ)^4527*100000000000000^3503 ≤ 33086630481599^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4249191961 10000000000 33086630481599 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1199174817/2500000000 : ℝ)^4527 ≤ (4837103008911/12500000000000 : ℝ)^3503 := by
    have hnat : (1199174817 : ℕ)^4527*12500000000000^3503 ≤ 4837103008911^3503*2500000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1199174817 2500000000 4837103008911 12500000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (150265391/400000000 : ℝ)^4527 ≤ (7054136356193/25000000000000 : ℝ)^3503 := by
    have hnat : (150265391 : ℕ)^4527*25000000000000^3503 ≤ 7054136356193^3503*400000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      150265391 400000000 7054136356193 25000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4249191961/10000000000 : ℝ), (1199174817/2500000000 : ℝ), (150265391/400000000 : ℝ)] ![(33086630481599/100000000000000 : ℝ), (4837103008911/12500000000000 : ℝ), (7054136356193/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4249191961/10000000000 : ℝ)|^4527 ≤ (33086630481599/100000000000000 : ℝ)^3503
        have hw : |(4249191961/10000000000 : ℝ)|=(4249191961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1199174817/2500000000 : ℝ)|^4527 ≤ (4837103008911/12500000000000 : ℝ)^3503
        have hw : |(1199174817/2500000000 : ℝ)|=(1199174817/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(150265391/400000000 : ℝ)|^4527 ≤ (7054136356193/25000000000000 : ℝ)^3503
        have hw : |(150265391/400000000 : ℝ)|=(150265391/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1515_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163618979/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5089/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1433/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2099/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (183/1000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5089/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1433/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5089/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1433/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5089/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1433/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5089/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1433/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5089/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1433/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5089/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1433/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1433/50000 : ℝ) ^ (4525/1024 : ℝ) ≤ (1904135486787/12500000000000000000 : ℝ) := by
    have hpowers : (1433/50000 : ℝ)^4525 ≤ (1904135486787/12500000000000000000 : ℝ)^1024 := by
      have hnat : (1433 : ℕ)^4525*12500000000000000000^1024 ≤ 1904135486787^1024*50000^4525 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1433 50000 1904135486787 12500000000000000000 4525 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1433/50000 : ℝ)) (X := (1904135486787/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4525 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (5089/20000 : ℝ) ^ (4525/1024 : ℝ) ≤ (118129879245953679/50000000000000000000 : ℝ) := by
    have hpowers : (5089/20000 : ℝ)^4525 ≤ (118129879245953679/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5089 : ℕ)^4525*50000000000000000000^1024 ≤ 118129879245953679^1024*20000^4525 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5089 20000 118129879245953679 50000000000000000000 4525 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5089/20000 : ℝ)) (X := (118129879245953679/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4525 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250001904135486787/6250000000000000000 : ℝ) ≤ (10000000689444247/10000000000000000 : ℝ) ^ (4525/1024 : ℝ) := by
    have hpowers : (6250001904135486787/6250000000000000000 : ℝ)^1024 ≤ (10000000689444247/10000000000000000 : ℝ)^4525 := by
      have hnat : (6250001904135486787 : ℕ)^1024*10000000000000000^4525 ≤ 10000000689444247^4525*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250001904135486787 6250000000000000000 10000000689444247 10000000000000000 1024 4525 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000689444247/10000000000000000 : ℝ)) (X := (6250001904135486787/6250000000000000000 : ℝ)) (by norm_num) 4525 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50118137495787900827/50000000000000000000 : ℝ) ≤ (10005341983510279/10000000000000000 : ℝ) ^ (4525/1024 : ℝ) := by
    have hpowers : (50118137495787900827/50000000000000000000 : ℝ)^1024 ≤ (10005341983510279/10000000000000000 : ℝ)^4525 := by
      have hnat : (50118137495787900827 : ℕ)^1024*10000000000000000^4525 ≤ 10005341983510279^4525*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50118137495787900827 50000000000000000000 10005341983510279 10000000000000000 1024 4525 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10005341983510279/10000000000000000 : ℝ)) (X := (50118137495787900827/50000000000000000000 : ℝ)) (by norm_num) 4525 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25118129879245953679/25000000000000000000 : ℝ) ≤ (10010683277576311/10000000000000000 : ℝ) ^ (4525/1024 : ℝ) := by
    have hpowers : (25118129879245953679/25000000000000000000 : ℝ)^1024 ≤ (10010683277576311/10000000000000000 : ℝ)^4525 := by
      have hnat : (25118129879245953679 : ℕ)^1024*10000000000000000^4525 ≤ 10010683277576311^4525*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25118129879245953679 25000000000000000000 10010683277576311 10000000000000000 1024 4525 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10010683277576311/10000000000000000 : ℝ)) (X := (25118129879245953679/25000000000000000000 : ℝ)) (by norm_num) 4525 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1904135486787/12500000000000000000 : ℝ) ≤ ((225759399269375157589/225790000000000000000 : ℝ)+2*(333830879127/141118750000000 : ℝ)*(1433/50000 : ℝ))^(4525/1024 : ℝ) := by
    rw [show (225759399269375157589/225790000000000000000 : ℝ)+2*(333830879127/141118750000000 : ℝ)*(1433/50000 : ℝ)=(10000000689444247/10000000000000000 : ℝ) by norm_num, show 1+2*(1904135486787/12500000000000000000 : ℝ)=(6250001904135486787/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(118129879245953679/50000000000000000000 : ℝ)+(1904135486787/12500000000000000000 : ℝ) ≤ ((225759399269375157589/225790000000000000000 : ℝ)+(333830879127/141118750000000 : ℝ)*((5089/20000 : ℝ)+(1433/50000 : ℝ)))^(4525/1024 : ℝ) := by
    rw [show (225759399269375157589/225790000000000000000 : ℝ)+(333830879127/141118750000000 : ℝ)*((5089/20000 : ℝ)+(1433/50000 : ℝ))=(10005341983510279/10000000000000000 : ℝ) by norm_num, show 1+(118129879245953679/50000000000000000000 : ℝ)+(1904135486787/12500000000000000000 : ℝ)=(50118137495787900827/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(118129879245953679/50000000000000000000 : ℝ) ≤ ((225759399269375157589/225790000000000000000 : ℝ)+2*(333830879127/141118750000000 : ℝ)*(5089/20000 : ℝ))^(4525/1024 : ℝ) := by
    rw [show (225759399269375157589/225790000000000000000 : ℝ)+2*(333830879127/141118750000000 : ℝ)*(5089/20000 : ℝ)=(10010683277576311/10000000000000000 : ℝ) by norm_num, show 1+2*(118129879245953679/50000000000000000000 : ℝ)=(25118129879245953679/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (225759399269375157589/225790000000000000000 : ℝ)*(X 1 0+X 2 0)+(333830879127/141118750000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4525/1024 : ℝ)) (lo := (1433/50000 : ℝ)) (hi := (5089/20000 : ℝ)) (c := (225759399269375157589/225790000000000000000 : ℝ)) (alpha := (333830879127/141118750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (225759399269375157589/225790000000000000000 : ℝ)*(X 0 1+X 2 1)+(333830879127/141118750000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4525/1024 : ℝ)) (lo := (1433/50000 : ℝ)) (hi := (5089/20000 : ℝ)) (c := (225759399269375157589/225790000000000000000 : ℝ)) (alpha := (333830879127/141118750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (225759399269375157589/225790000000000000000 : ℝ)*(X 0 2+X 1 2)+(333830879127/141118750000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4525/1024 : ℝ)) (lo := (1433/50000 : ℝ)) (hi := (5089/20000 : ℝ)) (c := (225759399269375157589/225790000000000000000 : ℝ)) (alpha := (333830879127/141118750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-73422719/400000000 : ℝ)*X 0 0+(2784259461/5000000000 : ℝ)*X 0 1+(2550154847/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5386074871/10000000000 : ℝ)*X 1 0+(-104100907/500000000 : ℝ)*X 1 1+(318769349/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5386075279/10000000000 : ℝ)*X 2 0+(5100309377/10000000000 : ℝ)*X 2 1+(-2082017871/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((849703679/2000000000 : ℝ)*X 0 0+(3744597163/10000000000 : ℝ)*X 0 1+(4808547439/10000000000 : ℝ)*X 0 2+(849703679/2000000000 : ℝ)*X 1 0+(3744597163/10000000000 : ℝ)*X 1 1+(4808547439/10000000000 : ℝ)*X 1 2+(849703679/2000000000 : ℝ)*X 2 0+(3744597163/10000000000 : ℝ)*X 2 1+(4808547439/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-91793211/500000000 : ℝ)*X 0 0+(319095221/625000000 : ℝ)*X 0 1+(1390805391/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2631353559/5000000000 : ℝ)*X 1 0+(-809552837/5000000000 : ℝ)*X 1 1+(2781610839/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((328919181/625000000 : ℝ)*X 2 0+(5563221793/10000000000 : ℝ)*X 2 1+(-1619105823/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4249191961/10000000000 : ℝ)*X 0 0+(1199174817/2500000000 : ℝ)*X 0 1+(150265391/400000000 : ℝ)*X 0 2+(4249191961/10000000000 : ℝ)*X 1 0+(1199174817/2500000000 : ℝ)*X 1 1+(150265391/400000000 : ℝ)*X 1 2+(4249191961/10000000000 : ℝ)*X 2 0+(1199174817/2500000000 : ℝ)*X 2 1+(150265391/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (990411366679990373075619/112895000000000000000000000000 : ℝ) := by norm_num
    linear_combination (44167747/100000000000000 : ℝ)*(base1) + (1526131387/100000000000000 : ℝ)*(base19) + (843960801/50000000000000 : ℝ)*(base23) + (82624441/100000000000000 : ℝ)*(upper3) + (251894499/100000000000000 : ℝ)*(upper5) + (1537863101619399/100000000000000 : ℝ)*(major0) + (1537863101619399/100000000000000 : ℝ)*(major1) + (1537863101619399/100000000000000 : ℝ)*(major2) + (533951874231767/25000000000000 : ℝ)*(sp0) + (2135819300917597/100000000000000 : ℝ)*(sp1) + (1067909569563691/50000000000000 : ℝ)*(sp2) + (117487450000649/12500000000000 : ℝ)*(sp3) + (13374289663/100000000000000 : ℝ)*(sp4) + (5439588401/100000000000000 : ℝ)*(sp7) + (46995254188067/5000000000000 : ℝ)*(f.failure) + (266977603381123/12500000000000 : ℝ)*(f.sum) + (50218427143927/112895000000000000000000000000 : ℝ)*base66 + (83923086424210730989/22579000000000000000000000000000000 : ℝ)*base68 + (177781333817928269011/22579000000000000000000000000000000 : ℝ)*base69 + (10925323026650730989/22579000000000000000000000000000000 : ℝ)*base72 + (2229468688527/440996093750000000000000000 : ℝ)*base74 + (99701807825532269011/22579000000000000000000000000000000 : ℝ)*base75 + (48259099693160269011/22579000000000000000000000000000000 : ℝ)*base77 + (22329198983260730989/22579000000000000000000000000000000 : ℝ)*base80 + (316062818577573/112895000000000000000000000000 : ℝ)*base81 + (1523593/500000000000000000000 : ℝ)*base89 + (1523593/500000000000000000000 : ℝ)*base91 + (1523593/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (27357843597920959816770405471/5644750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (980849823/100000000000000 : ℝ)*(base19) + (973061827/100000000000000 : ℝ)*(base23) + (6743497/5000000000000 : ℝ)*(upper3) + (39277449/100000000000000 : ℝ)*(lower4) + (65462591/100000000000000 : ℝ)*(upper5) + (786581057521487/50000000000000 : ℝ)*(major0) + (786581057521487/50000000000000 : ℝ)*(major1) + (786581057521487/50000000000000 : ℝ)*(major2) + (21954669/312500000000 : ℝ)*(sp1) + (7441082951/100000000000000 : ℝ)*(sp2) + (2184845073456519/100000000000000 : ℝ)*(sp4) + (273104633389077/12500000000000 : ℝ)*(sp5) + (109241832965587/5000000000000 : ℝ)*(sp6) + (961478995076099/100000000000000 : ℝ)*(sp7) + (961478995076099/100000000000000 : ℝ)*(f.failure) + (2184845073456519/100000000000000 : ℝ)*(f.sum) + (271496508237863/112895000000000000000000000000 : ℝ)*base65 + (10887547742944985157/11289500000000000000000000000000000 : ℝ)*base68 + (12808077227667514843/11289500000000000000000000000000000 : ℝ)*base69 + (45403814314439485157/11289500000000000000000000000000000 : ℝ)*base72 + (39269188486073/28223750000000000000000000000 : ℝ)*base74 + (77829087114913514843/11289500000000000000000000000000000 : ℝ)*base75 + (73100226985771014843/11289500000000000000000000000000000 : ℝ)*base77 + (82343963791866514843/11289500000000000000000000000000000 : ℝ)*base79 + (33755814634689/14111875000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (54317079/10000000000000000000000 : ℝ)*base90 + (54317079/10000000000000000000000 : ℝ)*base92 + (54317079/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1515_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163618979/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5089/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1433/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2099/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (183/1000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1515_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1515_s2_0 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-371948537/2000000000 : ℝ)*x 0 + (2728482079/5000000000 : ℝ)*x 1 + (1299050099/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (371948537/2000000000 : ℝ)^4527 ≤ (11373619236769/100000000000000 : ℝ)^3503 := by
    have hnat : (371948537 : ℕ)^4527*100000000000000^3503 ≤ 11373619236769^3503*2000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      371948537 2000000000 11373619236769 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2728482079/5000000000 : ℝ)^4527 ≤ (11428689338309/25000000000000 : ℝ)^3503 := by
    have hnat : (2728482079 : ℕ)^4527*25000000000000^3503 ≤ 11428689338309^3503*5000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2728482079 5000000000 11428689338309 25000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1299050099/2500000000 : ℝ)^4527 ≤ (10727905851077/25000000000000 : ℝ)^3503 := by
    have hnat : (1299050099 : ℕ)^4527*25000000000000^3503 ≤ 10727905851077^3503*2500000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1299050099 2500000000 10727905851077 25000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-371948537/2000000000 : ℝ), (2728482079/5000000000 : ℝ), (1299050099/2500000000 : ℝ)] ![(11373619236769/100000000000000 : ℝ), (11428689338309/25000000000000 : ℝ), (10727905851077/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-371948537/2000000000 : ℝ)|^4527 ≤ (11373619236769/100000000000000 : ℝ)^3503
        have hw : |(-371948537/2000000000 : ℝ)|=(371948537/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2728482079/5000000000 : ℝ)|^4527 ≤ (11428689338309/25000000000000 : ℝ)^3503
        have hw : |(2728482079/5000000000 : ℝ)|=(2728482079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1299050099/2500000000 : ℝ)|^4527 ≤ (10727905851077/25000000000000 : ℝ)^3503
        have hw : |(1299050099/2500000000 : ℝ)|=(1299050099/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_s2_1 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (6697129/12500000 : ℝ)*x 0 + (-398790969/2000000000 : ℝ)*x 1 + (259810053/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6697129/12500000 : ℝ)^4527 ≤ (44643008650039/100000000000000 : ℝ)^3503 := by
    have hnat : (6697129 : ℕ)^4527*100000000000000^3503 ≤ 44643008650039^3503*12500000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6697129 12500000 44643008650039 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (398790969/2000000000 : ℝ)^4527 ≤ (2489072170227/20000000000000 : ℝ)^3503 := by
    have hnat : (398790969 : ℕ)^4527*20000000000000^3503 ≤ 2489072170227^3503*2000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      398790969 2000000000 2489072170227 20000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (259810053/500000000 : ℝ)^4527 ≤ (21455815245369/50000000000000 : ℝ)^3503 := by
    have hnat : (259810053 : ℕ)^4527*50000000000000^3503 ≤ 21455815245369^3503*500000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259810053 500000000 21455815245369 50000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6697129/12500000 : ℝ), (-398790969/2000000000 : ℝ), (259810053/500000000 : ℝ)] ![(44643008650039/100000000000000 : ℝ), (2489072170227/20000000000000 : ℝ), (21455815245369/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6697129/12500000 : ℝ)|^4527 ≤ (44643008650039/100000000000000 : ℝ)^3503
        have hw : |(6697129/12500000 : ℝ)|=(6697129/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-398790969/2000000000 : ℝ)|^4527 ≤ (2489072170227/20000000000000 : ℝ)^3503
        have hw : |(-398790969/2000000000 : ℝ)|=(398790969/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(259810053/500000000 : ℝ)|^4527 ≤ (21455815245369/50000000000000 : ℝ)^3503
        have hw : |(259810053/500000000 : ℝ)|=(259810053/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_s2_2 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2678852023/5000000000 : ℝ)*x 0 + (129905013/250000000 : ℝ)*x 1 + (-199395443/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2678852023/5000000000 : ℝ)^4527 ≤ (2232150887999/5000000000000 : ℝ)^3503 := by
    have hnat : (2678852023 : ℕ)^4527*5000000000000^3503 ≤ 2232150887999^3503*5000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2678852023 5000000000 2232150887999 5000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (129905013/250000000 : ℝ)^4527 ≤ (42911624727677/100000000000000 : ℝ)^3503 := by
    have hnat : (129905013 : ℕ)^4527*100000000000000^3503 ≤ 42911624727677^3503*250000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129905013 250000000 42911624727677 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (199395443/1000000000 : ℝ)^4527 ≤ (12445357503711/100000000000000 : ℝ)^3503 := by
    have hnat : (199395443 : ℕ)^4527*100000000000000^3503 ≤ 12445357503711^3503*1000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      199395443 1000000000 12445357503711 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2678852023/5000000000 : ℝ), (129905013/250000000 : ℝ), (-199395443/1000000000 : ℝ)] ![(2232150887999/5000000000000 : ℝ), (42911624727677/100000000000000 : ℝ), (12445357503711/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2678852023/5000000000 : ℝ)|^4527 ≤ (2232150887999/5000000000000 : ℝ)^3503
        have hw : |(2678852023/5000000000 : ℝ)|=(2678852023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(129905013/250000000 : ℝ)|^4527 ≤ (42911624727677/100000000000000 : ℝ)^3503
        have hw : |(129905013/250000000 : ℝ)|=(129905013/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-199395443/1000000000 : ℝ)|^4527 ≤ (12445357503711/100000000000000 : ℝ)^3503
        have hw : |(-199395443/1000000000 : ℝ)|=(199395443/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_s2_3 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1066470343/2500000000 : ℝ)*x 0 + (3978309171/10000000000 : ℝ)*x 1 + (1142716127/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1066470343/2500000000 : ℝ)^4527 ≤ (3325466812037/10000000000000 : ℝ)^3503 := by
    have hnat : (1066470343 : ℕ)^4527*10000000000000^3503 ≤ 3325466812037^3503*2500000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1066470343 2500000000 3325466812037 10000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3978309171/10000000000 : ℝ)^4527 ≤ (15193298220601/50000000000000 : ℝ)^3503 := by
    have hnat : (3978309171 : ℕ)^4527*50000000000000^3503 ≤ 15193298220601^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3978309171 10000000000 15193298220601 50000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1142716127/2500000000 : ℝ)^4527 ≤ (36358735429303/100000000000000 : ℝ)^3503 := by
    have hnat : (1142716127 : ℕ)^4527*100000000000000^3503 ≤ 36358735429303^3503*2500000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1142716127 2500000000 36358735429303 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1066470343/2500000000 : ℝ), (3978309171/10000000000 : ℝ), (1142716127/2500000000 : ℝ)] ![(3325466812037/10000000000000 : ℝ), (15193298220601/50000000000000 : ℝ), (36358735429303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1066470343/2500000000 : ℝ)|^4527 ≤ (3325466812037/10000000000000 : ℝ)^3503
        have hw : |(1066470343/2500000000 : ℝ)|=(1066470343/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3978309171/10000000000 : ℝ)|^4527 ≤ (15193298220601/50000000000000 : ℝ)^3503
        have hw : |(3978309171/10000000000 : ℝ)|=(3978309171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1142716127/2500000000 : ℝ)|^4527 ≤ (36358735429303/100000000000000 : ℝ)^3503
        have hw : |(1142716127/2500000000 : ℝ)|=(1142716127/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_s2_4 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-929896417/5000000000 : ℝ)*x 0 + (324864209/625000000 : ℝ)*x 1 + (218212943/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (929896417/5000000000 : ℝ)^4527 ≤ (2843503896991/25000000000000 : ℝ)^3503 := by
    have hnat : (929896417 : ℕ)^4527*25000000000000^3503 ≤ 2843503896991^3503*5000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      929896417 5000000000 2843503896991 25000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (324864209/625000000 : ℝ)^4527 ≤ (8585797506277/20000000000000 : ℝ)^3503 := by
    have hnat : (324864209 : ℕ)^4527*20000000000000^3503 ≤ 8585797506277^3503*625000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324864209 625000000 8585797506277 20000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (218212943/400000000 : ℝ)^4527 ≤ (45696996869251/100000000000000 : ℝ)^3503 := by
    have hnat : (218212943 : ℕ)^4527*100000000000000^3503 ≤ 45696996869251^3503*400000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218212943 400000000 45696996869251 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-929896417/5000000000 : ℝ), (324864209/625000000 : ℝ), (218212943/400000000 : ℝ)] ![(2843503896991/25000000000000 : ℝ), (8585797506277/20000000000000 : ℝ), (45696996869251/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-929896417/5000000000 : ℝ)|^4527 ≤ (2843503896991/25000000000000 : ℝ)^3503
        have hw : |(-929896417/5000000000 : ℝ)|=(929896417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(324864209/625000000 : ℝ)|^4527 ≤ (8585797506277/20000000000000 : ℝ)^3503
        have hw : |(324864209/625000000 : ℝ)|=(324864209/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(218212943/400000000 : ℝ)|^4527 ≤ (45696996869251/100000000000000 : ℝ)^3503
        have hw : |(218212943/400000000 : ℝ)|=(218212943/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_s2_5 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644600699/5000000000 : ℝ)*x 0 + (-1734832089/10000000000 : ℝ)*x 1 + (1363831147/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644600699/5000000000 : ℝ)^4527 ≤ (21953373363471/50000000000000 : ℝ)^3503 := by
    have hnat : (2644600699 : ℕ)^4527*50000000000000^3503 ≤ 21953373363471^3503*5000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644600699 5000000000 21953373363471 50000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1734832089/10000000000 : ℝ)^4527 ≤ (1299530677781/12500000000000 : ℝ)^3503 := by
    have hnat : (1734832089 : ℕ)^4527*12500000000000^3503 ≤ 1299530677781^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1734832089 10000000000 1299530677781 12500000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1363831147/2500000000 : ℝ)^4527 ≤ (45697007835219/100000000000000 : ℝ)^3503 := by
    have hnat : (1363831147 : ℕ)^4527*100000000000000^3503 ≤ 45697007835219^3503*2500000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1363831147 2500000000 45697007835219 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644600699/5000000000 : ℝ), (-1734832089/10000000000 : ℝ), (1363831147/2500000000 : ℝ)] ![(21953373363471/50000000000000 : ℝ), (1299530677781/12500000000000 : ℝ), (45697007835219/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644600699/5000000000 : ℝ)|^4527 ≤ (21953373363471/50000000000000 : ℝ)^3503
        have hw : |(2644600699/5000000000 : ℝ)|=(2644600699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1734832089/10000000000 : ℝ)|^4527 ≤ (1299530677781/12500000000000 : ℝ)^3503
        have hw : |(-1734832089/10000000000 : ℝ)|=(1734832089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1363831147/2500000000 : ℝ)|^4527 ≤ (45697007835219/100000000000000 : ℝ)^3503
        have hw : |(1363831147/2500000000 : ℝ)|=(1363831147/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_s2_6 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644601131/5000000000 : ℝ)*x 0 + (1091064767/2000000000 : ℝ)*x 1 + (-346966389/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644601131/5000000000 : ℝ)^4527 ≤ (2195337799789/5000000000000 : ℝ)^3503 := by
    have hnat : (2644601131 : ℕ)^4527*5000000000000^3503 ≤ 2195337799789^3503*5000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644601131 5000000000 2195337799789 5000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1091064767/2000000000 : ℝ)^4527 ≤ (45696999683813/100000000000000 : ℝ)^3503 := by
    have hnat : (1091064767 : ℕ)^4527*100000000000000^3503 ≤ 45696999683813^3503*2000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091064767 2000000000 45696999683813 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (346966389/2000000000 : ℝ)^4527 ≤ (207924886141/2000000000000 : ℝ)^3503 := by
    have hnat : (346966389 : ℕ)^4527*2000000000000^3503 ≤ 207924886141^3503*2000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      346966389 2000000000 207924886141 2000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644601131/5000000000 : ℝ), (1091064767/2000000000 : ℝ), (-346966389/2000000000 : ℝ)] ![(2195337799789/5000000000000 : ℝ), (45696999683813/100000000000000 : ℝ), (207924886141/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644601131/5000000000 : ℝ)|^4527 ≤ (2195337799789/5000000000000 : ℝ)^3503
        have hw : |(2644601131/5000000000 : ℝ)|=(2644601131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1091064767/2000000000 : ℝ)|^4527 ≤ (45696999683813/100000000000000 : ℝ)^3503
        have hw : |(1091064767/2000000000 : ℝ)|=(1091064767/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-346966389/2000000000 : ℝ)|^4527 ≤ (207924886141/2000000000000 : ℝ)^3503
        have hw : |(-346966389/2000000000 : ℝ)|=(346966389/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_s2_7 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4265998771/10000000000 : ℝ)*x 0 + (4567169481/10000000000 : ℝ)*x 1 + (3982036469/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4265998771/10000000000 : ℝ)^4527 ≤ (16627925418013/50000000000000 : ℝ)^3503 := by
    have hnat : (4265998771 : ℕ)^4527*50000000000000^3503 ≤ 16627925418013^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4265998771 10000000000 16627925418013 50000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4567169481/10000000000 : ℝ)^4527 ≤ (4540094514929/12500000000000 : ℝ)^3503 := by
    have hnat : (4567169481 : ℕ)^4527*12500000000000^3503 ≤ 4540094514929^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4567169481 10000000000 4540094514929 12500000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3982036469/10000000000 : ℝ)^4527 ≤ (30423393021143/100000000000000 : ℝ)^3503 := by
    have hnat : (3982036469 : ℕ)^4527*100000000000000^3503 ≤ 30423393021143^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3982036469 10000000000 30423393021143 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4265998771/10000000000 : ℝ), (4567169481/10000000000 : ℝ), (3982036469/10000000000 : ℝ)] ![(16627925418013/50000000000000 : ℝ), (4540094514929/12500000000000 : ℝ), (30423393021143/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4265998771/10000000000 : ℝ)|^4527 ≤ (16627925418013/50000000000000 : ℝ)^3503
        have hw : |(4265998771/10000000000 : ℝ)|=(4265998771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4567169481/10000000000 : ℝ)|^4527 ≤ (4540094514929/12500000000000 : ℝ)^3503
        have hw : |(4567169481/10000000000 : ℝ)|=(4567169481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3982036469/10000000000 : ℝ)|^4527 ≤ (30423393021143/100000000000000 : ℝ)^3503
        have hw : |(3982036469/10000000000 : ℝ)|=(3982036469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1515_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163618979/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (183/1000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2099/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2093/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3197/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (183/1000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2099/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (183/1000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2099/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (183/1000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2099/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (183/1000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2099/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (183/1000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2099/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (183/1000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2099/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2099/25000 : ℝ) ^ (4525/1024 : ℝ) ≤ (880045064998091/50000000000000000000 : ℝ) := by
    have hpowers : (2099/25000 : ℝ)^4525 ≤ (880045064998091/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2099 : ℕ)^4525*50000000000000000000^1024 ≤ 880045064998091^1024*25000^4525 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2099 25000 880045064998091 50000000000000000000 4525 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2099/25000 : ℝ)) (X := (880045064998091/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4525 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (183/1000 : ℝ) ^ (4525/1024 : ℝ) ≤ (13764223275804813/25000000000000000000 : ℝ) := by
    have hpowers : (183/1000 : ℝ)^4525 ≤ (13764223275804813/25000000000000000000 : ℝ)^1024 := by
      have hnat : (183 : ℕ)^4525*25000000000000000000^1024 ≤ 13764223275804813^1024*1000^4525 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        183 1000 13764223275804813 25000000000000000000 4525 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (183/1000 : ℝ)) (X := (13764223275804813/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4525 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000880045064998091/25000000000000000000 : ℝ) ≤ (10000079660011039/10000000000000000 : ℝ) ^ (4525/1024 : ℝ) := by
    have hpowers : (25000880045064998091/25000000000000000000 : ℝ)^1024 ≤ (10000079660011039/10000000000000000 : ℝ)^4525 := by
      have hnat : (25000880045064998091 : ℕ)^1024*10000000000000000^4525 ≤ 10000079660011039^4525*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000880045064998091 25000000000000000000 10000079660011039 10000000000000000 1024 4525 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000079660011039/10000000000000000 : ℝ)) (X := (25000880045064998091/25000000000000000000 : ℝ)) (by norm_num) 4525 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50028408491616607717/50000000000000000000 : ℝ) ≤ (10001285476402371/10000000000000000 : ℝ) ^ (4525/1024 : ℝ) := by
    have hpowers : (50028408491616607717/50000000000000000000 : ℝ)^1024 ≤ (10001285476402371/10000000000000000 : ℝ)^4525 := by
      have hnat : (50028408491616607717 : ℕ)^1024*10000000000000000^4525 ≤ 10001285476402371^4525*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50028408491616607717 50000000000000000000 10001285476402371 10000000000000000 1024 4525 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001285476402371/10000000000000000 : ℝ)) (X := (50028408491616607717/50000000000000000000 : ℝ)) (by norm_num) 4525 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12513764223275804813/12500000000000000000 : ℝ) ≤ (10002491292793703/10000000000000000 : ℝ) ^ (4525/1024 : ℝ) := by
    have hpowers : (12513764223275804813/12500000000000000000 : ℝ)^1024 ≤ (10002491292793703/10000000000000000 : ℝ)^4525 := by
      have hnat : (12513764223275804813 : ℕ)^1024*10000000000000000^4525 ≤ 10002491292793703^4525*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12513764223275804813 12500000000000000000 10002491292793703 10000000000000000 1024 4525 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002491292793703/10000000000000000 : ℝ)) (X := (12513764223275804813/12500000000000000000 : ℝ)) (by norm_num) 4525 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(880045064998091/50000000000000000000 : ℝ) ≤ ((6188783805244130207/6190000000000000000 : ℝ)+2*(301454097833/247600000000000 : ℝ)*(2099/25000 : ℝ))^(4525/1024 : ℝ) := by
    rw [show (6188783805244130207/6190000000000000000 : ℝ)+2*(301454097833/247600000000000 : ℝ)*(2099/25000 : ℝ)=(10000079660011039/10000000000000000 : ℝ) by norm_num, show 1+2*(880045064998091/50000000000000000000 : ℝ)=(25000880045064998091/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13764223275804813/25000000000000000000 : ℝ)+(880045064998091/50000000000000000000 : ℝ) ≤ ((6188783805244130207/6190000000000000000 : ℝ)+(301454097833/247600000000000 : ℝ)*((183/1000 : ℝ)+(2099/25000 : ℝ)))^(4525/1024 : ℝ) := by
    rw [show (6188783805244130207/6190000000000000000 : ℝ)+(301454097833/247600000000000 : ℝ)*((183/1000 : ℝ)+(2099/25000 : ℝ))=(10001285476402371/10000000000000000 : ℝ) by norm_num, show 1+(13764223275804813/25000000000000000000 : ℝ)+(880045064998091/50000000000000000000 : ℝ)=(50028408491616607717/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13764223275804813/25000000000000000000 : ℝ) ≤ ((6188783805244130207/6190000000000000000 : ℝ)+2*(301454097833/247600000000000 : ℝ)*(183/1000 : ℝ))^(4525/1024 : ℝ) := by
    rw [show (6188783805244130207/6190000000000000000 : ℝ)+2*(301454097833/247600000000000 : ℝ)*(183/1000 : ℝ)=(10002491292793703/10000000000000000 : ℝ) by norm_num, show 1+2*(13764223275804813/25000000000000000000 : ℝ)=(12513764223275804813/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6188783805244130207/6190000000000000000 : ℝ)*(X 1 0+X 2 0)+(301454097833/247600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4525/1024 : ℝ)) (lo := (2099/25000 : ℝ)) (hi := (183/1000 : ℝ)) (c := (6188783805244130207/6190000000000000000 : ℝ)) (alpha := (301454097833/247600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6188783805244130207/6190000000000000000 : ℝ)*(X 0 1+X 2 1)+(301454097833/247600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4525/1024 : ℝ)) (lo := (2099/25000 : ℝ)) (hi := (183/1000 : ℝ)) (c := (6188783805244130207/6190000000000000000 : ℝ)) (alpha := (301454097833/247600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6188783805244130207/6190000000000000000 : ℝ)*(X 0 2+X 1 2)+(301454097833/247600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4525/1024 : ℝ)) (lo := (2099/25000 : ℝ)) (hi := (183/1000 : ℝ)) (c := (6188783805244130207/6190000000000000000 : ℝ)) (alpha := (301454097833/247600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-371948537/2000000000 : ℝ)*X 0 0+(2728482079/5000000000 : ℝ)*X 0 1+(1299050099/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((6697129/12500000 : ℝ)*X 1 0+(-398790969/2000000000 : ℝ)*X 1 1+(259810053/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2678852023/5000000000 : ℝ)*X 2 0+(129905013/250000000 : ℝ)*X 2 1+(-199395443/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1066470343/2500000000 : ℝ)*X 0 0+(3978309171/10000000000 : ℝ)*X 0 1+(1142716127/2500000000 : ℝ)*X 0 2+(1066470343/2500000000 : ℝ)*X 1 0+(3978309171/10000000000 : ℝ)*X 1 1+(1142716127/2500000000 : ℝ)*X 1 2+(1066470343/2500000000 : ℝ)*X 2 0+(3978309171/10000000000 : ℝ)*X 2 1+(1142716127/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-929896417/5000000000 : ℝ)*X 0 0+(324864209/625000000 : ℝ)*X 0 1+(218212943/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2644600699/5000000000 : ℝ)*X 1 0+(-1734832089/10000000000 : ℝ)*X 1 1+(1363831147/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2644601131/5000000000 : ℝ)*X 2 0+(1091064767/2000000000 : ℝ)*X 2 1+(-346966389/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4265998771/10000000000 : ℝ)*X 0 0+(4567169481/10000000000 : ℝ)*X 0 1+(3982036469/10000000000 : ℝ)*X 0 2+(4265998771/10000000000 : ℝ)*X 1 0+(4567169481/10000000000 : ℝ)*X 1 1+(3982036469/10000000000 : ℝ)*X 1 2+(4265998771/10000000000 : ℝ)*X 2 0+(4567169481/10000000000 : ℝ)*X 2 1+(3982036469/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (177641369922527367575232957/38687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (539085967/50000000000000 : ℝ)*(base19) + (664318553/50000000000000 : ℝ)*(base23) + (67079071/100000000000000 : ℝ)*(upper3) + (23780417/12500000000000 : ℝ)*(upper4) + (64853597/25000000000000 : ℝ)*(upper5) + (345160038351917/12500000000000 : ℝ)*(major0) + (345160038351917/12500000000000 : ℝ)*(major1) + (345160038351917/12500000000000 : ℝ)*(major2) + (23968155408381/625000000000 : ℝ)*(sp0) + (1917465506657287/50000000000000 : ℝ)*(sp1) + (1917465381424701/50000000000000 : ℝ)*(sp2) + (421904255244841/25000000000000 : ℝ)*(sp3) + (6806536387/25000000000000 : ℝ)*(sp4) + (11348108147/100000000000000 : ℝ)*(sp7) + (168762836908751/10000000000000 : ℝ)*(f.failure) + (958733022871627/25000000000000 : ℝ)*(f.sum) + (10438272511987/3095000000000000000000000000 : ℝ)*base65 + (60808643392956819/77375000000000000000000000000000 : ℝ)*base67 + (611143322565543181/77375000000000000000000000000000 : ℝ)*base70 + (798877440538206819/77375000000000000000000000000000 : ℝ)*base71 + (2473030626227/3095000000000000000000000000 : ℝ)*base73 + (1084642279743043181/77375000000000000000000000000000 : ℝ)*base76 + (118607740130293181/77375000000000000000000000000000 : ℝ)*base78 + (176462788221043181/77375000000000000000000000000000 : ℝ)*base80 + (4784363917803/3095000000000000000000000000 : ℝ)*base82 + (5214771/1000000000000000000000 : ℝ)*base90 + (5214771/1000000000000000000000 : ℝ)*base92 + (5214771/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (712603138564894709537689959/77375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (84880387/100000000000000 : ℝ)*(base23) + (44501107/12500000000000 : ℝ)*(lower2) + (34580241/20000000000000 : ℝ)*(upper3) + (67709759/100000000000000 : ℝ)*(lower4) + (1398145198004521/50000000000000 : ℝ)*(major0) + (1398145198004521/50000000000000 : ℝ)*(major1) + (1398145198004521/50000000000000 : ℝ)*(major2) + (1063695839/12500000000000 : ℝ)*(sp1) + (4083614657/50000000000000 : ℝ)*(sp2) + (410071789/10000000000000 : ℝ)*(sp3) + (97088869704799/2500000000000 : ℝ)*(sp4) + (121360821207039/3125000000000 : ℝ)*(sp5) + (194177326804113/5000000000000 : ℝ)*(sp6) + (1709021596117097/100000000000000 : ℝ)*(sp7) + (427256424208747/25000000000000 : ℝ)*(f.failure) + (97088869704799/2500000000000 : ℝ)*(f.sum) + (45956715477863/6190000000000000000000000000 : ℝ)*base65 + (2306716655346990847/309500000000000000000000000000000 : ℝ)*base67 + (4444781180049990847/309500000000000000000000000000000 : ℝ)*base69 + (4058558495248990847/309500000000000000000000000000000 : ℝ)*base71 + (10150258697343/6190000000000000000000000000 : ℝ)*base73 + (3741084789181990847/309500000000000000000000000000000 : ℝ)*base75 + (15911758093378990847/309500000000000000000000000000000 : ℝ)*base77 + (4148139869983009153/309500000000000000000000000000000 : ℝ)*base80 + (42426659585323/6190000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (17009313/2500000000000000000000 : ℝ)*base89 + (17009313/2500000000000000000000 : ℝ)*base91 + (17009313/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1515_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163618979/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (183/1000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2099/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2093/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3197/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1515_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1515_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163618979/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2093/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3197/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1515_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1515_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1515_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163618979/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2093/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3197/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1515_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
