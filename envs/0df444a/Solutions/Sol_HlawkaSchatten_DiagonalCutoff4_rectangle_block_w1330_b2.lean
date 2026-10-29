-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1330_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:01:53.61577+00:00
-- url     : https://prove2.me/submissions/6864dc2a-95ad-45e6-9b7e-51093c0f0c82

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
theorem support_rectangle_w1330_s6_0 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-51359401/250000000 : ℝ)*x 0 + (2706673177/5000000000 : ℝ)*x 1 + (5244216699/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (51359401/250000000 : ℝ)^2145 ≤ (6253917797111/50000000000000 : ℝ)^1633 := by
    have hnat : (51359401 : ℕ)^2145*50000000000000^1633 ≤ 6253917797111^1633*250000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51359401 250000000 6253917797111 50000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2706673177/5000000000 : ℝ)^2145 ≤ (44657915988731/100000000000000 : ℝ)^1633 := by
    have hnat : (2706673177 : ℕ)^2145*100000000000000^1633 ≤ 44657915988731^1633*5000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706673177 5000000000 44657915988731 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244216699/10000000000 : ℝ)^2145 ≤ (21417124201457/50000000000000 : ℝ)^1633 := by
    have hnat : (5244216699 : ℕ)^2145*50000000000000^1633 ≤ 21417124201457^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244216699 10000000000 21417124201457 50000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-51359401/250000000 : ℝ), (2706673177/5000000000 : ℝ), (5244216699/10000000000 : ℝ)] ![(6253917797111/50000000000000 : ℝ), (44657915988731/100000000000000 : ℝ), (21417124201457/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-51359401/250000000 : ℝ)|^2145 ≤ (6253917797111/50000000000000 : ℝ)^1633
        have hw : |(-51359401/250000000 : ℝ)|=(51359401/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2706673177/5000000000 : ℝ)|^2145 ≤ (44657915988731/100000000000000 : ℝ)^1633
        have hw : |(2706673177/5000000000 : ℝ)|=(2706673177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244216699/10000000000 : ℝ)|^2145 ≤ (21417124201457/50000000000000 : ℝ)^1633
        have hw : |(5244216699/10000000000 : ℝ)|=(5244216699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1330_s6_1 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5349207653/10000000000 : ℝ)*x 0 + (-2140558877/10000000000 : ℝ)*x 1 + (2622108361/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349207653/10000000000 : ℝ)^2145 ≤ (2747762241493/6250000000000 : ℝ)^1633 := by
    have hnat : (5349207653 : ℕ)^2145*6250000000000^1633 ≤ 2747762241493^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349207653 10000000000 2747762241493 6250000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2140558877/10000000000 : ℝ)^2145 ≤ (13201555472389/100000000000000 : ℝ)^1633 := by
    have hnat : (2140558877 : ℕ)^2145*100000000000000^1633 ≤ 13201555472389^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2140558877 10000000000 13201555472389 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622108361/5000000000 : ℝ)^2145 ≤ (42834248649677/100000000000000 : ℝ)^1633 := by
    have hnat : (2622108361 : ℕ)^2145*100000000000000^1633 ≤ 42834248649677^1633*5000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622108361 5000000000 42834248649677 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349207653/10000000000 : ℝ), (-2140558877/10000000000 : ℝ), (2622108361/5000000000 : ℝ)] ![(2747762241493/6250000000000 : ℝ), (13201555472389/100000000000000 : ℝ), (42834248649677/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349207653/10000000000 : ℝ)|^2145 ≤ (2747762241493/6250000000000 : ℝ)^1633
        have hw : |(5349207653/10000000000 : ℝ)|=(5349207653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2140558877/10000000000 : ℝ)|^2145 ≤ (13201555472389/100000000000000 : ℝ)^1633
        have hw : |(-2140558877/10000000000 : ℝ)|=(2140558877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622108361/5000000000 : ℝ)|^2145 ≤ (42834248649677/100000000000000 : ℝ)^1633
        have hw : |(2622108361/5000000000 : ℝ)|=(2622108361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1330_s6_2 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5349207591/10000000000 : ℝ)*x 0 + (1311054203/2500000000 : ℝ)*x 1 + (-53513971/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349207591/10000000000 : ℝ)^2145 ≤ (21982097597277/50000000000000 : ℝ)^1633 := by
    have hnat : (5349207591 : ℕ)^2145*50000000000000^1633 ≤ 21982097597277^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349207591 10000000000 21982097597277 50000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311054203/2500000000 : ℝ)^2145 ≤ (4283424961527/10000000000000 : ℝ)^1633 := by
    have hnat : (1311054203 : ℕ)^2145*10000000000000^1633 ≤ 4283424961527^1633*2500000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311054203 2500000000 4283424961527 10000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (53513971/250000000 : ℝ)^2145 ≤ (3300388793163/25000000000000 : ℝ)^1633 := by
    have hnat : (53513971 : ℕ)^2145*25000000000000^1633 ≤ 3300388793163^1633*250000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53513971 250000000 3300388793163 25000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349207591/10000000000 : ℝ), (1311054203/2500000000 : ℝ), (-53513971/250000000 : ℝ)] ![(21982097597277/50000000000000 : ℝ), (4283424961527/10000000000000 : ℝ), (3300388793163/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349207591/10000000000 : ℝ)|^2145 ≤ (21982097597277/50000000000000 : ℝ)^1633
        have hw : |(5349207591/10000000000 : ℝ)|=(5349207591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311054203/2500000000 : ℝ)|^2145 ≤ (4283424961527/10000000000000 : ℝ)^1633
        have hw : |(1311054203/2500000000 : ℝ)|=(1311054203/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-53513971/250000000 : ℝ)|^2145 ≤ (3300388793163/25000000000000 : ℝ)^1633
        have hw : |(-53513971/250000000 : ℝ)|=(53513971/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1330_s6_3 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4329764673/10000000000 : ℝ)*x 0 + (2078405407/5000000000 : ℝ)*x 1 + (4509465967/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4329764673/10000000000 : ℝ)^2145 ≤ (8325756869591/25000000000000 : ℝ)^1633 := by
    have hnat : (4329764673 : ℕ)^2145*25000000000000^1633 ≤ 8325756869591^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4329764673 10000000000 8325756869591 25000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2078405407/5000000000 : ℝ)^2145 ≤ (1262667110461/4000000000000 : ℝ)^1633 := by
    have hnat : (2078405407 : ℕ)^2145*4000000000000^1633 ≤ 1262667110461^1633*5000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2078405407 5000000000 1262667110461 4000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4509465967/10000000000 : ℝ)^2145 ≤ (35130294739567/100000000000000 : ℝ)^1633 := by
    have hnat : (4509465967 : ℕ)^2145*100000000000000^1633 ≤ 35130294739567^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4509465967 10000000000 35130294739567 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4329764673/10000000000 : ℝ), (2078405407/5000000000 : ℝ), (4509465967/10000000000 : ℝ)] ![(8325756869591/25000000000000 : ℝ), (1262667110461/4000000000000 : ℝ), (35130294739567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4329764673/10000000000 : ℝ)|^2145 ≤ (8325756869591/25000000000000 : ℝ)^1633
        have hw : |(4329764673/10000000000 : ℝ)|=(4329764673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2078405407/5000000000 : ℝ)|^2145 ≤ (1262667110461/4000000000000 : ℝ)^1633
        have hw : |(2078405407/5000000000 : ℝ)|=(2078405407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4509465967/10000000000 : ℝ)|^2145 ≤ (35130294739567/100000000000000 : ℝ)^1633
        have hw : |(4509465967/10000000000 : ℝ)|=(4509465967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1330_s6_4 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-513597233/2500000000 : ℝ)*x 0 + (1311205407/2500000000 : ℝ)*x 1 + (5412737879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (513597233/2500000000 : ℝ)^2145 ≤ (6253969347751/50000000000000 : ℝ)^1633 := by
    have hnat : (513597233 : ℕ)^2145*50000000000000^1633 ≤ 6253969347751^1633*2500000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513597233 2500000000 6253969347751 50000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311205407/2500000000 : ℝ)^2145 ≤ (10710184672441/25000000000000 : ℝ)^1633 := by
    have hnat : (1311205407 : ℕ)^2145*25000000000000^1633 ≤ 10710184672441^1633*2500000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311205407 2500000000 10710184672441 25000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5412737879/10000000000 : ℝ)^2145 ≤ (22325661298829/50000000000000 : ℝ)^1633 := by
    have hnat : (5412737879 : ℕ)^2145*50000000000000^1633 ≤ 22325661298829^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412737879 10000000000 22325661298829 50000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-513597233/2500000000 : ℝ), (1311205407/2500000000 : ℝ), (5412737879/10000000000 : ℝ)] ![(6253969347751/50000000000000 : ℝ), (10710184672441/25000000000000 : ℝ), (22325661298829/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-513597233/2500000000 : ℝ)|^2145 ≤ (6253969347751/50000000000000 : ℝ)^1633
        have hw : |(-513597233/2500000000 : ℝ)|=(513597233/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311205407/2500000000 : ℝ)|^2145 ≤ (10710184672441/25000000000000 : ℝ)^1633
        have hw : |(1311205407/2500000000 : ℝ)|=(1311205407/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5412737879/10000000000 : ℝ)|^2145 ≤ (22325661298829/50000000000000 : ℝ)^1633
        have hw : |(5412737879/10000000000 : ℝ)|=(5412737879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1330_s6_5 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1326426287/2500000000 : ℝ)*x 0 + (-1972037273/10000000000 : ℝ)*x 1 + (216509507/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326426287/2500000000 : ℝ)^2145 ≤ (43495155756637/100000000000000 : ℝ)^1633 := by
    have hnat : (1326426287 : ℕ)^2145*100000000000000^1633 ≤ 43495155756637^1633*2500000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326426287 2500000000 43495155756637 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1972037273/10000000000 : ℝ)^2145 ≤ (11853523837993/100000000000000 : ℝ)^1633 := by
    have hnat : (1972037273 : ℕ)^2145*100000000000000^1633 ≤ 11853523837993^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1972037273 10000000000 11853523837993 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216509507/400000000 : ℝ)^2145 ≤ (1395353762099/3125000000000 : ℝ)^1633 := by
    have hnat : (216509507 : ℕ)^2145*3125000000000^1633 ≤ 1395353762099^1633*400000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216509507 400000000 1395353762099 3125000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326426287/2500000000 : ℝ), (-1972037273/10000000000 : ℝ), (216509507/400000000 : ℝ)] ![(43495155756637/100000000000000 : ℝ), (11853523837993/100000000000000 : ℝ), (1395353762099/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326426287/2500000000 : ℝ)|^2145 ≤ (43495155756637/100000000000000 : ℝ)^1633
        have hw : |(1326426287/2500000000 : ℝ)|=(1326426287/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1972037273/10000000000 : ℝ)|^2145 ≤ (11853523837993/100000000000000 : ℝ)^1633
        have hw : |(-1972037273/10000000000 : ℝ)|=(1972037273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216509507/400000000 : ℝ)|^2145 ≤ (1395353762099/3125000000000 : ℝ)^1633
        have hw : |(216509507/400000000 : ℝ)|=(216509507/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1330_s6_6 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1061141027/2000000000 : ℝ)*x 0 + (2706368783/5000000000 : ℝ)*x 1 + (-1972037441/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061141027/2000000000 : ℝ)^2145 ≤ (10873788904163/25000000000000 : ℝ)^1633 := by
    have hnat : (1061141027 : ℕ)^2145*25000000000000^1633 ≤ 10873788904163^1633*2000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061141027 2000000000 10873788904163 25000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2706368783/5000000000 : ℝ)^2145 ≤ (44651319206073/100000000000000 : ℝ)^1633 := by
    have hnat : (2706368783 : ℕ)^2145*100000000000000^1633 ≤ 44651319206073^1633*5000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706368783 5000000000 44651319206073 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1972037441/10000000000 : ℝ)^2145 ≤ (5926762582209/50000000000000 : ℝ)^1633 := by
    have hnat : (1972037441 : ℕ)^2145*50000000000000^1633 ≤ 5926762582209^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1972037441 10000000000 5926762582209 50000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061141027/2000000000 : ℝ), (2706368783/5000000000 : ℝ), (-1972037441/10000000000 : ℝ)] ![(10873788904163/25000000000000 : ℝ), (44651319206073/100000000000000 : ℝ), (5926762582209/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061141027/2000000000 : ℝ)|^2145 ≤ (10873788904163/25000000000000 : ℝ)^1633
        have hw : |(1061141027/2000000000 : ℝ)|=(1061141027/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2706368783/5000000000 : ℝ)|^2145 ≤ (44651319206073/100000000000000 : ℝ)^1633
        have hw : |(2706368783/5000000000 : ℝ)|=(2706368783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1972037441/10000000000 : ℝ)|^2145 ≤ (5926762582209/50000000000000 : ℝ)^1633
        have hw : |(-1972037441/10000000000 : ℝ)|=(1972037441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1330_s6_7 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (8659581/20000000 : ℝ)*x 0 + (563525523/1250000000 : ℝ)*x 1 + (83161579/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8659581/20000000 : ℝ)^2145 ≤ (16651644207453/50000000000000 : ℝ)^1633 := by
    have hnat : (8659581 : ℕ)^2145*50000000000000^1633 ≤ 16651644207453^1633*20000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8659581 20000000 16651644207453 50000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (563525523/1250000000 : ℝ)^2145 ≤ (17558691817303/50000000000000 : ℝ)^1633 := by
    have hnat : (563525523 : ℕ)^2145*50000000000000^1633 ≤ 17558691817303^1633*1250000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563525523 1250000000 17558691817303 50000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (83161579/200000000 : ℝ)^2145 ≤ (31579327930581/100000000000000 : ℝ)^1633 := by
    have hnat : (83161579 : ℕ)^2145*100000000000000^1633 ≤ 31579327930581^1633*200000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83161579 200000000 31579327930581 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8659581/20000000 : ℝ), (563525523/1250000000 : ℝ), (83161579/200000000 : ℝ)] ![(16651644207453/50000000000000 : ℝ), (17558691817303/50000000000000 : ℝ), (31579327930581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8659581/20000000 : ℝ)|^2145 ≤ (16651644207453/50000000000000 : ℝ)^1633
        have hw : |(8659581/20000000 : ℝ)|=(8659581/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(563525523/1250000000 : ℝ)|^2145 ≤ (17558691817303/50000000000000 : ℝ)^1633
        have hw : |(563525523/1250000000 : ℝ)|=(563525523/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(83161579/200000000 : ℝ)|^2145 ≤ (31579327930581/100000000000000 : ℝ)^1633
        have hw : |(83161579/200000000 : ℝ)|=(83161579/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1330_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154255973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14709/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1389/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (139/1250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (147/1000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14709/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1389/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14709/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1389/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14709/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1389/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14709/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1389/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14709/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1389/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14709/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1389/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1389/12500 : ℝ) ^ (4289/1024 : ℝ) ≤ (1259601427186213/12500000000000000000 : ℝ) := by
    have hpowers : (1389/12500 : ℝ)^4289 ≤ (1259601427186213/12500000000000000000 : ℝ)^1024 := by
      have hnat : (1389 : ℕ)^4289*12500000000000000000^1024 ≤ 1259601427186213^1024*12500^4289 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1389 12500 1259601427186213 12500000000000000000 4289 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1389/12500 : ℝ)) (X := (1259601427186213/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4289 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14709/100000 : ℝ) ^ (4289/1024 : ℝ) ≤ (16308406549214159/50000000000000000000 : ℝ) := by
    have hpowers : (14709/100000 : ℝ)^4289 ≤ (16308406549214159/50000000000000000000 : ℝ)^1024 := by
      have hnat : (14709 : ℕ)^4289*50000000000000000000^1024 ≤ 16308406549214159^1024*100000^4289 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14709 100000 16308406549214159 50000000000000000000 4289 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14709/100000 : ℝ)) (X := (16308406549214159/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4289 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251259601427186213/6250000000000000000 : ℝ) ≤ (10000481131426639/10000000000000000 : ℝ) ^ (4289/1024 : ℝ) := by
    have hpowers : (6251259601427186213/6250000000000000000 : ℝ)^1024 ≤ (10000481131426639/10000000000000000 : ℝ)^4289 := by
      have hnat : (6251259601427186213 : ℕ)^1024*10000000000000000^4289 ≤ 10000481131426639^4289*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251259601427186213 6250000000000000000 10000481131426639 10000000000000000 1024 4289 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000481131426639/10000000000000000 : ℝ)) (X := (6251259601427186213/6250000000000000000 : ℝ)) (by norm_num) 4289 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50021346812257959011/50000000000000000000 : ℝ) ≤ (10001019145930381/10000000000000000 : ℝ) ^ (4289/1024 : ℝ) := by
    have hpowers : (50021346812257959011/50000000000000000000 : ℝ)^1024 ≤ (10001019145930381/10000000000000000 : ℝ)^4289 := by
      have hnat : (50021346812257959011 : ℕ)^1024*10000000000000000^4289 ≤ 10001019145930381^4289*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021346812257959011 50000000000000000000 10001019145930381 10000000000000000 1024 4289 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001019145930381/10000000000000000 : ℝ)) (X := (50021346812257959011/50000000000000000000 : ℝ)) (by norm_num) 4289 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016308406549214159/25000000000000000000 : ℝ) ≤ (10001557160434123/10000000000000000 : ℝ) ^ (4289/1024 : ℝ) := by
    have hpowers : (25016308406549214159/25000000000000000000 : ℝ)^1024 ≤ (10001557160434123/10000000000000000 : ℝ)^4289 := by
      have hnat : (25016308406549214159 : ℕ)^1024*10000000000000000^4289 ≤ 10001557160434123^4289*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016308406549214159 25000000000000000000 10001557160434123 10000000000000000 1024 4289 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001557160434123/10000000000000000 : ℝ)) (X := (25016308406549214159/25000000000000000000 : ℝ)) (by norm_num) 4289 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1259601427186213/12500000000000000000 : ℝ) ≤ ((479463650605472777/479600000000000000 : ℝ)+2*(89669083957/59950000000000 : ℝ)*(1389/12500 : ℝ))^(4289/1024 : ℝ) := by
    rw [show (479463650605472777/479600000000000000 : ℝ)+2*(89669083957/59950000000000 : ℝ)*(1389/12500 : ℝ)=(10000481131426639/10000000000000000 : ℝ) by norm_num, show 1+2*(1259601427186213/12500000000000000000 : ℝ)=(6251259601427186213/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16308406549214159/50000000000000000000 : ℝ)+(1259601427186213/12500000000000000000 : ℝ) ≤ ((479463650605472777/479600000000000000 : ℝ)+(89669083957/59950000000000 : ℝ)*((14709/100000 : ℝ)+(1389/12500 : ℝ)))^(4289/1024 : ℝ) := by
    rw [show (479463650605472777/479600000000000000 : ℝ)+(89669083957/59950000000000 : ℝ)*((14709/100000 : ℝ)+(1389/12500 : ℝ))=(10001019145930381/10000000000000000 : ℝ) by norm_num, show 1+(16308406549214159/50000000000000000000 : ℝ)+(1259601427186213/12500000000000000000 : ℝ)=(50021346812257959011/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16308406549214159/50000000000000000000 : ℝ) ≤ ((479463650605472777/479600000000000000 : ℝ)+2*(89669083957/59950000000000 : ℝ)*(14709/100000 : ℝ))^(4289/1024 : ℝ) := by
    rw [show (479463650605472777/479600000000000000 : ℝ)+2*(89669083957/59950000000000 : ℝ)*(14709/100000 : ℝ)=(10001557160434123/10000000000000000 : ℝ) by norm_num, show 1+2*(16308406549214159/50000000000000000000 : ℝ)=(25016308406549214159/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (479463650605472777/479600000000000000 : ℝ)*(X 1 0+X 2 0)+(89669083957/59950000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4289/1024 : ℝ)) (lo := (1389/12500 : ℝ)) (hi := (14709/100000 : ℝ)) (c := (479463650605472777/479600000000000000 : ℝ)) (alpha := (89669083957/59950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (479463650605472777/479600000000000000 : ℝ)*(X 0 1+X 2 1)+(89669083957/59950000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4289/1024 : ℝ)) (lo := (1389/12500 : ℝ)) (hi := (14709/100000 : ℝ)) (c := (479463650605472777/479600000000000000 : ℝ)) (alpha := (89669083957/59950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (479463650605472777/479600000000000000 : ℝ)*(X 0 2+X 1 2)+(89669083957/59950000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4289/1024 : ℝ)) (lo := (1389/12500 : ℝ)) (hi := (14709/100000 : ℝ)) (c := (479463650605472777/479600000000000000 : ℝ)) (alpha := (89669083957/59950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-51359401/250000000 : ℝ)*X 0 0+(2706673177/5000000000 : ℝ)*X 0 1+(5244216699/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349207653/10000000000 : ℝ)*X 1 0+(-2140558877/10000000000 : ℝ)*X 1 1+(2622108361/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349207591/10000000000 : ℝ)*X 2 0+(1311054203/2500000000 : ℝ)*X 2 1+(-53513971/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4329764673/10000000000 : ℝ)*X 0 0+(2078405407/5000000000 : ℝ)*X 0 1+(4509465967/10000000000 : ℝ)*X 0 2+(4329764673/10000000000 : ℝ)*X 1 0+(2078405407/5000000000 : ℝ)*X 1 1+(4509465967/10000000000 : ℝ)*X 1 2+(4329764673/10000000000 : ℝ)*X 2 0+(2078405407/5000000000 : ℝ)*X 2 1+(4509465967/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-513597233/2500000000 : ℝ)*X 0 0+(1311205407/2500000000 : ℝ)*X 0 1+(5412737879/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326426287/2500000000 : ℝ)*X 1 0+(-1972037273/10000000000 : ℝ)*X 1 1+(216509507/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1061141027/2000000000 : ℝ)*X 2 0+(2706368783/5000000000 : ℝ)*X 2 1+(-1972037441/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((8659581/20000000 : ℝ)*X 0 0+(563525523/1250000000 : ℝ)*X 0 1+(83161579/200000000 : ℝ)*X 0 2+(8659581/20000000 : ℝ)*X 1 0+(563525523/1250000000 : ℝ)*X 1 1+(83161579/200000000 : ℝ)*X 1 2+(8659581/20000000 : ℝ)*X 2 0+(563525523/1250000000 : ℝ)*X 2 1+(83161579/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (72502241723806195945432923/11990000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (997603529/100000000000000 : ℝ)*(base19) + (393952199/50000000000000 : ℝ)*(base23) + (2359809/3125000000000 : ℝ)*(lower2) + (133064661/100000000000000 : ℝ)*(upper3) + (15347003/25000000000000 : ℝ)*(upper5) + (4374158263560033/100000000000000 : ℝ)*(major0) + (4374158263560033/100000000000000 : ℝ)*(major1) + (4374158263560033/100000000000000 : ℝ)*(major2) + (5912646062049373/100000000000000 : ℝ)*(sp0) + (5912666128450469/100000000000000 : ℝ)*(sp1) + (7390832922687/125000000000 : ℝ)*(sp2) + (354454942418607/12500000000000 : ℝ)*(sp3) + (168512037/800000000000 : ℝ)*(sp4) + (2415038531/25000000000000 : ℝ)*(sp7) + (141782459975149/5000000000000 : ℝ)*(f.failure) + (2956333563026999/50000000000000 : ℝ)*(f.sum) + (3785473068251/2997500000000000000000000000 : ℝ)*base65 + (287142425761049641/47960000000000000000000000000000 : ℝ)*base67 + (24031383034470359/47960000000000000000000000000000 : ℝ)*base70 + (118492520934830359/47960000000000000000000000000000 : ℝ)*base72 + (37603092760597/5995000000000000000000000000 : ℝ)*base73 + (36538032901830359/47960000000000000000000000000000 : ℝ)*base76 + (281910194425110359/47960000000000000000000000000000 : ℝ)*base78 + (130181977436630359/47960000000000000000000000000000 : ℝ)*base80 + (2789533058461/2997500000000000000000000000 : ℝ)*base81 + (185023/500000000000000000000 : ℝ)*base90 + (185023/500000000000000000000 : ℝ)*base92 + (185023/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (38494597996118102924930301/23980000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2275406369/100000000000000 : ℝ)*(base19) + (2752316341/100000000000000 : ℝ)*(base23) + (63947777/25000000000000 : ℝ)*(upper2) + (163820499/100000000000000 : ℝ)*(upper3) + (49555699/20000000000000 : ℝ)*(upper5) + (4405732277002957/100000000000000 : ℝ)*(major0) + (4405732277002957/100000000000000 : ℝ)*(major1) + (4405732277002957/100000000000000 : ℝ)*(major2) + (11251998721/25000000000000 : ℝ)*(sp1) + (9230801171/20000000000000 : ℝ)*(sp2) + (1488836679242829/25000000000000 : ℝ)*(sp4) + (5955299433570063/100000000000000 : ℝ)*(sp5) + (37220611316557/625000000000 : ℝ)*(sp6) + (1428058891762641/50000000000000 : ℝ)*(sp7) + (1428058891762641/50000000000000 : ℝ)*(f.failure) + (1488836679242829/25000000000000 : ℝ)*(f.sum) + (11417165336931/2997500000000000000000000000 : ℝ)*base66 + (416751054335766411/47960000000000000000000000000000 : ℝ)*base68 + (186202074466646411/47960000000000000000000000000000 : ℝ)*base70 + (263785043846166411/47960000000000000000000000000000 : ℝ)*base72 + (32491615822197/5995000000000000000000000000 : ℝ)*base74 + (178806403098286411/47960000000000000000000000000000 : ℝ)*base76 + (327871350641006411/47960000000000000000000000000000 : ℝ)*base78 + (406864279322486411/47960000000000000000000000000000 : ℝ)*base80 + (11506362819701/2997500000000000000000000000 : ℝ)*base82 + (22504693/5000000000000000000000 : ℝ)*base89 + (22504693/5000000000000000000000 : ℝ)*base91 + (22504693/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1330_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154255973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14709/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1389/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (139/1250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (147/1000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1330_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1330_s7_0 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-513596789/2500000000 : ℝ)*x 0 + (5413274179/10000000000 : ℝ)*x 1 + (524428131/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (513596789/2500000000 : ℝ)^2145 ≤ (12507924492273/100000000000000 : ℝ)^1633 := by
    have hnat : (513596789 : ℕ)^2145*100000000000000^1633 ≤ 12507924492273^1633*2500000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513596789 2500000000 12507924492273 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5413274179/10000000000 : ℝ)^2145 ≤ (44657133893507/100000000000000 : ℝ)^1633 := by
    have hnat : (5413274179 : ℕ)^2145*100000000000000^1633 ≤ 44657133893507^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413274179 10000000000 44657133893507 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524428131/1000000000 : ℝ)^2145 ≤ (42834941603523/100000000000000 : ℝ)^1633 := by
    have hnat : (524428131 : ℕ)^2145*100000000000000^1633 ≤ 42834941603523^1633*1000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524428131 1000000000 42834941603523 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-513596789/2500000000 : ℝ), (5413274179/10000000000 : ℝ), (524428131/1000000000 : ℝ)] ![(12507924492273/100000000000000 : ℝ), (44657133893507/100000000000000 : ℝ), (42834941603523/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-513596789/2500000000 : ℝ)|^2145 ≤ (12507924492273/100000000000000 : ℝ)^1633
        have hw : |(-513596789/2500000000 : ℝ)|=(513596789/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5413274179/10000000000 : ℝ)|^2145 ≤ (44657133893507/100000000000000 : ℝ)^1633
        have hw : |(5413274179/10000000000 : ℝ)|=(5413274179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(524428131/1000000000 : ℝ)|^2145 ≤ (42834941603523/100000000000000 : ℝ)^1633
        have hw : |(524428131/1000000000 : ℝ)|=(524428131/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1330_s7_1 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1069837457/2000000000 : ℝ)*x 0 + (-535124139/2500000000 : ℝ)*x 1 + (327767767/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069837457/2000000000 : ℝ)^2145 ≤ (43963975977211/100000000000000 : ℝ)^1633 := by
    have hnat : (1069837457 : ℕ)^2145*100000000000000^1633 ≤ 43963975977211^1633*2000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069837457 2000000000 43963975977211 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (535124139/2500000000 : ℝ)^2145 ≤ (13201050611799/100000000000000 : ℝ)^1633 := by
    have hnat : (535124139 : ℕ)^2145*100000000000000^1633 ≤ 13201050611799^1633*2500000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535124139 2500000000 13201050611799 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (327767767/625000000 : ℝ)^2145 ≤ (42834973382389/100000000000000 : ℝ)^1633 := by
    have hnat : (327767767 : ℕ)^2145*100000000000000^1633 ≤ 42834973382389^1633*625000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327767767 625000000 42834973382389 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069837457/2000000000 : ℝ), (-535124139/2500000000 : ℝ), (327767767/625000000 : ℝ)] ![(43963975977211/100000000000000 : ℝ), (13201050611799/100000000000000 : ℝ), (42834973382389/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069837457/2000000000 : ℝ)|^2145 ≤ (43963975977211/100000000000000 : ℝ)^1633
        have hw : |(1069837457/2000000000 : ℝ)|=(1069837457/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-535124139/2500000000 : ℝ)|^2145 ≤ (13201050611799/100000000000000 : ℝ)^1633
        have hw : |(-535124139/2500000000 : ℝ)|=(535124139/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(327767767/625000000 : ℝ)|^2145 ≤ (42834973382389/100000000000000 : ℝ)^1633
        have hw : |(327767767/625000000 : ℝ)|=(327767767/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1330_s7_2 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5349189237/10000000000 : ℝ)*x 0 + (1311070579/2500000000 : ℝ)*x 1 + (-2140496547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349189237/10000000000 : ℝ)^2145 ≤ (5495499631299/12500000000000 : ℝ)^1633 := by
    have hnat : (5349189237 : ℕ)^2145*12500000000000^1633 ≤ 5495499631299^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349189237 10000000000 5495499631299 12500000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311070579/2500000000 : ℝ)^2145 ≤ (171339809587/400000000000 : ℝ)^1633 := by
    have hnat : (1311070579 : ℕ)^2145*400000000000^1633 ≤ 171339809587^1633*2500000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311070579 2500000000 171339809587 400000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2140496547/10000000000 : ℝ)^2145 ≤ (13201050538891/100000000000000 : ℝ)^1633 := by
    have hnat : (2140496547 : ℕ)^2145*100000000000000^1633 ≤ 13201050538891^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2140496547 10000000000 13201050538891 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349189237/10000000000 : ℝ), (1311070579/2500000000 : ℝ), (-2140496547/10000000000 : ℝ)] ![(5495499631299/12500000000000 : ℝ), (171339809587/400000000000 : ℝ), (13201050538891/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349189237/10000000000 : ℝ)|^2145 ≤ (5495499631299/12500000000000 : ℝ)^1633
        have hw : |(5349189237/10000000000 : ℝ)|=(5349189237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311070579/2500000000 : ℝ)|^2145 ≤ (171339809587/400000000000 : ℝ)^1633
        have hw : |(1311070579/2500000000 : ℝ)|=(1311070579/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2140496547/10000000000 : ℝ)|^2145 ≤ (13201050538891/100000000000000 : ℝ)^1633
        have hw : |(-2140496547/10000000000 : ℝ)|=(2140496547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1330_s7_3 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4329768251/10000000000 : ℝ)*x 0 + (166278317/400000000 : ℝ)*x 1 + (450931903/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4329768251/10000000000 : ℝ)^2145 ≤ (133212254511/400000000000 : ℝ)^1633 := by
    have hnat : (4329768251 : ℕ)^2145*400000000000^1633 ≤ 133212254511^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4329768251 10000000000 133212254511 400000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (166278317/400000000 : ℝ)^2145 ≤ (7892036297791/25000000000000 : ℝ)^1633 := by
    have hnat : (166278317 : ℕ)^2145*25000000000000^1633 ≤ 7892036297791^1633*400000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166278317 400000000 7892036297791 25000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (450931903/1000000000 : ℝ)^2145 ≤ (35128791158869/100000000000000 : ℝ)^1633 := by
    have hnat : (450931903 : ℕ)^2145*100000000000000^1633 ≤ 35128791158869^1633*1000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450931903 1000000000 35128791158869 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4329768251/10000000000 : ℝ), (166278317/400000000 : ℝ), (450931903/1000000000 : ℝ)] ![(133212254511/400000000000 : ℝ), (7892036297791/25000000000000 : ℝ), (35128791158869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4329768251/10000000000 : ℝ)|^2145 ≤ (133212254511/400000000000 : ℝ)^1633
        have hw : |(4329768251/10000000000 : ℝ)|=(4329768251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(166278317/400000000 : ℝ)|^2145 ≤ (7892036297791/25000000000000 : ℝ)^1633
        have hw : |(166278317/400000000 : ℝ)|=(166278317/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(450931903/1000000000 : ℝ)|^2145 ≤ (35128791158869/100000000000000 : ℝ)^1633
        have hw : |(450931903/1000000000 : ℝ)|=(450931903/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1330_s7_4 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2054397717/10000000000 : ℝ)*x 0 + (1311221913/2500000000 : ℝ)*x 1 + (270633301/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2054397717/10000000000 : ℝ)^2145 ≤ (12508008951959/100000000000000 : ℝ)^1633 := by
    have hnat : (2054397717 : ℕ)^2145*100000000000000^1633 ≤ 12508008951959^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2054397717 10000000000 12508008951959 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311221913/2500000000 : ℝ)^2145 ≤ (42841447075861/100000000000000 : ℝ)^1633 := by
    have hnat : (1311221913 : ℕ)^2145*100000000000000^1633 ≤ 42841447075861^1633*2500000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311221913 2500000000 42841447075861 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270633301/500000000 : ℝ)^2145 ≤ (11162635988519/25000000000000 : ℝ)^1633 := by
    have hnat : (270633301 : ℕ)^2145*25000000000000^1633 ≤ 11162635988519^1633*500000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270633301 500000000 11162635988519 25000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2054397717/10000000000 : ℝ), (1311221913/2500000000 : ℝ), (270633301/500000000 : ℝ)] ![(12508008951959/100000000000000 : ℝ), (42841447075861/100000000000000 : ℝ), (11162635988519/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2054397717/10000000000 : ℝ)|^2145 ≤ (12508008951959/100000000000000 : ℝ)^1633
        have hw : |(-2054397717/10000000000 : ℝ)|=(2054397717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311221913/2500000000 : ℝ)|^2145 ≤ (42841447075861/100000000000000 : ℝ)^1633
        have hw : |(1311221913/2500000000 : ℝ)|=(1311221913/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(270633301/500000000 : ℝ)|^2145 ≤ (11162635988519/25000000000000 : ℝ)^1633
        have hw : |(270633301/500000000 : ℝ)|=(270633301/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1330_s7_5 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1061144361/2000000000 : ℝ)*x 0 + (-1972113587/10000000000 : ℝ)*x 1 + (1082533103/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061144361/2000000000 : ℝ)^2145 ≤ (43495335120889/100000000000000 : ℝ)^1633 := by
    have hnat : (1061144361 : ℕ)^2145*100000000000000^1633 ≤ 43495335120889^1633*2000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061144361 2000000000 43495335120889 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1972113587/10000000000 : ℝ)^2145 ≤ (5927063185139/50000000000000 : ℝ)^1633 := by
    have hnat : (1972113587 : ℕ)^2145*50000000000000^1633 ≤ 5927063185139^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1972113587 10000000000 5927063185139 50000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082533103/2000000000 : ℝ)^2145 ≤ (11162634620513/25000000000000 : ℝ)^1633 := by
    have hnat : (1082533103 : ℕ)^2145*25000000000000^1633 ≤ 11162634620513^1633*2000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082533103 2000000000 11162634620513 25000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061144361/2000000000 : ℝ), (-1972113587/10000000000 : ℝ), (1082533103/2000000000 : ℝ)] ![(43495335120889/100000000000000 : ℝ), (5927063185139/50000000000000 : ℝ), (11162634620513/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061144361/2000000000 : ℝ)|^2145 ≤ (43495335120889/100000000000000 : ℝ)^1633
        have hw : |(1061144361/2000000000 : ℝ)|=(1061144361/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1972113587/10000000000 : ℝ)|^2145 ≤ (5927063185139/50000000000000 : ℝ)^1633
        have hw : |(-1972113587/10000000000 : ℝ)|=(1972113587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1082533103/2000000000 : ℝ)|^2145 ≤ (11162634620513/25000000000000 : ℝ)^1633
        have hw : |(1082533103/2000000000 : ℝ)|=(1082533103/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1330_s7_6 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652861081/5000000000 : ℝ)*x 0 + (5412665509/10000000000 : ℝ)*x 1 + (-197211311/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652861081/5000000000 : ℝ)^2145 ≤ (43495338965103/100000000000000 : ℝ)^1633 := by
    have hnat : (2652861081 : ℕ)^2145*100000000000000^1633 ≤ 43495338965103^1633*5000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652861081 5000000000 43495338965103 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5412665509/10000000000 : ℝ)^2145 ≤ (22325269208519/50000000000000 : ℝ)^1633 := by
    have hnat : (5412665509 : ℕ)^2145*50000000000000^1633 ≤ 22325269208519^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412665509 10000000000 22325269208519 50000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (197211311/1000000000 : ℝ)^2145 ≤ (2963530651033/25000000000000 : ℝ)^1633 := by
    have hnat : (197211311 : ℕ)^2145*25000000000000^1633 ≤ 2963530651033^1633*1000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197211311 1000000000 2963530651033 25000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652861081/5000000000 : ℝ), (5412665509/10000000000 : ℝ), (-197211311/1000000000 : ℝ)] ![(43495338965103/100000000000000 : ℝ), (22325269208519/50000000000000 : ℝ), (2963530651033/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652861081/5000000000 : ℝ)|^2145 ≤ (43495338965103/100000000000000 : ℝ)^1633
        have hw : |(2652861081/5000000000 : ℝ)|=(2652861081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5412665509/10000000000 : ℝ)|^2145 ≤ (22325269208519/50000000000000 : ℝ)^1633
        have hw : |(5412665509/10000000000 : ℝ)|=(5412665509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-197211311/1000000000 : ℝ)|^2145 ≤ (2963530651033/25000000000000 : ℝ)^1633
        have hw : |(-197211311/1000000000 : ℝ)|=(197211311/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1330_s7_7 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2164897761/5000000000 : ℝ)*x 0 + (4508060679/10000000000 : ℝ)*x 1 + (1039555263/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2164897761/5000000000 : ℝ)^2145 ≤ (16651669576733/50000000000000 : ℝ)^1633 := by
    have hnat : (2164897761 : ℕ)^2145*50000000000000^1633 ≤ 16651669576733^1633*5000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2164897761 5000000000 16651669576733 50000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4508060679/10000000000 : ℝ)^2145 ≤ (137171544147/390625000000 : ℝ)^1633 := by
    have hnat : (4508060679 : ℕ)^2145*390625000000^1633 ≤ 137171544147^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4508060679 10000000000 137171544147 390625000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1039555263/2500000000 : ℝ)^2145 ≤ (3158074553083/10000000000000 : ℝ)^1633 := by
    have hnat : (1039555263 : ℕ)^2145*10000000000000^1633 ≤ 3158074553083^1633*2500000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039555263 2500000000 3158074553083 10000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2164897761/5000000000 : ℝ), (4508060679/10000000000 : ℝ), (1039555263/2500000000 : ℝ)] ![(16651669576733/50000000000000 : ℝ), (137171544147/390625000000 : ℝ), (3158074553083/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2164897761/5000000000 : ℝ)|^2145 ≤ (16651669576733/50000000000000 : ℝ)^1633
        have hw : |(2164897761/5000000000 : ℝ)|=(2164897761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4508060679/10000000000 : ℝ)|^2145 ≤ (137171544147/390625000000 : ℝ)^1633
        have hw : |(4508060679/10000000000 : ℝ)|=(4508060679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1039555263/2500000000 : ℝ)|^2145 ≤ (3158074553083/10000000000000 : ℝ)^1633
        have hw : |(1039555263/2500000000 : ℝ)|=(1039555263/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1330_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154255973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (147/1000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (139/1250 : ℝ)*pair X i i ≤ pair X i h) :
    (11121/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14699/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (147/1000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (139/1250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (147/1000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (139/1250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (147/1000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (139/1250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (147/1000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (139/1250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (147/1000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (139/1250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (147/1000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (139/1250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (139/1250 : ℝ) ^ (4289/1024 : ℝ) ≤ (5053616276348327/50000000000000000000 : ℝ) := by
    have hpowers : (139/1250 : ℝ)^4289 ≤ (5053616276348327/50000000000000000000 : ℝ)^1024 := by
      have hnat : (139 : ℕ)^4289*50000000000000000000^1024 ≤ 5053616276348327^1024*1250^4289 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        139 1250 5053616276348327 50000000000000000000 4289 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (139/1250 : ℝ)) (X := (5053616276348327/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4289 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (147/1000 : ℝ) ^ (4289/1024 : ℝ) ≤ (4066663011450489/12500000000000000000 : ℝ) := by
    have hpowers : (147/1000 : ℝ)^4289 ≤ (4066663011450489/12500000000000000000 : ℝ)^1024 := by
      have hnat : (147 : ℕ)^4289*12500000000000000000^1024 ≤ 4066663011450489^1024*1000^4289 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        147 1000 4066663011450489 12500000000000000000 4289 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (147/1000 : ℝ)) (X := (4066663011450489/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4289 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005053616276348327/25000000000000000000 : ℝ) ≤ (10000482583814463/10000000000000000 : ℝ) ^ (4289/1024 : ℝ) := by
    have hpowers : (25005053616276348327/25000000000000000000 : ℝ)^1024 ≤ (10000482583814463/10000000000000000 : ℝ)^4289 := by
      have hnat : (25005053616276348327 : ℕ)^1024*10000000000000000^4289 ≤ 10000482583814463^4289*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005053616276348327 25000000000000000000 10000482583814463 10000000000000000 1024 4289 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000482583814463/10000000000000000 : ℝ)) (X := (25005053616276348327/25000000000000000000 : ℝ)) (by norm_num) 4289 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50021320268322150283/50000000000000000000 : ℝ) ≤ (312531808714607/312500000000000 : ℝ) ^ (4289/1024 : ℝ) := by
    have hpowers : (50021320268322150283/50000000000000000000 : ℝ)^1024 ≤ (312531808714607/312500000000000 : ℝ)^4289 := by
      have hnat : (50021320268322150283 : ℕ)^1024*312500000000000^4289 ≤ 312531808714607^4289*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021320268322150283 50000000000000000000 312531808714607 312500000000000 1024 4289 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312531808714607/312500000000000 : ℝ)) (X := (50021320268322150283/50000000000000000000 : ℝ)) (by norm_num) 4289 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254066663011450489/6250000000000000000 : ℝ) ≤ (2000310634784077/2000000000000000 : ℝ) ^ (4289/1024 : ℝ) := by
    have hpowers : (6254066663011450489/6250000000000000000 : ℝ)^1024 ≤ (2000310634784077/2000000000000000 : ℝ)^4289 := by
      have hnat : (6254066663011450489 : ℕ)^1024*2000000000000000^4289 ≤ 2000310634784077^4289*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254066663011450489 6250000000000000000 2000310634784077 2000000000000000 1024 4289 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000310634784077/2000000000000000 : ℝ)) (X := (6254066663011450489/6250000000000000000 : ℝ)) (by norm_num) 4289 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5053616276348327/50000000000000000000 : ℝ) ≤ ((357898226880779249/358000000000000000 : ℝ)+2*(535295052961/358000000000000 : ℝ)*(139/1250 : ℝ))^(4289/1024 : ℝ) := by
    rw [show (357898226880779249/358000000000000000 : ℝ)+2*(535295052961/358000000000000 : ℝ)*(139/1250 : ℝ)=(10000482583814463/10000000000000000 : ℝ) by norm_num, show 1+2*(5053616276348327/50000000000000000000 : ℝ)=(25005053616276348327/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4066663011450489/12500000000000000000 : ℝ)+(5053616276348327/50000000000000000000 : ℝ) ≤ ((357898226880779249/358000000000000000 : ℝ)+(535295052961/358000000000000 : ℝ)*((147/1000 : ℝ)+(139/1250 : ℝ)))^(4289/1024 : ℝ) := by
    rw [show (357898226880779249/358000000000000000 : ℝ)+(535295052961/358000000000000 : ℝ)*((147/1000 : ℝ)+(139/1250 : ℝ))=(312531808714607/312500000000000 : ℝ) by norm_num, show 1+(4066663011450489/12500000000000000000 : ℝ)+(5053616276348327/50000000000000000000 : ℝ)=(50021320268322150283/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4066663011450489/12500000000000000000 : ℝ) ≤ ((357898226880779249/358000000000000000 : ℝ)+2*(535295052961/358000000000000 : ℝ)*(147/1000 : ℝ))^(4289/1024 : ℝ) := by
    rw [show (357898226880779249/358000000000000000 : ℝ)+2*(535295052961/358000000000000 : ℝ)*(147/1000 : ℝ)=(2000310634784077/2000000000000000 : ℝ) by norm_num, show 1+2*(4066663011450489/12500000000000000000 : ℝ)=(6254066663011450489/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (357898226880779249/358000000000000000 : ℝ)*(X 1 0+X 2 0)+(535295052961/358000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4289/1024 : ℝ)) (lo := (139/1250 : ℝ)) (hi := (147/1000 : ℝ)) (c := (357898226880779249/358000000000000000 : ℝ)) (alpha := (535295052961/358000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (357898226880779249/358000000000000000 : ℝ)*(X 0 1+X 2 1)+(535295052961/358000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4289/1024 : ℝ)) (lo := (139/1250 : ℝ)) (hi := (147/1000 : ℝ)) (c := (357898226880779249/358000000000000000 : ℝ)) (alpha := (535295052961/358000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (357898226880779249/358000000000000000 : ℝ)*(X 0 2+X 1 2)+(535295052961/358000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4289/1024 : ℝ)) (lo := (139/1250 : ℝ)) (hi := (147/1000 : ℝ)) (c := (357898226880779249/358000000000000000 : ℝ)) (alpha := (535295052961/358000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-513596789/2500000000 : ℝ)*X 0 0+(5413274179/10000000000 : ℝ)*X 0 1+(524428131/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069837457/2000000000 : ℝ)*X 1 0+(-535124139/2500000000 : ℝ)*X 1 1+(327767767/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349189237/10000000000 : ℝ)*X 2 0+(1311070579/2500000000 : ℝ)*X 2 1+(-2140496547/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4329768251/10000000000 : ℝ)*X 0 0+(166278317/400000000 : ℝ)*X 0 1+(450931903/1000000000 : ℝ)*X 0 2+(4329768251/10000000000 : ℝ)*X 1 0+(166278317/400000000 : ℝ)*X 1 1+(450931903/1000000000 : ℝ)*X 1 2+(4329768251/10000000000 : ℝ)*X 2 0+(166278317/400000000 : ℝ)*X 2 1+(450931903/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2054397717/10000000000 : ℝ)*X 0 0+(1311221913/2500000000 : ℝ)*X 0 1+(270633301/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1061144361/2000000000 : ℝ)*X 1 0+(-1972113587/10000000000 : ℝ)*X 1 1+(1082533103/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652861081/5000000000 : ℝ)*X 2 0+(5412665509/10000000000 : ℝ)*X 2 1+(-197211311/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2164897761/5000000000 : ℝ)*X 0 0+(4508060679/10000000000 : ℝ)*X 0 1+(1039555263/2500000000 : ℝ)*X 0 2+(2164897761/5000000000 : ℝ)*X 1 0+(4508060679/10000000000 : ℝ)*X 1 1+(1039555263/2500000000 : ℝ)*X 1 2+(2164897761/5000000000 : ℝ)*X 2 0+(4508060679/10000000000 : ℝ)*X 2 1+(1039555263/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15946926953333713313607849/1790000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1573736361/100000000000000 : ℝ)*(base19) + (2057638493/100000000000000 : ℝ)*(base23) + (15590669/12500000000000 : ℝ)*(upper2) + (402518409/50000000000000 : ℝ)*(upper3) + (1020992733/100000000000000 : ℝ)*(upper4) + (437780983144511/10000000000000 : ℝ)*(major0) + (437780983144511/10000000000000 : ℝ)*(major1) + (437780983144511/10000000000000 : ℝ)*(major2) + (5917502220629149/100000000000000 : ℝ)*(sp0) + (2958800689701529/50000000000000 : ℝ)*(sp1) + (2958800447750463/50000000000000 : ℝ)*(sp2) + (354749249935991/12500000000000 : ℝ)*(sp3) + (10073251027/10000000000000 : ℝ)*(sp4) + (2801662451/12500000000000 : ℝ)*(sp7) + (177376025799221/6250000000000 : ℝ)*(f.failure) + (5917602953139419/100000000000000 : ℝ)*(f.sum) + (3636174255771/1790000000000000000000000000 : ℝ)*base65 + (34054448368183239/3580000000000000000000000000000 : ℝ)*base67 + (33332809499443239/3580000000000000000000000000000 : ℝ)*base69 + (54447295838403239/3580000000000000000000000000000 : ℝ)*base71 + (3818118774289/1790000000000000000000000000 : ℝ)*base74 + (27797509493563239/3580000000000000000000000000000 : ℝ)*base75 + (31753618801843239/3580000000000000000000000000000 : ℝ)*base77 + (45937202608283239/3580000000000000000000000000000 : ℝ)*base79 + (3182857715211/1790000000000000000000000000 : ℝ)*base81 + (497033/625000000000000000000 : ℝ)*base89 + (497033/625000000000000000000 : ℝ)*base91 + (497033/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (44433401558426126844139029/4475000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1885182551/100000000000000 : ℝ)*(base19) + (1646241737/50000000000000 : ℝ)*(base23) + (288946263/100000000000000 : ℝ)*(lower1) + (274859233/100000000000000 : ℝ)*(upper3) + (353323367/100000000000000 : ℝ)*(lower4) + (1102333272687593/25000000000000 : ℝ)*(major0) + (1102333272687593/25000000000000 : ℝ)*(major1) + (1102333272687593/25000000000000 : ℝ)*(major2) + (41542210237/100000000000000 : ℝ)*(sp2) + (118553039/6250000000000 : ℝ)*(sp3) + (5960213756258719/100000000000000 : ℝ)*(sp4) + (745026483884521/12500000000000 : ℝ)*(sp5) + (372510557597813/6250000000000 : ℝ)*(sp6) + (2858450197418333/100000000000000 : ℝ)*(sp7) + (1429226047133479/50000000000000 : ℝ)*(f.failure) + (5960213756258719/100000000000000 : ℝ)*(f.sum) + (5051347841137/1118750000000000000000000000 : ℝ)*base65 + (8495931686780657/8950000000000000000000000000000 : ℝ)*base67 + (49090640713830657/8950000000000000000000000000000 : ℝ)*base69 + (41627278011530657/8950000000000000000000000000000 : ℝ)*base71 + (42462441169/559375000000000000000000000 : ℝ)*base74 + (128226026639169343/8950000000000000000000000000000 : ℝ)*base76 + (218412303147780657/8950000000000000000000000000000 : ℝ)*base77 + (41227942888419343/8950000000000000000000000000000 : ℝ)*base80 + (14654089324649/2237500000000000000000000000 : ℝ)*base81 + (64020067/5000000000000000000000 : ℝ)*base89 + (64020067/5000000000000000000000 : ℝ)*base91 + (64020067/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1330_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154255973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (147/1000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (139/1250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11121/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14699/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1330_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1330_s8_0 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5349186477/10000000000 : ℝ)*x 0 + (-1070244173/5000000000 : ℝ)*x 1 + (2622145643/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349186477/10000000000 : ℝ)^2145 ≤ (5495495906787/12500000000000 : ℝ)^1633 := by
    have hnat : (5349186477 : ℕ)^2145*12500000000000^1633 ≤ 5495495906787^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349186477 10000000000 5495495906787 12500000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1070244173/5000000000 : ℝ)^2145 ≤ (6600492051587/50000000000000 : ℝ)^1633 := by
    have hnat : (1070244173 : ℕ)^2145*50000000000000^1633 ≤ 6600492051587^1633*5000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070244173 5000000000 6600492051587 50000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622145643/5000000000 : ℝ)^2145 ≤ (10708762158649/25000000000000 : ℝ)^1633 := by
    have hnat : (2622145643 : ℕ)^2145*25000000000000^1633 ≤ 10708762158649^1633*5000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622145643 5000000000 10708762158649 25000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349186477/10000000000 : ℝ), (-1070244173/5000000000 : ℝ), (2622145643/5000000000 : ℝ)] ![(5495495906787/12500000000000 : ℝ), (6600492051587/50000000000000 : ℝ), (10708762158649/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349186477/10000000000 : ℝ)|^2145 ≤ (5495495906787/12500000000000 : ℝ)^1633
        have hw : |(5349186477/10000000000 : ℝ)|=(5349186477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1070244173/5000000000 : ℝ)|^2145 ≤ (6600492051587/50000000000000 : ℝ)^1633
        have hw : |(-1070244173/5000000000 : ℝ)|=(1070244173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622145643/5000000000 : ℝ)|^2145 ≤ (10708762158649/25000000000000 : ℝ)^1633
        have hw : |(2622145643/5000000000 : ℝ)|=(2622145643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1330_s8_1 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-205439883/1000000000 : ℝ)*x 0 + (655611891/1250000000 : ℝ)*x 1 + (1353164449/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (205439883/1000000000 : ℝ)^2145 ≤ (12508017852983/100000000000000 : ℝ)^1633 := by
    have hnat : (205439883 : ℕ)^2145*100000000000000^1633 ≤ 12508017852983^1633*1000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205439883 1000000000 12508017852983 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655611891/1250000000 : ℝ)^2145 ≤ (21420763643847/50000000000000 : ℝ)^1633 := by
    have hnat : (655611891 : ℕ)^2145*50000000000000^1633 ≤ 21420763643847^1633*1250000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655611891 1250000000 21420763643847 50000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1353164449/2500000000 : ℝ)^2145 ≤ (4465045484137/10000000000000 : ℝ)^1633 := by
    have hnat : (1353164449 : ℕ)^2145*10000000000000^1633 ≤ 4465045484137^1633*2500000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353164449 2500000000 4465045484137 10000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-205439883/1000000000 : ℝ), (655611891/1250000000 : ℝ), (1353164449/2500000000 : ℝ)] ![(12508017852983/100000000000000 : ℝ), (21420763643847/50000000000000 : ℝ), (4465045484137/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-205439883/1000000000 : ℝ)|^2145 ≤ (12508017852983/100000000000000 : ℝ)^1633
        have hw : |(-205439883/1000000000 : ℝ)|=(205439883/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655611891/1250000000 : ℝ)|^2145 ≤ (21420763643847/50000000000000 : ℝ)^1633
        have hw : |(655611891/1250000000 : ℝ)|=(655611891/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1353164449/2500000000 : ℝ)|^2145 ≤ (4465045484137/10000000000000 : ℝ)^1633
        have hw : |(1353164449/2500000000 : ℝ)|=(1353164449/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1330_s8_2 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (331607727/625000000 : ℝ)*x 0 + (-1972121867/10000000000 : ℝ)*x 1 + (5412657667/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (331607727/625000000 : ℝ)^2145 ≤ (43495354794219/100000000000000 : ℝ)^1633 := by
    have hnat : (331607727 : ℕ)^2145*100000000000000^1633 ≤ 43495354794219^1633*625000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331607727 625000000 43495354794219 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1972121867/10000000000 : ℝ)^2145 ≤ (5927095872463/50000000000000 : ℝ)^1633 := by
    have hnat : (1972121867 : ℕ)^2145*50000000000000^1633 ≤ 5927095872463^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1972121867 10000000000 5927095872463 50000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5412657667/10000000000 : ℝ)^2145 ≤ (22325226721783/50000000000000 : ℝ)^1633 := by
    have hnat : (5412657667 : ℕ)^2145*50000000000000^1633 ≤ 22325226721783^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412657667 10000000000 22325226721783 50000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(331607727/625000000 : ℝ), (-1972121867/10000000000 : ℝ), (5412657667/10000000000 : ℝ)] ![(43495354794219/100000000000000 : ℝ), (5927095872463/50000000000000 : ℝ), (22325226721783/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(331607727/625000000 : ℝ)|^2145 ≤ (43495354794219/100000000000000 : ℝ)^1633
        have hw : |(331607727/625000000 : ℝ)|=(331607727/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1972121867/10000000000 : ℝ)|^2145 ≤ (5927095872463/50000000000000 : ℝ)^1633
        have hw : |(-1972121867/10000000000 : ℝ)|=(1972121867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5412657667/10000000000 : ℝ)|^2145 ≤ (22325226721783/50000000000000 : ℝ)^1633
        have hw : |(5412657667/10000000000 : ℝ)|=(5412657667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1330_s8_3 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (106114471/200000000 : ℝ)*x 0 + (2706328833/5000000000 : ℝ)*x 1 + (-1972121981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106114471/200000000 : ℝ)^2145 ≤ (8699070782247/20000000000000 : ℝ)^1633 := by
    have hnat : (106114471 : ℕ)^2145*20000000000000^1633 ≤ 8699070782247^1633*200000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106114471 200000000 8699070782247 20000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2706328833/5000000000 : ℝ)^2145 ≤ (4465045343273/10000000000000 : ℝ)^1633 := by
    have hnat : (2706328833 : ℕ)^2145*10000000000000^1633 ≤ 4465045343273^1633*5000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706328833 5000000000 4465045343273 10000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1972121981/10000000000 : ℝ)^2145 ≤ (2963548161253/25000000000000 : ℝ)^1633 := by
    have hnat : (1972121981 : ℕ)^2145*25000000000000^1633 ≤ 2963548161253^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1972121981 10000000000 2963548161253 25000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(106114471/200000000 : ℝ), (2706328833/5000000000 : ℝ), (-1972121981/10000000000 : ℝ)] ![(8699070782247/20000000000000 : ℝ), (4465045343273/10000000000000 : ℝ), (2963548161253/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(106114471/200000000 : ℝ)|^2145 ≤ (8699070782247/20000000000000 : ℝ)^1633
        have hw : |(106114471/200000000 : ℝ)|=(106114471/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2706328833/5000000000 : ℝ)|^2145 ≤ (4465045343273/10000000000000 : ℝ)^1633
        have hw : |(2706328833/5000000000 : ℝ)|=(2706328833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1972121981/10000000000 : ℝ)|^2145 ≤ (2963548161253/25000000000000 : ℝ)^1633
        have hw : |(-1972121981/10000000000 : ℝ)|=(1972121981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1330_s8_4 (p : ℝ) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1082448921/2500000000 : ℝ)*x 0 + (2254021837/5000000000 : ℝ)*x 1 + (4158238329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1082448921/2500000000 : ℝ)^2145 ≤ (16651670395097/50000000000000 : ℝ)^1633 := by
    have hnat : (1082448921 : ℕ)^2145*50000000000000^1633 ≤ 16651670395097^1633*2500000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082448921 2500000000 16651670395097 50000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2254021837/5000000000 : ℝ)^2145 ≤ (702314826173/2000000000000 : ℝ)^1633 := by
    have hnat : (2254021837 : ℕ)^2145*2000000000000^1633 ≤ 702314826173^1633*5000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254021837 5000000000 702314826173 2000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4158238329/10000000000 : ℝ)^2145 ≤ (31580917886087/100000000000000 : ℝ)^1633 := by
    have hnat : (4158238329 : ℕ)^2145*100000000000000^1633 ≤ 31580917886087^1633*10000000000^2145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4158238329 10000000000 31580917886087 100000000000000 2145 1633 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2145/512 : ℝ)) 2145 1633 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1082448921/2500000000 : ℝ), (2254021837/5000000000 : ℝ), (4158238329/10000000000 : ℝ)] ![(16651670395097/50000000000000 : ℝ), (702314826173/2000000000000 : ℝ), (31580917886087/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1082448921/2500000000 : ℝ)|^2145 ≤ (16651670395097/50000000000000 : ℝ)^1633
        have hw : |(1082448921/2500000000 : ℝ)|=(1082448921/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2254021837/5000000000 : ℝ)|^2145 ≤ (702314826173/2000000000000 : ℝ)^1633
        have hw : |(2254021837/5000000000 : ℝ)|=(2254021837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4158238329/10000000000 : ℝ)|^2145 ≤ (31580917886087/100000000000000 : ℝ)^1633
        have hw : |(4158238329/10000000000 : ℝ)|=(4158238329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1330_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154255973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14699/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11121/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11121/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7349/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14699/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11121/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14699/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11121/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14699/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11121/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14699/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11121/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14699/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11121/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14699/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11121/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11121/100000 : ℝ) ^ (4289/1024 : ℝ) ≤ (10111040104525033/100000000000000000000 : ℝ) := by
    have hpowers : (11121/100000 : ℝ)^4289 ≤ (10111040104525033/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11121 : ℕ)^4289*100000000000000000000^1024 ≤ 10111040104525033^1024*100000^4289 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11121 100000 10111040104525033 100000000000000000000 4289 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11121/100000 : ℝ)) (X := (10111040104525033/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4289 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14699/100000 : ℝ) ^ (4289/1024 : ℝ) ≤ (8131008842556273/25000000000000000000 : ℝ) := by
    have hpowers : (14699/100000 : ℝ)^4289 ≤ (8131008842556273/25000000000000000000 : ℝ)^1024 := by
      have hnat : (14699 : ℕ)^4289*25000000000000000000^1024 ≤ 8131008842556273^1024*100000^4289 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14699 100000 8131008842556273 25000000000000000000 4289 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14699/100000 : ℝ)) (X := (8131008842556273/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4289 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010111040104525033/50000000000000000000 : ℝ) ≤ (5000241382798653/5000000000000000 : ℝ) ^ (4289/1024 : ℝ) := by
    have hpowers : (50010111040104525033/50000000000000000000 : ℝ)^1024 ≤ (5000241382798653/5000000000000000 : ℝ)^4289 := by
      have hnat : (50010111040104525033 : ℕ)^1024*5000000000000000^4289 ≤ 5000241382798653^4289*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010111040104525033 50000000000000000000 5000241382798653 5000000000000000 1024 4289 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000241382798653/5000000000000000 : ℝ)) (X := (50010111040104525033/50000000000000000000 : ℝ)) (by norm_num) 4289 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (800341080603798001/800000000000000000 : ℝ) ≤ (5000508874262073/5000000000000000 : ℝ) ^ (4289/1024 : ℝ) := by
    have hpowers : (800341080603798001/800000000000000000 : ℝ)^1024 ≤ (5000508874262073/5000000000000000 : ℝ)^4289 := by
      have hnat : (800341080603798001 : ℕ)^1024*5000000000000000^4289 ≤ 5000508874262073^4289*800000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        800341080603798001 800000000000000000 5000508874262073 5000000000000000 1024 4289 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000508874262073/5000000000000000 : ℝ)) (X := (800341080603798001/800000000000000000 : ℝ)) (by norm_num) 4289 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508131008842556273/12500000000000000000 : ℝ) ≤ (5000776365725493/5000000000000000 : ℝ) ^ (4289/1024 : ℝ) := by
    have hpowers : (12508131008842556273/12500000000000000000 : ℝ)^1024 ≤ (5000776365725493/5000000000000000 : ℝ)^4289 := by
      have hnat : (12508131008842556273 : ℕ)^1024*5000000000000000^4289 ≤ 5000776365725493^4289*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508131008842556273 12500000000000000000 5000776365725493 5000000000000000 1024 4289 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000776365725493/5000000000000000 : ℝ)) (X := (12508131008842556273/12500000000000000000 : ℝ)) (by norm_num) 4289 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10111040104525033/100000000000000000000 : ℝ) ≤ ((8942457061262096397/8945000000000000000 : ℝ)+2*(13374573171/8945000000000 : ℝ)*(11121/100000 : ℝ))^(4289/1024 : ℝ) := by
    rw [show (8942457061262096397/8945000000000000000 : ℝ)+2*(13374573171/8945000000000 : ℝ)*(11121/100000 : ℝ)=(5000241382798653/5000000000000000 : ℝ) by norm_num, show 1+2*(10111040104525033/100000000000000000000 : ℝ)=(50010111040104525033/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8131008842556273/25000000000000000000 : ℝ)+(10111040104525033/100000000000000000000 : ℝ) ≤ ((8942457061262096397/8945000000000000000 : ℝ)+(13374573171/8945000000000 : ℝ)*((14699/100000 : ℝ)+(11121/100000 : ℝ)))^(4289/1024 : ℝ) := by
    rw [show (8942457061262096397/8945000000000000000 : ℝ)+(13374573171/8945000000000 : ℝ)*((14699/100000 : ℝ)+(11121/100000 : ℝ))=(5000508874262073/5000000000000000 : ℝ) by norm_num, show 1+(8131008842556273/25000000000000000000 : ℝ)+(10111040104525033/100000000000000000000 : ℝ)=(800341080603798001/800000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8131008842556273/25000000000000000000 : ℝ) ≤ ((8942457061262096397/8945000000000000000 : ℝ)+2*(13374573171/8945000000000 : ℝ)*(14699/100000 : ℝ))^(4289/1024 : ℝ) := by
    rw [show (8942457061262096397/8945000000000000000 : ℝ)+2*(13374573171/8945000000000 : ℝ)*(14699/100000 : ℝ)=(5000776365725493/5000000000000000 : ℝ) by norm_num, show 1+2*(8131008842556273/25000000000000000000 : ℝ)=(12508131008842556273/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8942457061262096397/8945000000000000000 : ℝ)*(X 1 0+X 2 0)+(13374573171/8945000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4289/1024 : ℝ)) (lo := (11121/100000 : ℝ)) (hi := (14699/100000 : ℝ)) (c := (8942457061262096397/8945000000000000000 : ℝ)) (alpha := (13374573171/8945000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8942457061262096397/8945000000000000000 : ℝ)*(X 0 1+X 2 1)+(13374573171/8945000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4289/1024 : ℝ)) (lo := (11121/100000 : ℝ)) (hi := (14699/100000 : ℝ)) (c := (8942457061262096397/8945000000000000000 : ℝ)) (alpha := (13374573171/8945000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8942457061262096397/8945000000000000000 : ℝ)*(X 0 2+X 1 2)+(13374573171/8945000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4289/1024 : ℝ)) (lo := (11121/100000 : ℝ)) (hi := (14699/100000 : ℝ)) (c := (8942457061262096397/8945000000000000000 : ℝ)) (alpha := (13374573171/8945000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((5349186477/10000000000 : ℝ)*X 1 0+(-1070244173/5000000000 : ℝ)*X 1 1+(2622145643/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s8_0 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-205439883/1000000000 : ℝ)*X 0 0+(655611891/1250000000 : ℝ)*X 0 1+(1353164449/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s8_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((331607727/625000000 : ℝ)*X 1 0+(-1972121867/10000000000 : ℝ)*X 1 1+(5412657667/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s8_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((106114471/200000000 : ℝ)*X 2 0+(2706328833/5000000000 : ℝ)*X 2 1+(-1972121981/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s8_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((1082448921/2500000000 : ℝ)*X 0 0+(2254021837/5000000000 : ℝ)*X 0 1+(4158238329/10000000000 : ℝ)*X 0 2+(1082448921/2500000000 : ℝ)*X 1 0+(2254021837/5000000000 : ℝ)*X 1 1+(4158238329/10000000000 : ℝ)*X 1 2+(1082448921/2500000000 : ℝ)*X 2 0+(2254021837/5000000000 : ℝ)*X 2 1+(4158238329/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1330_s8_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (172077623572055756023848057/44725000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (598159701/100000000000000 : ℝ)*(base19) + (514947067/100000000000000 : ℝ)*(base23) + (22867617/25000000000000 : ℝ)*(lower1) + (29320233/50000000000000 : ℝ)*(upper3) + (16961943/100000000000000 : ℝ)*(lower4) + (23194059/100000000000000 : ℝ)*(upper5) + (440976193623927/10000000000000 : ℝ)*(major0) + (440976193623927/10000000000000 : ℝ)*(major1) + (440976193623927/10000000000000 : ℝ)*(major2) + (2814763837/100000000000000 : ℝ)*(sp0) + (2980396820481167/50000000000000 : ℝ)*(sp1) + (1490197557009699/25000000000000 : ℝ)*(sp2) + (1490198281503817/25000000000000 : ℝ)*(sp3) + (1429365051633777/50000000000000 : ℝ)*(sp4) + (1429365051633777/50000000000000 : ℝ)*(f.failure) + (2980396820481167/50000000000000 : ℝ)*(f.sum) + (2188519235811/447250000000000000000000000 : ℝ)*base66 + (78747046018091019/89450000000000000000000000000000 : ℝ)*base67 + (220433773321808981/89450000000000000000000000000000 : ℝ)*base70 + (766952085031958981/89450000000000000000000000000000 : ℝ)*base72 + (1711151128319/894500000000000000000000000 : ℝ)*base74 + (41750014224308981/89450000000000000000000000000000 : ℝ)*base76 + (168361815998508981/89450000000000000000000000000000 : ℝ)*base78 + (298334654432891019/89450000000000000000000000000000 : ℝ)*base79 + (2281854379391/894500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (10800021/5000000000000000000000 : ℝ)*base89 + (10800021/5000000000000000000000 : ℝ)*base91 + (10800021/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1330_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154255973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14699/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11121/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11121/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7349/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1330_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1330_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154255973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14709/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1389/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11121/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7349/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1330_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1330_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1330_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4289/1024 : ℝ) ≤ p) (hpb : p ≤ (2145/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154255973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14709/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1389/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11121/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7349/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1330_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
